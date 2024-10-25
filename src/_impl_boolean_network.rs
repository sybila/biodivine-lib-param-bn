use crate::symbolic_async_graph::{RegulationConstraint, SymbolicContext};
use crate::Monotonicity::Inhibition;
use crate::{
    BooleanNetwork, FnUpdate, Monotonicity, Parameter, ParameterId, ParameterIdIterator,
    RegulatoryGraph, Variable, VariableId, VariableIdIterator, ID_REGEX,
};
use std::collections::{HashMap, HashSet};
use std::ops::Index;
use std::path::Path;
use Monotonicity::Activation;

/// Basic methods for safely building `BooleanNetwork`s.
impl BooleanNetwork {
    /// Build a copy of this Boolean network where all essentiality and monotonicity constraints
    /// are removed. This is basically the "inverse" of [BooleanNetwork::infer_valid_graph].
    pub fn remove_static_constraints(&self) -> BooleanNetwork {
        let mut new_bn = self.clone();
        for reg in self.as_graph().regulations() {
            new_bn
                .graph
                .remove_regulation(reg.regulator, reg.target)
                .unwrap();
            let mut reg = reg.clone();
            reg.observable = false;
            reg.monotonicity = None;
            new_bn.graph.add_raw_regulation(reg).unwrap();
        }
        new_bn
    }

    /// Construct a new `BooleanNetwork` from a `RegulatoryGraph` without any parameters.
    pub fn new(graph: RegulatoryGraph) -> BooleanNetwork {
        BooleanNetwork {
            update_functions: vec![None; graph.num_vars()],
            graph,
            parameters: Vec::new(),
            parameter_to_index: HashMap::new(),
        }
    }

    pub fn try_from_file<T: AsRef<Path>>(path: T) -> Result<BooleanNetwork, String> {
        let path: &Path = path.as_ref();
        let extension = path.extension().and_then(|it| it.to_str());
        let is_aeon = extension == Some("aeon");
        let is_bnet = extension == Some("bnet");
        let is_sbml = extension == Some("sbml");
        if is_aeon || is_bnet || is_sbml {
            let content = std::fs::read_to_string(path);
            match content {
                Ok(content) => {
                    if is_aeon {
                        Self::try_from(content.as_str())
                    } else if is_bnet {
                        Self::try_from_bnet(content.as_str())
                    } else {
                        Self::try_from_sbml(content.as_str()).map(|(x, _)| x)
                    }
                }
                Err(e) => Err(format!("File not readable: {}", e)),
            }
        } else {
            Err("Unknown file format.".to_string())
        }
    }

    /// Add a new `Parameter` to the `BooleanNetwork`.
    ///
    /// The parameter name must be different from other parameters and variables.
    pub fn add_parameter(&mut self, name: &str, arity: u32) -> Result<ParameterId, String> {
        self.assert_no_such_variable(name)?;
        self.assert_no_such_parameter(name)?;
        let id = ParameterId(self.parameters.len());
        self.parameter_to_index.insert(name.to_string(), id);
        self.parameters.push(Parameter::new(name, arity));
        Ok(id)
    }

    /// Set parameter name. This should be relatively safe since we use IDs everywhere.
    fn rename_parameter(&mut self, parameter: ParameterId, new_name: &str) -> Result<(), String> {
        self.assert_no_such_parameter(new_name)?;
        let param = self.parameters.get_mut(parameter.to_index()).unwrap();
        self.parameter_to_index.remove(param.name.as_str());
        param.name = new_name.to_string();
        self.parameter_to_index
            .insert(param.name.clone(), parameter);
        Ok(())
    }

    /// Add a new `UpdateFunction` to the `BooleanNetwork`.
    ///
    /// The variable must not already have an update function. We assume all the variables
    /// and parameters in the function are used correctly. If you are not sure how to safely
    /// build an instance of a `FnUpdate`, look at the variants of this method which parse
    /// the function safely from a string.
    pub fn add_update_function(
        &mut self,
        variable: VariableId,
        function: FnUpdate,
    ) -> Result<(), String> {
        self.assert_no_update_function(variable)?;
        self.assert_arguments_are_valid(variable, function.collect_arguments())?;
        self.update_functions[variable.0] = Some(function);
        Ok(())
    }

    /// Allows to directly replace (or remove) the update function.
    ///
    /// The function will replace existing function (if any), but it still needs to satisfy
    /// the declared regulations.
    pub fn set_update_function(
        &mut self,
        variable: VariableId,
        function: Option<FnUpdate>,
    ) -> Result<(), String> {
        if let Some(function) = function.as_ref() {
            self.assert_arguments_are_valid(variable, function.collect_arguments())?;
        }
        self.update_functions[variable.0] = function;
        Ok(())
    }

    /// **(internal)** Utility method to ensure that a parameter is also not a variable.
    fn assert_no_such_variable(&self, name: &str) -> Result<(), String> {
        if self.graph.find_variable(name).is_none() {
            Ok(())
        } else {
            Err(format!(
                "Cannot add parameter. '{}' is already a variable.",
                name
            ))
        }
    }

    /// **(internal)** Utility method to ensure that a parameter is not a duplicate.
    fn assert_no_such_parameter(&self, name: &str) -> Result<(), String> {
        if self.find_parameter(name).is_none() {
            Ok(())
        } else {
            Err(format!("Cannot add parameter. '{}' already added.", name))
        }
    }

    /// **(internal)** Utility method to ensure that an update function is not set yet.
    fn assert_no_update_function(&self, variable: VariableId) -> Result<(), String> {
        if self.update_functions[variable.0].is_none() {
            Ok(())
        } else {
            Err(format!(
                "Cannot set update function for {}. Function already set.",
                self.graph.get_variable(variable)
            ))
        }
    }

    /// **(internal)** Utility method to check that the arguments of a function are a subset
    /// of the actual regulators.
    pub(crate) fn assert_arguments_are_valid(
        &self,
        variable: VariableId,
        actual: Vec<VariableId>,
    ) -> Result<(), String> {
        let expected = self.graph.regulators(variable);
        let mut i_expected = 0;
        let mut i_actual = 0;
        while i_expected < expected.len() && i_actual < actual.len() {
            if expected[i_expected] == actual[i_actual] {
                i_actual += 1;
            }
            i_expected += 1;
        }
        return if i_actual == actual.len() {
            Ok(())
        } else {
            let expected_names: Vec<String> = expected
                .into_iter()
                .map(|v| self.graph.get_variable(v).name.clone())
                .collect();
            let actual_names: Vec<String> = actual
                .into_iter()
                .map(|v| self.graph.get_variable(v).name.clone())
                .collect();
            let var_name = self.graph.get_variable(variable);
            Err(format!(
                "Variable '{}' is regulated by {:?}, but {:?} were found as arguments",
                var_name, expected_names, actual_names
            ))
        };
    }
}

/// Some utility methods for accessing the structure of a `BooleanNetwork`. Some of them are just
/// delegating to the internal `RegulatoryGraph`, but we have a copy here as well because they
/// are used very often.
impl BooleanNetwork {
    /// Obtain a reference to the underlying `RegulatoryGraph` of the `BooleanNetwork`.
    pub fn as_graph(&self) -> &RegulatoryGraph {
        &self.graph
    }

    /// Obtain a mutable reference to the underlying `RegulatoryGraph`.
    ///
    /// However, note that at the moment, you can't really do much with this reference, only
    /// add new regulations.
    pub fn as_graph_mut(&mut self) -> &mut RegulatoryGraph {
        &mut self.graph
    }

    /// The number of variables in this `BooleanNetwork`.
    pub fn num_vars(&self) -> usize {
        self.graph.num_vars()
    }

    /// The number of *explicit* parameters in this `BooleanNetwork` (there can be network
    /// variables using erased functions--implicit parameters--that are not counted here).
    pub fn num_parameters(&self) -> usize {
        self.parameters.len()
    }

    /// The number of variables with erased update functions in this `BooleanNetwork`.
    pub fn num_implicit_parameters(&self) -> usize {
        self.update_functions
            .iter()
            .filter(|it| it.is_none())
            .count()
    }

    /// Return an iterator over all variable ids of this network.
    pub fn variables(&self) -> VariableIdIterator {
        self.graph.variables()
    }

    /// Return the variable object based on the given `VariableId`.
    pub fn get_variable(&self, id: VariableId) -> &Variable {
        self.graph.get_variable(id)
    }

    /// Shorthand for `self.as_graph().get_variable(id).get_name()`.
    pub fn get_variable_name(&self, id: VariableId) -> &String {
        self.graph.get_variable_name(id)
    }

    /// Return a sorted list of variables that regulate the given `target` variable.
    pub fn regulators(&self, target: VariableId) -> Vec<VariableId> {
        self.graph.regulators(target)
    }

    /// Return a sorted list of variables that are regulated by the given `regulator` variable.
    pub fn targets(&self, regulator: VariableId) -> Vec<VariableId> {
        self.graph.targets(regulator)
    }

    /// Find a `ParameterId` corresponding to the given parameter `name`.
    pub fn find_parameter(&self, name: &str) -> Option<ParameterId> {
        self.parameter_to_index.get(name).cloned()
    }

    /// Get a `Parameter` corresponding to the given `ParameterId`.
    pub fn get_parameter(&self, id: ParameterId) -> &Parameter {
        &self.parameters[id.0]
    }

    /// Get a `FnUpdate` corresponding to the given `VariableId`.
    pub fn get_update_function(&self, variable: VariableId) -> &Option<FnUpdate> {
        &self.update_functions[variable.0]
    }

    /// Return an iterator over all parameter ids of this network.
    pub fn parameters(&self) -> ParameterIdIterator {
        (0..self.parameters.len()).map(ParameterId)
    }

    /// Iterate over all variables of this network that do not have update functions
    /// assigned for them.
    pub fn implicit_parameters(&self) -> Vec<VariableId> {
        (0..self.update_functions.len())
            .filter(|it| self.update_functions[*it].is_none())
            .map(VariableId)
            .collect()
    }

    /// A static check that allows to verify validity of a parameter or variable name.
    pub fn is_valid_name(name: &str) -> bool {
        ID_REGEX.is_match(name)
    }

    /// Compute the set of network variables which depend (syntactically) on the
    /// given `parameter`.
    pub fn parameter_appears_in(&self, parameter: ParameterId) -> HashSet<VariableId> {
        self.variables()
            .filter(|var| {
                self.get_update_function(*var)
                    .as_ref()
                    .map(|it| it.contains_parameter(parameter))
                    .unwrap_or(false)
            })
            .collect()
    }

    /// Return a copy of this network where all unused parameters (uninterpreted functions)
    /// are removed.
    ///
    /// Note that `VariableId` objects are still valid for the result network, but `ParameterId`
    /// objects can now refer to different parameters.
    pub fn prune_unused_parameters(&self) -> BooleanNetwork {
        let mut used = HashSet::new();
        for var in self.variables() {
            if let Some(update) = self.get_update_function(var) {
                used.extend(update.collect_parameters().into_iter());
            }
        }

        if used.len() == self.num_parameters() {
            // Skip analysis if all parameters are used.
            return self.clone();
        }

        // Ensure the parameter ordering is as similar as possible.
        let mut used = Vec::from_iter(used);
        used.sort();

        let mut new_bn = BooleanNetwork::new(self.graph.clone());
        let mut old_to_new_map = HashMap::new();
        for old_id in used {
            let old_param = &self[old_id];
            let new_id = new_bn
                .add_parameter(old_param.name.as_str(), old_param.arity)
                .unwrap_or_else(|_| {
                    unreachable!("Parameter was valid in the old BN.");
                });
            old_to_new_map.insert(old_id, new_id);
        }

        let empty = HashMap::new();
        for var in self.variables() {
            if let Some(update) = self.get_update_function(var) {
                let update = update.rename_all(&empty, &old_to_new_map);
                new_bn
                    .set_update_function(var, Some(update))
                    .unwrap_or_else(|_| unreachable!("Function was valid in the old BN."));
            }
        }

        new_bn
    }
}

impl BooleanNetwork {
    /// Infer a *sufficient local regulatory graph* based on the update functions of
    /// this `BooleanNetwork`.
    ///
    /// ## Notes
    ///
    ///  - The method will simplify the update functions when it detects that a variable
    ///    is not an essential input of the update function (for any instantiation).
    ///  - This also removes any unused parameters (uninterpreted functions), or parameters that
    ///    become unused due to the transformation.
    ///  - For fully specified update functions, the method simply updates the regulations to
    ///    match the actual behaviour of the function (i.e. any non-essential regulations are
    ///    removed, monotonicity is always specified unless the input is truly non-monotonic).
    ///  - For regulations that interact with uninterpreted functions:
    ///     - Observability: If there are no instantiations where the regulation is essential,
    ///       we remove the regulation completely. Otherwise, we preserve the original
    ///       observability constraint.
    ///     - Monotonicity: Similarly, if every instantiation of the function has a known
    ///       monotonicity, then we use this monotonicity. Otherwise, if the original constraint
    ///       is still satisfied for a subset of all instantiations, we use the original one.
    ///
    /// ## Limitations
    ///
    /// The result only guarantees that the constraints are *locally consistent**, meaning they
    /// are valid when applied to the singular update function, not necessarily the whole model.
    /// In other words, uninterpreted functions that are used by multiple variables can still cause
    /// the model to be invalid if they use contradictory constraints, but this usually cannot be
    /// resolved deterministically.
    ///
    /// ## Output
    ///
    /// The function can fail we, for whatever reason, cannot create [SymbolicContext] for
    /// the old network.
    ///
    pub fn infer_valid_graph(&self) -> Result<BooleanNetwork, String> {
        let mut old_bn = self.prune_unused_parameters();
        let ctx = SymbolicContext::new(&old_bn)?;

        // Copying the old variable names means VariableId objects should be still valid.
        let var_names = old_bn.as_graph().variable_names();

        // Now we can recreate the regulatory graph from scratch:
        let mut new_rg = RegulatoryGraph::new(var_names);
        for target_var in old_bn.variables() {
            if let Some(function) = old_bn.get_update_function(target_var) {
                let fn_is_true = ctx.mk_fn_update_true(function);

                for regulator_var in old_bn.regulators(target_var) {
                    let old_regulation = old_bn
                        .as_graph()
                        .find_regulation(regulator_var, target_var)
                        .unwrap_or_else(|| {
                            unreachable!("Regulation must exist.");
                        });

                    let Some(regulation) =
                        RegulationConstraint::fix_regulation(&ctx, old_regulation, &fn_is_true)
                    else {
                        // The regulator is completely unused. We can replace it with a constant
                        // and simplify the function.
                        let function = old_bn
                            .get_update_function(target_var)
                            .as_ref()
                            .unwrap_or_else(|| {
                                unreachable!("We already know `target_var` has a function.");
                            });
                        let function = function
                            .substitute_variable(regulator_var, &FnUpdate::Const(false))
                            .simplify_constants();
                        old_bn
                            .set_update_function(target_var, Some(function))
                            .unwrap_or_else(|_| {
                                unreachable!("Transformed function should be also valid.");
                            });
                        continue;
                    };

                    new_rg.add_raw_regulation(regulation).unwrap_or_else(|_| {
                        unreachable!("The regulation must be valid.");
                    })
                }
            } else {
                // If the update function is missing, just copy the existing regulators.
                // Any constraint is satisfiable with an unknown function.
                for regulator_var in old_bn.regulators(target_var) {
                    let old_regulation = old_bn
                        .as_graph()
                        .find_regulation(regulator_var, target_var)
                        .unwrap_or_else(|| {
                            unreachable!("Regulation must exist.");
                        });
                    new_rg
                        .add_raw_regulation(old_regulation.clone())
                        .unwrap_or_else(|_| {
                            unreachable!("The regulation must be valid.");
                        });
                }
            }
        }

        // Next, we create a new BN and copy over the (potentially simplified) functions.
        let mut new_bn = BooleanNetwork::new(new_rg);

        // Copy over existing parameters
        for parameter_id in old_bn.parameters() {
            let parameter = &old_bn[parameter_id];
            new_bn
                .add_parameter(&parameter.name, parameter.arity)
                .unwrap_or_else(|_| {
                    unreachable!("Parameter was valid in the old network.");
                });
        }

        for var in old_bn.variables() {
            if let Some(update) = old_bn.get_update_function(var) {
                // At this point, all non-essential variables are already removed from the
                // function and we can thus safely copy it into the new network.
                new_bn
                    .set_update_function(var, Some(update.clone()))
                    .unwrap_or_else(|_| {
                        unreachable!("The transformed function must be valid.");
                    });
            }
        }

        // In the end, we still have to prune the network in case we just made some uninterpreted
        // function irrelevant by eliminating unused inputs.
        Ok(new_bn.prune_unused_parameters())
    }

    /// Similar to [BooleanNetwork::inline_inputs], but inlines constant values (i.e. `x=true` or
    /// `x=false`).
    ///
    /// By default, the constant check is purely syntactic, but we do perform basic constant
    /// propagation (e.g. `x | true = true`) in order to catch the most obvious non-trivial cases.
    /// However, you can set `infer_constants` to `true`, in which case a symbolic method will
    /// be used to check if the variable uses a constant function. Note that this can also
    /// eliminate parameters in some cases (e.g. inlining `x=true` into `y=x | f(z)`).
    ///
    /// Furthermore, similar to [BooleanNetwork::inline_inputs], you can set `repair_graph` to
    /// `true` in order to fix any inconsistent regulations that arise due to the inlining
    /// (this is highly recommended if you are using `infer_constants`).
    ///
    /// The inlining is performed iteratively, meaning if the inlining produces a new constant,
    /// it is eventually also inlined.
    ///
    /// ## Panics
    ///
    /// The method can fail if `infer_constants` or `repair_graph` is specified and the network
    /// does not have a valid symbolic representation.
    pub fn inline_constants(&self, infer_constants: bool, repair_graph: bool) -> BooleanNetwork {
        let mut result = self.clone();
        'inlining: loop {
            // These are two very similar algorithms, but we don't want to create the context
            // needlessly if we don't have to.
            if infer_constants {
                let ctx = SymbolicContext::new(&result).unwrap_or_else(|_| {
                    panic!("Cannot create symbolic context for a network.");
                });
                for var in result.variables() {
                    if let Some(update) = result.get_update_function(var) {
                        // Even if the value is not constant, we want to do constant propagation,
                        // just in case it makes the problem simpler.
                        let update_simplified = update.simplify_constants();
                        let is_constant = update_simplified.as_const();
                        result
                            .set_update_function(var, Some(update_simplified))
                            .unwrap_or_else(|_| {
                                unreachable!(
                                    "A simplified function can always replace the original."
                                )
                            });
                        if is_constant.is_some() {
                            result = result.inline_variable_internal(var, repair_graph);
                            continue 'inlining;
                        }

                        // If constant propagation failed, we can recompute the
                        // result symbolically.
                        let update = result
                            .get_update_function(var)
                            .as_ref()
                            .unwrap_or_else(|| unreachable!("The function is known (see above)."));
                        let fn_is_true = ctx.mk_fn_update_true(update);
                        let constant = if fn_is_true.is_true() {
                            Some(true)
                        } else if fn_is_true.is_false() {
                            Some(false)
                        } else {
                            None
                        };
                        if let Some(value) = constant {
                            // "Clean up" the function before inlining it.
                            result
                                .set_update_function(var, Some(FnUpdate::Const(value)))
                                .unwrap_or_else(|_| {
                                    unreachable!("Constant function should be always allowed.");
                                });
                            result = result.inline_variable_internal(var, repair_graph);
                            // The network has changed, so we need to recreate the symbolic context.
                            continue 'inlining;
                        }
                    }
                }
            } else {
                for var in result.variables() {
                    if let Some(update) = result.get_update_function(var) {
                        // This is necessary to enable propagation beyond the first iteration,
                        // because we need to be able to detect things like `x | true` as `true`.
                        let update_simplified = update.simplify_constants();
                        let is_constant = update_simplified.as_const();
                        result
                            .set_update_function(var, Some(update_simplified))
                            .unwrap_or_else(|_| {
                                unreachable!(
                                    "A simplified function can always repalce the original."
                                )
                            });
                        if is_constant.is_some() {
                            result = result.inline_variable_internal(var, repair_graph);
                            continue 'inlining;
                        }
                    }
                }
            }
            // If nothing was inlined, we can stop.
            break;
        }
        result
    }

    /// Try to inline the input nodes (variables) of the network as logical parameters
    /// (uninterpreted functions of arity 0).
    ///
    /// Here, an "input" is a variable `x` such that:
    ///   - `x` has no incoming regulations and a missing update function.
    ///   - `x` has an identity update function. This is either checked syntactically (default),
    ///     or semantically using BDDs (if `infer_inputs` is set to `true`).
    ///
    /// Note that this does not include constant nodes (e.g. `x=true`). These are handled
    /// separately by [BooleanNetwork::inline_constants]. Also note that input variables that
    /// do not influence any other variable are removed.
    ///
    /// Variables with update functions `x=f(true, false)` or `x=a` (where `a` is a zero-arity
    /// parameter) are currently not considered to be inputs, although their role is conceptually
    /// similar.
    ///
    /// This method is equivalent to calling [BooleanNetwork::inline_variable] on each input,
    /// but the current implementation of [BooleanNetwork::inline_variable] does not permit
    /// inlining of self-regulating variables, hence we have a special method for inputs only.
    ///
    /// Finally, just as [BooleanNetwork::inline_variable], the method can generate an
    /// inconsistent regulatory graph. If `repair_graph` is set to true, the static properties
    /// of relevant regulations are inferred using BDDs.
    ///
    pub fn inline_inputs(&self, infer_inputs: bool, repair_graph: bool) -> BooleanNetwork {
        let inputs: Vec<VariableId> = {
            if infer_inputs {
                let ctx = SymbolicContext::new(self).unwrap_or_else(|_| {
                    panic!("Cannot create symbolic context for a network.");
                });
                self.variables()
                    .filter(|it| {
                        // Check if the variable is an input.
                        let has_no_regulators = self.as_graph().regulators(*it).is_empty();
                        let has_update_function = self.get_update_function(*it).is_some();
                        let is_free_input = has_no_regulators && !has_update_function;

                        let has_identity_update =
                            if let Some(update) = self.get_update_function(*it) {
                                let bdd_var = ctx.get_state_variable(*it);
                                let bdd_identity = ctx.bdd_variable_set().mk_var(bdd_var);
                                let bdd_fn = ctx.mk_fn_update_true(update);

                                bdd_fn.iff(&bdd_identity).is_true()
                            } else {
                                false
                            };
                        is_free_input || has_identity_update
                    })
                    .collect()
            } else {
                self.variables()
                    .filter(|it| {
                        // Check if the variable is an input.
                        let has_no_regulators = self.as_graph().regulators(*it).is_empty();
                        let has_update_function = self.get_update_function(*it).is_some();
                        let is_free_input = has_no_regulators && !has_update_function;

                        let has_identity_update =
                            self.get_update_function(*it) == &Some(FnUpdate::Var(*it));
                        is_free_input || has_identity_update
                    })
                    .collect()
            }
        };

        /*
           This is not super efficient, because we make a new copy of the BN every time,
           but we also want to avoid copying the inlining logic here, because it is already
           sufficiently complex.
        */

        let mut result = self.clone();
        for input in inputs {
            let name = self.get_variable_name(input);
            let new_id = result.as_graph().find_variable(name).unwrap();
            // Simplify the function for the purposes of inlining.
            if result.get_update_function(new_id).is_some() {
                result
                    .set_update_function(new_id, Some(FnUpdate::Var(new_id)))
                    .unwrap_or_else(|_| {
                        println!("Identity update must be allowed for these variables.");
                    });
            }
            result = result.inline_variable_internal(new_id, repair_graph);
        }

        result
    }

    /// Produce a new [BooleanNetwork] where the given [VariableId] `var` has been eliminated
    /// by inlining its update function into all downstream variables.
    ///
    /// Note that the inlining operation is purely syntactic. This means that even if we create
    /// new regulations when relevant, the resulting regulatory graph may be inconsistent with
    /// the update functions. If you set `repair_graph` to `true`, the method will perform
    /// semantic analysis on the new functions and repair regulatory graph where relevant.
    /// If `repair_graph` is set to `false`, the operation does not perform any post-processing.
    ///
    ///  > A simple example where "inconsistent" regulatory graph is produced is the inlining
    ///  > of a constant input variable `f_a = true` into the update function `f_c = a | b`.
    ///  > Here, we have regulations `a -> c` and `b -> c`. However, for the inlined function,
    ///  > we have `f_c = (true | b) = true`. As such, `b` is no longer observable in `f_c` and
    ///  > the resulting model is thus not "logically consistent". We need to either fix this
    ///  > manually, or using [BooleanNetwork::infer_valid_graph].
    ///
    /// ### Limitations
    ///
    /// **At the moment, the reduced variable cannot have a self-regulation.** If such a variable
    /// is targeted with reduction, the result is `None`. If a variable is inlined into a missing
    /// function, the function is given a name as a new parameter, and the variable is inlined
    /// into this new parameter function.
    ///
    /// Note that variables that don't regulate anything (outputs) are simply removed by this
    /// reduction. However, this is correct behaviour, just not super intuitive.
    ///
    /// Also note that because the set of variables is different between this and the
    /// resulting [BooleanNetwork], any [VariableId] that is valid in this network is not
    /// valid in the resulting network.
    ///
    /// ### Logical parameters
    ///
    /// Finally, note the set of admissible parameter instantiations (interpretations of
    /// uninterpreted functions) can change between the original and the reduced model. The reason
    /// for this is the same as in the example of a "logically inconsistent" system described
    /// above. For example, consider `a -> b` and `b -> c`, but also `a -| c`. Then, let's have
    /// `f_b = f(a)` and `f_c = b & !a`. Then `f(a) = a` is the only admissible interpretation
    /// of `f`. However, suppose we reduce variable `b`, obtaining `f_c = f(a) & !a` with
    /// regulation `a -? c` (because `a -> b -> c` and `a -| c` in the original system).
    /// Then `f` can actually be `false`, `a`, or `!a`.
    ///
    /// This does not mean you cannot use reduction on systems with uninterpreted functions
    /// at all, but be careful about the new meaning of the static constraints on these
    /// functions.
    ///
    pub fn inline_variable(&self, var: VariableId, repair_graph: bool) -> Option<BooleanNetwork> {
        if self.as_graph().targets(var).contains(&var) {
            // Cannot inline variable if it is self-regulated.
            return None;
        }
        Some(self.inline_variable_internal(var, repair_graph))
    }

    /// Compute a valid name for an "anonymous update function" of the corresponding variable.
    pub(crate) fn get_implicit_function_name(&self, variable: VariableId) -> String {
        let mut name = format!("f_{}", self.get_variable_name(variable));
        loop {
            if self.find_parameter(name.as_str()).is_none()
                && self.as_graph().find_variable(name.as_str()).is_none()
            {
                return name;
            }
            // If there is a collision with existing variable or parameter, prefix the name with an underscore.
            name = format!("_{}", name);
        }
    }

    /// Replace the implicit parameter of the given `variable` (i.e. its anonymous uninterpreted
    /// update function) with an explicit (i.e. named) parameter.
    ///
    /// 1. This is only allowed if the update function of `variable` actually is
    ///    an implicit parameter.
    ///
    /// 2. You can provide an optional parameter `name`. If the name is not specified, the new
    ///    explicit parameter will be named `f_VAR`, where `VAR` is the name of the variable. If
    ///    the default name clashes with an existing parameter or variable name, it is prefixed
    ///    with enough underscores (`_`) to eliminate any ambiguity.
    ///
    /// 3. The arguments of `f_VAR` will be sorted based on standard ordering of `VariableId`.
    ///
    /// Note that this operation modifies the current network.
    pub fn assign_parameter_name(
        &mut self,
        variable: VariableId,
        name: Option<&str>,
    ) -> Result<ParameterId, String> {
        // Ensure that the update function for that variable indeed does not exist.
        if self.get_update_function(variable).is_some() {
            return Err(format!(
                "Variable {} has an explicit update function.",
                self.get_variable_name(variable)
            ));
        }
        // Either use the provided name, or the default one.
        let name = name
            .map(|it| it.to_string())
            .unwrap_or_else(|| self.get_implicit_function_name(variable));

        // Get the regulators, register the parameter, and set the update function.
        let regulators = self.as_graph().regulators(variable);
        let arity = regulators.len();
        // Note that this should never fail because the new name is always safe and unambiguous.
        let id = self.add_parameter(name.as_str(), u32::try_from(arity).unwrap())?;
        let function = FnUpdate::mk_basic_param(id, &regulators);
        self.set_update_function(variable, Some(function))?;

        Ok(id)
    }

    /// Make a copy of this [BooleanNetwork] where all implicit parameters (i.e. anonymous update
    /// functions) are replaced with explicit parameters using a default naming scheme (see also
    /// [BooleanNetwork::assign_parameter_name]).
    pub fn name_implicit_parameters(&self) -> BooleanNetwork {
        let mut copy = self.clone();
        for var in self.variables() {
            if self.get_update_function(var).is_none() {
                // This can never fail because we check that the variable is indeed an
                // implicit parameter.
                copy.assign_parameter_name(var, None).unwrap();
            }
        }
        copy
    }

    /// An internal infallible version of [BooleanNetwork::inline_variable] which does not check
    /// for self-regulations. The idea is that you can use this function if you are *sure* the
    /// inlining is reasonable even if a self-regulation is present.
    fn inline_variable_internal(&self, var: VariableId, repair_graph: bool) -> BooleanNetwork {
        // TODO: Please break this up into smaller methods. I'm just not sure how... yet.
        let mut old_bn = self.clone();
        let old_rg = self.as_graph();

        // Remove `var` from regulators and target if it is there, since we want to ignore
        // the self-regulation (because the precondition is that it is safe to ignore).
        let var_regulators = old_rg
            .regulators(var)
            .into_iter()
            .filter(|it| *it != var)
            .collect::<Vec<_>>();
        let var_targets = old_rg
            .targets(var)
            .into_iter()
            .filter(|it| *it != var)
            .collect::<Vec<_>>();

        // If we have to create an explicit uninterpreted function for the inlined variable,
        // we have to give it a unique name at first. But once the variable is inlined, we can
        // use the old name. So here, we save whether a parameter needs to be removed, and if
        // so, to what.
        let mut rename_parameter: Option<(ParameterId, String)> = None;

        // 1. The very first step is to replace anonymous functions with explicit ones if they
        //    are somehow related to `var`. Hence, in the next steps, we can assume the inlined
        //    function and the target functions are all explicit.
        for check_var in var_targets.iter().chain(&[var]) {
            let has_missing_function = old_bn.get_update_function(*check_var).is_none();
            let contains_self = old_bn
                .get_update_function(*check_var)
                .as_ref()
                .map(|it| it.contains_variable(var))
                .unwrap_or(false);
            let contains_self = *check_var == var && contains_self;
            if has_missing_function || contains_self {
                // Regulators, but without any self-regulation on the inlined variable.
                // That self-regulation will be no longer there, hence we need to ignore it.
                let regulators = old_rg
                    .regulators(*check_var)
                    .into_iter()
                    .filter(|it| !(*check_var == var && *it == var))
                    .collect::<Vec<_>>();
                let arity = u32::try_from(regulators.len()).unwrap();
                let name = old_bn.get_implicit_function_name(*check_var);
                let Ok(p_id) = old_bn.add_parameter(name.as_str(), arity) else {
                    unreachable!("Parameter name is known to be valid.");
                };
                if *check_var == var {
                    rename_parameter = Some((p_id, old_bn.get_variable_name(*check_var).clone()));
                }
                if has_missing_function {
                    // If we are creating the parameter due to a missing function, simply create
                    // a new update function and place it there.
                    let update = FnUpdate::mk_basic_param(p_id, &regulators);
                    old_bn
                        .set_update_function(*check_var, Some(update))
                        .unwrap();
                } else {
                    // Otherwise we are here due to `contains_self`, in which case we need to swap
                    // the variable for the fresh parameter.
                    let function = old_bn.get_update_function(*check_var).as_ref().unwrap();
                    let function =
                        function.substitute_variable(*check_var, &FnUpdate::mk_param(p_id, &[]));
                    old_bn
                        .set_update_function(*check_var, Some(function))
                        .unwrap();
                }
            }
        }

        // 2. Compute variable list without the inlined variable.
        let new_variables = {
            let mut names = Vec::from_iter(
                old_bn
                    .variables()
                    .map(|it| old_bn.get_variable_name(it).clone()),
            );
            names.remove(var.to_index());
            names
        };

        // 3. Create an initial regulatory graph. We may try to further "fix" this graph later
        // if `repair_graph` is set to true. But this should be enough for us to start inlining.
        let mut new_rg = RegulatoryGraph::new(new_variables);

        // 3a. First, create new regulations related to regulators/targets of `var`.
        //     Specifically, add a new regulation for every combination of an
        //     old regulator and an old target, preserving the monotonicity/observability.
        for old_regulator in &var_regulators {
            for old_target in &var_targets {
                let old_one = old_rg.find_regulation(*old_regulator, var).unwrap();
                let old_two = old_rg.find_regulation(var, *old_target).unwrap();
                let old_feed_forward = old_rg.find_regulation(*old_regulator, *old_target);

                // The new regulation is observable only if both partial regulations are
                // observable, or if the feed forward regulation exists and is observable.
                let ff_observable = old_feed_forward.map(|it| it.observable);
                let new_observable =
                    (old_one.observable && old_two.observable) || ff_observable.unwrap_or(false);

                let combined_monotonicity =
                    match (old_one.monotonicity, old_two.monotonicity) {
                        // ? and anything = ?
                        (None, _) | (_, None) => None,
                        // + and + = +, - and - = +
                        (Some(Activation), Some(Activation))
                        | (Some(Inhibition), Some(Inhibition)) => Some(Activation),
                        // + and - = -, - and + = -
                        (Some(Activation), Some(Inhibition))
                        | (Some(Inhibition), Some(Activation)) => Some(Inhibition),
                    };

                let new_monotonicity =
                    if let Some(ff_monotonicity) = old_feed_forward.map(|it| it.monotonicity) {
                        // If the feed forward regulation exists, we can only set regulation
                        // monotonicity if both regulations are the same.
                        if ff_monotonicity == combined_monotonicity {
                            combined_monotonicity
                        } else {
                            None
                        }
                    } else {
                        // If there is no feed forward regulation, we just use the new monotonicity.
                        combined_monotonicity
                    };

                new_rg
                    .add_regulation(
                        old_bn.get_variable_name(*old_regulator),
                        old_bn.get_variable_name(*old_target),
                        new_observable,
                        new_monotonicity,
                    )
                    .unwrap();
            }
        }

        // 3b. Copy the remaining regulations into the new graph (i.e. those that do not
        // involve `var` and are not "feed forward").
        for reg in old_rg.regulations() {
            if reg.target == var || reg.regulator == var {
                continue;
            }
            let name_regulator = self.get_variable_name(reg.regulator);
            let name_target = self.get_variable_name(reg.target);
            let new_regulator = new_rg.find_variable(name_regulator).unwrap();
            let new_target = new_rg.find_variable(name_target).unwrap();

            if new_rg.find_regulation(new_regulator, new_target).is_some() {
                // Skip if the regulation already exists. These are "feed forward"
                // regulations that we already created.
                continue;
            }

            new_rg
                .add_regulation(
                    name_regulator,
                    name_target,
                    reg.observable,
                    reg.monotonicity,
                )
                .unwrap();
        }

        // 4. Now we can actually create a new network and all the relevant parameters.
        //    Here, we have to account for the fact that if a variable is unused and has an unknown
        //    function, we created an explicit parameter for it, which is now also unused. Such
        //    parameter should not be copied as it is redundant.
        let mut new_bn = BooleanNetwork::new(new_rg);
        for id in old_bn.parameters() {
            if rename_parameter.as_ref().map(|(a, _)| *a) == Some(id) {
                // The rename_parameter is the one created *for* the inlined variable. We
                // should check that the variable is actually used somewhere before copying it.
                let mut is_used = false;
                for target in &var_targets {
                    let update = old_bn.get_update_function(*target).as_ref().unwrap();
                    if update.collect_arguments().contains(&var) {
                        is_used = true;
                        break;
                    }
                }
                if !is_used {
                    // No need to rename the parameter if it is skipped.
                    rename_parameter = None;
                    continue;
                }
            }
            let parameter = old_bn.get_parameter(id);
            new_bn
                .add_parameter(&parameter.name, parameter.arity)
                .unwrap();
        }

        // 5. Next, we build a map which assigns each old variable and parameter its new ID
        //    (except for `var`).
        let new_var_id = old_bn
            .variables()
            .filter(|it| *it != var)
            .map(|it| {
                let name = old_bn.get_variable_name(it);
                (it, new_bn.as_graph().find_variable(name).unwrap())
            })
            .collect::<HashMap<_, _>>();
        // This needs to be a filter-map, because we might have skipped the parameter of the
        // inlined variable if it is never used.
        let new_param_id = old_bn
            .parameters()
            .filter_map(|it| {
                let name = &old_bn.get_parameter(it).name;
                new_bn.find_parameter(name).map(|new_id| (it, new_id))
            })
            .collect::<HashMap<_, _>>();

        // 6. We can now move the update functions to the new network. If the function involves
        //    `var`, we substitute it.
        let var_function = old_bn.get_update_function(var).clone().unwrap();
        for old_var in old_bn.variables() {
            if old_var == var {
                continue;
            }
            let new_id = new_var_id.get(&old_var).unwrap();
            if var_targets.contains(&old_var) {
                // This variable is regulated by `var`. We need to inline `var_function`.
                let update = old_bn.get_update_function(old_var).as_ref().unwrap();
                let inlined = update.substitute_variable(var, &var_function);
                // Then we rename everything to new names...
                let inlined = inlined.rename_all(&new_var_id, &new_param_id);
                new_bn.set_update_function(*new_id, Some(inlined)).unwrap();
            } else {
                // This variable is not regulated by `var`, hence we just copy.
                if let Some(update) = old_bn.get_update_function(old_var).as_ref() {
                    let renamed = update.rename_all(&new_var_id, &new_param_id);
                    new_bn.set_update_function(*new_id, Some(renamed)).unwrap();
                }
            }
        }

        if let Some((p_id, name)) = rename_parameter {
            new_bn.rename_parameter(p_id, name.as_str()).unwrap();
        }

        // 7. Prune unused parameters. This is necessary because if we are inlining an output
        //    variable, we might delete the last occurrence of a parameter, in which case we
        //    ideally want to remove it from the network completely.
        new_bn = new_bn.prune_unused_parameters();

        // 8. If we don't want to fix the regulatory graph afterwards, we are done.
        //    However, if we do want to fix it, we will need to create a symbolic context
        //    and start building the network from scratch.
        //    This is essentially `infer_valid_graph`, but only for the relevant regulations.
        if !repair_graph {
            new_bn
        } else {
            let ctx = SymbolicContext::new(&new_bn).unwrap();

            let repair_targets = var_targets
                .iter()
                .filter_map(|it| new_var_id.get(it).cloned())
                .collect::<HashSet<_>>();

            let mut new_new_rg = RegulatoryGraph::new(new_bn.as_graph().variable_names());

            // We need to clone the regulations because we will might be modifying the BN
            // in the loop (not the regulations though).
            for reg in Vec::from_iter(new_bn.as_graph().regulations().cloned()) {
                if !repair_targets.contains(&reg.target) {
                    // Regulations that do not involve one of the relevant targets are copied.
                    new_new_rg.add_raw_regulation(reg).unwrap();
                } else {
                    // Otherwise, let's try to build the update function (we know that all of
                    // these exist, since we just inlined into them) and infer its properties.

                    let fun = new_bn.get_update_function(reg.target).as_ref().unwrap();
                    let fun_bdd = ctx.mk_fn_update_true(fun);
                    let Some(new_reg) = RegulationConstraint::fix_regulation(&ctx, &reg, &fun_bdd)
                    else {
                        // This regulation is irrelevant, hence we can substitute the variable
                        // for a constant, and use that instead. This simplified function will
                        // be copied into the result instead of the original one.
                        let eliminated = fun
                            .substitute_variable(reg.regulator, &FnUpdate::Const(false))
                            .simplify_constants();
                        new_bn
                            .set_update_function(reg.target, Some(eliminated))
                            .unwrap_or_else(|_| {
                                unreachable!("Simplified function must be still valid.");
                            });
                        continue;
                    };
                    new_new_rg.add_raw_regulation(new_reg).unwrap();
                }
            }

            // Finally, just copy all the functions to the new network. They should still be valid.
            let mut new_new_bn = BooleanNetwork::new(new_new_rg);
            for param in new_bn.parameters() {
                let param = new_bn.get_parameter(param);
                new_new_bn
                    .add_parameter(param.name.as_str(), param.arity)
                    .unwrap();
            }
            for var in new_bn.variables() {
                let Some(update) = new_bn.get_update_function(var).as_ref() else {
                    continue;
                };
                new_new_bn
                    .set_update_function(var, Some(update.clone()))
                    .unwrap();
            }

            // In very rare instances, we can eliminate a parameter by detecting an unused
            // regulation and simplifying the variable away (e.g. `x & !x & f(z)` simplifies
            // to `false`). Hence we have to prune parameters again here.
            new_new_bn.prune_unused_parameters()
        }
    }
}

/// Allow indexing `BooleanNetwork` using `VariableId` objects.
impl Index<VariableId> for BooleanNetwork {
    type Output = Variable;

    fn index(&self, index: VariableId) -> &Self::Output {
        self.graph.get_variable(index)
    }
}

/// Allow indexing `BooleanNetwork` using `ParameterId` objects.
impl Index<ParameterId> for BooleanNetwork {
    type Output = Parameter;

    fn index(&self, index: ParameterId) -> &Self::Output {
        &self.parameters[index.0]
    }
}

#[cfg(test)]
mod test {
    use crate::{BooleanNetwork, FnUpdate, ParameterId};
    use std::convert::TryFrom;

    #[test]
    fn test_try_from_file() {
        assert!(BooleanNetwork::try_from_file("aeon_models/g2a_p9.aeon").is_ok());
        assert!(BooleanNetwork::try_from_file("sbml_models/g2a.sbml").is_ok())
    }

    #[test]
    fn test_rg_inference() {
        let bn = BooleanNetwork::try_from_bnet(
            r"
        A, B | !C
        B, B & !(A | C)
        C, (A | !A) & (C <=> B)
        ",
        )
        .unwrap();

        let expected = BooleanNetwork::try_from(
            r"
        B -> A
        C -| A
        A -| B
        B -> B
        C -| B
        B -? C
        C -? C
        ",
        )
        .unwrap();

        let inferred = bn.infer_valid_graph().unwrap();
        assert_eq!(expected.as_graph(), inferred.as_graph());
    }

    #[test]
    fn test_rg_inference_with_parameters() {
        let bn = BooleanNetwork::try_from(
            r"
                a ->? c
                b -? c
                d -> c
                $d: true
                $c: f(a, b, d | !d)
            ",
        )
        .unwrap();
        let expected = BooleanNetwork::try_from(
            r"
                a ->? c
                b -? c
                $c: f(a, b, true)
                $d: true
            ",
        )
        .unwrap();

        assert_eq!(expected, bn.infer_valid_graph().unwrap());

        let bn = BooleanNetwork::try_from(
            r"
                a -> c
                # This monotonicity is intentionally wrong.
                b -| c
                $a: true
                $b: true
                # x is a parameter.
                $c: b & ((a | !a) | x)
            ",
        )
        .unwrap();

        let expected = BooleanNetwork::try_from(
            r"
                b -> c
                $a: true
                $b: true
                $c: b
            ",
        )
        .unwrap();
        assert_eq!(expected, bn.infer_valid_graph().unwrap());
    }

    #[test]
    fn test_input_inlining() {
        let bn = BooleanNetwork::try_from(
            r"
            a -> x
            b -> x
            c -> x

            # a has no regulators and is unknown
            # b has identity function
            # c is a constant
            b -> b
            $b: b
            $c: true

            # All three have a known function in x
            $x: a | b | c

            d ->? y
            e ->? y

            # Both d and e appear in y, but d appears in an uninterpreted function.
            $y: fun(d) | e

            f ->? z
            z ->? z
            # f does not appear in z, hence it will just disappear.
            # z is an input based on identity function, hence it will be inlined, but
            # it isn't used either, so it will also disappear.
            $z: z

            g ->? w
            # g will be inlined into a newly created function for w.
        ",
        )
        .unwrap();

        let inlined = bn.inline_inputs(false, true);

        // Should be a,b,e,d,g,fn_w,fun.
        assert_eq!(inlined.num_parameters(), 7);
        // Should be c,w,x,y.
        assert_eq!(inlined.num_vars(), 4);

        assert!(inlined.find_parameter("a").is_some());
        assert!(inlined.find_parameter("b").is_some());
        assert!(inlined.find_parameter("e").is_some());
        assert!(inlined.find_parameter("d").is_some());
        assert!(inlined.find_parameter("g").is_some());
        assert!(inlined.find_parameter("fun").is_some());
        assert!(inlined.find_parameter("f_w").is_some());
        assert!(inlined.as_graph().find_variable("c").is_some());
        assert!(inlined.as_graph().find_variable("w").is_some());
        assert!(inlined.as_graph().find_variable("x").is_some());
        assert!(inlined.as_graph().find_variable("y").is_some());

        // This should be only detected using BDDs.
        let bn = BooleanNetwork::try_from(
            r"
            a -? a
            a -> b
            $a: (!a => a)
            $b: _f(a)
        ",
        )
        .unwrap();

        let expected = BooleanNetwork::try_from(
            r"
            $b: _f(a)
        ",
        )
        .unwrap();
        assert_ne!(expected, bn.inline_inputs(false, true));
        assert_eq!(expected, bn.inline_inputs(true, true));
    }

    #[test]
    fn test_variable_inlining() {
        let bn = BooleanNetwork::try_from(
            r"
            a -| b
            b -| c
            a -> c
            c -?? a
            b -> d
            $a: p(c)
            $b: !a
            $c: !b & a
            $d: b
        ",
        )
        .unwrap();

        let a = bn.as_graph().find_variable("a").unwrap();
        let b = bn.as_graph().find_variable("b").unwrap();
        let c = bn.as_graph().find_variable("c").unwrap();
        let d = bn.as_graph().find_variable("d").unwrap();

        // First, a very normal reduction which removes variable `b`. Test combinations
        // of different regulation monotonicity.
        let expected = BooleanNetwork::try_from(
            r"
            a -> c
            c -?? a
            a -| d
            $a: p(c)
            $c: !!a & a
            $d: !a
        ",
        )
        .unwrap();
        assert_eq!(bn.inline_variable(b, false), Some(expected));

        // Then remove `d`, which is an output, so does not connect to anything.
        let expected = BooleanNetwork::try_from(
            r"
            a -| b
            b -| c
            a -> c
            c -?? a
            $a: p(c)
            $b: !a
            $c: !b & a
        ",
        )
        .unwrap();
        assert_eq!(bn.inline_variable(d, false), Some(expected));

        // Reducing `a` should correctly propagate the unknown function.
        let expected = BooleanNetwork::try_from(
            r"
            b -| c
            c -?? b
            c -?? c
            b -> d
            $b: !p(c)
            $c: !b & p(c)
            $d: b
        ",
        )
        .unwrap();
        assert_eq!(bn.inline_variable(a, false), Some(expected));

        let expected = BooleanNetwork::try_from(
            r"
            a -| b
            b -?? a
            a -?? a
            b -> d
            $a: p(!b & a)
            $b: !a
            $d: b
        ",
        )
        .unwrap();
        assert_eq!(bn.inline_variable(c, false), Some(expected));

        // Finally, a quick test for self-regulations:
        let bn = BooleanNetwork::try_from(
            r"
            a -> b
            b -> a
            b -| b
            $a: b
            $b: !b | a
        ",
        )
        .unwrap();
        let b = bn.as_graph().find_variable("b").unwrap();
        assert_eq!(bn.inline_variable(b, false), None);

        // Test that a parameter is indeed removed if it is no longer relevant.
        let bn = BooleanNetwork::try_from(
            r"
            a -> b
            $a: true
            $b: f(a)
        ",
        )
        .unwrap();
        let expected = BooleanNetwork::try_from(
            r"
            $a: true
        ",
        )
        .unwrap();
        let b = bn.as_graph().find_variable("b").unwrap();

        assert_eq!(expected, bn.inline_variable(b, true).unwrap());
    }

    #[test]
    fn test_constant_inlining() {
        let bn = BooleanNetwork::try_from(
            r"
            b -> x
            c -> x

            # Only c is a constant, but it is enough to turn x into a constant.
            b -> b
            $b: b
            $c: true

            $x: b | c

            # This will also inline because x is a constant.
            x -> y
            $y: (x & !x)

            # Here, y will inline, but b should stay.
            y -> z
            b -| z
            $z: !b | y
        ",
        )
        .unwrap();

        let expected = BooleanNetwork::try_from(
            r"
            b -> b
            $b: b
            b -| z
            $z: !b
            ",
        )
        .unwrap();

        assert_eq!(bn.inline_constants(false, true), expected);

        // Here, a/b should be only detected as constants through BDDs.
        let bn = BooleanNetwork::try_from(
            r"
            a -? a
            $a: (a & !a)
            b -? b
            $b: (b | !b)
            a -> c
            b -> c
            c -> c
            $c: (a & b) | c
        ",
        )
        .unwrap();

        let expected = BooleanNetwork::try_from(
            r"
            c -> c
            $c: c
            ",
        )
        .unwrap();

        assert_ne!(bn.inline_constants(false, true), expected);
        assert_eq!(bn.inline_constants(true, true), expected);
    }

    #[test]
    fn test_constraint_remove() {
        let bn = BooleanNetwork::try_from(
            r"
            a -> b
            b -> a
            b -| b
            $a: b
            $b: !b | a
        ",
        )
        .unwrap();

        let expected = BooleanNetwork::try_from(
            r"
            a -?? b
            b -?? a
            b -?? b
            $a: b
            $b: !b | a
        ",
        )
        .unwrap();

        assert_eq!(expected, bn.remove_static_constraints());
    }

    #[test]
    fn test_constant_inlining_real_world_1() {
        // This network actually uses the infer_constants parameter in a way that can break
        // the function if the self-regulations are not properly handled.
        let bn = BooleanNetwork::try_from_file("./aeon_models/constants.aeon").unwrap();
        let inlined = bn.inline_constants(true, true);
        assert!(inlined.num_vars() < bn.num_vars());
    }

    #[test]
    fn test_assign_parameter_name() {
        let mut bn = BooleanNetwork::try_from(
            r#"
        a -> b
        b -> c
        a -| c
        c -? a
        "#,
        )
        .unwrap();
        let vars = bn.variables().collect::<Vec<_>>();
        bn.assign_parameter_name(vars[0], Some("foo_a")).unwrap();
        assert_eq!(bn.num_parameters(), 1);
        let update = bn.get_update_function(vars[0]).as_ref().unwrap();
        assert_eq!(bn.get_parameter(ParameterId::from_index(0)).name, "foo_a");
        assert!(matches!(update, &FnUpdate::Param(_, _)));

        let copy = bn.name_implicit_parameters();
        assert_eq!(copy.num_parameters(), 3);
        assert!(copy.get_update_function(vars[0]).is_some());
        assert!(copy.get_update_function(vars[1]).is_some());
        assert!(copy.get_update_function(vars[2]).is_some());
    }
}

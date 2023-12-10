use crate::symbolic_async_graph::{RegulationConstraint, SymbolicContext};
use crate::Monotonicity::Inhibition;
use crate::{
    BooleanNetwork, FnUpdate, Monotonicity, Parameter, ParameterId, ParameterIdIterator,
    Regulation, RegulatoryGraph, Variable, VariableId, VariableIdIterator, ID_REGEX,
};
use std::collections::{HashMap, HashSet};
use std::ops::Index;
use std::path::Path;
use Monotonicity::Activation;

/// Basic methods for safely building `BooleanNetwork`s.
impl BooleanNetwork {
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
    fn assert_arguments_are_valid(
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
}

impl BooleanNetwork {
    /// Infer a *sufficient* regulatory graph based on the update functions of
    /// this `BooleanNetwork`.
    ///
    /// The resulting graph is solely based on the information that can be inferred from the
    /// update functions. In particular, if the BN contains uninterpreted functions,
    /// the monotonicity of variables appearing within these functions is unknown. Overall,
    /// the method is typically only useful for fully specified networks with minor errors
    /// in the regulatory graph.
    ///
    /// The BN still has to satisfy basic integrity constraints. In particular, every uninterpreted
    /// function must be used, and must be used consistently (i.e. correct arity). Also, every
    /// update function may only use variables declared as regulators. Otherwise, an error
    /// is returned.
    ///
    /// The method can also fail if a non-observable regulator is removed from a partially
    /// specified function, because in such case we cannot always transform the function
    /// in a way that is valid.
    pub fn infer_valid_graph(&self) -> Result<BooleanNetwork, String> {
        let ctx = SymbolicContext::new(self)?;

        // This should ensure the variable IDs in the old and the new network are compatible,
        // so that we can reuse Regulation and FnUpdate objects.
        let var_names = self
            .variables()
            .map(|id| self.get_variable_name(id))
            .cloned()
            .collect::<Vec<_>>();

        let mut new_rg = RegulatoryGraph::new(var_names);
        for target_var in self.variables() {
            if let Some(function) = self.get_update_function(target_var) {
                let fn_is_true = ctx.mk_fn_update_true(function);
                for regulator_var in self.as_graph().regulators(target_var) {
                    let Some(regulation) = RegulationConstraint::infer_sufficient_regulation(
                        &ctx,
                        regulator_var,
                        target_var,
                        &fn_is_true,
                    ) else {
                        continue;
                    };

                    new_rg.add_raw_regulation(regulation).unwrap();
                }
            } else {
                // If the update function is missing, just copy the existing regulators, but
                // remove any monotonicity/observability.
                for regulator_var in self.as_graph().regulators(target_var) {
                    new_rg
                        .add_raw_regulation(Regulation {
                            regulator: regulator_var,
                            target: target_var,
                            observable: false,
                            monotonicity: None,
                        })
                        .unwrap();
                }
            }
        }

        let mut new_bn = BooleanNetwork::new(new_rg);

        // Copy over existing parameters
        for parameter_id in self.parameters() {
            let parameter = &self[parameter_id];
            new_bn
                .add_parameter(&parameter.name, parameter.arity)
                .unwrap();
        }

        for var in self.variables() {
            let name = self.get_variable_name(var);
            if let Some(update) = self.get_update_function(var) {
                // At the moment, there is no way to "fix" the function in a way that
                // works with logical parameters if one of the arguments is non-observable.
                // As such, we first try to copy the function with no change. then we try to
                // run it through a string translation, but this only works on functions without
                // parameters. If this fails, the conversion fails.
                let Err(_) = new_bn.set_update_function(var, Some(update.clone())) else {
                    continue;
                };
                let fn_bdd = ctx.mk_fn_update_true(update);
                let fn_string = fn_bdd
                    .to_boolean_expression(ctx.bdd_variable_set())
                    .to_string();
                let Err(_) = new_bn.add_string_update_function(name, &fn_string) else {
                    continue;
                };
                return Err(format!(
                    "Cannot translate function for variable {} due to elimianted arguments.",
                    name
                ));
            }
        }

        Ok(new_bn)
    }

    /// Try to inline the input nodes (variables) of the network as logical parameters
    /// (uninterpreted functions of arity 0).
    ///
    /// The operation also removes all observability requirements, as the transformation between
    /// variable and parameter can cause them to be unsatisfiable (in particular, some
    /// regulations can become observable only for certain parameter valuations).
    ///
    /// This often reduces the overall symbolic complexity of working with the network, as
    /// fewer symbolic variables are necessary. However, note that at the moment, not all input
    /// nodes can be correctly inlined. In particular, in order for a node to be inlined,
    /// the following must hold:
    ///
    ///  - Either it has no regulators and its update function is unknown, or it has exactly one
    ///    regulator and its update function is the identity function (update(x) = x). That is,
    ///    constant source nodes are not inlined.
    ///  - Every variable that depends on it has an explicit update function, the source node
    ///    does appear in this function (syntactically; we do not check for observability), and
    ///    it does not appear as an argument to any of the nested uninterpreted functions.
    ///
    /// The second requirement is necessary to ensure that the newly created parameter will still
    /// appear in the network, and that we are not losing any information about its effect in the
    /// downstream functions. However, note that we are still technically losing the
    /// monotonicity/observability requirements. You should thus always check the integrity of
    /// both the original and transformed network.
    pub fn inline_inputs(&self) -> BooleanNetwork {
        let inputs: HashSet<VariableId> = self
            .variables()
            .filter(|it| {
                // Check if the variable is an input.
                let has_no_regulators = self.as_graph().regulators(*it).is_empty();
                let has_update_function = self.get_update_function(*it).is_some();
                let is_free_input = has_no_regulators && !has_update_function;

                let has_identity_update =
                    self.get_update_function(*it) == &Some(FnUpdate::Var(*it));
                let is_only_regulator = self.as_graph().regulators(*it) == vec![*it];
                let is_identity_input = has_identity_update && is_only_regulator;
                is_free_input || is_identity_input
            })
            .filter(|input| {
                // Only retain inputs that are safe to remove.
                let mut is_ok = true;
                for target in self.targets(*input) {
                    if let Some(update) = self.get_update_function(target) {
                        // If the input does not appear in the function at all, we can't remove
                        // it, because we'd lose information about that input.
                        is_ok = is_ok && update.contains_variable(*input);
                    } else {
                        // The target variable does not have an update function - we'd lose
                        // one implicit argument if we just delete this input variable.
                        is_ok = false;
                    }
                }
                is_ok
            })
            .collect();

        let variables: HashSet<VariableId> =
            self.variables().filter(|it| !inputs.contains(it)).collect();
        let mut variable_names: Vec<String> = variables
            .iter()
            .map(|it| self.get_variable_name(*it))
            .cloned()
            .collect();

        variable_names.sort();

        let mut new_rg = RegulatoryGraph::new(variable_names);
        for reg in self.as_graph().regulations() {
            if variables.contains(&reg.get_regulator()) {
                let source_name = self.get_variable_name(reg.get_regulator());
                let target_name = self.get_variable_name(reg.get_target());
                new_rg
                    .add_regulation(
                        source_name.as_str(),
                        target_name.as_str(),
                        false, // necessary for this to work...
                        reg.get_monotonicity(),
                    )
                    .unwrap();
            }
        }

        let mut new_bn = BooleanNetwork::new(new_rg);

        // Copy old parameters.
        for param in self.parameters() {
            let param = self.get_parameter(param);
            new_bn
                .add_parameter(param.get_name().as_str(), param.get_arity())
                .unwrap();
        }

        // Add new inlined parameters.
        // Note that integrity of the original BN ensures that there is no parameter
        // with the same name already.
        for var in &inputs {
            let name = self.get_variable_name(*var);
            new_bn.add_parameter(name.as_str(), 0).unwrap();
        }

        // Copy update functions. Technically, they should still be syntactically correct, so
        // we just have to re-parse them in the new context.
        for var in &variables {
            let update = self.get_update_function(*var);
            let name = self.get_variable_name(*var);
            if let Some(update) = update {
                new_bn
                    .add_string_update_function(name.as_str(), update.to_string(self).as_str())
                    .unwrap();
            }
        }

        new_bn
    }

    /// Produce a new [BooleanNetwork] where the given [VariableId] `var` has been eliminated
    /// by inlining its update function into all downstream variables.
    ///
    /// Note that the inlining operation is purely syntactic. This means that even if we create
    /// new regulations when relevant, the resulting regulatory graph may be inconsistent with
    /// the update functions. If you set `repair_graph` to `true`, the function will perform
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
    /// **At the moment, the reduced variable cannot have a self-regulation.** If such variable
    /// is targeted with reduction, the result is `None`. If a variable is inlined into a missing
    /// function, the function is given a name as a new parameter, and the variable is inlined
    /// into this new parameter.
    ///
    /// Note that variables that don't regulate anything (outputs) are simply removed by this
    /// reduction (although this is correct behaviour, just not super intuitive).
    ///
    /// Finally, note that because the set of variables is different between this and the
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
        let mut old_bn = self.clone();
        let old_rg = self.as_graph();

        let var_regulators = old_rg.regulators(var);
        let var_targets = old_rg.targets(var);
        if var_targets.contains(&var) {
            // Cannot inline variable if it is self-regulated.
            return None;
        }

        // 1. The very first step is to replace anonymous functions with explicit ones if they
        //    are somehow related to `var`. Hence in the next steps, we can assume the inlined
        //    function and the target functions are all explicit.
        for var in var_targets.iter().chain(&[var]) {
            if old_bn.get_update_function(*var).is_none() {
                let regulators = old_rg.regulators(*var);
                let name = format!("fn__{}", old_bn.get_variable_name(*var));
                let arity = u32::try_from(regulators.len()).unwrap();
                let Ok(p_id) = old_bn.add_parameter(&name, arity) else {
                    // This could happen if we accidentally name a new parameter after an existing
                    // one, but this should be extremely rare.
                    eprintln!("WARNING: Cannot inline variable due to parameter name collision.");
                    return None;
                };
                let update = FnUpdate::mk_basic_param(p_id, &regulators);
                old_bn.set_update_function(*var, Some(update)).unwrap();
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
        let mut new_bn = BooleanNetwork::new(new_rg);
        for id in old_bn.parameters() {
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
        let new_param_id = old_bn
            .parameters()
            .map(|it| {
                let name = &old_bn.get_parameter(it).name;
                (it, new_bn.find_parameter(name).unwrap())
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

        // 7. If we don't want to fix the regulatory graph afterwards, we are done.
        //    However, if we do want to fix it, we will need to create a symbolic context
        //    and start building the network from scratch.
        //    This is essentially `infer_valid_graph`, but only for the relevant regulations.
        if !repair_graph {
            Some(new_bn)
        } else {
            let ctx = SymbolicContext::new(&new_bn).unwrap();

            // This is always ok because we know that there is no self-regulation.
            let repair_targets = var_targets
                .iter()
                .map(|it| *new_var_id.get(it).unwrap())
                .collect::<HashSet<_>>();

            let names = new_bn
                .variables()
                .map(|it| new_bn.get_variable_name(it).clone())
                .collect::<Vec<_>>();
            let mut new_new_rg = RegulatoryGraph::new(names);

            for reg in new_bn.as_graph().regulations() {
                if !repair_targets.contains(&reg.target) {
                    // Regulations that do not involve one of the relevant targets are copied.
                    new_new_rg.add_raw_regulation(reg.clone()).unwrap();
                } else {
                    // Otherwise, let's try to build the update function (we know that all of
                    // these exist, since we just inlined into them) and infer its properties.

                    let fun = new_bn.get_update_function(reg.target).as_ref().unwrap();
                    let fun_bdd = ctx.mk_fn_update_true(fun);
                    let Some(mut new_reg) = RegulationConstraint::infer_sufficient_regulation(
                        &ctx,
                        reg.regulator,
                        reg.target,
                        &fun_bdd,
                    ) else {
                        // This regulation is irrelevant.
                        continue;
                    };
                    if new_reg.monotonicity.is_none() {
                        // If "sufficient_regulation" is not monotonous, we can use the old
                        // monotonicity, because that constraint comes from the old regulations,
                        // hence it cannot be inferred from BDD alone.
                        new_reg.monotonicity = reg.monotonicity;
                    }
                    new_new_rg.add_raw_regulation(new_reg).unwrap();
                }
            }

            // Finally, just copy all the functions to the new network. They should still be valid.
            let mut new_new_bn = BooleanNetwork::new(new_new_rg);
            for var in new_bn.variables() {
                let Some(update) = new_bn.get_update_function(var).as_ref() else {
                    continue;
                };
                new_new_bn
                    .set_update_function(var, Some(update.clone()))
                    .unwrap();
            }

            Some(new_new_bn)
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
    use crate::BooleanNetwork;
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
                a -> c
                b -| c
                $c: f(a, b)
            ",
        )
        .unwrap();
        let expected = BooleanNetwork::try_from(
            r"
                a -?? c
                b -?? c
                $c: f(a, b)
            ",
        )
        .unwrap();

        assert_eq!(expected, bn.infer_valid_graph().unwrap());

        let invalid = BooleanNetwork::try_from(
            r"
                a -> c
                b -| c
                $c: b & x & (a | !a)
            ",
        )
        .unwrap();
        assert!(invalid.infer_valid_graph().is_err());
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
            # f cannot be erased because it does not appear in z
            $z: z

            g ->? w
            # g cannot be erased because w does not have a function
        ",
        )
        .unwrap();

        let inlined = bn.inline_inputs();

        assert_eq!(inlined.num_parameters(), 5);
        assert_eq!(inlined.num_vars(), 7);
        assert!(inlined.find_parameter("a").is_some());
        assert!(inlined.find_parameter("b").is_some());
        assert!(inlined.find_parameter("e").is_some());
        assert!(inlined.find_parameter("d").is_some());
        assert!(inlined.find_parameter("fun").is_some());
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
    }
}

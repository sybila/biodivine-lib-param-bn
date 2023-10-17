use crate::symbolic_async_graph::SymbolicContext;
use crate::Monotonicity::Inhibition;
use crate::{
    BooleanNetwork, FnUpdate, Monotonicity, Parameter, ParameterId, ParameterIdIterator,
    RegulatoryGraph, Variable, VariableId, VariableIdIterator, ID_REGEX,
};
use biodivine_lib_bdd::bdd;
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
    /// Infer a regulatory graph based on the update functions of this `BooleanNetwork`.
    ///
    /// The resulting graph is solely based on the information that can be inferred from the
    /// update functions. In particular, if the BN contains uninterpreted functions,
    /// the monotonicity of variables appearing within these functions is unknown. Overall,
    /// this method is typically only useful for fully specified networks with minor errors
    /// in the regulatory graph.
    ///
    /// The BN still has to satisfy basic integrity constraints. In particular, every uninterpreted
    /// function must be used, and must be used consistently (i.e. correct arity). Also, every
    /// update function may only use variables declared as regulators. Otherwise, an error
    /// is returned.
    pub fn infer_valid_graph(&self) -> Result<BooleanNetwork, String> {
        let ctx = SymbolicContext::new(self)?;

        let var_names = self
            .variables()
            .map(|id| self.get_variable_name(id))
            .cloned()
            .collect::<Vec<_>>();

        let mut new_rg = RegulatoryGraph::new(var_names);
        for target_var in self.variables() {
            let target_name = self.get_variable_name(target_var);
            if let Some(function) = self.get_update_function(target_var) {
                // If the update function exists, compute a BDD which describes all satisfying
                // inputs to that function, and then infer function properties from this BDD.
                let fn_is_true = ctx.mk_fn_update_true(function);
                let fn_is_false = fn_is_true.not();

                // All non-trivial code is explained in `impl_regulation_constraint`.

                for regulator_var in self.as_graph().regulators(target_var) {
                    let regulator_name = self.get_variable_name(regulator_var);

                    let regulator = ctx.state_variables()[regulator_var.0];
                    let regulator_is_true = ctx.bdd_variable_set().mk_var(regulator);
                    let regulator_is_false = ctx.bdd_variable_set().mk_not_var(regulator);

                    let observability = {
                        let fn_x1_to_1 = bdd!(fn_is_true & regulator_is_true).var_exists(regulator);
                        let fn_x0_to_1 =
                            bdd!(fn_is_true & regulator_is_false).var_exists(regulator);
                        bdd!(fn_x1_to_1 ^ fn_x0_to_1).exists(ctx.state_variables())
                    };

                    if !observability.is_false() {
                        let activation = {
                            let fn_x1_to_0 =
                                bdd!(fn_is_false & regulator_is_true).var_exists(regulator);
                            let fn_x0_to_1 =
                                bdd!(fn_is_true & regulator_is_false).var_exists(regulator);
                            bdd!(fn_x0_to_1 & fn_x1_to_0).exists(ctx.state_variables())
                        }
                        .not();

                        let inhibition = {
                            let fn_x0_to_0 =
                                bdd!(fn_is_false & regulator_is_false).var_exists(regulator);
                            let fn_x1_to_1 =
                                bdd!(fn_is_true & regulator_is_true).var_exists(regulator);
                            bdd!(fn_x0_to_0 & fn_x1_to_1).exists(ctx.state_variables())
                        }
                        .not();

                        let monotonicity = match (activation.is_false(), inhibition.is_false()) {
                            (false, true) => Some(Activation),
                            (true, false) => Some(Inhibition),
                            _ => None,
                        };

                        new_rg
                            .add_regulation(regulator_name, target_name, true, monotonicity)
                            .unwrap();
                    }
                }
            } else {
                // If the update function is missing, just copy the existing regulators, but
                // remove any monotonicity/observability.
                for regulator in self.as_graph().regulators(target_var) {
                    let regulator_name = self.get_variable_name(regulator);
                    new_rg
                        .add_regulation(regulator_name, target_name, false, None)
                        .unwrap();
                }
            }
        }

        let mut new_bn = BooleanNetwork::new(new_rg);
        for var in self.variables() {
            let name = self.get_variable_name(var);
            if let Some(update) = self.get_update_function(var) {
                // We first try to just copy the function. If there are no non-observable
                // variables this should work. If there is an error, we have to copy the
                // function using a string translation.
                if new_bn
                    .set_update_function(var, Some(update.clone()))
                    .is_err()
                {
                    let fn_bdd = ctx.mk_fn_update_true(update);
                    let fn_string = fn_bdd
                        .to_boolean_expression(ctx.bdd_variable_set())
                        .to_string();
                    new_bn.add_string_update_function(name, &fn_string).unwrap();
                }
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
                        update.walk_postorder(&mut |it: &FnUpdate| {
                            if let FnUpdate::Param(_, args) = it {
                                // If the input appears as function argument, we can't remove
                                // it because we don't have a way of substituting the argument.
                                is_ok = is_ok && !args.contains(input)
                            }
                        })
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
    /// The regulatory graph is updated to reflect this change. However, no further analysis
    /// of logical consistency is performed. You can use [BooleanNetwork::infer_valid_graph]
    /// to clean up the resulting graph if desired (for example, the method will remove any
    /// unused regulations should these be introduced by the reduction process).
    ///
    ///  > A simple example where "inconsistent" regulatory graph is produced is the inlining
    ///  > of a constant input variable `f_a = true` into the update function `f_c = a | b`.
    ///  > Here, we have regulations `a -> c` and `b -> c`. However, for the inlined function,
    ///  > we have `f_c = true | b = true`. As such, `b` is no longer observable in `f_c` and
    ///  > the resulting model is thus not "logically consistent". We need to either fix this
    ///  > manually, or using [BooleanNetwork::infer_valid_graph].
    ///
    /// ### Limitations
    ///
    /// **At the moment, the reduced variable cannot have a self-regulation.** If such variable
    /// is targeted with reduction, the result is `None`. Also, the variable cannot be inlined
    /// into uninterpreted functions (see [FnUpdate::substitute_variable]), in which case we also
    /// return `None`. We also cannot inline into *missing* update functions, but this is the
    /// same as inlining into uninterpreted functions.
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
    /// This does not mean you cannot use reduction on systems with uninterpreted functions at all,
    /// but be careful about the new meaning of the static constraints on these functions.
    ///
    pub fn inline_variable(&self, var: VariableId) -> Option<BooleanNetwork> {
        let var_regulators = self.as_graph().regulators(var);
        let var_targets = self.as_graph().targets(var);
        if var_targets.contains(&var) {
            // Cannot inline variable if it is self-regulated.
            return None;
        }
        let new_variables = self
            .variables()
            .filter(|it| *it != var)
            .map(|it| self[it].name.clone())
            .collect::<Vec<_>>();
        let mut new_rg = RegulatoryGraph::new(new_variables);

        // First, copy every regulation that does not involve `var` or is not "feed forward".
        for reg in self.as_graph().regulations() {
            if reg.target == var || reg.regulator == var {
                // Skip regulations where `var` is involved.
                continue;
            }
            if var_regulators.contains(&reg.regulator) && var_targets.contains(&reg.target) {
                // Skip regulations that directly circumvent `var`, because these will be
                // recreated in the next step, possibly with different monotonicity/observability.
                continue;
            }
            new_rg
                .add_regulation(
                    self.get_variable_name(reg.regulator),
                    self.get_variable_name(reg.target),
                    reg.observable,
                    reg.monotonicity,
                )
                .unwrap();
        }

        // Now, add a new regulation for every combination of the old regulators and targets,
        // but also incorporate the old "feed forward" regulations if present.
        for old_regulator in &var_regulators {
            for old_target in &var_targets {
                let old_one = self
                    .as_graph()
                    .find_regulation(*old_regulator, var)
                    .unwrap();
                let old_two = self.as_graph().find_regulation(var, *old_target).unwrap();
                let old_feed_forward = self.as_graph().find_regulation(*old_regulator, *old_target);

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
                        // If there is no feed forward regulation, we juse use the new monotonicity.
                        combined_monotonicity
                    };

                new_rg
                    .add_regulation(
                        self.get_variable_name(*old_regulator),
                        self.get_variable_name(*old_target),
                        new_observable,
                        new_monotonicity,
                    )
                    .unwrap();
            }
        }

        // Finally, we can actually inline the update functions, but as always, this is a bit
        // trickier than it sounds, because we have to translate [VariableId] and [ParameterId]
        // between the old and the new model.
        let mut new_bn = BooleanNetwork::new(new_rg);

        // First, build a map which assigns each "old" variable a "new" variable id. For the erased
        // variable, we use an invalid value.
        let mut old_to_new_var = Vec::with_capacity(self.num_vars());
        for v in self.variables() {
            if v == var {
                old_to_new_var.push(VariableId::from_index(usize::MAX));
            } else {
                let name = self.get_variable_name(v);
                let new_id = new_bn.as_graph().find_variable(name.as_str()).unwrap();
                old_to_new_var.push(new_id);
            }
        }

        // Then we do the same for parameters. However, since we are only doing inlining, the new
        // network will actually contain exactly the same parameters.
        let mut old_to_new_param = Vec::with_capacity(self.num_parameters());
        for param in self.parameters() {
            let param = &self[param];
            let new_id = new_bn
                .add_parameter(param.get_name(), param.get_arity())
                .unwrap();
            old_to_new_param.push(new_id);
        }

        // Now we can finally copy all the update functions, possibly inlining them along the way.
        let Some(var_function) = self.get_update_function(var).as_ref() else {
            // Cannot inline variable with implicit update function.
            return None;
        };

        for v in self.variables() {
            if v == var {
                continue;
            }

            let new_id = old_to_new_var[v.to_index()];
            let old_function = self.get_update_function(v).as_ref();
            if !var_targets.contains(&v) {
                // This variable is not regulated by `var`, hence we don't need any inlining
                // and we can just move the function to the new network.
                let new_function =
                    old_function.map(|it| it.substitute(&old_to_new_var, &old_to_new_param));
                new_bn.set_update_function(new_id, new_function).unwrap();
            } else {
                // This variable is regulated by `var`, hence we first need to inline the
                // update function and then translate the result into the new network.
                let Some(old_function) = old_function else {
                    // Cannot inline into missing update function.
                    return None;
                };
                let Some(inlined_function) = old_function.substitute_variable(var, var_function)
                else {
                    // We tried to inline the function, but it did not work. Most likely
                    // because there is an unknown function where
                    // the variable is used as an argument.
                    return None;
                };
                let new_function = inlined_function.substitute(&old_to_new_var, &old_to_new_param);
                new_bn
                    .set_update_function(new_id, Some(new_function))
                    .unwrap();
            }
        }

        Some(new_bn)
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

            # Both d and e appear in y, but only e can be erased as d appears in an uninterpreted
            # function.
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

        assert_eq!(inlined.num_parameters(), 4);
        assert_eq!(inlined.num_vars(), 8);
        assert!(inlined.find_parameter("a").is_some());
        assert!(inlined.find_parameter("b").is_some());
        assert!(inlined.find_parameter("e").is_some());
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
        assert_eq!(bn.inline_variable(b), Some(expected));

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
        assert_eq!(bn.inline_variable(d), Some(expected));

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
        assert_eq!(bn.inline_variable(a), Some(expected));

        // Reducing `c` should fail because it is inlining into an unknown function.
        assert_eq!(bn.inline_variable(c), None);

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
        assert_eq!(bn.inline_variable(b), None);
    }
}

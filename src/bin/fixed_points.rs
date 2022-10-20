use biodivine_lib_param_bn::fixed_points::FixedPoints;
use biodivine_lib_param_bn::symbolic_async_graph::SymbolicAsyncGraph;
use biodivine_lib_param_bn::{BinaryOp, BooleanNetwork, FnUpdate};
use z3::ast;
use z3::ast::{Ast, Dynamic};
use z3::{Context, FuncDecl, Solver, Sort};

fn main() {
    let args = std::env::args().collect::<Vec<_>>();
    let buffer = std::fs::read_to_string(&args[1]).unwrap();

    let model = BooleanNetwork::try_from(buffer.as_str()).unwrap();
    let model = model.inline_inputs();
    println!(
        "Loaded model with {} variables and {} inputs.",
        model.num_vars(),
        model.num_parameters()
    );
    // Fix inputs to true.
    /*for var in model.variables() {
        if model.get_update_function(var).is_none() {
            model
                .set_update_function(var, Some(FnUpdate::Const(true)))
                .unwrap();
        }
    }*/

    let stg = SymbolicAsyncGraph::new(model).unwrap();
    //println!("{}", stg.fixed_points_2().approx_cardinality());
    println!(
        "{}",
        FixedPoints::naive_greedy_bdd(&stg, stg.unit_colored_vertices()).approx_cardinality()
    );

    /*let z3_config = z3::Config::new();
    let z3 = z3::Context::new(&z3_config);
    let solver = Solver::new(&z3);

    let e_bool = MyContext::new(&z3, &model);

    for var in model.variables() {
        let update = model.get_update_function(var).as_ref().unwrap();
        let eval = e_bool.eval_with(update, &e_bool.variables).as_datatype().unwrap();
        let x = e_bool.variables[var.to_index()].apply(&[]).as_datatype().unwrap();
        let eq = e_bool.check_eq(&x, &eval);
        //println!("{:?}", eq);
        solver.assert(&eq);
    }

    println!("{:?}", solver.check());
    println!("{:?}", solver.get_model());*/

    /*let (sort, constants, checks) = Sort::enumeration(
        &z3,
        "ebool".into(),
        &["0".into(), "1".into(), "*".into()]
    );

    let zero = &constants[0];
    let one = &constants[1];
    let star = &constants[2];

    let is_zero = &checks[0];
    let is_one = &checks[1];
    let is_star = &checks[2];

    println!("{:?}", star);
    println!("{:?}", is_star);

    let zero_obj = zero.apply(&[]);
    let star_obj = star.apply(&[]);


    let some_e_bool = FuncDecl::new::<&str>(&z3, "x".into(), &[], &sort);
    let x = some_e_bool.apply(&[]);

    let check_star = is_star.apply(&[&x]);

    let solver = Solver::new(&z3);
    solver.assert(&check_star.try_into().unwrap());
    println!("{:?}", solver.check());
    println!("{:?}", solver.get_model());*/
}

struct MyContext<'ctx> {
    pub ctx: &'ctx Context,
    pub e_bool: (Sort<'ctx>, Vec<FuncDecl<'ctx>>, Vec<FuncDecl<'ctx>>),
    pub variables: Vec<FuncDecl<'ctx>>,
}

impl<'ctx> MyContext<'ctx> {
    pub fn new(z3: &'ctx Context, network: &BooleanNetwork) -> Self {
        let sort = Sort::enumeration(&z3, "ebool".into(), &["0".into(), "1".into(), "*".into()]);
        let constructors = network
            .variables()
            .map(|it| {
                let name = network.get_variable_name(it);
                FuncDecl::new::<&str>(z3, name.as_str(), &[], &sort.0)
            })
            .collect();
        MyContext {
            ctx: z3,
            e_bool: sort,
            variables: constructors,
        }
    }

    pub fn is_zero(&self, x: &dyn ast::Ast<'ctx>) -> ast::Bool<'ctx> {
        self.e_bool.2[0].apply(&[x]).as_bool().unwrap()
    }

    pub fn is_one(&self, x: &dyn ast::Ast<'ctx>) -> ast::Bool<'ctx> {
        self.e_bool.2[1].apply(&[x]).as_bool().unwrap()
    }

    pub fn is_star(&self, x: &dyn ast::Ast<'ctx>) -> ast::Bool<'ctx> {
        self.e_bool.2[2].apply(&[x]).as_bool().unwrap()
    }

    pub fn mk_zero(&self) -> Dynamic {
        self.e_bool.1[0].apply(&[])
    }

    pub fn mk_one(&self) -> Dynamic {
        self.e_bool.1[1].apply(&[])
    }

    pub fn mk_star(&self) -> Dynamic {
        self.e_bool.1[2].apply(&[])
    }

    pub fn e_bool_and(&self, left: &dyn ast::Ast<'ctx>, right: &dyn ast::Ast<'ctx>) -> Dynamic {
        let left_is_one = self.is_one(left);
        let right_is_one = self.is_one(right);
        let left_is_zero = self.is_zero(left);
        let right_is_zero = self.is_zero(right);
        let left_and_right_is_zero = left_is_zero & right_is_zero;
        let left_or_right_is_one = left_is_one | right_is_one;
        /*
           if left == One or right == One {
               One
           } else if left == Zero and right == Zero {
               Zero
           } else {
               Star
           }
        */
        let x = left_and_right_is_zero.ite(&self.mk_zero(), &self.mk_star());
        let x = left_or_right_is_one.ite(&self.mk_one(), &x);
        x
    }

    pub fn e_bool_or(&self, left: &dyn ast::Ast<'ctx>, right: &dyn ast::Ast<'ctx>) -> Dynamic {
        let left_is_one = self.is_one(left);
        let right_is_one = self.is_one(right);
        let left_is_zero = self.is_zero(left);
        let right_is_zero = self.is_zero(right);
        let left_or_right_is_zero = left_is_zero | right_is_zero;
        let left_and_right_is_one = left_is_one & right_is_one;
        /*
           if left == Zero or right == Zero {
               Zero
           } else if left == One and right == One {
               One
           } else {
               Star
           }
        */
        let x = left_and_right_is_one.ite(&self.mk_one(), &self.mk_star());
        let x = left_or_right_is_zero.ite(&self.mk_zero(), &x);
        x
    }

    pub fn e_bool_not(&self, inner: &dyn ast::Ast<'ctx>) -> Dynamic {
        let inner_is_one = self.is_one(inner);
        let inner_is_zero = self.is_zero(inner);
        let x = inner_is_zero.ite(&self.mk_one(), &self.mk_star());
        let x = inner_is_one.ite(&self.mk_zero(), &x);
        x
    }

    pub fn check_eq(&self, left: &ast::Datatype<'ctx>, right: &ast::Datatype<'ctx>) -> ast::Bool {
        left._eq(right)
    }

    pub fn eval_with(&'ctx self, update: &FnUpdate, valuation: &[FuncDecl<'ctx>]) -> Dynamic<'ctx> {
        match update {
            FnUpdate::Const(value) => {
                if *value {
                    self.mk_one()
                } else {
                    self.mk_zero()
                }
            }
            FnUpdate::Var(var) => valuation[var.to_index()].apply(&[]),
            FnUpdate::Param(_, _) => {
                unimplemented!()
            }
            FnUpdate::Not(inner) => {
                let inner = self.eval_with(inner, valuation);
                self.e_bool_not(&inner)
            }
            FnUpdate::Binary(op, left, right) => {
                let left = self.eval_with(left, valuation);
                let right = self.eval_with(right, valuation);
                match op {
                    BinaryOp::And => self.e_bool_and(&left, &right),
                    BinaryOp::Or => self.e_bool_or(&left, &right),
                    _ => unimplemented!(),
                }
            }
        }
    }
}

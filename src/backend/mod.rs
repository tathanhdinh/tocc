// Back-end:
//  - register allocation
//  - machine code generation

use std::{
	collections::HashMap,
	mem,
	sync::atomic::{AtomicUsize, Ordering},
};

use cranelift::prelude::*;
use cranelift_module::{Linkage, Module};
use cranelift_simplejit::{SimpleJITBackend, SimpleJITBuilder};

use crate::frontend::ast::{
	BinaryOperator, BinaryOperatorExpression, Constant, Declaration,
	Expression, FunctionDefinition, Identifier, Integer, Statement,
	TranslationUnit, TypeSpecifier, UnaryOperator, UnaryOperatorExpression,
};

static NEW_VAR_INDEX: AtomicUsize = AtomicUsize::new(0);

fn translate_expression(
	expr: &Expression,
	fb: &mut FunctionBuilder,
	scope: &HashMap<String, Variable>,
) -> Value {
	use Expression::*;
	match expr {
		UnaryOperatorExpr(UnaryOperatorExpression { op, rhs }) => {
			let rhs = translate_expression(rhs, fb, scope);

			use UnaryOperator::*;
			match op {
				Neg => {
					let lhs = fb.ins().iconst(types::I64, 0);
					fb.ins().isub(lhs, rhs)
				}
			}
		}

		BinaryOperatorExpr(BinaryOperatorExpression { op, lhs, rhs }) => {
			let lhs = translate_expression(lhs, fb, scope);
			let rhs = translate_expression(rhs, fb, scope);

			use BinaryOperator::*;
			match op {
				Mul => fb.ins().imul(lhs, rhs),

				Div => fb.ins().sdiv(lhs, rhs),

				Add => fb.ins().iadd(lhs, rhs),

				Sub => fb.ins().isub(lhs, rhs),

				_ => {
					unreachable!();
				}
			}
		}

		ConstantExpr(Constant::IntegerConst(Integer(i))) => {
			fb.ins().iconst(types::I64, *i)
		}

		IdentifierExpr(Identifier(var_name)) => {
			let var = scope.get(var_name).unwrap(); // check in semantics analysis
			fb.use_var(*var)
		}
	}
}

fn translate_statement(
	stmt: &Statement,
	fb: &mut FunctionBuilder,
	scope: &mut HashMap<String, Variable>,
) {
	use Statement::*;
	match stmt {
		CompoundStmt(statements) => {
			for s in statements.iter() {
				translate_statement(s, fb, scope);
			}
		}

		DeclarationStmt(Declaration {
			specifier,
			declarator: Identifier(var_name),
		}) => {
			let new_var =
				Variable::new(NEW_VAR_INDEX.fetch_add(1, Ordering::Relaxed));
			use TypeSpecifier::*;
			match specifier {
				Int => {
					fb.declare_var(new_var, types::I64);
					let default_val = fb.ins().iconst(types::I64, 0);
					fb.def_var(new_var, default_val);
				}
			}
			scope.insert(var_name.into(), new_var);
		}

		ExpressionStmt(e) => {
			use Expression::*;
			match &**e {
				BinaryOperatorExpr(BinaryOperatorExpression {
					op,
					lhs,
					rhs,
				}) => {
					use BinaryOperator::*;
					match op {
						Asg => match &**lhs {
							IdentifierExpr(Identifier(var_name)) => {
								let var = scope.get(var_name).unwrap(); // should be checked in semantics analysis
								let new_val =
									translate_expression(&*rhs, fb, scope);
								fb.def_var(*var, new_val);
							}

							_ => {}
						},

						_ => {}
					}
				}

				_ => {}
			}
		}

		ReturnStmt(opt_expr) => {
			if let Some(expr) = opt_expr {
				let v = translate_expression(expr, fb, scope);
				fb.ins().return_(&[v]);
			}
		}
	}
}

pub fn compile(
	tu: &TranslationUnit,
) -> (Box<unsafe extern "C" fn() -> i64>, usize) {
	let TranslationUnit::FunctionDefinition(FunctionDefinition {
		specifier: TypeSpecifier::Int,
		declarator: Identifier(fname),
		// body: Statement::CompoundStmt(s),
		body,
	}) = tu;
	let builder =
		SimpleJITBuilder::new(cranelift_module::default_libcall_names());
	let mut module = Module::<SimpleJITBackend>::new(builder);
	let mut context = module.make_context();
	context
		.func
		.signature
		.returns
		.push(AbiParam::new(types::I64));

	// layout
	let mut fbc = FunctionBuilderContext::new();
	let mut fb = FunctionBuilder::new(&mut context.func, &mut fbc);
	let ebb = fb.create_ebb();
	fb.switch_to_block(ebb);

	let mut scope = HashMap::new();
	translate_statement(body, &mut fb, &mut scope);

	// finalize function
	fb.seal_block(ebb);
	fb.finalize();

	let fid = module
		.declare_function(fname, Linkage::Export, &context.func.signature)
		.expect("Failed to declare function");
	let flen = module
		.define_function(fid, &mut context)
		.expect("Failed to define function");

	module.clear_context(&mut context);
	// SELinux workaround: "sudo setenforce 0"
	module.finalize_definitions();

	let fptr = module.get_finalized_function(fid);
	let fptr = unsafe { mem::transmute::<_, _>(fptr) };

	(Box::new(fptr), flen as _)
}

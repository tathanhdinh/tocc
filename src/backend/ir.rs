use std::{
	collections::HashMap,
	hint::unreachable_unchecked,
	mem,
	sync::atomic::{AtomicUsize, Ordering},
};

use cranelift::prelude::*;
use cranelift_module::{Linkage, Module};
use cranelift_simplejit::{SimpleJITBackend, SimpleJITBuilder};

use crate::frontend::syntax::{
	BinaryOperator, BinaryOperatorExpression, Constant, Declaration,
	Expression, ExternalDeclaration, FunctionDefinition, Identifier, Integer,
	Statement, TranslationUnit, TypeSpecifier, UnaryOperator,
	UnaryOperatorExpression,
};

static NEW_VAR_ID: AtomicUsize = AtomicUsize::new(0);

fn translate_expression(
	expr: &Expression,
	fb: &mut FunctionBuilder,
	env: &HashMap<&str, Variable>,
) -> Value {
	use Expression::*;
	match expr {
		UnaryOperatorExpr(UnaryOperatorExpression { op, rhs }) => {
			let rhs = translate_expression(rhs, fb, env);

			use UnaryOperator::*;
			match op {
				Neg => {
					let lhs = fb.ins().iconst(types::I64, 0);
					fb.ins().isub(lhs, rhs)
				}
			}
		}

		BinaryOperatorExpr(BinaryOperatorExpression { op, lhs, rhs }) => {
			let lhs = translate_expression(lhs, fb, env);
			let rhs = translate_expression(rhs, fb, env);

			use BinaryOperator::*;
			match op {
				Mul => fb.ins().imul(lhs, rhs),
				Div => fb.ins().sdiv(lhs, rhs),
				Add => fb.ins().iadd(lhs, rhs),
				Sub => fb.ins().isub(lhs, rhs),
				_ => unsafe { unreachable_unchecked() },
			}
		}

		ConstantExpr(Constant::IntegerConst(Integer(i))) => {
			fb.ins().iconst(types::I64, *i)
		}

		IdentifierExpr(Identifier(var_name)) => {
			if let Some(var) = env.get(var_name.as_str()) {
				fb.use_var(*var)
			} else {
				// checked already in semantics analysis
				unsafe { unreachable_unchecked() }
			}
		}
	}
}

fn translate_declaration_statement<'a>(
	stmt: &'a Statement,
	fb: &mut FunctionBuilder,
	env: &mut HashMap<&'a str, Variable>,
) {
	use Statement::*;
	match stmt {
		DeclarationStmt(Declaration {
			specifier,
			declarator: Identifier(var_name),
		}) => {
			let new_var =
				Variable::new(NEW_VAR_ID.fetch_add(1, Ordering::Relaxed));

			use TypeSpecifier::*;
			match specifier {
				Int => {
					fb.declare_var(new_var, types::I64);
					let default_val = fb.ins().iconst(types::I64, 0);
					fb.def_var(new_var, default_val);
				}
			}

			// add new or update current binding
			env.insert(var_name.as_str(), new_var);
		}

		_ => unsafe { unreachable_unchecked() },
	}
}

fn translate_expression_statement(
	stmt: &Statement,
	fb: &mut FunctionBuilder,
	env: &HashMap<&str, Variable>,
) {
	use Statement::*;
	match stmt {
		ExpressionStmt(expr) => {
			if let Some(expr) = expr {
				use Expression::*;
				match &**expr {
					BinaryOperatorExpr(BinaryOperatorExpression {
						op,
						lhs,
						rhs,
					}) => {
						use BinaryOperator::*;
						match op {
							Asg => match &**lhs {
								IdentifierExpr(Identifier(var_name)) => {
									if let Some(var) =
										env.get(var_name.as_str())
									{
										let new_val = translate_expression(
											&*rhs, fb, env,
										);
										fb.def_var(*var, new_val);
									} else {
										// already checked in semantics analysis
										unsafe { unreachable_unchecked() }
									}
								},

								_ => {
									// TODO
								}
							},

							_ => {
								// TODO
							}
						}
					}

					_ => {
						// TODO
					}
				}
			}
		}

		_ => unsafe { unreachable_unchecked() },
	}
}

fn translate_return_statement(
	stmt: &Statement,
	fb: &mut FunctionBuilder,
	env: &HashMap<&str, Variable>,
) {
	use Statement::*;
	match stmt {
		ReturnStmt(opt_expr) => {
			if let Some(expr) = opt_expr {
				let v = translate_expression(expr, fb, env);
				fb.ins().return_(&[v]);
			}
		}

		_ => unsafe { unreachable_unchecked() },
	}
}

fn translate_statement<'a>(
	stmt: &'a Statement,
	fb: &mut FunctionBuilder,
	env: &mut HashMap<&'a str, Variable>,
) {
	use Statement::*;
	match stmt {
		CompoundStmt(statements) => {
			let mut nested_env = env.clone();
			for s in statements.iter() {
				translate_statement(s, fb, &mut nested_env);
			}
		}
		DeclarationStmt(_) => translate_declaration_statement(stmt, fb, env),
		ExpressionStmt(_) => translate_expression_statement(stmt, fb, env),
		ReturnStmt(_) => translate_return_statement(stmt, fb, env),
		_ => {}
	}
}

pub fn compile(
	tu: &TranslationUnit,
) -> Option<(Box<unsafe extern "C" fn() -> i64>, usize)> {
	let mut result = None;

	let TranslationUnit(eds) = tu;
	for ed in eds.iter() {
		use ExternalDeclaration::*;
		match ed {
			FunctionDefinitionDecl(FunctionDefinition {
				specifier,
				declarator: Identifier(fname),
				body,
			}) => {
				let builder = SimpleJITBuilder::new(
					cranelift_module::default_libcall_names(),
				);
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
					.declare_function(
						fname,
						Linkage::Export,
						&context.func.signature,
					)
					.expect("Failed to declare function");
				let flen = module
					.define_function(fid, &mut context)
					.expect("Failed to define function");

				module.clear_context(&mut context);
				// SELinux workaround: "sudo setenforce 0"
				module.finalize_definitions();

				let fptr = module.get_finalized_function(fid);
				let fptr = unsafe { mem::transmute::<_, _>(fptr) };

				result = Some((Box::new(fptr), flen as _));
			}
		}
	}

	return result;
}

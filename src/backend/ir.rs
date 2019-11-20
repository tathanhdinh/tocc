use std::{
	collections::HashMap,
	hint::unreachable_unchecked,
	mem, slice,
	sync::atomic::{AtomicUsize, Ordering},
};

use cranelift::prelude::*;
use cranelift_codegen::{
	ir::{entities::StackSlot, Function},
	Context,
};
use cranelift_module::{Linkage, Module};
use cranelift_simplejit::SimpleJITBackend;

use crate::frontend::syntax::{
	BinaryOperator, BinaryOperatorExpression, Constant, Declaration, Expression,
	ExternalDeclaration, FunctionDeclarator, FunctionDefinition, Identifier, Integer,
	MemberExpression, Statement, TranslationUnit, TypeSpecifier, UnaryOperator,
	UnaryOperatorExpression,
};

static NEW_VAR_ID: AtomicUsize = AtomicUsize::new(0);

#[derive(Clone)]
enum SimpleTypedVariable {
	Primitive(Variable),
	Aggregate(StackSlot),
}

// binding context
type Environment<'a> = HashMap<&'a str, SimpleTypedVariable>;

fn translate_expression(expr: &Expression, fb: &mut FunctionBuilder, env: &Environment) -> Value {
	use Expression::*;
	match expr {
		UnaryOperatorExpr(UnaryOperatorExpression { op, rhs }) => {
			let rhs = translate_expression(rhs, fb, env);

			use UnaryOperator::*;
			match op {
				Neg => {
					let lhs = fb.ins().iconst(types::I32, 0);
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

		ConstantExpr(Constant::IntegerConst(Integer(i))) => fb.ins().iconst(types::I32, *i as i64),

		IdentifierExpr(Identifier(var_name)) => {
			if let Some(var) = env.get(var_name.as_str()) {
				use SimpleTypedVariable::*;
				if let Primitive(var) = var {
					fb.use_var(*var)
				} else {
					// an identifier never has Aggregate type
					unsafe { unreachable_unchecked() }
				}
			} else {
				// checked already in semantics analysis
				unsafe { unreachable_unchecked() }
			}
		}

		// e.g. 3 + s.i for some struct s with member i
		MemberExpr(MemberExpression { expression, .. }) => {
			use Expression::*;
			// simplification: suppose that each struct has a single member, so
			// we just need to remember the name of the struct
			if let IdentifierExpr(Identifier(var_name)) = &**expression {
				if let Some(var) = env.get(var_name.as_str()) {
					use SimpleTypedVariable::*;
					if let Aggregate(stack_slot) = var {
						fb.ins().stack_load(types::I32, *stack_slot, 0)
					} else {
						unsafe { unreachable_unchecked() }
					}
				} else {
					// TODO: check in semantics analysis
					panic!(format!("Variable {} doesn't exist", var_name))
				}
			} else {
				// TODO
				panic!("Failed to translate struct expression")
			}
		}
	}
}

fn translate_declaration_statement<'a>(
	stmt: &'a Statement,
	fb: &mut FunctionBuilder,
	env: &mut Environment<'a>,
) {
	use Statement::*;
	match stmt {
		DeclarationStmt(Declaration {
			specifier,
			declarator: Identifier(var_name),
		}) => {
			use SimpleTypedVariable::*;
			use TypeSpecifier::*;
			match specifier {
				Int => {
					let new_var = Variable::new(NEW_VAR_ID.fetch_add(1, Ordering::Relaxed));
					fb.declare_var(new_var, types::I32);
					let default_val = fb.ins().iconst(types::I32, 0);
					fb.def_var(new_var, default_val);
					env.insert(var_name.as_str(), Primitive(new_var));
				}

				Struct(_) => {
					let struct_data =
						StackSlotData::new(StackSlotKind::ExplicitSlot, types::I32.bytes());
					let stack_slot = fb.create_stack_slot(struct_data);
					env.insert(var_name.as_str(), Aggregate(stack_slot));
				}
			}
		}

		_ => unsafe { unreachable_unchecked() },
	}
}

fn translate_binary_operator_expression_statement(
	expr: &Expression,
	fb: &mut FunctionBuilder,
	env: &Environment,
) {
	use Expression::*;
	match expr {
		BinaryOperatorExpr(BinaryOperatorExpression { op, lhs, rhs }) => {
			use BinaryOperator::*;
			match op {
				Asg => match &**lhs {
					IdentifierExpr(Identifier(var_name)) => {
						if let Some(var) = env.get(var_name.as_str()) {
							use SimpleTypedVariable::*;
							if let Primitive(var) = var {
								let new_val = translate_expression(&*rhs, fb, env);
								fb.def_var(*var, new_val);
							} else {
								// an identifier never has Aggregate type
								unsafe { unreachable_unchecked() }
							}
						} else {
							// already checked in semantics analysis
							unsafe { unreachable_unchecked() }
						}
					}

					MemberExpr(MemberExpression {
						// identifier: Identifier(var_name),
						expression,
						..
					}) => {
						// simplification: suppose that each struct has a single member, so
						// we just need to remember the name of the struct
						if let IdentifierExpr(Identifier(var_name)) = &**expression {
							if let Some(var) = env.get(var_name.as_str()) {
								use SimpleTypedVariable::*;
								if let Aggregate(stack_slot) = var {
									let rhs_val = translate_expression(&*rhs, fb, env);
									fb.ins().stack_store(rhs_val, *stack_slot, 0);
								} else {
									unsafe { unreachable_unchecked() }
								}
							} else {
								// already checked in semantics analysis
								unsafe { unreachable_unchecked() }
							}
						} else {
							// TODO
							panic!("Failed to translate struct expression")
						}
					}

					_ => panic!("Unhandled expression for assignment's LHS"),
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

fn translate_expression_statement(stmt: &Statement, fb: &mut FunctionBuilder, env: &Environment) {
	use Statement::*;
	if let ExpressionStmt(expr) = stmt {
		if let Some(expr) = expr {
			use Expression::*;
			match expr {
				BinaryOperatorExpr(_) => {
					translate_binary_operator_expression_statement(expr, fb, env)
				}

				_ => {
					// TODO
				}
			}
		}
	} else {
		unsafe { unreachable_unchecked() }
	}
}

fn translate_return_statement(stmt: &Statement, fb: &mut FunctionBuilder, env: &Environment) {
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
	env: &mut Environment<'a>,
) {
	use Statement::*;
	match stmt {
		CompoundStmt(stmts) => {
			let mut nested_env = env.clone();
			for stmt in stmts.iter() {
				translate_statement(stmt, fb, &mut nested_env);
			}
		}
		DeclarationStmt(_) => translate_declaration_statement(stmt, fb, env),
		ExpressionStmt(_) => translate_expression_statement(stmt, fb, env),
		ReturnStmt(_) => translate_return_statement(stmt, fb, env),
	}
}

fn translate_function_definition<'a>(
	func: &ExternalDeclaration,
	module: &'a mut Module<SimpleJITBackend>,
	context: &mut Context,
	env: &mut Environment,
) -> &'a [u8] {
	use ExternalDeclaration::*;
	if let FunctionDefinitionDecl(FunctionDefinition {
		specifier,
		declarator: FunctionDeclarator {
			identifier: Identifier(fname),
			parameters,
		},
		body,
	}) = func
	{
		use TypeSpecifier::*;
		// return type
		match specifier {
			Int => context
				.func
				.signature
				.returns
				.push(AbiParam::new(types::I32)),

			_ => {
				// TODO
				panic!("Unsupported return type");
			}
		}
		// parameter types
		for param in parameters.iter() {
			let Declaration { specifier, .. } = param;
			match specifier {
				Int => context
					.func
					.signature
					.params
					.push(AbiParam::new(types::I32)),

				_ => {
					// TODO
					panic!("Unsupported parameter type");
				}
			}
		}

		let mut fb_ctxt = FunctionBuilderContext::new();
		let mut fb = FunctionBuilder::new(&mut context.func, &mut fb_ctxt);

		// create entry extended basic block, set parameters as function parameters, and switch to the block
		let entry_ebb = fb.create_ebb();
		fb.append_ebb_params_for_function_params(entry_ebb);
		fb.switch_to_block(entry_ebb);
		fb.seal_block(entry_ebb);

		let mut env = env.clone();

		// declare parameters
		for (i, param) in parameters.iter().enumerate() {
			let Declaration {
				declarator: Identifier(pname),
				specifier,
			} = param;
			let pval = fb.ebb_params(entry_ebb)[i];
			let pvar = Variable::new(NEW_VAR_ID.fetch_add(1, Ordering::Relaxed));
			// fb.declare_var(pvar, ctxt.func.dfg.value_type(pval));
			use SimpleTypedVariable::*;
			match specifier {
				Int => {
					fb.declare_var(pvar, types::I32);
					env.insert(pname.as_str(), Primitive(pvar));
				}

				_ => panic!("Unsupported parameter type"),
			}
			fb.def_var(pvar, pval);
		}

		// translate function body
		translate_statement(body, &mut fb, &mut env);

		// finalize the function translation
		fb.finalize();

		let fid = module
			.declare_function(fname, Linkage::Export, &context.func.signature)
			.expect("Failed to declare function");
		let flen = module
			.define_function(fid, context)
			.expect("Failed to define function");

		module.clear_context(context);
		// SELinux workaround: "sudo setenforce 0"
		module.finalize_definitions();

		let fptr = module.get_finalized_function(fid);
		unsafe { slice::from_raw_parts(mem::transmute::<_, *const u8>(fptr), flen as _) }
	} else {
		unsafe { unreachable_unchecked() }
	}
}

fn evaluate_function_definition<'a>(
	func: &ExternalDeclaration,
	module: &'a mut Module<SimpleJITBackend>,
	context: &'a mut Context,
	env: &mut Environment,
) -> &'a Function {
	use ExternalDeclaration::*;
	if let FunctionDefinitionDecl(FunctionDefinition {
		specifier,
		declarator: FunctionDeclarator {
			identifier: Identifier(fname),
			parameters,
		},
		body,
	}) = func
	{
		use TypeSpecifier::*;
		// return type
		match specifier {
			Int => context
				.func
				.signature
				.returns
				.push(AbiParam::new(types::I32)),

			_ => {
				// TODO
				panic!("Unsupported return type");
			}
		}
		// parameter types
		for param in parameters.iter() {
			let Declaration { specifier, .. } = param;
			match specifier {
				Int => context
					.func
					.signature
					.params
					.push(AbiParam::new(types::I32)),

				_ => {
					// TODO
					panic!("Unsupported parameter type");
				}
			}
		}

		let mut fb_ctxt = FunctionBuilderContext::new();
		let mut fb = FunctionBuilder::new(&mut context.func, &mut fb_ctxt);

		// create entry extended basic block, set parameters as function parameters, and switch to the block
		let entry_ebb = fb.create_ebb();
		fb.append_ebb_params_for_function_params(entry_ebb);
		fb.switch_to_block(entry_ebb);
		fb.seal_block(entry_ebb);

		let mut env = env.clone();

		// declare parameters
		for (i, param) in parameters.iter().enumerate() {
			let Declaration {
				declarator: Identifier(pname),
				specifier,
			} = param;
			let pval = fb.ebb_params(entry_ebb)[i];
			let pvar = Variable::new(NEW_VAR_ID.fetch_add(1, Ordering::Relaxed));
			// fb.declare_var(pvar, ctxt.func.dfg.value_type(pval));
			use SimpleTypedVariable::*;
			match specifier {
				Int => {
					fb.declare_var(pvar, types::I32);
					env.insert(pname.as_str(), Primitive(pvar));
				}

				_ => panic!("Unsupported parameter type"),
			}
			fb.def_var(pvar, pval);
		}

		// translate function body
		translate_statement(body, &mut fb, &mut env);

		// finalize the function translation
		fb.finalize();

		&context.func
	} else {
		unsafe { unreachable_unchecked() }
	}
}

pub fn compile_function<'a>(
	fname: &str,
	module: &'a mut Module<SimpleJITBackend>,
	context: &'a mut Context,
) -> &'a [u8] {
	let fid = module
		.declare_function(fname, Linkage::Export, &context.func.signature)
		.expect("Failed to declare function");
	let flen = module
		.define_function(fid, context)
		.expect("Failed to define function");

	module.clear_context(context);
	module.finalize_definitions(); // SELinux workaround: "sudo setenforce 0"

	let fptr = module.get_finalized_function(fid);
	unsafe { slice::from_raw_parts(mem::transmute::<_, *const u8>(fptr), flen as _) }
}

pub fn evaluate<'a>(
	tu: &TranslationUnit,
	module: &'a mut Module<SimpleJITBackend>,
	context: &'a mut Context,
) -> &'a Function {
	let TranslationUnit(extern_decs) = tu;
	let mut env = Environment::new();

	for dec in extern_decs.iter() {
		use ExternalDeclaration::*;
		match dec {
			FunctionDefinitionDecl(_) => {
				return evaluate_function_definition(dec, module, context, &mut env)
			}
			_ => panic!("Unsupported external declaration"),
		}
	}

	panic!("No function to evaluate")
}

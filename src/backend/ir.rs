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
use cranelift_module::{FuncId, Linkage, Module};
use cranelift_simplejit::SimpleJITBackend;

use crate::{
	error,
	frontend::syntax::{
		BinaryOperator, BinaryOperatorExpression, CallExpression, Constant, Declaration,
		Expression, ExternalDeclaration, FunctionDeclarator, FunctionDefinition, Identifier,
		Integer, MemberExpression, Statement, TranslationUnit, TypeSpecifier, UnaryOperator,
		UnaryOperatorExpression,
	},
	unimpl,
};

static NEW_VAR_ID: AtomicUsize = AtomicUsize::new(0);

#[derive(Clone)]
pub struct PrimitiveIdentifier {
	pub variable: Variable,
	pub variable_type: Type,
}

#[derive(Clone)]
pub struct FunctionIdentifier {
	pub function_id: FuncId,
	pub return_type: Type,
	pub parameter_types: Vec<Type>,
}

#[derive(Clone)]
pub enum SimpleTypedIdentifier {
	Primitive(PrimitiveIdentifier),
	Aggregate(StackSlot),
	Function(FunctionIdentifier),
}

// binding context
pub type Environment<'a> = HashMap<&'a str, SimpleTypedIdentifier>;

// backend-ed module
pub type BackedModule = Module<SimpleJITBackend>;

fn translate_expression<'clif, 'tcx>(
	expr: &'tcx Expression,
	fb: &'clif mut FunctionBuilder,
	bm: &'clif mut BackedModule,
	env: &Environment<'tcx>,
) -> Value {
	use Expression::*;
	match expr {
		UnaryOperatorExpr(UnaryOperatorExpression { op, rhs }) => {
			let rhs = translate_expression(rhs, fb, bm, env);

			use UnaryOperator::*;
			match op {
				Neg => {
					let lhs = fb.ins().iconst(types::I32, 0);
					fb.ins().isub(lhs, rhs)
				}
			}
		}

		BinaryOperatorExpr(BinaryOperatorExpression { op, lhs, rhs }) => {
			let lhs = translate_expression(lhs, fb, bm, env);
			let rhs = translate_expression(rhs, fb, bm, env);

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
				use SimpleTypedIdentifier::*;
				if let Primitive(PrimitiveIdentifier { variable, .. }) = var {
					fb.use_var(*variable)
				} else {
					// an identifier never has Aggregate type
					// unsafe { unreachable_unchecked() }
					error!("identifier has non primitive type")
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
					use SimpleTypedIdentifier::*;
					if let Aggregate(stack_slot) = var {
						fb.ins().stack_load(types::I32, *stack_slot, 0)
					} else {
						unsafe { unreachable_unchecked() }
					}
				} else {
					// TODO: check in semantics analysis
					error!("Variable {} doesn't exist", var_name)
				}
			} else {
				// TODO
				error!("Failed to translate struct expression")
			}
		}

		CallExpr(CallExpression {
			callee: Identifier(fname),
			arguments,
		}) => {
			if let Some(SimpleTypedIdentifier::Function(FunctionIdentifier {
				return_type,
				parameter_types,
				..
			})) = env.get(fname.as_str())
			{
				let mut sig = bm.make_signature();
				// let mut sig = Signature::new(CallConv::SystemV);
				// return type
				sig.returns.push(AbiParam::new(*return_type));
				// parameter types
				for ptype in parameter_types {
					sig.params.push(AbiParam::new(*ptype));
				}
				let callee = bm
					.declare_function(fname.as_str(), Linkage::Import, &sig)
					.expect("Failed to declare function");
				let local_callee = bm.declare_func_in_func(callee, fb.func);
				let arg_values: Vec<_> = arguments
					.iter()
					.map(|arg| translate_expression(arg, fb, bm, env))
					.collect();
				let call = fb.ins().call(local_callee, &arg_values);
				fb.inst_results(call)[0]
			} else {
				// TODO: check in semantics analysis
				unsafe { unreachable_unchecked() }
			}
		}
	}
}

fn translate_declaration_statement<'clif, 'tcx>(
	stmt: &'tcx Statement,
	fb: &'clif mut FunctionBuilder,
	env: &mut Environment<'tcx>,
) {
	use Statement::*;
	match stmt {
		DeclarationStmt(Declaration {
			specifier,
			declarator: Identifier(var_name),
		}) => {
			use SimpleTypedIdentifier::*;
			use TypeSpecifier::*;
			match specifier {
				Int => {
					let new_var = Variable::new(NEW_VAR_ID.fetch_add(1, Ordering::Relaxed));
					fb.declare_var(new_var, types::I32);
					let default_val = fb.ins().iconst(types::I32, 0);
					fb.def_var(new_var, default_val);

					// update environment
					env.insert(
						var_name.as_str(),
						Primitive(PrimitiveIdentifier {
							variable: new_var,
							variable_type: types::I32,
						}),
					);
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

fn translate_binary_operator_expression_statement<'clif, 'tcx>(
	expr: &'tcx Expression,
	fb: &'clif mut FunctionBuilder,
	bm: &'clif mut BackedModule,
	env: &'tcx Environment<'tcx>,
) {
	use Expression::*;
	match expr {
		BinaryOperatorExpr(BinaryOperatorExpression { op, lhs, rhs }) => {
			use BinaryOperator::*;
			match op {
				Asg => match &**lhs {
					IdentifierExpr(Identifier(var_name)) => {
						if let Some(var) = env.get(var_name.as_str()) {
							use SimpleTypedIdentifier::*;
							if let Primitive(PrimitiveIdentifier { variable, .. }) = var {
								let new_val = translate_expression(&*rhs, fb, bm, env);
								fb.def_var(*variable, new_val);
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
								use SimpleTypedIdentifier::*;
								if let Aggregate(stack_slot) = var {
									let rhs_val = translate_expression(&*rhs, fb, bm, env);
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

					_ => unimpl!("Unhandled expression for assignment's LHS"),
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

fn translate_expression_statement<'clif, 'tcx>(
	stmt: &'tcx Statement,
	fb: &'clif mut FunctionBuilder,
	bm: &'clif mut BackedModule,
	env: &'tcx Environment<'tcx>,
) {
	use Statement::*;
	if let ExpressionStmt(expr) = stmt {
		if let Some(expr) = expr {
			use Expression::*;
			match expr {
				BinaryOperatorExpr(_) => {
					translate_binary_operator_expression_statement(expr, fb, bm, env)
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

fn translate_return_statement<'clif, 'tcx>(
	stmt: &'tcx Statement,
	fb: &'clif mut FunctionBuilder,
	bm: &'clif mut BackedModule,
	env: &'tcx Environment<'tcx>,
) {
	use Statement::*;
	match stmt {
		ReturnStmt(opt_expr) => {
			if let Some(expr) = opt_expr {
				let v = translate_expression(expr, fb, bm, env);
				fb.ins().return_(&[v]);
			}
		}

		_ => unsafe { unreachable_unchecked() },
	}
}

fn translate_statement<'clif, 'tcx>(
	stmt: &'tcx Statement,
	fb: &'clif mut FunctionBuilder,
	bm: &'clif mut BackedModule,
	env: &mut Environment<'tcx>,
) {
	use Statement::*;
	match stmt {
		CompoundStmt(stmts) => {
			let mut nested_env = env.clone();
			for stmt in stmts {
				translate_statement(stmt, fb, bm, &mut nested_env);
			}
		}
		DeclarationStmt(_) => translate_declaration_statement(stmt, fb, env),
		ExpressionStmt(_) => translate_expression_statement(stmt, fb, bm, env),
		ReturnStmt(_) => translate_return_statement(stmt, fb, bm, env),
	}
}

fn translate_function_definition<'clif, 'tcx>(
	func: &'tcx ExternalDeclaration,
	ctxt: &'clif mut Context,
	bm: &'clif mut BackedModule,
	env: &mut Environment<'tcx>,
) -> (Function, FuncId, usize) {
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
		let return_type;
		match specifier {
			Int => {
				ctxt.func.signature.returns.push(AbiParam::new(types::I32));
				return_type = types::I32;
			}

			_ => {
				// TODO
				unimpl!("Unsupported return type")
			}
		}
		// parameter types
		let mut parameter_types = Vec::new();
		for Declaration { specifier, .. } in parameters {
			match specifier {
				Int => {
					ctxt.func.signature.params.push(AbiParam::new(types::I32));
					parameter_types.push(types::I32);
				}

				_ => {
					// TODO
					unimpl!("Unsupported parameter type");
				}
			}
		}

		// declare function
		let function_id = bm
			.declare_function(fname, Linkage::Export, &ctxt.func.signature)
			.expect("Failed to declare function");

		// update environment
		env.insert(
			fname.as_str(),
			SimpleTypedIdentifier::Function(FunctionIdentifier {
				function_id,
				return_type,
				parameter_types,
			}),
		);

		// clone a local environment
		let mut env = env.clone();

		let mut fb_ctxt = FunctionBuilderContext::new();
		let mut fb = FunctionBuilder::new(&mut ctxt.func, &mut fb_ctxt);

		// create entry extended basic block,
		let entry_ebb = fb.create_ebb();
		// set parameters as function parameters,
		fb.append_ebb_params_for_function_params(entry_ebb);
		// and switch to the block
		fb.switch_to_block(entry_ebb);

		// declare parameters
		for (
			i,
			Declaration {
				declarator: Identifier(pname),
				specifier,
			},
		) in parameters.iter().enumerate()
		{
			let pval = fb.ebb_params(entry_ebb)[i];
			let pvar = Variable::new(NEW_VAR_ID.fetch_add(1, Ordering::Relaxed));

			use SimpleTypedIdentifier::*;
			match specifier {
				Int => {
					fb.declare_var(pvar, types::I32);
					// update local environment
					env.insert(
						pname.as_str(),
						Primitive(PrimitiveIdentifier {
							variable: pvar,
							variable_type: types::I32,
						}),
					);
				}

				_ => unimpl!("Unsupported parameter type"),
			}
			fb.def_var(pvar, pval);
		}
		fb.seal_block(entry_ebb);

		// translate function body
		translate_statement(body, &mut fb, bm, &mut env);

		// finalize the function translation
		fb.finalize();

		let function_len = bm
			.define_function(function_id, ctxt)
			.expect("Failed to define function");

		(ctxt.func.clone(), function_id, function_len as _)
	} else {
		unsafe { unreachable_unchecked() }
	}
}

pub fn compiled_function<'clif>(
	fid: FuncId,
	flen: usize,
	bm: &'clif mut BackedModule,
) -> &'clif [u8] {
	let fptr = bm.get_finalized_function(fid);
	unsafe { slice::from_raw_parts(mem::transmute::<_, *const u8>(fptr), flen as _) }
}

pub fn compile<'clif, 'tcx>(
	tu: &'tcx TranslationUnit,
	bm: &'clif mut BackedModule,
	env: &mut Environment<'tcx>,
) -> Vec<(Function, FuncId, usize)> {
	let TranslationUnit(extern_decs) = tu;

	let mut ctxt = bm.make_context();
	let mut funcs = Vec::new();

	for dec in extern_decs.iter() {
		use ExternalDeclaration::*;
		match dec {
			FunctionDefinitionDecl(_) => {
				let func = translate_function_definition(dec, &mut ctxt, bm, env);
				funcs.push(func);
				bm.clear_context(&mut ctxt);
			}
			_ => unimpl!("Unsupported external declaration"),
		}
	}

	bm.finalize_definitions();
	funcs
}

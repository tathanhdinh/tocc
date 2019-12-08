use std::{
	hint::unreachable_unchecked,
	mem, slice,
	sync::atomic::{AtomicUsize, Ordering},
};

use cranelift::prelude::*;
use cranelift_codegen::{ir::Function, Context};
use cranelift_module::{FuncId, Linkage};

use crate::{
	checked_if_let, checked_match, checked_unwrap, error,
	frontend::syntax::{
		BinaryOperator, BinaryOperatorExpression, CallExpression, Constant, Declaration,
		Declarator, DerivedDeclarator, Expression, ExternalDeclaration, FunctionDeclarator,
		FunctionDefinition, Identifier, IfStatement, Integer, MemberExpression, MemberOperator,
		Statement, StructType, TranslationUnit, TypeSpecifier, UnaryOperator,
		UnaryOperatorExpression,
	},
	unimpl,
};

use super::support::{
	AggregateIdentifier, AggregateType, ConcreteModule, FunctionIdentifier, FunctionType,
	NameBindingEnvironment, PointerIdentifer, PrimitiveIdentifier, SimpleType,
	SimpleTypedIdentifier, TypeBindingEnvironment,
};

static NEW_VAR_ID: AtomicUsize = AtomicUsize::new(0);

fn evaluate_in_function_expression<'clif, 'tcx>(
	expr: &'tcx Expression, fb: &'clif mut FunctionBuilder, bm: &'clif mut ConcreteModule,
	name_env: &'_ NameBindingEnvironment<'tcx>, type_env: &'_ TypeBindingEnvironment<'tcx>,
) -> Value {
	use BinaryOperator::*;
	use Expression::*;
	use MemberOperator::*;
	use SimpleType::*;
	use SimpleTypedIdentifier::*;
	use UnaryOperator::*;

	let pointer_ty = bm.target_config().pointer_type();

	match expr {
		UnaryOperatorExpr(UnaryOperatorExpression { op, rhs }) => {
			match op {
				Negation => {
					let rhs = evaluate_in_function_expression(rhs, fb, bm, name_env, type_env);
					let lhs = fb.ins().iconst(types::I32, 0);
					fb.ins().isub(lhs, rhs)
				}

				Address => {
					// no need to evaluate rhs
					match rhs.as_ref() {
						IdentifierExpr(Identifier(ident)) => {
							let typed_ident = checked_unwrap!(name_env.get(ident));
							match typed_ident {
								AggregateIdent(AggregateIdentifier { ident, .. }) => {
									fb.ins().stack_addr(pointer_ty, *ident, 0)
								}

								_ => unimpl!("address operator on unsupported type"),
							}
						}

						// calculate address of a field given struct (or pointer to struct)
						MemberExpr(MemberExpression {
							expression,
							identifier: Identifier(field_name),
							operator,
						}) => match expression.as_ref() {
							IdentifierExpr(Identifier(ident)) => {
								let typed_ident = checked_unwrap!(name_env.get(ident));
								match typed_ident {
									// e.g. s.i
									AggregateIdent(AggregateIdentifier {
										ident,
										ty: AggregateTy(aggre_ty),
									}) => checked_match!(operator, Direct, {
										let offset = checked_unwrap!(aggre_ty.offset(field_name));
										fb.ins().stack_addr(pointer_ty, *ident, offset as i32)
									}),

									// e.g. ps->i
									PointerIdent(PointerIdentifer { ident, ty }) => {
										checked_match!(operator, Indirect, {
											checked_match!(ty, AggregateTy(aggre_ty), {
												let ident_addr = fb.use_var(*ident);
												let offset =
													checked_unwrap!(aggre_ty.offset(field_name));
												let offset =
													fb.ins().iconst(pointer_ty, offset as i64);
												fb.ins().iadd(ident_addr, offset)
											})
										})
									}

									_ => unsafe { unreachable_unchecked() },
								}
							}

							_ => unimpl!("expression unsupported in member expression"),
						},

						_ => {
							// TODO: check in semantics analysis
							unsafe { unreachable_unchecked() }
						}
					}
				}
			}
		}

		BinaryOperatorExpr(BinaryOperatorExpression { op, lhs, rhs }) => {
			let lhs = evaluate_in_function_expression(lhs, fb, bm, name_env, type_env);
			let rhs = evaluate_in_function_expression(rhs, fb, bm, name_env, type_env);

			match op {
				Multiplication => fb.ins().imul(lhs, rhs),
				Division => fb.ins().sdiv(lhs, rhs),
				Addition => fb.ins().iadd(lhs, rhs),
				Subtraction => fb.ins().isub(lhs, rhs),

				Less => fb.ins().icmp(IntCC::SignedLessThan, lhs, rhs),
				LessOrEqual => fb.ins().icmp(IntCC::SignedLessThanOrEqual, lhs, rhs),
				Greater => fb.ins().icmp(IntCC::SignedGreaterThan, lhs, rhs),
				GreaterOrEqual => fb.ins().icmp(IntCC::SignedGreaterThanOrEqual, lhs, rhs),
				Equal => fb.ins().icmp(IntCC::Equal, lhs, rhs),

				Assignment => unsafe {
					// TODO: check in semantics analysis
					unreachable_unchecked()
				},
			}
		}

		ConstantExpr(Constant::IntegerConst(Integer(i))) => fb.ins().iconst(types::I32, *i as i64),

		IdentifierExpr(Identifier(var_name)) => {
			let var = checked_unwrap!(name_env.get(var_name));
			if let SimpleTypedIdentifier::PrimitiveIdent(PrimitiveIdentifier { ident, .. }) = var {
				fb.use_var(*ident)
			} else {
				unimpl!("identifier has not primitive type")
			}
		}

		// e.g. s.i for some struct s with member i
		MemberExpr(MemberExpression {
			expression,
			identifier: Identifier(field_name),
			operator,
		}) => {
			if let IdentifierExpr(Identifier(var_name)) = expression.as_ref() {
				let typed_ident = checked_unwrap!(name_env.get(var_name));
				match typed_ident {
					// e.g. s.i
					AggregateIdent(AggregateIdentifier { ident, ty: AggregateTy(aggre_ty) }) => {
						checked_match!(operator, Direct, {
							let offset = checked_unwrap!(aggre_ty.offset(field_name));
							let (_, ty) = checked_unwrap!(aggre_ty
								.fields
								.iter()
								.find(|(fname, _)| fname == field_name));
							fb.ins().stack_load(*ty, *ident, offset as i32)
						})
					}

					// e.g. ps->i
					PointerIdent(PointerIdentifer { ident, ty }) => {
						checked_match!(operator, Indirect, {
							checked_match!(ty, PointerTy(pty), {
								checked_match!(pty.as_ref(), AggregateTy(aggre_ty), {
									// Simplifcation: assume no struct alignment
									// C11 Standard 6.7.2.1 Structure and union specifiers
									let offset = checked_unwrap!(aggre_ty.offset(field_name));

									let (_, ty) = checked_unwrap!(aggre_ty
										.fields
										.iter()
										.find(|(fname, _)| fname == field_name));

									let ident_val = fb.use_var(*ident);
									fb.ins().load(*ty, MemFlags::new(), ident_val, offset as i32)
								})
							})
						})
					}

					_ => unsafe { unreachable_unchecked() },
				}
			} else {
				unimpl!("unhandled expression for assignment")
			}
		}

		CallExpr(CallExpression { callee: Identifier(func_name), arguments }) => {
			use SimpleTypedIdentifier::*;

			let typed_ident = checked_unwrap!(name_env.get(func_name));
			match typed_ident {
				FunctionIdent(FunctionIdentifier {
					ty: SimpleType::FunctionTy(FunctionType { return_ty, param_ty }),
					..
				}) => {
					let mut sig = bm.make_signature();
					sig.returns.push(AbiParam::new(*return_ty)); // return type
					for pty in param_ty {
						sig.params.push(AbiParam::new(*pty)); // parameter types
					}

					let callee = bm
						.declare_function(func_name, Linkage::Import, &sig)
						.expect("failed to declare function");
					let local_callee = bm.declare_func_in_func(callee, fb.func);

					let arg_values: Vec<_> = arguments
						.iter()
						.map(|arg| evaluate_in_function_expression(arg, fb, bm, name_env, type_env))
						.collect();

					let call = fb.ins().call(local_callee, &arg_values);

					fb.inst_results(call)[0]
				}

				_ => unimpl!("call an unsupported identifier"),
			}
		}
	}
}

fn declare_in_function_new_variable<'clif, 'tcx>(
	ty: Type, init_val: Option<Value>, func_builder: &'clif mut FunctionBuilder,
) -> Variable {
	let new_var = Variable::new(NEW_VAR_ID.fetch_add(1, Ordering::Relaxed));
	func_builder.declare_var(new_var, ty);
	let init_val = init_val.unwrap_or_else(|| func_builder.ins().iconst(ty, 0));
	func_builder.def_var(new_var, init_val);
	new_var
}

fn translate_in_function_declaration<'clif, 'tcx>(
	Declaration { specifier, declarator }: &'tcx Declaration<'tcx>,
	func_builder: &'clif mut FunctionBuilder, bmod: &'clif mut ConcreteModule,
	name_env: &'_ mut NameBindingEnvironment<'tcx>, type_env: &'_ mut TypeBindingEnvironment<'tcx>,
) {
	use SimpleType::*;
	use SimpleTypedIdentifier::*;
	use TypeSpecifier::*;

	let pointer_ty = bmod.target_config().pointer_type();

	match specifier {
		CharTy | ShortTy | IntTy | LongTy => {
			let Declarator { ident: Identifier(var_name), derived } =
				checked_unwrap!(declarator.as_ref());

			if let Some(derived_decl) = derived {
				match derived_decl {
					DerivedDeclarator::Pointer => {
						let new_var =
							declare_in_function_new_variable(pointer_ty, None, func_builder);

						name_env.insert(
							var_name,
							PointerIdent(PointerIdentifer {
								ident: new_var,
								ty: PointerTy(Box::new(PrimitiveTy(specifier.into()))),
							}),
						);
					}
				}
			} else {
				let new_var =
					declare_in_function_new_variable(specifier.into(), None, func_builder);

				name_env.insert(
					var_name,
					SimpleTypedIdentifier::PrimitiveIdent(PrimitiveIdentifier {
						ident: new_var,
						ty: SimpleType::PrimitiveTy(specifier.into()),
					}),
				);
			}
		}

		StructTy(struct_ty) => {
			let StructType { identifier: Identifier(sname), declarations } = struct_ty;
			if declarations.is_some() {
				let struct_ty: AggregateType = struct_ty.into();
				let struct_data =
					StackSlotData::new(StackSlotKind::ExplicitSlot, struct_ty.bytes() as _);

				let stack_slot = func_builder.create_stack_slot(struct_data);
				if let Some(Declarator { ident: Identifier(var_name), .. }) = declarator {
					name_env.insert(
						var_name,
						SimpleTypedIdentifier::AggregateIdent(AggregateIdentifier {
							ident: stack_slot,
							ty: SimpleType::AggregateTy(struct_ty.clone()),
						}),
					);
				}

				type_env.insert(sname, SimpleType::AggregateTy(struct_ty));
			}

			if let Some(Declarator { ident: Identifier(var_name), derived }) = declarator {
				let struct_simple_ty = checked_unwrap!(type_env.get(sname));
				let struct_simple_ty = struct_simple_ty.to_owned();

				if let Some(derived_decl) = derived {
					match derived_decl {
						DerivedDeclarator::Pointer => {
							let new_var =
								declare_in_function_new_variable(pointer_ty, None, func_builder);

							name_env.insert(
								var_name,
								PointerIdent(PointerIdentifer {
									ident: new_var,
									ty: PointerTy(Box::new(struct_simple_ty)),
								}),
							);
						}
					}
				} else {
					let struct_data = checked_if_let!(AggregateTy(struct_ty), &struct_simple_ty, {
						StackSlotData::new(StackSlotKind::ExplicitSlot, struct_ty.bytes() as _)
					});

					let stack_slot = func_builder.create_stack_slot(struct_data);
					name_env.insert(
						var_name,
						AggregateIdent(AggregateIdentifier {
							ident: stack_slot,
							ty: struct_simple_ty,
						}),
					);
				}
			}
		}
	}
}

// C11 Standard: 6.8.3 Expression and null statements
// A statement expression is evaluated for its side effects only, its type is void.
// E.g. x = 5
fn translate_in_function_binary_operator_statement_expression<'clif, 'tcx>(
	BinaryOperatorExpression { op, lhs, rhs }: &'tcx BinaryOperatorExpression<'tcx>,
	fb: &'clif mut FunctionBuilder, bmod: &'clif mut ConcreteModule,
	name_env: &'_ NameBindingEnvironment<'tcx>, type_env: &'_ TypeBindingEnvironment<'tcx>,
) {
	use BinaryOperator::*;
	use Expression::*;
	use MemberOperator::*;
	use SimpleType::*;
	use SimpleTypedIdentifier::*;

	match op {
		// assignment operator, i.e. =
		Assignment => {
			let rhs_val =
				evaluate_in_function_expression(rhs.as_ref(), fb, bmod, name_env, type_env);

			match lhs.as_ref() {
				// e.g. x = 10
				IdentifierExpr(Identifier(var_name)) => {
					let lhs_var = checked_unwrap!(name_env.get(var_name));
					checked_if_let!(PrimitiveIdent(PrimitiveIdentifier { ident, .. }), lhs_var, {
						fb.def_var(*ident, rhs_val)
					});

					if let PrimitiveIdent(PrimitiveIdentifier { ident, .. }) = lhs_var {
						fb.def_var(*ident, rhs_val);
					} else {
						unimpl!("rhs is not of primitive type");
					}
				}

				// e.g. s.x = 17;
				MemberExpr(MemberExpression {
					expression,
					identifier: Identifier(field_name),
					operator,
				}) => {
					if let IdentifierExpr(Identifier(var_name)) = expression.as_ref() {
						let typed_ident = checked_unwrap!(name_env.get(var_name));
						match typed_ident {
							// e.g. s.x
							AggregateIdent(AggregateIdentifier {
								ident,
								ty: AggregateTy(aggre_ty),
							}) => {
								checked_match!(operator, Direct, {
									let offset = checked_unwrap!(aggre_ty.offset(field_name));
									fb.ins().stack_store(rhs_val, *ident, offset as i32);
								});
							}

							// e.g. ps->x
							PointerIdent(PointerIdentifer { ident, ty }) => {
								checked_match!(operator, Indirect, {
									checked_match!(ty, PointerTy(pty), {
										checked_match!(pty.as_ref(), AggregateTy(aggre_ty), {
											let offset =
												checked_unwrap!(aggre_ty.offset(field_name));
											// Simplification: assume no struct alignment
											// TODO: check in semantics analysis (rhs's type)
											let ident_val = fb.use_var(*ident);
											fb.ins().store(
												MemFlags::new(),
												rhs_val,
												ident_val,
												offset as i32,
											);
										})
									});
								});
							}

							_ => {
								// TODO: check in semantics analysis (member expression on incompatible type)
								unsafe { unreachable_unchecked() }
							}
						}
					} else {
						// TODO: check in semantics analysis
						error!("failed to translate struct expression")
					}
				}

				_ => unimpl!("unhandled expression for assignment"),
			}
		}

		_ => {
			// TODO
		}
	}
}

fn translate_in_function_statement_expression<'clif, 'tcx>(
	expr: &'tcx Expression, fb: &'clif mut FunctionBuilder, bmod: &'clif mut ConcreteModule,
	name_env: &'_ NameBindingEnvironment<'tcx>, type_env: &'_ TypeBindingEnvironment<'tcx>,
) {
	use Expression::*;
	match expr {
		BinaryOperatorExpr(bin_op_expr) => {
			translate_in_function_binary_operator_statement_expression(
				bin_op_expr,
				fb,
				bmod,
				name_env,
				type_env,
			)
		}

		_ => {
			// TODO: other expressions
		}
	}
}

fn translate_statement<'clif, 'tcx>(
	stmt: &'tcx Statement, func_builder: &'clif mut FunctionBuilder,
	backed_mod: &'clif mut ConcreteModule, name_env: &'_ mut NameBindingEnvironment<'tcx>,
	type_env: &'_ mut TypeBindingEnvironment<'tcx>,
) {
	use Statement::*;
	match stmt {
		CompoundStmt(stmts) => {
			let mut nested_name_env = name_env.clone();
			let mut nested_type_env = type_env.clone();
			for stmt in stmts {
				translate_statement(
					stmt,
					func_builder,
					backed_mod,
					&mut nested_name_env,
					&mut nested_type_env,
				);
			}
		}

		IfStmt(IfStatement { condition, then_statement, else_statement }) => {
			let cond = evaluate_in_function_expression(
				condition,
				func_builder,
				backed_mod,
				name_env,
				type_env,
			);

			let then_ebb = func_builder.create_ebb();
			let merge_ebb = func_builder.create_ebb();
			if let Some(else_stmt) = else_statement.as_ref() {
				let else_ebb = func_builder.create_ebb();
				func_builder.ins().brz(cond, else_ebb, &[]);
				func_builder.ins().jump(then_ebb, &[]);

				// generate else EBB
				func_builder.switch_to_block(else_ebb);
				func_builder.seal_block(else_ebb);
				translate_statement(
					else_stmt.as_ref(),
					func_builder,
					backed_mod,
					name_env,
					type_env,
				);
				func_builder.ins().jump(merge_ebb, &[]);
			} else {
				func_builder.ins().brz(cond, merge_ebb, &[]);
				func_builder.ins().jump(then_ebb, &[]);
			}

			// generate then EBB
			func_builder.switch_to_block(then_ebb);
			func_builder.seal_block(then_ebb);
			translate_statement(
				then_statement.as_ref(),
				func_builder,
				backed_mod,
				name_env,
				type_env,
			);
			func_builder.ins().jump(merge_ebb, &[]);

			func_builder.switch_to_block(merge_ebb);
			func_builder.seal_block(merge_ebb);
		}

		DeclarationStmt(decl) => {
			translate_in_function_declaration(decl, func_builder, backed_mod, name_env, type_env)
		}

		ExpressionStmt(expr) => {
			if let Some(expr) = expr {
				// C11 Standard: 6.8.3 Expression and null statements
				// A statement expression is an expression but its type is void,
				// i.e. it is evaluated for side-effect.
				// E.g. x = 5 is a binary expression where the operator is assignment
				translate_in_function_statement_expression(
					expr,
					func_builder,
					backed_mod,
					name_env,
					type_env,
				);
			}
		}

		ReturnStmt(expr) => {
			if let Some(expr) = expr {
				let v = evaluate_in_function_expression(
					expr,
					func_builder,
					backed_mod,
					name_env,
					type_env,
				);
				func_builder.ins().return_(&[v]);
			}
		}
	}
}

fn translate_function_definition<'clif, 'tcx>(
	func: &'tcx FunctionDefinition, ctxt: &'clif mut Context, bmod: &'clif mut ConcreteModule,
	name_env: &'_ mut NameBindingEnvironment<'tcx>, type_env: &'_ mut TypeBindingEnvironment<'tcx>,
) -> (Function, FuncId, usize) {
	use SimpleType::*;
	use TypeSpecifier::*;

	let pointer_ty = bmod.target_config().pointer_type();

	let FunctionDefinition {
		specifier,
		declarator: FunctionDeclarator { identifier: Identifier(fname), parameters },
		body,
	} = func;

	// return type
	let return_ty = specifier.into();
	ctxt.func.signature.returns.push(AbiParam::new(return_ty));

	// parameter types
	let mut param_ty = Vec::new();
	for Declaration { specifier, declarator } in parameters {
		let Declarator { derived, .. } = checked_unwrap!(declarator.as_ref());
		if let Some(derived_decl) = derived {
			match derived_decl {
				// parameter is some pointer
				DerivedDeclarator::Pointer => {
					ctxt.func.signature.params.push(AbiParam::new(pointer_ty));
					param_ty.push(pointer_ty);
				}
			}
		} else {
			match specifier {
				CharTy | ShortTy | IntTy | LongTy => {
					let pty = specifier.into();
					ctxt.func.signature.params.push(AbiParam::new(pty));
					param_ty.push(pty);
				}

				// simplification: struct definition does not occurs in parameter list
				StructTy(_) => {
					// simplification: struct has always MEMORY class
					// (i.e. larger than 8 bytes or contains unaligned field)
					// System V ABI AMD64: 3.2.3 Parameter Passing
					unimpl!("passing struct by value unsupported")
				}
			}
		}
	}

	// declare function
	let function_id = bmod
		.declare_function(fname, Linkage::Export, &ctxt.func.signature)
		.expect("failed to declare function");

	// update environment
	name_env.insert(
		fname,
		SimpleTypedIdentifier::FunctionIdent(FunctionIdentifier {
			ident: function_id,
			ty: SimpleType::FunctionTy(FunctionType { return_ty, param_ty }),
		}),
	);

	// clone local environments
	let mut name_env = name_env.clone();
	let mut type_env = type_env.clone();

	let mut fb_ctxt = FunctionBuilderContext::new();
	let mut func_builder = FunctionBuilder::new(&mut ctxt.func, &mut fb_ctxt);

	// create entry extended basic block,
	let entry_ebb = func_builder.create_ebb();
	// set parameters as function parameters,
	func_builder.append_ebb_params_for_function_params(entry_ebb);
	// and switch to the block
	func_builder.switch_to_block(entry_ebb);

	// declare parameters
	for (i, Declaration { declarator, specifier }) in parameters.iter().enumerate() {
		let Declarator { ident: Identifier(var_name), derived } =
			checked_unwrap!(declarator.as_ref()); // checked in syntax analysis
		let param_val = func_builder.ebb_params(entry_ebb)[i];

		match specifier {
			CharTy | ShortTy | IntTy | LongTy => {
				if let Some(derived_decl) = derived {
					match derived_decl {
						DerivedDeclarator::Pointer => {
							let new_var = declare_in_function_new_variable(
								pointer_ty,
								Some(param_val),
								&mut func_builder,
							);

							name_env.insert(
								var_name,
								SimpleTypedIdentifier::PointerIdent(PointerIdentifer {
									ident: new_var,
									ty: PointerTy(Box::new(PrimitiveTy(specifier.into()))),
								}),
							);
						}
					}
				} else {
					let new_var = declare_in_function_new_variable(
						specifier.into(),
						Some(param_val),
						&mut func_builder,
					);

					name_env.insert(
						var_name,
						SimpleTypedIdentifier::PrimitiveIdent(PrimitiveIdentifier {
							ident: new_var,
							ty: SimpleType::PrimitiveTy(specifier.into()),
						}),
					);
				}
			}

			StructTy(StructType { identifier: Identifier(sname), .. }) => {
				if let Some(derived_decl) = derived {
					match derived_decl {
						DerivedDeclarator::Pointer => {
							let new_var = declare_in_function_new_variable(
								pointer_ty,
								Some(param_val),
								&mut func_builder,
							);

							let aggre_ty = checked_unwrap!(type_env.get(sname));

							name_env.insert(
								var_name,
								SimpleTypedIdentifier::PointerIdent(PointerIdentifer {
									ident: new_var,
									ty: PointerTy(Box::new(aggre_ty.clone())),
								}),
							);
						}
					}
				} else {
					// simplification: struct has always MEMORY class
					// (i.e. larger than 8 bytes or  contains unaligned field)
					// System V ABI AMD64: 3.2.3 Parameter Passing
					unimpl!("passing struct by value unsupported")
				}
			}
		}
	}
	func_builder.seal_block(entry_ebb);

	// translate function body
	translate_statement(body, &mut func_builder, bmod, &mut name_env, &mut type_env);

	// finalize the function translation
	func_builder.finalize();
	// println!("{:?}", func_builder.func);

	let function_len = bmod.define_function(function_id, ctxt).expect("failed to define function");

	(ctxt.func.clone(), function_id, function_len as _)
}

pub fn compiled_function<'clif>(
	fid: FuncId, flen: usize, bmod: &'clif mut ConcreteModule,
) -> &'clif [u8] {
	let fptr = bmod.get_finalized_function(fid);
	unsafe { slice::from_raw_parts(mem::transmute::<_, *const u8>(fptr), flen as _) }
}

pub fn compile<'clif, 'tcx>(
	tu: &'tcx TranslationUnit, bm: &'clif mut ConcreteModule,
	name_env: &'_ mut NameBindingEnvironment<'tcx>, type_env: &'_ mut TypeBindingEnvironment<'tcx>,
) -> Vec<(Function, FuncId, usize)> {
	use ExternalDeclaration::*;
	use TypeSpecifier::*;

	let TranslationUnit(extern_decs) = tu;

	let mut ctxt = bm.make_context();
	let mut funcs = Vec::new();

	for dec in extern_decs {
		match dec {
			FunctionDefinitionDecl(func_def) => {
				let func =
					translate_function_definition(func_def, &mut ctxt, bm, name_env, type_env);
				funcs.push(func);
				bm.clear_context(&mut ctxt);
			}

			Decl(Declaration { specifier, .. }) => {
				// TODO: check in semantics analysis (global declaration)
				checked_match!(specifier, StructTy(struct_ty), {
					let StructType { identifier: Identifier(sname), .. } = struct_ty;
					let aggre_ty: AggregateType = struct_ty.into();
					type_env.insert(sname, SimpleType::AggregateTy(aggre_ty))
				});
			}
		}
	}

	bm.finalize_definitions();
	funcs
}

use std::{
	cmp,
	hint::unreachable_unchecked,
	i16, i32, i64, i8, mem, slice,
	sync::atomic::{AtomicUsize, Ordering},
};

use cranelift::prelude::*;
use cranelift_codegen::{ir::Function, Context};
use cranelift_module::{FuncId, Linkage};

use crate::{
	checked_if_let, checked_match, checked_unwrap, error,
	frontend::syntax::{
		BinaryOperator, BinaryOperatorExpression, CallExpression, Constant, Declaration,
		Declarator, DerivedDeclarator, Expression, ExternalDeclaration, ForStatement,
		FunctionDeclarator, FunctionDefinition, Identifier, IfStatement, Integer, MemberExpression,
		MemberOperator, Statement, StructType, TranslationUnit, TypeSpecifier, UnaryOperator,
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

fn type_cast_value<'clif>(val: Value, ty: Type, func_builder: &'clif mut FunctionBuilder) -> Value {
	let val_size = func_builder.func.dfg.value_type(val).bytes();
	let ty_size = ty.bytes();
	if val_size > ty_size {
		func_builder.ins().ireduce(ty, val)
	} else if val_size < ty_size {
		func_builder.ins().sextend(ty, val)
	} else {
		val
	}
}

fn translate_in_function_expression<'clif, 'tcx>(
	expr: &'tcx Expression, type_hint: Option<Type>, func_builder: &'clif mut FunctionBuilder,
	bm: &'clif mut ConcreteModule, name_env: &'_ NameBindingEnvironment<'tcx>,
	type_env: &'_ TypeBindingEnvironment<'tcx>,
) -> Value {
	use BinaryOperator::*;
	use Expression::*;
	use MemberOperator::*;
	use SimpleType::*;
	use SimpleTypedIdentifier::*;
	use UnaryOperator::*;

	let pointer_ty = bm.target_config().pointer_type();

	match expr {
		UnaryOperatorExpr(UnaryOperatorExpression { operator, operand }) => {
			match operator {
				Negation => {
					let rhs = translate_in_function_expression(
						operand,
						type_hint,
						func_builder,
						bm,
						name_env,
						type_env,
					);
					let rhs_ty = func_builder.func.dfg.value_type(rhs);
					let lhs = func_builder.ins().iconst(rhs_ty, 0);
					func_builder.ins().isub(lhs, rhs)
				}

				PreIncrement => checked_if_let!(IdentifierExpr(var_name), operand.as_ref(), {
					let var_name: &str = var_name.into();
					let ident_var = checked_unwrap!(name_env.get(var_name));
					checked_if_let!(
						PrimitiveIdent(PrimitiveIdentifier { ident, ty: PrimitiveTy(ident_ty) }),
						ident_var,
						{
							let ident_val = func_builder.use_var(*ident);
							let one = func_builder.ins().iconst(*ident_ty, 1);
							let ident_new_val = func_builder.ins().iadd(ident_val, one);
							func_builder.def_var(*ident, ident_new_val);
							ident_new_val
						}
					)
				}),

				PostIncrement => checked_if_let!(IdentifierExpr(var_name), operand.as_ref(), {
					let var_name: &str = var_name.into();
					let ident_var = checked_unwrap!(name_env.get(var_name));
					checked_if_let!(
						PrimitiveIdent(PrimitiveIdentifier { ident, ty: PrimitiveTy(ident_ty) }),
						ident_var,
						{
							let ident_val = func_builder.use_var(*ident);
							let one = func_builder.ins().iconst(*ident_ty, 1);
							let ident_new_val = func_builder.ins().iadd(ident_val, one);
							func_builder.def_var(*ident, ident_new_val);
							ident_val
						}
					)
				}),

				Address => {
					// no need to evaluate rhs
					match operand.as_ref() {
						IdentifierExpr(ident) => {
							let var_name: &str = ident.into();
							let typed_ident = checked_unwrap!(name_env.get(var_name));
							match typed_ident {
								AggregateIdent(AggregateIdentifier { ident, .. }) => {
									func_builder.ins().stack_addr(pointer_ty, *ident, 0)
								}

								_ => unimpl!("address operator on unsupported type"),
							}
						}

						// calculate address of a field given struct (or pointer to struct)
						MemberExpr(MemberExpression { expression, identifier, operator }) => {
							match expression.as_ref() {
								IdentifierExpr(struct_name) => {
									let field_name: &str = identifier.into();
									let struct_name: &str = struct_name.into();
									let typed_ident = checked_unwrap!(name_env.get(struct_name));
									match typed_ident {
										// e.g. s.i
										AggregateIdent(AggregateIdentifier {
											ident,
											ty: AggregateTy(aggre_ty),
										}) => checked_match!(operator, Direct, {
											let offset =
												checked_unwrap!(aggre_ty.field_offset(field_name));
											func_builder.ins().stack_addr(
												pointer_ty,
												*ident,
												offset as i32,
											)
										}),

										// e.g. ps->i
										PointerIdent(PointerIdentifer { ident, ty }) => {
											checked_match!(operator, Indirect, {
												checked_match!(ty, AggregateTy(aggre_ty), {
													let ident_addr = func_builder.use_var(*ident);
													let offset = checked_unwrap!(
														aggre_ty.field_offset(field_name)
													);
													let offset = func_builder
														.ins()
														.iconst(pointer_ty, offset as i64);
													func_builder.ins().iadd(ident_addr, offset)
												})
											})
										}

										_ => unsafe { unreachable_unchecked() },
									}
								}

								_ => unimpl!("expression unsupported in member expression"),
							}
						}

						_ => unsafe { unreachable_unchecked() },
					}
				}
			}
		}

		BinaryOperatorExpr(BinaryOperatorExpression { operator, lhs, rhs }) => {
			let (lhs, rhs) = match lhs.as_ref() {
				ConstantExpr(_) => {
					let rhs = translate_in_function_expression(
						rhs,
						type_hint,
						func_builder,
						bm,
						name_env,
						type_env,
					);
					let rhs_ty = func_builder.func.dfg.value_type(rhs);
					let lhs = translate_in_function_expression(
						lhs,
						Some(rhs_ty),
						func_builder,
						bm,
						name_env,
						type_env,
					);
					(lhs, rhs)
				}

				_ => {
					let lhs = translate_in_function_expression(
						lhs,
						type_hint,
						func_builder,
						bm,
						name_env,
						type_env,
					);
					let lhs_ty = func_builder.func.dfg.value_type(lhs);
					let rhs = translate_in_function_expression(
						rhs,
						Some(lhs_ty),
						func_builder,
						bm,
						name_env,
						type_env,
					);
					(lhs, rhs)
				}
			};

			// let lhs = translate_in_function_expression(lhs, func_builder, bm, name_env, type_env);
			// let rhs = translate_in_function_expression(rhs, func_builder, bm, name_env, type_env);

			let lhs_ty = func_builder.func.dfg.value_type(lhs);
			let rhs_ty = func_builder.func.dfg.value_type(rhs);
			let max_ty = if lhs_ty.bytes() > rhs_ty.bytes() { lhs_ty } else { rhs_ty };
			let lhs = type_cast_value(lhs, max_ty, func_builder);
			let rhs = type_cast_value(rhs, max_ty, func_builder);

			match operator {
				Multiplication => func_builder.ins().imul(lhs, rhs),
				Division => func_builder.ins().sdiv(lhs, rhs),
				Addition => func_builder.ins().iadd(lhs, rhs),
				Subtraction => func_builder.ins().isub(lhs, rhs),

				Less => func_builder.ins().icmp(IntCC::SignedLessThan, lhs, rhs),
				LessOrEqual => func_builder.ins().icmp(IntCC::SignedLessThanOrEqual, lhs, rhs),
				Greater => func_builder.ins().icmp(IntCC::SignedGreaterThan, lhs, rhs),
				GreaterOrEqual => {
					func_builder.ins().icmp(IntCC::SignedGreaterThanOrEqual, lhs, rhs)
				}
				Equal => func_builder.ins().icmp(IntCC::Equal, lhs, rhs),

				Assignment => unsafe {
					// because an assignment expression is of unit type
					unreachable_unchecked()
				},
			}
		}

		ConstantExpr(Constant::IntegerConst(i)) => {
			let i: i64 = i.into();
			let ty = if i >= i8::MIN as i64 && i <= i8::MAX as i64 {
				types::I8
			} else if i >= i16::MIN as i64 && i <= i16::MAX as i64 {
				types::I16
			} else if i >= i32::MIN as i64 && i <= i32::MAX as i64 {
				types::I32
			} else {
				types::I64
			};

			let ty = if let Some(type_hint) = type_hint {
				if ty.bytes() > type_hint.bytes() {
					ty
				} else {
					type_hint
				}
			} else {
				ty
			};

			func_builder.ins().iconst(ty, i)
		}

		IdentifierExpr(Identifier(var_name)) => {
			let var = checked_unwrap!(name_env.get(var_name));
			checked_if_let!(
				SimpleTypedIdentifier::PrimitiveIdent(PrimitiveIdentifier { ident, .. }),
				var,
				{ func_builder.use_var(*ident) }
			)
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
							let offset = checked_unwrap!(aggre_ty.field_offset(field_name));
							let (_, ty) = checked_unwrap!(aggre_ty
								.fields
								.iter()
								.find(|(fname, _)| fname == field_name));
							func_builder.ins().stack_load(*ty, *ident, offset as i32)
						})
					}

					// e.g. ps->i
					PointerIdent(PointerIdentifer { ident, ty }) => {
						checked_match!(operator, Indirect, {
							checked_match!(ty, PointerTy(pty), {
								checked_match!(pty.as_ref(), AggregateTy(aggre_ty), {
									// Simplifcation: assume no struct alignment
									// C11 Standard 6.7.2.1 Structure and union specifiers
									let offset = checked_unwrap!(aggre_ty.field_offset(field_name));

									let (_, ty) = checked_unwrap!(aggre_ty
										.fields
										.iter()
										.find(|(fname, _)| fname == field_name));

									let ident_val = func_builder.use_var(*ident);
									func_builder.ins().load(
										*ty,
										MemFlags::new(),
										ident_val,
										offset as i32,
									)
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

		CallExpr(CallExpression { callee, arguments }) => {
			use SimpleTypedIdentifier::*;

			let func_name: &str = callee.into();
			let func = checked_unwrap!(name_env.get(func_name));
			match func {
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
					let local_callee = bm.declare_func_in_func(callee, func_builder.func);

					let arg_values: Vec<_> = arguments
						.iter()
						.zip(param_ty.iter())
						.map(|(arg, ty)| {
							translate_in_function_expression(
								arg,
								Some(*ty),
								func_builder,
								bm,
								name_env,
								type_env,
							)
						})
						.collect();

					let arg_values: Vec<_> = arg_values
						.into_iter()
						.zip(param_ty.iter())
						.map(|(val, ty)| type_cast_value(val, *ty, func_builder))
						.collect();

					let call = func_builder.ins().call(local_callee, &arg_values);

					func_builder.inst_results(call)[0]
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
// A statement expression is evaluated for its side effects only, it has unit type.
// E.g. x = 5
fn translate_in_function_binary_operator_statement_expression<'clif, 'tcx>(
	BinaryOperatorExpression { operator, lhs, rhs }: &'tcx BinaryOperatorExpression<'tcx>,
	func_builder: &'clif mut FunctionBuilder, cmod: &'clif mut ConcreteModule,
	name_env: &'_ NameBindingEnvironment<'tcx>, type_env: &'_ TypeBindingEnvironment<'tcx>,
) {
	use BinaryOperator::*;
	use Expression::*;
	use MemberOperator::*;
	use SimpleType::*;
	use SimpleTypedIdentifier::*;

	match operator {
		// assignment operator, i.e. =
		Assignment => {
			match lhs.as_ref() {
				// e.g. x = 10
				IdentifierExpr(Identifier(var_name)) => {
					let lhs_var = checked_unwrap!(name_env.get(var_name));
					checked_if_let!(
						PrimitiveIdent(PrimitiveIdentifier { ident, ty: PrimitiveTy(ty) }),
						lhs_var,
						{
							let rhs_val = translate_in_function_expression(
								rhs.as_ref(),
								Some(*ty),
								func_builder,
								cmod,
								name_env,
								type_env,
							);
							let rhs_val = type_cast_value(rhs_val, *ty, func_builder);
							func_builder.def_var(*ident, rhs_val)
						}
					);
				}

				// e.g. s.x = 17;
				MemberExpr(MemberExpression {
					expression,
					identifier: Identifier(field_name),
					operator,
				}) => {
					checked_match!(expression.as_ref(), IdentifierExpr(Identifier(var_name)), {
						let typed_ident = checked_unwrap!(name_env.get(var_name));
						match typed_ident {
							// e.g. s.x
							AggregateIdent(AggregateIdentifier {
								ident,
								ty: AggregateTy(aggre_ty),
							}) => {
								checked_match!(operator, Direct, {
									let field_offset =
										checked_unwrap!(aggre_ty.field_offset(field_name));
									let field_ty = checked_unwrap!(aggre_ty.field_type(field_name));
									let rhs_val = translate_in_function_expression(
										rhs.as_ref(),
										Some(field_ty),
										func_builder,
										cmod,
										name_env,
										type_env,
									);
									let rhs_val = type_cast_value(rhs_val, field_ty, func_builder);
									func_builder.ins().stack_store(
										rhs_val,
										*ident,
										field_offset as i32,
									);
								});
							}

							// e.g. ps->x
							PointerIdent(PointerIdentifer { ident, ty }) => {
								checked_match!(operator, Indirect, {
									checked_match!(ty, PointerTy(pty), {
										checked_match!(pty.as_ref(), AggregateTy(aggre_ty), {
											let field_offset =
												checked_unwrap!(aggre_ty.field_offset(field_name));
											let field_ty =
												checked_unwrap!(aggre_ty.field_type(field_name));
											let ident_val = func_builder.use_var(*ident);
											let rhs_val = translate_in_function_expression(
												rhs.as_ref(),
												Some(field_ty),
												func_builder,
												cmod,
												name_env,
												type_env,
											);
											let rhs_val =
												type_cast_value(rhs_val, field_ty, func_builder);
											func_builder.ins().store(
												MemFlags::new(),
												rhs_val,
												ident_val,
												field_offset as i32,
											);
										})
									});
								});
							}

							_ => unsafe { unreachable_unchecked() },
						}
					});
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
	expr: &'tcx Expression, func_builder: &'clif mut FunctionBuilder,
	cmod: &'clif mut ConcreteModule, name_env: &'_ NameBindingEnvironment<'tcx>,
	type_env: &'_ TypeBindingEnvironment<'tcx>,
) {
	use Expression::*;
	match expr {
		BinaryOperatorExpr(bin_op_expr) => {
			translate_in_function_binary_operator_statement_expression(
				bin_op_expr,
				func_builder,
				cmod,
				name_env,
				type_env,
			)
		}

		_ => {
			// TODO: other expressions
		}
	}
}

fn translate_in_function_statement<'clif, 'tcx>(
	stmt: &'tcx Statement, return_ty: &'clif Type, func_builder: &'clif mut FunctionBuilder,
	cmod: &'clif mut ConcreteModule, name_env: &'_ mut NameBindingEnvironment<'tcx>,
	type_env: &'_ mut TypeBindingEnvironment<'tcx>,
) {
	use Statement::*;

	// Programming Language Concepts: 8.6 Compilation of Statements
	// Introduction to Compiler Design: 6.5 Translating Statements
	// Tiger book: 7.2 Translation in to trees
	match stmt {
		// C11 Standard: 6.8.5.3 The for statement
		ForStmt(ForStatement { initializer, condition, step, statement }) => {
			if let Some(expr) = initializer.as_ref() {
				translate_in_function_statement_expression(
					expr,
					func_builder,
					cmod,
					name_env,
					type_env,
				);
			}

			let header_ebb = func_builder.create_ebb();
			let loop_ebb = func_builder.create_ebb();
			let exit_ebb = func_builder.create_ebb();

			func_builder.ins().jump(header_ebb, &[]);

			// header EBB
			func_builder.switch_to_block(header_ebb);
			let cond = translate_in_function_expression(
				condition,
				None,
				func_builder,
				cmod,
				name_env,
				type_env,
			);
			func_builder.ins().brz(cond, exit_ebb, &[]);
			func_builder.ins().jump(loop_ebb, &[]);

			// loop EBB
			func_builder.switch_to_block(loop_ebb);
			func_builder.seal_block(loop_ebb);
			translate_in_function_statement(
				statement.as_ref(),
				return_ty,
				func_builder,
				cmod,
				name_env,
				type_env,
			);
			if let Some(expr) = step.as_ref() {
				translate_in_function_expression(
					expr,
					None,
					func_builder,
					cmod,
					name_env,
					type_env,
				);
			}
			func_builder.ins().jump(header_ebb, &[]);

			func_builder.switch_to_block(exit_ebb);

			func_builder.seal_block(header_ebb);
			func_builder.seal_block(exit_ebb);
		}

		CompoundStmt(stmts) => {
			let mut nested_name_env = name_env.clone();
			let mut nested_type_env = type_env.clone();
			for stmt in stmts {
				translate_in_function_statement(
					stmt,
					return_ty,
					func_builder,
					cmod,
					&mut nested_name_env,
					&mut nested_type_env,
				);
			}
		}

		IfStmt(IfStatement { condition, then_statement, else_statement }) => {
			let cond = translate_in_function_expression(
				condition,
				None,
				func_builder,
				cmod,
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
				translate_in_function_statement(
					else_stmt.as_ref(),
					return_ty,
					func_builder,
					cmod,
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
			translate_in_function_statement(
				then_statement.as_ref(),
				return_ty,
				func_builder,
				cmod,
				name_env,
				type_env,
			);
			func_builder.ins().jump(merge_ebb, &[]);

			func_builder.switch_to_block(merge_ebb);
			func_builder.seal_block(merge_ebb);
		}

		DeclarationStmt(decl) => {
			translate_in_function_declaration(decl, func_builder, cmod, name_env, type_env)
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
					cmod,
					name_env,
					type_env,
				);
			}
		}

		ReturnStmt(expr) => {
			if let Some(expr) = expr {
				let v = translate_in_function_expression(
					expr,
					Some(*return_ty),
					func_builder,
					cmod,
					name_env,
					type_env,
				);
				let v = type_cast_value(v, *return_ty, func_builder);
				func_builder.ins().return_(&[v]);
			}
		}
	}
}

fn translate_function_definition<'clif, 'tcx>(
	func: &'tcx FunctionDefinition, ctxt: &'clif mut Context, cmod: &'clif mut ConcreteModule,
	name_env: &'_ mut NameBindingEnvironment<'tcx>, type_env: &'_ mut TypeBindingEnvironment<'tcx>,
) -> (Function, FuncId, usize) {
	use SimpleType::*;
	use TypeSpecifier::*;

	let pointer_ty = cmod.target_config().pointer_type();

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
	let function_id = cmod
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
	translate_in_function_statement(
		body,
		&return_ty,
		&mut func_builder,
		cmod,
		&mut name_env,
		&mut type_env,
	);

	// finalize the function translation
	func_builder.finalize();
	// println!("{:?}", func_builder.func);

	let function_len = cmod.define_function(function_id, ctxt).expect("failed to define function");

	(ctxt.func.clone(), function_id, function_len as _)
}

pub fn compiled_function<'clif>(
	fid: FuncId, flen: usize, cmod: &'clif mut ConcreteModule,
) -> &'clif [u8] {
	let fptr = cmod.get_finalized_function(fid);
	unsafe { slice::from_raw_parts(mem::transmute::<_, *const u8>(fptr), flen as _) }
}

pub fn compile<'clif, 'tcx>(
	tu: &'tcx TranslationUnit, cmod: &'clif mut ConcreteModule,
	name_env: &'_ mut NameBindingEnvironment<'tcx>, type_env: &'_ mut TypeBindingEnvironment<'tcx>,
) -> Vec<(Function, FuncId, usize)> {
	use ExternalDeclaration::*;
	use TypeSpecifier::*;

	let TranslationUnit(extern_decs) = tu;

	let mut ctxt = cmod.make_context();
	let mut funcs = Vec::new();

	for dec in extern_decs {
		match dec {
			FunctionDefinitionDecl(func_def) => {
				let func =
					translate_function_definition(func_def, &mut ctxt, cmod, name_env, type_env);
				funcs.push(func);
				cmod.clear_context(&mut ctxt);
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

	cmod.finalize_definitions();
	funcs
}

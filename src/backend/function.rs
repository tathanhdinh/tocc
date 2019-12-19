#![allow(dead_code)]

use std::{
	cell::RefCell,
	cmp,
	hint::unreachable_unchecked,
	i16, i32, i64, i8,
	marker::PhantomData,
	mem, slice,
	sync::atomic::{AtomicUsize, Ordering},
};

use cranelift::prelude::*;
use cranelift_codegen::{
	ir::{entities::StackSlot, Function, Inst},
	Context,
};
use cranelift_module::{FuncId, Linkage};

use crate::{
	checked_if_let, checked_match, checked_unwrap, error,
	frontend::syntax::{
		BinaryOperator, BinaryOperatorExpression, CallExpression, Constant, Declaration, Declarator, DerivedDeclarator,
		DoWhileStatement, Expression, ExternalDeclaration, ForStatement, FunctionDeclarator, FunctionDefinition, Identifier,
		IfStatement, Integer, MemberExpression, MemberOperator, Statement, StructType, TranslationUnit, TypeSpecifier,
		UnaryOperator, UnaryOperatorExpression, WhileStatement,
	},
	unimpl,
};

use super::support::{
	evaluate_constant_arithmetic_expression, AggregateIdentifier, AggregateType, ConcreteModule, FunctionIdentifier,
	FunctionType, NameBindingEnvironment, PointerIdentifer, PrimitiveIdentifier, SimpleConcreteType, SimpleType,
	SimpleTypedIdentifier, TypeBindingEnvironment,
};

static NEW_VAR_ID: AtomicUsize = AtomicUsize::new(0);

struct FunctionTranslator<'clif, 'tcx> {
	pub func_builder: RefCell<FunctionBuilder<'clif>>,
	module: &'clif mut ConcreteModule,
	name_env: NameBindingEnvironment<'tcx>,
	type_env: TypeBindingEnvironment<'tcx>,
	pointer_ty: Type,
	return_ty: Option<Type>,
}

pub fn translate_function<'clif, 'tcx>(
	func_def: &'tcx FunctionDefinition<'tcx>, ctxt: &'clif mut Context, module: &'clif mut ConcreteModule,
	name_env: &'_ mut NameBindingEnvironment<'tcx>, type_env: &'_ mut TypeBindingEnvironment<'tcx>,
) -> (FuncId, usize) {
	use SimpleType::*;
	use TypeSpecifier::*;

	let FunctionDefinition { specifier, declarator: FunctionDeclarator { identifier: Identifier(fname), parameters }, body } =
		func_def;

	let pointer_ty = module.target_config().pointer_type();

	// function signature: return type
	let return_ty = match specifier {
		CharTy | ShortTy | IntTy | LongTy => Some(specifier.into()),

		StructTy(_) => todo!(),

		VoidTy => None,
	};
	if let Some(ty) = return_ty {
		ctxt.func.signature.returns.push(AbiParam::new(ty));
	}

	// function signature: param type
	let mut param_ty = Vec::new();
	for Declaration { specifier, declarator } in parameters {
		let Declarator { derived, .. } = checked_unwrap!(declarator.as_ref());
		if let Some(derived_decl) = derived {
			match derived_decl {
				// some pointer types
				DerivedDeclarator::Pointer => {
					ctxt.func.signature.params.push(AbiParam::new(pointer_ty));
					param_ty.push(pointer_ty);
				}
			}
		} else {
			// non pointer types
			match specifier {
				CharTy | ShortTy | IntTy | LongTy => {
					let ty = specifier.into();
					ctxt.func.signature.params.push(AbiParam::new(ty));
					param_ty.push(ty)
				}

				// simplification: struct definition does not occurs in parameter list
				StructTy(_) => todo!(),

				VoidTy => unsafe { unreachable_unchecked() },
			}
		}
	}

	let func_id = module.declare_function(fname, Linkage::Export, &ctxt.func.signature).expect("failed to declare function");

	name_env.insert(
		fname,
		SimpleTypedIdentifier::FunctionIdent(FunctionIdentifier {
			ident: func_id,
			ty: SimpleType::FunctionTy(FunctionType { return_ty, param_ty }),
		}),
	);

	let mut func_builder_ctxt = FunctionBuilderContext::new();
	let mut func_builder = FunctionBuilder::new(&mut ctxt.func, &mut func_builder_ctxt);

	let entry_ebb = func_builder.create_ebb();
	func_builder.append_ebb_params_for_function_params(entry_ebb);
	func_builder.switch_to_block(entry_ebb);

	for (i, Declaration { declarator, specifier }) in parameters.iter().enumerate() {
		let Declarator { ident: Identifier(var_name), derived, .. } = checked_unwrap!(declarator.as_ref()); // checked in syntax analysis
		let param_val = func_builder.ebb_params(entry_ebb)[i];

		match specifier {
			VoidTy => todo!(),

			CharTy | ShortTy | IntTy | LongTy => {
				if let Some(derived_decl) = derived {
					match derived_decl {
						DerivedDeclarator::Pointer => {
							let new_var = declare_variable(&mut func_builder, pointer_ty, Some(param_val));

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
					let new_var = declare_variable(&mut func_builder, specifier.into(), Some(param_val));

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
							let new_var = declare_variable(&mut func_builder, pointer_ty, Some(param_val));

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

	let mut func_translator = FunctionTranslator::new(func_builder, module, return_ty, name_env, type_env);
	func_translator.translate_statement(body);
	func_translator.func_builder.get_mut().finalize();

	let func_len = module.define_function(func_id, ctxt).expect("failed to define function");
	// let func = ctxt.func.clone();

	module.clear_context(ctxt);

	// let fptr = module.get_finalized_function(func_id);
	// unsafe { slice::from_raw_parts(mem::transmute::<_, *const u8>(fptr), func_len as _) }

	(func_id, func_len as usize)
}

fn declare_variable(func_builder: &'_ mut FunctionBuilder, ty: Type, init_val: Option<Value>) -> Variable {
	let new_var = Variable::new(NEW_VAR_ID.fetch_add(1, Ordering::Relaxed));
	func_builder.declare_var(new_var, ty);
	// let init_val = init_val.unwrap_or_else(|| Self::iconst(self, ty, 0));
	// Self::def_var(self, new_var, init_val);
	if let Some(init_val) = init_val {
		func_builder.def_var(new_var, init_val)
	}
	new_var
}

impl<'clif, 'tcx> FunctionTranslator<'clif, 'tcx> {
	pub fn new(
		func_builder: FunctionBuilder<'clif>, module: &'clif mut ConcreteModule, return_ty: Option<Type>,
		outer_name_env: &'_ NameBindingEnvironment<'tcx>, outer_type_env: &'_ TypeBindingEnvironment<'tcx>,
	) -> Self {
		let func_builder = RefCell::new(func_builder);
		let pointer_ty = module.target_config().pointer_type();

		let name_env = outer_name_env.clone();
		let type_env = outer_type_env.clone();

		Self { func_builder, module, name_env, type_env, pointer_ty, return_ty }
	}

	fn blur_signature(&mut self) {
		let call_conv = isa::CallConv::SystemV;

		let entry_ebb = checked_unwrap!(self.func_builder.borrow().func.layout.entry_block());
		let param_values = self.func_builder.borrow().ebb_params(entry_ebb);

		let sig = Signature {

		}
	}

	fn translate_declaration(&mut self, Declaration { specifier, declarator }: &'_ Declaration<'tcx>) {
		use SimpleConcreteType::*;
		use SimpleType::*;
		use SimpleTypedIdentifier::*;
		use TypeSpecifier::*;

		match specifier {
			CharTy | ShortTy | IntTy | LongTy | VoidTy => {
				let Declarator { ident: Identifier(var_name), derived, initializer } = checked_unwrap!(declarator.as_ref());

				let new_var;
				let new_var_ty;
				if let Some(derived_decl) = derived {
					match derived_decl {
						DerivedDeclarator::Pointer => {
							new_var = declare_variable(self.func_builder.get_mut(), self.pointer_ty, None);
							new_var_ty = self.pointer_ty;
							self.name_env.insert(
								var_name,
								PointerIdent(PointerIdentifer {
									ident: new_var,
									ty: PointerTy(Box::new(PrimitiveTy(specifier.into()))),
								}),
							);
						}
					}
				} else {
					match specifier {
						VoidTy => unsafe { unreachable_unchecked() },
						_ => {
							new_var_ty = specifier.into();
							new_var = declare_variable(self.func_builder.get_mut(), new_var_ty, None);

							self.name_env.insert(
								var_name,
								SimpleTypedIdentifier::PrimitiveIdent(PrimitiveIdentifier {
									ident: new_var,
									ty: SimpleType::PrimitiveTy(new_var_ty),
								}),
							);
						}
					}
				}

				if let Some(initializer) = initializer.as_ref() {
					let init_val = self.translate_expression(initializer);
					let init_val = match init_val {
						ConstantTy(val) => self.iconst(new_var_ty, val),
						ValueTy(val) => self.cast_value(new_var_ty, val),
						_ => unsafe { unreachable_unchecked() },
					};
					self.def_var(new_var, init_val);
				}
			}

			StructTy(struct_ty) => {
				let StructType { identifier: Identifier(sname), declarations } = struct_ty;
				if declarations.is_some() {
					let struct_ty: AggregateType = struct_ty.into();
					let struct_data = StackSlotData::new(StackSlotKind::ExplicitSlot, struct_ty.bytes() as _);

					let stack_slot = Self::create_stack_slot(self, struct_data);
					if let Some(Declarator { ident: Identifier(var_name), .. }) = declarator {
						self.name_env.insert(
							var_name,
							SimpleTypedIdentifier::AggregateIdent(AggregateIdentifier {
								ident: stack_slot,
								ty: SimpleType::AggregateTy(struct_ty.clone()),
							}),
						);
					}

					self.type_env.insert(sname, SimpleType::AggregateTy(struct_ty));
				}

				if let Some(Declarator { ident: Identifier(var_name), derived, .. }) = declarator {
					let struct_simple_ty = checked_unwrap!(self.type_env.get(sname));
					let struct_simple_ty = struct_simple_ty.to_owned();

					if let Some(derived_decl) = derived {
						match derived_decl {
							DerivedDeclarator::Pointer => {
								let new_var = declare_variable(self.func_builder.get_mut(), self.pointer_ty, None);
								self.name_env.insert(
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

						let stack_slot = self.create_stack_slot(struct_data);
						self.name_env.insert(
							var_name,
							AggregateIdent(AggregateIdentifier { ident: stack_slot, ty: struct_simple_ty }),
						);
					}
				}
			}
		}
	}

	fn translate_do_while_statement(&'_ mut self, DoWhileStatement { statement, condition }: &'_ DoWhileStatement<'tcx>) {
		use SimpleConcreteType::*;

		let loop_ebb = self.new_ebb();
		let exit_ebb = self.new_ebb();

		self.insert_jmp(loop_ebb);

		self.switch_to_ebb(loop_ebb);
		self.translate_statement(statement.as_ref());
		let cond = self.translate_expression(condition);
		let cond = match cond {
			ConstantTy(c) => self.iconst(types::I64, c),
			ValueTy(v) => v,
			_ => unsafe { unreachable_unchecked() },
		};
		self.insert_brz(cond, exit_ebb);
		self.insert_jmp(loop_ebb);
		self.seal_ebb(loop_ebb);

		self.switch_to_ebb(exit_ebb);
		self.seal_ebb(exit_ebb);
	}

	fn translate_while_statement(&'_ mut self, WhileStatement { condition, statement }: &'_ WhileStatement<'tcx>) {
		use SimpleConcreteType::*;

		let header_ebb = self.new_ebb();
		let loop_ebb = self.new_ebb();
		let exit_ebb = self.new_ebb();

		self.insert_jmp(header_ebb);

		// header EBB
		self.switch_to_ebb(header_ebb);
		let cond = self.translate_expression(condition);
		let cond = match cond {
			ConstantTy(c) => self.iconst(types::I64, c),
			ValueTy(v) => v,
			_ => unsafe { unreachable_unchecked() },
		};
		self.insert_brz(cond, exit_ebb);
		self.insert_jmp(loop_ebb);

		// loop EBB
		self.switch_to_ebb(loop_ebb);
		self.seal_ebb(loop_ebb);
		self.translate_statement(statement.as_ref());
		self.insert_jmp(header_ebb);

		self.seal_ebb(header_ebb);

		self.switch_to_ebb(exit_ebb);
		self.seal_ebb(exit_ebb);
	}

	fn translate_statement(&mut self, stmt: &'_ Statement<'tcx>) {
		use SimpleConcreteType::*;
		use Statement::*;

		match stmt {
			DoWhileStmt(stmt) => self.translate_do_while_statement(stmt),

			WhileStmt(stmt) => self.translate_while_statement(stmt),

			ForStmt(ForStatement { initializer, condition, step, statement }) => {
				if let Some(initializer) = initializer.as_ref() {
					self.translate_expression(initializer);
				}

				let header_ebb = self.new_ebb();
				let loop_ebb = self.new_ebb();
				let exit_ebb = self.new_ebb();

				self.insert_jmp(header_ebb);

				// header EBB
				self.switch_to_ebb(header_ebb);
				let cond = self.translate_expression(condition);
				let cond = match cond {
					ConstantTy(c) => self.iconst(types::I64, c),
					ValueTy(v) => v,
					_ => unsafe { unreachable_unchecked() },
				};
				self.insert_brz(cond, exit_ebb);
				self.insert_jmp(loop_ebb);

				// loop EBB
				self.switch_to_ebb(loop_ebb);
				self.seal_ebb(loop_ebb);
				self.translate_statement(statement.as_ref());
				if let Some(step) = step.as_ref() {
					self.translate_expression(step);
				}
				self.insert_jmp(header_ebb);
				self.seal_ebb(header_ebb);

				self.switch_to_ebb(exit_ebb);
				self.seal_ebb(exit_ebb);
			}

			IfStmt(IfStatement { condition, then_statement, else_statement }) => {
				let cond = self.translate_expression(condition);
				let cond = match cond {
					ConstantTy(c) => self.iconst(types::I64, c),
					ValueTy(v) => v,
					_ => unsafe { unreachable_unchecked() },
				};

				let then_ebb = self.new_ebb();
				let merge_ebb = self.new_ebb();
				if let Some(else_stmt) = else_statement.as_ref() {
					let else_ebb = self.new_ebb();
					self.insert_brz(cond, else_ebb);
					self.insert_jmp(then_ebb);

					// else EBB
					self.switch_to_ebb(else_ebb);
					self.seal_ebb(else_ebb);
					self.translate_statement(else_stmt.as_ref());
					self.insert_jmp(merge_ebb);
				} else {
					self.insert_brz(cond, merge_ebb);
					self.insert_jmp(then_ebb);
				}

				// then EBB
				self.switch_to_ebb(then_ebb);
				self.seal_ebb(then_ebb);
				self.translate_statement(then_statement.as_ref());
				self.insert_jmp(merge_ebb);

				self.switch_to_ebb(merge_ebb);
				self.seal_ebb(merge_ebb);
			}

			ReturnStmt(expr) => {
				if let Some(expr) = expr {
					let val = self.translate_expression(expr);
					let return_ty = checked_unwrap!(self.return_ty);
					let val = match val {
						ConstantTy(c) => self.iconst(return_ty, c),
						ValueTy(v) => v,
						StackSlotTy(ss) => self.stack_load(return_ty, ss, 0),
						_ => unsafe { unreachable_unchecked() },
					};

					self.func_builder.borrow_mut().ins().return_(&[val]);
				}
			}

			CompoundStmt(stmts) => {
				let original_name_env = self.name_env.clone();
				let original_type_env = self.type_env.clone();

				for stmt in stmts {
					self.translate_statement(stmt);
				}
				self.name_env = original_name_env;
				self.type_env = original_type_env;
			}

			ExpressionStmt(expr) => {
				if let Some(expr) = expr {
					// C11 Standard: 6.8.3 Expression and null statements
					// A statement expression is an expression but its type is void,
					// i.e. it is evaluated for side-effect.
					// E.g. x = 5 is a binary expression where the operator is assignment
					self.translate_expression(expr);
				}
			}

			DeclarationStmt(decl) => self.translate_declaration(decl),
			// _ => todo!(),
		}
	}

	fn translate_unary_operator_expression(
		&'_ mut self, UnaryOperatorExpression { operator, operand }: &'_ UnaryOperatorExpression<'tcx>,
	) -> SimpleConcreteType {
		use Expression::*;
		use MemberOperator::*;
		use SimpleConcreteType::*;
		use SimpleType::*;
		use SimpleTypedIdentifier::*;
		use UnaryOperator::*;

		match operator {
			Negation => {
				let rhs = self.translate_expression(operand.as_ref());
				match rhs {
					ConstantTy(rhs) => ConstantTy(-rhs),
					ValueTy(rhs) => ValueTy(self.ineg(rhs)),
					_ => unsafe { unreachable_unchecked() },
				}
			}

			// e.g. ++i
			PreIncrement => checked_if_let!(IdentifierExpr(var_name), operand.as_ref(), {
				let var_name: &str = var_name.into();
				let ident_var = checked_unwrap!(self.name_env.get(var_name));
				checked_if_let!(PrimitiveIdent(PrimitiveIdentifier { ident, .. }), ident_var, {
					let ident_val = self.use_var(*ident);
					let ident_new_val = self.iadd_imm(ident_val, 1);
					self.def_var(*ident, ident_new_val);
					ValueTy(ident_new_val)
				})
			}),

			// e.g. i++
			PostIncrement => checked_if_let!(IdentifierExpr(var_name), operand.as_ref(), {
				let var_name: &str = var_name.into();
				let ident_var = checked_unwrap!(self.name_env.get(var_name));
				checked_if_let!(PrimitiveIdent(PrimitiveIdentifier { ident, .. }), ident_var, {
					let ident_val = self.use_var(*ident);
					let ident_new_val = self.iadd_imm(ident_val, 1);
					self.def_var(*ident, ident_new_val);
					ValueTy(ident_val)
				})
			}),

			Address => match operand.as_ref() {
				IdentifierExpr(ident) => {
					let var_name: &str = ident.into();
					let typed_ident = checked_unwrap!(self.name_env.get(var_name));
					match typed_ident {
						AggregateIdent(AggregateIdentifier { ident, .. }) => {
							ValueTy(self.stack_addr(self.pointer_ty, *ident, 0))
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
							let typed_ident = checked_unwrap!(self.name_env.get(struct_name));
							match typed_ident {
								// e.g. s.i
								AggregateIdent(AggregateIdentifier { ident, ty: AggregateTy(aggre_ty) }) => {
									checked_match!(operator, Direct, {
										let offset = checked_unwrap!(aggre_ty.field_offset(field_name));
										ValueTy(self.stack_addr(self.pointer_ty, *ident, offset as i32))
									})
								}

								// e.g. ps->i
								PointerIdent(PointerIdentifer { ident, ty }) => checked_match!(operator, Indirect, {
									checked_match!(ty, AggregateTy(aggre_ty), {
										let ident_addr = self.use_var(*ident);
										let offset = checked_unwrap!(aggre_ty.field_offset(field_name));
										ValueTy(self.iadd_imm(ident_addr, offset as i64))
									})
								}),

								_ => unsafe { unreachable_unchecked() },
							}
						}

						_ => unimpl!("expression unsupported in member expression"),
					}
				}

				_ => unsafe { unreachable_unchecked() },
			},
		}
	}

	fn translate_binary_operator_expression(
		&'_ mut self, BinaryOperatorExpression { operator, lhs, rhs }: &'_ BinaryOperatorExpression<'tcx>,
	) -> SimpleConcreteType {
		use BinaryOperator::*;
		use Expression::*;
		use MemberOperator::*;
		use SimpleConcreteType::*;
		use SimpleType::*;
		use SimpleTypedIdentifier::*;

		let lhs_val = self.translate_expression(lhs.as_ref());
		let rhs_val = self.translate_expression(rhs.as_ref());

		match (lhs_val, rhs_val) {
			(ConstantTy(lhs), ConstantTy(rhs)) => match operator {
				Multiplication => ConstantTy(lhs * rhs),
				Division => ConstantTy(lhs / rhs),
				Addition => ConstantTy(lhs + rhs),
				Subtraction => ConstantTy(lhs - rhs),

				Less => ValueTy(self.bconst(types::B64, lhs < rhs)),
				LessOrEqual => ValueTy(self.bconst(types::B64, lhs <= rhs)),
				Greater => ValueTy(self.bconst(types::I64, lhs > rhs)),
				GreaterOrEqual => ValueTy(self.bconst(types::I64, lhs >= rhs)),
				Equal => ValueTy(self.bconst(types::I64, lhs == rhs)),

				Assignment | AdditionAssignment | SubtractionAssignment | MultiplicationAssignment | DivisionAssignment => unsafe {
					unreachable_unchecked()
				},
			},

			(ConstantTy(lhs), ValueTy(rhs)) => match operator {
				Multiplication => ValueTy(Self::imul_imm(self, rhs, lhs)),
				Division => {
					let rhs_ty = Self::value_type(self, rhs);
					let lhs = Self::iconst(self, rhs_ty, lhs);
					ValueTy(Self::idiv(self, lhs, rhs))
				}
				Addition => ValueTy(self.iadd_imm(rhs, lhs)),
				Subtraction => {
					let rhs_ty = self.value_type(rhs);
					let lhs = Self::iconst(self, rhs_ty, lhs);
					ValueTy(Self::isub(self, lhs, rhs))
				}

				Less => ValueTy(self.icmp_imm(IntCC::SignedGreaterThan, rhs, lhs)),
				LessOrEqual => ValueTy(Self::icmp_imm(self, IntCC::SignedGreaterThanOrEqual, rhs, lhs)),
				Greater => ValueTy(Self::icmp_imm(self, IntCC::SignedLessThan, rhs, lhs)),
				GreaterOrEqual => ValueTy(Self::icmp_imm(self, IntCC::SignedLessThanOrEqual, rhs, lhs)),
				Equal => ValueTy(Self::icmp_imm(self, IntCC::Equal, rhs, lhs)),

				Assignment | AdditionAssignment | SubtractionAssignment | MultiplicationAssignment | DivisionAssignment => unsafe {
					unreachable_unchecked()
				},
			},

			(ValueTy(lhs_val), ConstantTy(rhs_val)) => match operator {
				Multiplication => ValueTy(self.imul_imm(lhs_val, rhs_val)),
				Division => ValueTy(self.idiv_imm(lhs_val, rhs_val)),
				Addition => ValueTy(self.iadd_imm(lhs_val, rhs_val)),
				Subtraction => {
					let lhs_ty = self.value_type(lhs_val);
					let rhs = self.iconst(lhs_ty, rhs_val);
					ValueTy(self.isub(lhs_val, rhs))
				}

				Less => ValueTy(self.icmp_imm(IntCC::SignedLessThan, lhs_val, rhs_val)),
				LessOrEqual => ValueTy(self.icmp_imm(IntCC::SignedLessThanOrEqual, lhs_val, rhs_val)),
				Greater => ValueTy(self.icmp_imm(IntCC::SignedGreaterThan, lhs_val, rhs_val)),
				GreaterOrEqual => ValueTy(self.icmp_imm(IntCC::SignedGreaterThanOrEqual, lhs_val, rhs_val)),
				Equal => ValueTy(self.icmp_imm(IntCC::Equal, lhs_val, rhs_val)),

				Assignment | AdditionAssignment | SubtractionAssignment | MultiplicationAssignment | DivisionAssignment => {
					match lhs.as_ref() {
						IdentifierExpr(Identifier(var_name)) => {
							let lhs_var = checked_unwrap!(self.name_env.get(var_name));
							checked_if_let!(PrimitiveIdent(PrimitiveIdentifier { ident, .. }), lhs_var, {
								let lhs_ty = Self::value_type(self, lhs_val);
								let new_lhs_val = match operator {
									Assignment => Self::iconst(self, lhs_ty, rhs_val),
									AdditionAssignment => Self::iadd_imm(self, lhs_val, rhs_val),
									SubtractionAssignment => {
										let rhs_val = Self::iconst(self, lhs_ty, rhs_val);
										Self::isub(self, lhs_val, rhs_val)
									}
									MultiplicationAssignment => Self::imul_imm(self, lhs_val, rhs_val),
									DivisionAssignment => Self::idiv_imm(self, lhs_val, rhs_val),
									_ => unsafe { unreachable_unchecked() },
								};
								Self::def_var(self, *ident, new_lhs_val);
							});
						}

						MemberExpr(MemberExpression { expression, identifier: Identifier(field_name), operator }) => {
							checked_match!(expression.as_ref(), IdentifierExpr(Identifier(var_name)), {
								let typed_ident = checked_unwrap!(self.name_env.get(var_name));
								match typed_ident {
									// e.g. s.x
									AggregateIdent(AggregateIdentifier { ident, ty: AggregateTy(aggre_ty) }) => {
										checked_match!(operator, Direct, {
											let field_offset = checked_unwrap!(aggre_ty.field_offset(field_name));
											let field_ty = checked_unwrap!(aggre_ty.field_type(field_name));
											let rhs_val = self.iconst(field_ty, rhs_val);
											self.stack_store(rhs_val, *ident, field_offset as i32);
										});
									}

									// e.g. ps->x
									PointerIdent(PointerIdentifer { ident, ty }) => {
										checked_match!(operator, Indirect, {
											checked_match!(ty, PointerTy(pty), {
												checked_match!(pty.as_ref(), AggregateTy(aggre_ty), {
													let field_offset = checked_unwrap!(aggre_ty.field_offset(field_name));
													let field_ty = checked_unwrap!(aggre_ty.field_type(field_name));
													let ident_val = self.use_var(*ident);
													let rhs_val = self.iconst(field_ty, rhs_val);
													self.store(rhs_val, ident_val, field_offset as i32);
												})
											});
										});
									}

									_ => unsafe { unreachable_unchecked() },
								}
							});
						}

						_ => unsafe { unreachable_unchecked() },
					}

					UnitTy
				}
			},

			(ValueTy(lhs_val), ValueTy(rhs_val)) => match operator {
				Multiplication => ValueTy(self.iadd(lhs_val, rhs_val)),
				Division => ValueTy(self.idiv(lhs_val, rhs_val)),
				Addition => ValueTy(self.iadd(lhs_val, rhs_val)),
				Subtraction => ValueTy(self.isub(lhs_val, rhs_val)),

				Less => ValueTy(self.icmp(IntCC::SignedLessThan, lhs_val, rhs_val)),
				LessOrEqual => ValueTy(self.icmp(IntCC::SignedLessThanOrEqual, lhs_val, rhs_val)),
				Greater => ValueTy(self.icmp(IntCC::SignedGreaterThan, lhs_val, rhs_val)),
				GreaterOrEqual => ValueTy(self.icmp(IntCC::SignedGreaterThanOrEqual, lhs_val, rhs_val)),
				Equal => ValueTy(self.icmp(IntCC::Equal, lhs_val, rhs_val)),

				Assignment | AdditionAssignment | SubtractionAssignment | MultiplicationAssignment | DivisionAssignment => {
					match lhs.as_ref() {
						IdentifierExpr(Identifier(var_name)) => {
							let lhs_var = checked_unwrap!(self.name_env.get(var_name));
							checked_if_let!(PrimitiveIdent(PrimitiveIdentifier { ident, .. }), lhs_var, {
								let new_lhs_val = match operator {
									Assignment => rhs_val,
									AdditionAssignment => self.iadd(lhs_val, rhs_val),
									SubtractionAssignment => self.isub(lhs_val, rhs_val),
									MultiplicationAssignment => self.imul(lhs_val, rhs_val),
									DivisionAssignment => self.idiv(lhs_val, rhs_val),
									_ => unsafe { unreachable_unchecked() },
								};
								Self::def_var(self, *ident, new_lhs_val);
							});
						}

						MemberExpr(MemberExpression { expression, identifier: Identifier(field_name), operator }) => {
							checked_match!(expression.as_ref(), IdentifierExpr(Identifier(var_name)), {
								let typed_ident = checked_unwrap!(self.name_env.get(var_name));
								match typed_ident {
									// e.g. s.x
									AggregateIdent(AggregateIdentifier { ident, ty: AggregateTy(aggre_ty) }) => {
										checked_match!(operator, Direct, {
											let field_offset = checked_unwrap!(aggre_ty.field_offset(field_name));
											// let field_ty = checked_unwrap!(aggre_ty.field_type(field_name));
											// let rhs_val = self.iconst(self, field_ty, rhs_val);
											self.stack_store(rhs_val, *ident, field_offset as i32);
										});
									}

									// e.g. ps->x
									PointerIdent(PointerIdentifer { ident, ty }) => {
										checked_match!(operator, Indirect, {
											checked_match!(ty, PointerTy(pty), {
												checked_match!(pty.as_ref(), AggregateTy(aggre_ty), {
													let field_offset = checked_unwrap!(aggre_ty.field_offset(field_name));
													// let field_ty = checked_unwrap!(aggre_ty.field_type(field_name));
													let ident_val = self.use_var(*ident);
													// let rhs_val = Self::iconst(self, field_ty, rhs_val);
													self.store(rhs_val, ident_val, field_offset as i32);
												})
											});
										});
									}

									_ => unsafe { unreachable_unchecked() },
								}
							});
						}

						_ => unsafe { unreachable_unchecked() },
					}

					UnitTy
				}
			},

			(StackSlotTy(_lhs_ss), StackSlotTy(_rhs_ss)) => match operator {
				Assignment => {
					// zone for obfuscator
					todo!()
				}

				_ => unsafe { unreachable_unchecked() },
			},

			_ => unsafe { unreachable_unchecked() },
		}
	}

	fn translate_member_expression(
		&'_ self, MemberExpression { expression, identifier: Identifier(field_name), operator }: &'_ MemberExpression<'tcx>,
	) -> SimpleConcreteType {
		use Expression::*;
		use MemberOperator::*;
		use SimpleConcreteType::*;
		use SimpleType::*;
		use SimpleTypedIdentifier::*;

		if let IdentifierExpr(Identifier(var_name)) = expression.as_ref() {
			let typed_ident = checked_unwrap!(self.name_env.get(var_name));
			match typed_ident {
				// e.g. s.i
				AggregateIdent(AggregateIdentifier { ident, ty: AggregateTy(aggre_ty) }) => {
					checked_match!(operator, Direct, {
						let offset = checked_unwrap!(aggre_ty.field_offset(field_name));
						let (_, ty) = checked_unwrap!(aggre_ty.fields.iter().find(|(fname, _)| fname == field_name));
						ValueTy(Self::stack_load(self, *ty, *ident, offset as i32))
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

								let (_, ty) = checked_unwrap!(aggre_ty.fields.iter().find(|(fname, _)| fname == field_name));

								let ident_val = Self::use_var(self, *ident);
								ValueTy(Self::load(self, *ty, ident_val, offset as i32))
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

	fn translate_call_expression(
		&'_ mut self, CallExpression { callee: Identifier(func_name), arguments }: &'_ CallExpression<'tcx>,
	) -> SimpleConcreteType {
		use SimpleConcreteType::*;
		use SimpleTypedIdentifier::*;

		// let func_name: &str = callee.into();
		let func = checked_unwrap!(self.name_env.get(func_name)).clone();
		match func {
			FunctionIdent(FunctionIdentifier {
				ty: SimpleType::FunctionTy(FunctionType { return_ty, param_ty }), ..
			}) => {
				let mut sig = self.module.make_signature();
				if let Some(return_ty) = return_ty {
					sig.returns.push(AbiParam::new(return_ty)); // return type
				}
				for pty in param_ty.iter() {
					sig.params.push(AbiParam::new(*pty)); // parameter types
				}

				let callee =
					self.module.declare_function(func_name, Linkage::Import, &sig).expect("failed to declare function");
				let local_callee = self.module.declare_func_in_func(callee, self.func_builder.get_mut().func);

				let arg_values: Vec<_> = arguments
					.iter()
					.zip(param_ty.iter())
					.map(|(arg, ty)| {
						let arg_val = Self::translate_expression(self, arg);
						match arg_val {
							ValueTy(val) => Self::cast_value(self, *ty, val),
							ConstantTy(val) => Self::iconst(self, *ty, val),
							_ => unsafe { unreachable_unchecked() },
						}
					})
					.collect();

				let call = self.func_builder.borrow_mut().ins().call(local_callee, &arg_values);

				if return_ty.is_some() {
					ValueTy(self.func_builder.borrow_mut().inst_results(call)[0])
				} else {
					UnitTy
				}
			}

			_ => unimpl!("unsupported call identifier"),
		}
	}

	fn translate_identifier_expression(&'_ self, Identifier(var_name): &'_ Identifier<'tcx>) -> SimpleConcreteType {
		let var = checked_unwrap!(self.name_env.get(var_name));
		checked_match!(var, SimpleTypedIdentifier::PrimitiveIdent(PrimitiveIdentifier { ident, .. }), {
			SimpleConcreteType::ValueTy(Self::use_var(self, *ident))
		})
	}

	fn translate_expression(&'_ mut self, expr: &'_ Expression<'tcx>) -> SimpleConcreteType {
		use Expression::*;

		if let Some(val) = evaluate_constant_arithmetic_expression(expr) {
			SimpleConcreteType::ConstantTy(val)
		} else {
			match expr {
				CallExpr(expr) => Self::translate_call_expression(self, expr),

				MemberExpr(expr) => Self::translate_member_expression(self, expr),

				IdentifierExpr(ident) => Self::translate_identifier_expression(self, ident),

				UnaryOperatorExpr(expr) => Self::translate_unary_operator_expression(self, expr),

				BinaryOperatorExpr(expr) => Self::translate_binary_operator_expression(self, expr),

				ConstantExpr(_) => unsafe { unreachable_unchecked() },
			}
		}
	}

	fn cast_value(&'_ self, ty: Type, val: Value) -> Value {
		let val_size = Self::value_type(self, val).bytes();
		let ty_size = ty.bytes();
		if val_size > ty_size {
			self.func_builder.borrow_mut().ins().ireduce(ty, val)
		} else if val_size < ty_size {
			self.func_builder.borrow_mut().ins().sextend(ty, val)
		} else {
			val
		}
	}

	fn new_ebb(&'_ self) -> Ebb {
		self.func_builder.borrow_mut().create_ebb()
	}

	fn switch_to_ebb(&'_ self, ebb: Ebb) {
		self.func_builder.borrow_mut().switch_to_block(ebb)
	}

	fn seal_ebb(&'_ self, ebb: Ebb) {
		self.func_builder.borrow_mut().seal_block(ebb)
	}

	fn value_type(&'_ self, val: Value) -> Type {
		self.func_builder.borrow_mut().func.dfg.value_type(val)
	}

	fn use_var(&'_ self, var: Variable) -> Value {
		self.func_builder.borrow_mut().use_var(var)
	}

	fn def_var(&'_ self, var: Variable, val: Value) {
		self.func_builder.borrow_mut().def_var(var, val)
	}

	fn create_stack_slot(&'_ self, data: StackSlotData) -> StackSlot {
		self.func_builder.borrow_mut().create_stack_slot(data)
	}

	fn stack_addr(&'_ self, addr_ty: Type, ss: StackSlot, offset: impl Into<i32>) -> Value {
		self.func_builder.borrow_mut().ins().stack_addr(addr_ty, ss, offset.into())
	}

	fn stack_load(&'_ self, ty: Type, ss: StackSlot, offset: impl Into<i32>) -> Value {
		self.func_builder.borrow_mut().ins().stack_load(ty, ss, offset.into())
	}

	fn load(&'_ self, ty: Type, p: Value, offset: impl Into<i32>) -> Value {
		self.func_builder.borrow_mut().ins().load(ty, MemFlags::new(), p, offset.into())
	}

	fn stack_store(&self, x: Value, ss: StackSlot, offset: impl Into<i32>) -> Inst {
		self.func_builder.borrow_mut().ins().stack_store(x, ss, offset.into())
	}

	fn store(&self, x: Value, p: Value, offset: impl Into<i32>) -> Inst {
		self.func_builder.borrow_mut().ins().store(MemFlags::new(), x, p, offset.into())
	}

	fn iconst(&self, nty: Type, n: impl Into<i64>) -> Value {
		self.func_builder.borrow_mut().ins().iconst(nty, n.into())
	}

	fn iadd(&self, x: Value, y: Value) -> Value {
		self.func_builder.borrow_mut().ins().iadd(x, y)
	}

	fn iadd_imm(&self, x: Value, n: impl Into<i64>) -> Value {
		self.func_builder.borrow_mut().ins().iadd_imm(x, n.into())
	}

	fn isub(&self, x: Value, y: Value) -> Value {
		self.func_builder.borrow_mut().ins().isub(x, y)
	}

	fn idiv(&self, x: Value, y: Value) -> Value {
		self.func_builder.borrow_mut().ins().sdiv(x, y)
	}

	fn idiv_imm(&self, x: Value, n: impl Into<i64>) -> Value {
		self.func_builder.borrow_mut().ins().sdiv_imm(x, n.into())
	}

	fn imul(&self, x: Value, y: Value) -> Value {
		self.func_builder.borrow_mut().ins().imul(x, y)
	}

	fn imul_imm(&self, x: Value, n: impl Into<i64>) -> Value {
		self.func_builder.borrow_mut().ins().imul_imm(x, n.into())
	}

	fn ineg(&self, x: Value) -> Value {
		self.func_builder.borrow_mut().ins().ineg(x)
	}

	fn bconst(&self, bty: Type, n: impl Into<bool>) -> Value {
		self.func_builder.borrow_mut().ins().bconst(bty, n)
	}

	fn icmp(&self, cond: impl Into<IntCC>, x: Value, y: Value) -> Value {
		self.func_builder.borrow_mut().ins().icmp(cond, x, y)
	}

	fn icmp_imm(&self, cond: impl Into<IntCC>, x: Value, y: impl Into<i64>) -> Value {
		self.func_builder.borrow_mut().ins().icmp_imm(cond, x, y.into())
	}

	fn insert_brz(&self, cond: Value, ebb: Ebb) -> Inst {
		self.func_builder.borrow_mut().ins().brz(cond, ebb, &[])
	}

	fn insert_jmp(&self, ebb: Ebb) -> Inst {
		self.func_builder.borrow_mut().ins().jump(ebb, &[])
	}
}

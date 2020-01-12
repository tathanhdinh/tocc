#![allow(dead_code)]

use std::{
	cell::RefCell,
	collections::HashMap,
	hint::unreachable_unchecked,
	i16, i32, i64, i8,
	marker::PhantomData,
	mem, slice,
	sync::atomic::{AtomicUsize, Ordering},
};

use cranelift::prelude::*;
use cranelift_codegen::{
	ir::{
		entities::{FuncRef, SigRef, StackSlot},
		Inst,
	},
	Context,
};
use cranelift_module::{Backend, FuncId, Linkage, Module};

use crate::{
	checked_if_let, checked_match, checked_unwrap_option, checked_unwrap_result, generate_random_maps,
	frontend::syntax::{
		BinaryOperator, BinaryOperatorExpression, CallExpression, Constant, Declaration,
		Declarator, DerivedDeclarator, DoWhileStatement, Expression, ExternalDeclaration,
		ForStatement, FunctionDeclarator, FunctionDefinition, Identifier, IfStatement, Integer,
		MemberExpression, MemberOperator, Statement, StructType, TranslationUnit, TypeSpecifier,
		UnaryOperator, UnaryOperatorExpression, WhileStatement,
	},
	unimpl,
};

use super::support::{
	evaluate_constant_arithmetic_expression, generate_random_maps_bv16, generate_random_maps_bv32,
	generate_random_maps_bv8, generate_random_partition, AggregateIdentifier, AggregateType,
	FunctionIdentifier, FunctionType, NameBindingEnvironment, PointerIdentifer,
	PrimitiveIdentifier, SimpleConcreteType, SimpleType, SimpleTypedIdentifier,
	TypeBindingEnvironment,
};

static NEW_VAR_ID: AtomicUsize = AtomicUsize::new(0);

struct FunctionTranslator<'clif, 'tcx, B: Backend> {
	pub func_builder: RefCell<FunctionBuilder<'clif>>,
	module: &'clif mut Module<B>,
	func_id: FuncId,
	func_ref: FuncRef,
	imported_sigs: RefCell<HashMap<Signature, SigRef>>,
	name_env: NameBindingEnvironment<'tcx>,
	type_env: TypeBindingEnvironment<'tcx>,
	pointer_ty: Type,
	return_ty: Option<Type>,
}

pub fn translate_function<'clif, 'tcx>(
	func_def: &'tcx FunctionDefinition<'tcx>, ctxt: &'clif mut Context,
	module: &'clif mut Module<impl Backend>, name_env: &'_ mut NameBindingEnvironment<'tcx>,
	type_env: &'_ mut TypeBindingEnvironment<'tcx>,
) -> (FuncId, usize) {
	use SimpleType::*;
	use TypeSpecifier::*;

	let FunctionDefinition {
		specifier,
		declarator: FunctionDeclarator { identifier: Identifier(fname), parameters },
		body,
	} = func_def;

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
		let Declarator { derived, .. } = checked_unwrap_option!(declarator.as_ref());
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

	let func_id = checked_unwrap_result!(module.declare_function(
		fname,
		Linkage::Export,
		&ctxt.func.signature
	));

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
		let Declarator { ident: Identifier(var_name), derived, .. } =
			checked_unwrap_option!(declarator.as_ref()); // checked in syntax analysis
		let param_val = func_builder.ebb_params(entry_ebb)[i];

		match specifier {
			VoidTy => todo!(),

			CharTy | ShortTy | IntTy | LongTy => {
				if let Some(derived_decl) = derived {
					match derived_decl {
						DerivedDeclarator::Pointer => {
							let new_var =
								declare_variable(&mut func_builder, pointer_ty, Some(param_val));

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
					let new_var =
						declare_variable(&mut func_builder, specifier.into(), Some(param_val));

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
							let new_var =
								declare_variable(&mut func_builder, pointer_ty, Some(param_val));

							let aggre_ty = checked_unwrap_option!(type_env.get(sname));

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

	let body_ebb = func_builder.create_ebb();
	func_builder.ins().jump(body_ebb, &[]);
	func_builder.seal_block(entry_ebb);
	func_builder.switch_to_block(body_ebb);
	func_builder.seal_block(body_ebb);

	// for _ in func_builder.func.layout.ebbs() {
	// 	println!("ebb");
	// }
	// let entry_ebb = checked_unwrap_option!(func_builder.func.layout.entry_block());
	// println!("ok");

	let mut func_translator =
		FunctionTranslator::new(func_builder, module, func_id, return_ty, name_env, type_env);
	func_translator.blur_signature();
	func_translator.translate_statement(body);
	func_translator.func_builder.get_mut().finalize();
	println!("{:?}", func_translator.func_builder.borrow().func);

	let func_len = module.define_function(func_id, ctxt).expect("failed to define function");
	// let func = ctxt.func.clone();

	module.clear_context(ctxt);

	// let fptr = module.get_finalized_function(func_id);
	// unsafe { slice::from_raw_parts(mem::transmute::<_, *const u8>(fptr), func_len as _) }

	(func_id, func_len as usize)
}

fn declare_variable(
	func_builder: &'_ mut FunctionBuilder, ty: Type, init_val: Option<Value>,
) -> Variable {
	let new_var = Variable::new(NEW_VAR_ID.fetch_add(1, Ordering::Relaxed));
	func_builder.declare_var(new_var, ty);
	if let Some(init_val) = init_val {
		func_builder.def_var(new_var, init_val)
	}
	new_var
}

impl<'clif, 'tcx, B: Backend> FunctionTranslator<'clif, 'tcx, B> {
	pub fn new(
		func_builder: FunctionBuilder<'clif>, module: &'clif mut Module<B>, func_id: FuncId,
		return_ty: Option<Type>, outer_name_env: &'_ NameBindingEnvironment<'tcx>,
		outer_type_env: &'_ TypeBindingEnvironment<'tcx>,
	) -> Self {
		let mut func_builder = RefCell::new(func_builder);
		let pointer_ty = module.target_config().pointer_type();
		let func_ref = module.declare_func_in_func(func_id, func_builder.get_mut().func);

		// let name_env = outer_name_env.clone();
		// let type_env = outer_type_env.clone();

		Self {
			func_builder,
			module,
			func_id,
			func_ref,
			imported_sigs: RefCell::new(HashMap::new()),
			name_env: outer_name_env.clone(),
			type_env: outer_type_env.clone(),
			pointer_ty,
			return_ty,
		}
	}

	pub fn blur_signature(&'_ mut self) {
		let call_conv = isa::CallConv::SystemV;
		let param_vals = {
			let entry_ebb =
				checked_unwrap_option!(self.func_builder.borrow().func.layout.entry_block());
			self.func_builder.borrow().ebb_params(entry_ebb).to_owned()
		};

		for pval in param_vals {
			let sig = Signature {
				params: vec![AbiParam::new(self.value_type(pval)), AbiParam::new(self.pointer_ty)],
				returns: if let Some(return_ty) = self.return_ty {
					vec![AbiParam::new(return_ty)]
				} else {
					vec![]
				},
				call_conv,
			};
			let sigref = self.import_signature(&sig);

			// let self_func = self.module.declare_func_in_func(self.func_id, self.func_builder.get_mut().func);
			// let faddr = self.func_addr(self_func);
			// let faddr = self.self_func_addr();
			let pval_blurred = self.blur_value(pval);
			let faddr = self.func_addr(self.func_ref);

			// opaque predicate: x != y
			let pval2 = self.imul(pval, pval_blurred);
			// let pval2 = self.blur_value(pval2);
			let x = self.iadd_imm(pval2, 1); // x^2 + 2
			let y = self.imul(pval_blurred, pval2); // x^3

			let merge_ebb = self.new_ebb();
			let never_ebb = self.new_ebb();
			let x = self.cast_value(self.pointer_ty, x);
			let y = self.cast_value(self.pointer_ty, y);
			self.insert_br_icmp(IntCC::NotEqual, x, y, merge_ebb);
			self.insert_jmp(never_ebb);

			self.switch_to_ebb(never_ebb);
			let func = self.cast_value(self.pointer_ty, pval);
			self.insert_indirect_call(sigref, func, &[pval, faddr]);
			self.insert_jmp(merge_ebb);
			self.seal_ebb(never_ebb);

			self.switch_to_ebb(merge_ebb);
			self.seal_ebb(merge_ebb);
		}
	}

	fn blur_value(&'_ self, val: Value) -> Value {
		let val_ty = self.value_type(val);
		let val_size = val_ty.bytes();

		let ss = {
			let ss = self.create_stack_slot(val_size as _);

			let random_type_partition = generate_random_partition(val_size);
			let mut offset = 0i32;
			for ty in random_type_partition {
				let pval = {
					let pval = self.logical_shr_imm(val, offset * 8);
					let pval = checked_unwrap_option!(self.ireduce(ty, pval));
					match ty {
						types::I8 => {
							// let (a0, b0, a1, b1) = generate_random_maps_bv8();
							let (a0, b0, a1, b1) = generate_random_maps!(i8);
							self.iadd_imm(
								self.blur_imul_imm(self.blur_iadd_imm(self.blur_imul_imm(pval, a0), b0), a1),
								b1,
							)
						}

						types::I16 => {
							let (a0, b0, a1, b1) = generate_random_maps!(i16);
							self.iadd_imm(
								self.blur_imul_imm(self.blur_iadd_imm(self.blur_imul_imm(pval, a0), b0), a1),
								b1,
							)
						}

						types::I32 => {
							let (a0, b0, a1, b1) = generate_random_maps!(i32);
							self.iadd_imm(
								self.blur_imul_imm(self.blur_iadd_imm(self.blur_imul_imm(pval, a0), b0), a1),
								b1,
							)
						}

						_ => pval,
					}
				};
				self.stack_store(pval, ss, offset);

				offset += ty.bytes() as i32;
			}

			ss
		};

		self.stack_load(val_ty, ss, 0)
	}

	fn blur_def_var(&'_ self, var: Variable, val: Value) {
		let val = self.blur_value(val);
		self.def_var(var, val)
	}

	fn blur_use_var(&'_ self, var: Variable) -> Value {
		let val = self.use_var(var);
		self.blur_value(val)
	}

	fn translate_declaration(
		&mut self, Declaration { specifier, declarator }: &'_ Declaration<'tcx>,
	) {
		use SimpleConcreteType::*;
		use SimpleType::*;
		use SimpleTypedIdentifier::*;
		use TypeSpecifier::*;

		match specifier {
			CharTy | ShortTy | IntTy | LongTy | VoidTy => {
				let Declarator { ident: Identifier(var_name), derived, initializer } =
					checked_unwrap_option!(declarator.as_ref());

				let new_var;
				let new_var_ty;
				if let Some(derived_decl) = derived {
					match derived_decl {
						DerivedDeclarator::Pointer => {
							new_var = declare_variable(
								self.func_builder.get_mut(),
								self.pointer_ty,
								None,
							);
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
							new_var =
								declare_variable(self.func_builder.get_mut(), new_var_ty, None);

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
					let stack_slot = self.create_stack_slot(struct_ty.bytes());
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
					let struct_simple_ty = checked_unwrap_option!(self.type_env.get(sname));
					let struct_simple_ty = struct_simple_ty.to_owned();

					if let Some(derived_decl) = derived {
						match derived_decl {
							DerivedDeclarator::Pointer => {
								let new_var = declare_variable(
									self.func_builder.get_mut(),
									self.pointer_ty,
									None,
								);
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
						let struct_len =
							checked_if_let!(AggregateTy(struct_ty), &struct_simple_ty, {
								// StackSlotData::new(StackSlotKind::ExplicitSlot, struct_ty.bytes() as _)
								struct_ty.bytes()
							});

						let stack_slot = self.create_stack_slot(struct_len);
						self.name_env.insert(
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

	fn translate_do_while_statement(
		&'_ mut self, DoWhileStatement { statement, condition }: &'_ DoWhileStatement<'tcx>,
	) {
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

	fn translate_while_statement(
		&'_ mut self, WhileStatement { condition, statement }: &'_ WhileStatement<'tcx>,
	) {
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

	fn translate_compound_statements(&'_ mut self, stmts: &'_ [Statement<'tcx>]) {
		let original_name_env = self.name_env.clone();
		let original_type_env = self.type_env.clone();

		for stmt in stmts {
			self.translate_statement(stmt);
		}
		self.name_env = original_name_env;
		self.type_env = original_type_env;
	}

	fn translate_for_statement(
		&'_ mut self,
		ForStatement { initializer, condition, step, statement }: &'_ ForStatement<'tcx>,
	) {
		use SimpleConcreteType::*;

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

	fn translate_if_statement(
		&'_ mut self,
		IfStatement { condition, then_statement, else_statement }: &'_ IfStatement<'tcx>,
	) {
		use SimpleConcreteType::*;

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

	fn translate_statement(&'_ mut self, stmt: &'_ Statement<'tcx>) {
		use SimpleConcreteType::*;
		use Statement::*;

		match stmt {
			DoWhileStmt(stmt) => self.translate_do_while_statement(stmt),

			WhileStmt(stmt) => self.translate_while_statement(stmt),

			ForStmt(stmt) => self.translate_for_statement(stmt),

			IfStmt(stmt) => self.translate_if_statement(stmt),

			ReturnStmt(expr) => {
				if let Some(expr) = expr {
					let val = self.translate_expression(expr);
					let return_ty = checked_unwrap_option!(self.return_ty);
					let val = match val {
						ConstantTy(c) => self.iconst(return_ty, c),
						ValueTy(v) => v,
						StackSlotTy(ss) => self.stack_load(return_ty, ss, 0),
						_ => unsafe { unreachable_unchecked() },
					};

					self.insert_return(&val);
				}
			}

			CompoundStmt(stmts) => self.translate_compound_statements(stmts.as_slice()),

			ExpressionStmt(expr) => {
				if let Some(expr) = expr {
					// C11 Standard: 6.8.3 Expression and null statements
					// A statement expression is an expression but its type is void, i.e. it is evaluated for side-effect
					// E.g. x = 5 is a binary expression where the operator is assignment
					self.translate_expression(expr);
				}
			}

			DeclarationStmt(decl) => self.translate_declaration(decl),
		}
	}

	fn translate_unary_operator_expression(
		&'_ mut self,
		UnaryOperatorExpression { operator, operand }: &'_ UnaryOperatorExpression<'tcx>,
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
				let ident_var = checked_unwrap_option!(self.name_env.get(var_name));
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
				let ident_var = checked_unwrap_option!(self.name_env.get(var_name));
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
					let typed_ident = checked_unwrap_option!(self.name_env.get(var_name));
					match typed_ident {
						AggregateIdent(AggregateIdentifier { ident, .. }) => {
							ValueTy(self.stack_addr(*ident, 0))
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
							let typed_ident =
								checked_unwrap_option!(self.name_env.get(struct_name));
							match typed_ident {
								// e.g. s.i
								AggregateIdent(AggregateIdentifier {
									ident,
									ty: AggregateTy(aggre_ty),
								}) => checked_match!(operator, Direct, {
									let offset =
										checked_unwrap_option!(aggre_ty.field_offset(field_name));
									ValueTy(self.stack_addr(*ident, offset as i32))
								}),

								// e.g. ps->i
								PointerIdent(PointerIdentifer { ident, ty }) => {
									checked_match!(operator, Indirect, {
										checked_match!(ty, AggregateTy(aggre_ty), {
											let ident_addr = self.use_var(*ident);
											let offset = checked_unwrap_option!(
												aggre_ty.field_offset(field_name)
											);
											ValueTy(self.iadd_imm(ident_addr, offset as i64))
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
			},
		}
	}

	fn translate_binary_operator_expression(
		&'_ mut self,
		BinaryOperatorExpression { operator, lhs, rhs }: &'_ BinaryOperatorExpression<'tcx>,
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

				Assignment
				| AdditionAssignment
				| SubtractionAssignment
				| MultiplicationAssignment
				| DivisionAssignment => unsafe { unreachable_unchecked() },
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
				LessOrEqual => {
					ValueTy(Self::icmp_imm(self, IntCC::SignedGreaterThanOrEqual, rhs, lhs))
				}
				Greater => ValueTy(Self::icmp_imm(self, IntCC::SignedLessThan, rhs, lhs)),
				GreaterOrEqual => {
					ValueTy(Self::icmp_imm(self, IntCC::SignedLessThanOrEqual, rhs, lhs))
				}
				Equal => ValueTy(Self::icmp_imm(self, IntCC::Equal, rhs, lhs)),

				Assignment
				| AdditionAssignment
				| SubtractionAssignment
				| MultiplicationAssignment
				| DivisionAssignment => unsafe { unreachable_unchecked() },
			},

			(ValueTy(lhs_val), ConstantTy(rhs_val)) => {
				match operator {
					Multiplication => ValueTy(self.imul_imm(lhs_val, rhs_val)),
					Division => ValueTy(self.idiv_imm(lhs_val, rhs_val)),
					Addition => ValueTy(self.iadd_imm(lhs_val, rhs_val)),
					Subtraction => {
						let lhs_ty = self.value_type(lhs_val);
						let rhs = self.iconst(lhs_ty, rhs_val);
						ValueTy(self.isub(lhs_val, rhs))
					}

					Less => ValueTy(self.icmp_imm(IntCC::SignedLessThan, lhs_val, rhs_val)),
					LessOrEqual => {
						ValueTy(self.icmp_imm(IntCC::SignedLessThanOrEqual, lhs_val, rhs_val))
					}
					Greater => ValueTy(self.icmp_imm(IntCC::SignedGreaterThan, lhs_val, rhs_val)),
					GreaterOrEqual => {
						ValueTy(self.icmp_imm(IntCC::SignedGreaterThanOrEqual, lhs_val, rhs_val))
					}
					Equal => ValueTy(self.icmp_imm(IntCC::Equal, lhs_val, rhs_val)),

					Assignment
					| AdditionAssignment
					| SubtractionAssignment
					| MultiplicationAssignment
					| DivisionAssignment => {
						match lhs.as_ref() {
							IdentifierExpr(Identifier(var_name)) => {
								let lhs_var = checked_unwrap_option!(self.name_env.get(var_name));
								checked_if_let!(
									PrimitiveIdent(PrimitiveIdentifier { ident, .. }),
									lhs_var,
									{
										let lhs_ty = Self::value_type(self, lhs_val);
										let new_lhs_val = match operator {
											Assignment => Self::iconst(self, lhs_ty, rhs_val),
											AdditionAssignment => {
												Self::iadd_imm(self, lhs_val, rhs_val)
											}
											SubtractionAssignment => {
												let rhs_val = Self::iconst(self, lhs_ty, rhs_val);
												Self::isub(self, lhs_val, rhs_val)
											}
											MultiplicationAssignment => {
												Self::imul_imm(self, lhs_val, rhs_val)
											}
											DivisionAssignment => {
												Self::idiv_imm(self, lhs_val, rhs_val)
											}
											_ => unsafe { unreachable_unchecked() },
										};
										Self::def_var(self, *ident, new_lhs_val);
									}
								);
							}

							MemberExpr(MemberExpression {
								expression,
								identifier: Identifier(field_name),
								operator,
							}) => {
								checked_match!(
									expression.as_ref(),
									IdentifierExpr(Identifier(var_name)),
									{
										let typed_ident =
											checked_unwrap_option!(self.name_env.get(var_name));
										match typed_ident {
											// e.g. s.x
											AggregateIdent(AggregateIdentifier {
												ident,
												ty: AggregateTy(aggre_ty),
											}) => {
												checked_match!(operator, Direct, {
													let field_offset = checked_unwrap_option!(
														aggre_ty.field_offset(field_name)
													);
													let field_ty = checked_unwrap_option!(
														aggre_ty.field_type(field_name)
													);
													let rhs_val = self.iconst(field_ty, rhs_val);
													self.stack_store(
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
														checked_match!(
															pty.as_ref(),
															AggregateTy(aggre_ty),
															{
																let field_offset = checked_unwrap_option!(
																	aggre_ty
																		.field_offset(field_name)
																);
																let field_ty = checked_unwrap_option!(
																	aggre_ty.field_type(field_name)
																);
																let ident_val =
																	self.use_var(*ident);
																let rhs_val =
																	self.iconst(field_ty, rhs_val);
																self.store(
																	rhs_val,
																	ident_val,
																	field_offset as i32,
																);
															}
														)
													});
												});
											}

											_ => unsafe { unreachable_unchecked() },
										}
									}
								);
							}

							_ => unsafe { unreachable_unchecked() },
						}

						UnitTy
					}
				}
			}

			(ValueTy(lhs_val), ValueTy(rhs_val)) => {
				let lhs_val = self.blur_value(lhs_val);
				let rhs_val = self.blur_value(rhs_val);
				match operator {
					Multiplication => ValueTy(self.iadd(lhs_val, rhs_val)),
					Division => ValueTy(self.idiv(lhs_val, rhs_val)),
					Addition => ValueTy(self.iadd(lhs_val, rhs_val)),
					Subtraction => ValueTy(self.isub(lhs_val, rhs_val)),

					Less => ValueTy(self.icmp(IntCC::SignedLessThan, lhs_val, rhs_val)),
					LessOrEqual => {
						ValueTy(self.icmp(IntCC::SignedLessThanOrEqual, lhs_val, rhs_val))
					}
					Greater => ValueTy(self.icmp(IntCC::SignedGreaterThan, lhs_val, rhs_val)),
					GreaterOrEqual => {
						ValueTy(self.icmp(IntCC::SignedGreaterThanOrEqual, lhs_val, rhs_val))
					}
					Equal => ValueTy(self.icmp(IntCC::Equal, lhs_val, rhs_val)),

					Assignment
					| AdditionAssignment
					| SubtractionAssignment
					| MultiplicationAssignment
					| DivisionAssignment => {
						match lhs.as_ref() {
							IdentifierExpr(Identifier(var_name)) => {
								let lhs_var = checked_unwrap_option!(self.name_env.get(var_name));
								checked_if_let!(
									PrimitiveIdent(PrimitiveIdentifier { ident, .. }),
									lhs_var,
									{
										let new_lhs_val = match operator {
											Assignment => rhs_val,
											AdditionAssignment => self.iadd(lhs_val, rhs_val),
											SubtractionAssignment => self.isub(lhs_val, rhs_val),
											MultiplicationAssignment => self.imul(lhs_val, rhs_val),
											DivisionAssignment => self.idiv(lhs_val, rhs_val),
											_ => unsafe { unreachable_unchecked() },
										};
										// self.def_var(*ident, new_lhs_val);
										self.blur_def_var(*ident, new_lhs_val);
									}
								);
							}

							MemberExpr(MemberExpression {
								expression,
								identifier: Identifier(field_name),
								operator,
							}) => {
								checked_match!(
									expression.as_ref(),
									IdentifierExpr(Identifier(var_name)),
									{
										let typed_ident =
											checked_unwrap_option!(self.name_env.get(var_name));
										match typed_ident {
											// e.g. s.x
											AggregateIdent(AggregateIdentifier {
												ident,
												ty: AggregateTy(aggre_ty),
											}) => {
												checked_match!(operator, Direct, {
													let field_offset = checked_unwrap_option!(
														aggre_ty.field_offset(field_name)
													);
													// let field_ty = checked_unwrap!(aggre_ty.field_type(field_name));
													// let rhs_val = self.iconst(self, field_ty, rhs_val);
													self.stack_store(
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
														checked_match!(
															pty.as_ref(),
															AggregateTy(aggre_ty),
															{
																let field_offset = checked_unwrap_option!(
																	aggre_ty
																		.field_offset(field_name)
																);
																// let field_ty = checked_unwrap!(aggre_ty.field_type(field_name));
																let ident_val =
																	self.use_var(*ident);
																// let rhs_val = Self::iconst(self, field_ty, rhs_val);
																self.store(
																	rhs_val,
																	ident_val,
																	field_offset as i32,
																);
															}
														)
													});
												});
											}

											_ => unsafe { unreachable_unchecked() },
										}
									}
								);
							}

							_ => unsafe { unreachable_unchecked() },
						}

						UnitTy
					}
				}
			}

			(StackSlotTy(_lhs_ss), StackSlotTy(_rhs_ss)) => match operator {
				Assignment => {
					// zone for blurring
					todo!()
				}

				_ => unsafe { unreachable_unchecked() },
			},

			_ => unsafe { unreachable_unchecked() },
		}
	}

	fn translate_member_expression(
		&'_ self,
		MemberExpression { expression, identifier: Identifier(field_name), operator }: &'_ MemberExpression<'tcx>,
	) -> SimpleConcreteType {
		use Expression::*;
		use MemberOperator::*;
		use SimpleConcreteType::*;
		use SimpleType::*;
		use SimpleTypedIdentifier::*;

		if let IdentifierExpr(Identifier(var_name)) = expression.as_ref() {
			let typed_ident = checked_unwrap_option!(self.name_env.get(var_name));
			match typed_ident {
				// e.g. s.i
				AggregateIdent(AggregateIdentifier { ident, ty: AggregateTy(aggre_ty) }) => {
					checked_match!(operator, Direct, {
						let offset = checked_unwrap_option!(aggre_ty.field_offset(field_name));
						let (_, ty) = checked_unwrap_option!(aggre_ty
							.fields
							.iter()
							.find(|(fname, _)| fname == field_name));
						ValueTy(Self::stack_load(self, *ty, *ident, offset as i32))
					})
				}

				// e.g. ps->i
				PointerIdent(PointerIdentifer { ident, ty }) => {
					checked_match!(operator, Indirect, {
						checked_match!(ty, PointerTy(pty), {
							checked_match!(pty.as_ref(), AggregateTy(aggre_ty), {
								// Simplification: assume no struct alignment
								// C11 Standard 6.7.2.1 Structure and union specifiers
								let offset =
									checked_unwrap_option!(aggre_ty.field_offset(field_name));

								let (_, ty) = checked_unwrap_option!(aggre_ty
									.fields
									.iter()
									.find(|(fname, _)| fname == field_name));

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
		&'_ mut self,
		CallExpression { callee: Identifier(func_name), arguments }: &'_ CallExpression<'tcx>,
	) -> SimpleConcreteType {
		use SimpleConcreteType::*;
		use SimpleTypedIdentifier::*;

		// let func_name: &str = callee.into();
		let func = checked_unwrap_option!(self.name_env.get(func_name)).clone();
		match func {
			FunctionIdent(FunctionIdentifier {
				ty: SimpleType::FunctionTy(FunctionType { return_ty, param_ty }),
				..
			}) => {
				let mut sig = self.module.make_signature();
				if let Some(return_ty) = return_ty {
					sig.returns.push(AbiParam::new(return_ty)); // return type
				}
				for pty in param_ty.iter() {
					sig.params.push(AbiParam::new(*pty)); // parameter types
				}

				let callee = checked_unwrap_result!(self.module.declare_function(
					func_name,
					Linkage::Import,
					&sig
				));
				let local_callee =
					self.module.declare_func_in_func(callee, self.func_builder.get_mut().func);

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

				// let call = self.func_builder.borrow_mut().ins().call(local_callee, &arg_values);
				let call = self.insert_call(local_callee, &arg_values);

				if return_ty.is_some() {
					// ValueTy(self.func_builder.borrow_mut().inst_results(call)[0])
					ValueTy(self.inst_result(call))
				} else {
					UnitTy
				}
			}

			_ => unimpl!("unsupported call identifier"),
		}
	}

	fn translate_identifier_expression(
		&'_ self, Identifier(var_name): &'_ Identifier<'tcx>,
	) -> SimpleConcreteType {
		let var = checked_unwrap_option!(self.name_env.get(var_name));
		checked_match!(
			var,
			SimpleTypedIdentifier::PrimitiveIdent(PrimitiveIdentifier { ident, .. }),
			{
				// SimpleConcreteType::ValueTy(self.use_var(*ident))
				SimpleConcreteType::ValueTy(self.blur_use_var(*ident))
			}
		)
	}

	fn translate_expression(&'_ mut self, expr: &'_ Expression<'tcx>) -> SimpleConcreteType {
		use Expression::*;

		if let Some(val) = evaluate_constant_arithmetic_expression(expr) {
			SimpleConcreteType::ConstantTy(val)
		} else {
			match expr {
				CallExpr(expr) => self.translate_call_expression(expr),

				MemberExpr(expr) => self.translate_member_expression(expr),

				IdentifierExpr(ident) => self.translate_identifier_expression(ident),

				UnaryOperatorExpr(expr) => self.translate_unary_operator_expression(expr),

				BinaryOperatorExpr(expr) => self.translate_binary_operator_expression(expr),

				ConstantExpr(_) => unsafe { unreachable_unchecked() },
			}
		}
	}

	fn cast_value(&'_ self, ty: Type, val: Value) -> Value {
		let val_size = self.value_type(val).bytes();
		let ty_size = ty.bytes();
		if val_size > ty_size {
			self.func_builder.borrow_mut().ins().ireduce(ty, val)
		} else if val_size < ty_size {
			self.func_builder.borrow_mut().ins().sextend(ty, val)
		} else {
			val
		}
	}

	fn uextend(&'_ self, ty: Type, val: Value) -> Option<Value> {
		let val_size = self.value_type(val).bytes();
		let ty_size = ty.bytes();
		if ty_size > val_size {
			Some(self.func_builder.borrow_mut().ins().uextend(ty, val))
		} else if ty_size == val_size {
			Some(val)
		} else {
			None
		}
	}

	fn ireduce(&'_ self, ty: Type, val: Value) -> Option<Value> {
		let val_size = self.value_type(val).bytes();
		let ty_size = ty.bytes();
		if ty_size < val_size {
			Some(self.func_builder.borrow_mut().ins().ireduce(ty, val))
		} else if ty_size == val_size {
			Some(val)
		} else {
			None
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

	fn create_stack_slot(&'_ self, len: usize) -> StackSlot {
		let ss_data = StackSlotData::new(StackSlotKind::ExplicitSlot, len as _);
		self.func_builder.borrow_mut().create_stack_slot(ss_data)
	}

	fn stack_addr(&'_ self, ss: StackSlot, offset: impl Into<i32>) -> Value {
		self.func_builder.borrow_mut().ins().stack_addr(self.pointer_ty, ss, offset.into())
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

	fn iadd(&'_ self, x: Value, y: Value) -> Value {
		self.func_builder.borrow_mut().ins().iadd(x, y)
	}

	fn blur_iadd(&'_ self, x: Value, y: Value) -> Option<Value> {
		let ty_x = self.value_type(x);
		let ty_y = self.value_type(y);
		if ty_x != ty_y {
			None
		} else {
			Some(self.iadd(self.bor(x, y), self.band(x, y)))
		}
	}

	fn iadd_imm(&'_ self, x: Value, n: impl Into<i64>) -> Value {
		self.func_builder.borrow_mut().ins().iadd_imm(x, n.into())
	}

	fn blur_iadd_imm(&'_ self, x: Value, y: impl Into<i64> + Copy) -> Value {
		self.iadd(self.bor_imm(x, y), self.band_imm(x, y))
	}

	fn isub(&'_ self, x: Value, y: Value) -> Value {
		self.func_builder.borrow_mut().ins().isub(x, y)
	}

	fn idiv(&'_ self, x: Value, y: Value) -> Value {
		self.func_builder.borrow_mut().ins().sdiv(x, y)
	}

	fn idiv_imm(&'_ self, x: Value, n: impl Into<i64>) -> Value {
		self.func_builder.borrow_mut().ins().sdiv_imm(x, n.into())
	}

	fn imul(&'_ self, x: Value, y: Value) -> Value {
		self.func_builder.borrow_mut().ins().imul(x, y)
	}

	fn blur_imul(&'_ self, x: Value, y: Value) -> Value {
		let lhs = self.imul(self.bor(x, y), self.band(x, y));
		let rhs = self.imul(self.band_not(x, y), self.band_not(y, x));
		self.iadd(lhs, rhs)
	}

	fn imul_imm(&'_ self, x: Value, n: impl Into<i64>) -> Value {
		self.func_builder.borrow_mut().ins().imul_imm(x, n.into())
	}

	fn blur_imul_imm(&'_ self, x: Value, y: impl Into<i64> + Copy) -> Value {
		let lhs = self.imul(self.bor_imm(x, y), self.band_imm(x, y));
		let y = self.iconst(self.value_type(x), y);
		let rhs = self.imul(self.band_not(x, y), self.band_not(y, x));
		self.iadd(lhs, rhs)
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

	fn inst_result(&'_ self, inst: Inst) -> Value {
		self.func_builder.borrow().inst_results(inst)[0]
	}

	fn logical_shr_imm(&'_ self, x: Value, y: impl Into<i64>) -> Value {
		self.func_builder.borrow_mut().ins().ushr_imm(x, y.into())
	}

	fn band(&'_ self, x: Value, y: Value) -> Value {
		self.func_builder.borrow_mut().ins().band(x, y)
	}

	fn bor(&'_ self, x: Value, y: Value) -> Value {
		self.func_builder.borrow_mut().ins().bor(x, y)
	}

	fn bxor(&'_ self, x: Value, y: Value) -> Value {
		self.func_builder.borrow_mut().ins().bxor(x, y)
	}

	fn bnot(&'_ self, x: Value) -> Value {
		self.func_builder.borrow_mut().ins().bnot(x)
	}

	fn band_not(&'_ self, x: Value, y: Value) -> Value {
		self.func_builder.borrow_mut().ins().band_not(x, y)
	}

	fn bor_not(&'_ self, x: Value, y: Value) -> Value {
		self.func_builder.borrow_mut().ins().bor_not(x, y)
	}

	fn bxor_not(&'_ self, x: Value, y: Value) -> Value {
		self.func_builder.borrow_mut().ins().bxor_not(x, y)
	}

	fn band_imm(&'_ self, x: Value, y: impl Into<i64>) -> Value {
		self.func_builder.borrow_mut().ins().band_imm(x, y.into())
	}

	fn bor_imm(&'_ self, x: Value, y: impl Into<i64>) -> Value {
		self.func_builder.borrow_mut().ins().bor_imm(x, y.into())
	}

	fn bxor_imm(&'_ self, x: Value, y: impl Into<i64>) -> Value {
		self.func_builder.borrow_mut().ins().bxor_imm(x, y.into())
	}

	fn insert_brz(&'_ self, cond: Value, ebb: Ebb) -> Inst {
		self.func_builder.borrow_mut().ins().brz(cond, ebb, &[])
	}

	fn insert_br_icmp(&'_ self, cond: impl Into<IntCC>, x: Value, y: Value, ebb: Ebb) -> Inst {
		self.func_builder.borrow_mut().ins().br_icmp(cond, x, y, ebb, &[])
	}

	fn insert_jmp(&'_ self, ebb: Ebb) -> Inst {
		self.func_builder.borrow_mut().ins().jump(ebb, &[])
	}

	fn insert_call(&'_ self, fref: FuncRef, args: &[Value]) -> Inst {
		self.func_builder.borrow_mut().ins().call(fref, args)
	}

	fn insert_indirect_call(&'_ self, sigref: SigRef, callee: Value, args: &[Value]) -> Inst {
		self.func_builder.borrow_mut().ins().call_indirect(sigref, callee, args)
	}

	fn insert_return(&'_ self, val: &'_ Value) {
		self.func_builder.borrow_mut().ins().return_(&[val.to_owned()]);
	}

	fn import_signature(&'_ self, fsig: &'_ Signature) -> SigRef {
		if self.imported_sigs.borrow().contains_key(fsig) {
			checked_unwrap_option!(self.imported_sigs.borrow().get(fsig)).to_owned()
		} else {
			let fsigref = self.func_builder.borrow_mut().import_signature(fsig.to_owned());
			self.imported_sigs.borrow_mut().insert(fsig.to_owned(), fsigref);
			fsigref
		}
	}

	fn func_addr(&'_ self, fref: FuncRef) -> Value {
		self.func_builder.borrow_mut().ins().func_addr(self.pointer_ty, fref)
	}
}

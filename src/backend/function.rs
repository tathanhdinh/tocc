use std::{
	cell::RefCell,
	collections::HashMap,
	hint::unreachable_unchecked,
	i16, i32, i64, i8,
	str::FromStr,
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
use cranelift_module::{Backend, FuncId, Module};
use cranelift_preopt::optimize;

use target_lexicon::triple;

use crate::{
	checked_if_let, checked_match, checked_unwrap_option, checked_unwrap_result,
	frontend::syntax::{
		BinaryOperator, BinaryOperatorExpression, CallExpression, Declaration, Declarator,
		DerivedDeclarator, DoWhileStatement, Expression, ForStatement, FunctionDeclarator,
		FunctionDefinition, Identifier, IfStatement, MemberExpression, MemberOperator, Statement,
		StructType, TypeSpecifier, UnaryOperator, UnaryOperatorExpression, WhileStatement,
	},
	generate_combinations, generate_inverted_polynomial, generate_linear_maps,
	generate_master_coefficients, generate_polynomial_maps, generate_random_invertible_polynomial,
	heavy, inverse, light, semantically_unreachable, unimpl, verbose,
};

use super::support::{
	evaluate_constant_arithmetic_expression, generate_random_partition, AggregateIdentifier,
	AggregateType, ConcreteValue, EffectiveType, FunctionIdentifier, FunctionType,
	NameBindingEnvironment, PointerIdentifer, PrimitiveIdentifier, SimpleTypedConcreteValue,
	SimpleTypedIdentifier, TypeBindingEnvironment,
};

static NEW_VAR_ID: AtomicUsize = AtomicUsize::new(0);

struct FunctionTranslator<'clif: 'tcx, 'tcx, B: Backend> {
	pub func_builder: RefCell<FunctionBuilder<'clif>>,
	module: &'clif mut Module<B>,
	imported_sigs: RefCell<HashMap<Signature, SigRef>>,
	name_env: NameBindingEnvironment<'tcx>,
	type_env: TypeBindingEnvironment<'tcx>,
	pointer_ty: Type,
	return_ty: Option<Type>,
}

pub fn get_function_signature(
	func_def: &'_ FunctionDefinition<'_>, pointer_ty: Type,
) -> (Option<Type>, Vec<Type>) {
	use TypeSpecifier::*;

	let FunctionDefinition { specifier, declarator: FunctionDeclarator { parameters, .. }, .. } =
		func_def;

	let return_ty = match specifier {
		CharTy | ShortTy | IntTy | LongTy => Some(specifier.into()),
		StructTy(_) => todo!(),
		VoidTy => None,
	};

	let param_ty: Vec<_> = parameters
		.iter()
		.map(|Declaration { specifier, declarator }| {
			let Declarator { derived, .. } = checked_unwrap_option!(declarator.as_ref());
			if let Some(derived_decl) = derived {
				match derived_decl {
					// some pointer types
					DerivedDeclarator::Pointer => pointer_ty,
				}
			} else {
				// non pointer types
				match specifier {
					CharTy | ShortTy | IntTy | LongTy => specifier.into(),
					StructTy(_) => todo!(),
					VoidTy => semantically_unreachable!(),
				}
			}
		})
		.collect();

	(return_ty, param_ty)
}

pub fn blur_function_signature(
	return_ty: Option<Type>, param_ty: &'_ [Type], pointer_ty: Type, ctxt: &'_ mut Context,
) {
	if return_ty.is_some() {
		ctxt.func.signature.returns.push(AbiParam::new(pointer_ty));
	}
	for _ in param_ty {
		ctxt.func.signature.params.push(AbiParam::new(pointer_ty));
	}
}

fn blur_bor(fb: &'_ mut FunctionBuilder, x: Value, y: Value) -> Value {
	let x_add_y = fb.ins().iadd(x, y);
	let x_and_y = fb.ins().band(x, y);
	fb.ins().isub(x_add_y, x_and_y)
}

fn blur_value(fb: &'_ mut FunctionBuilder, val: Value) -> Value {
	if light() {
		return val;
	}

	let val_ty = fb.func.dfg.value_type(val);
	let val_size = val_ty.bytes();

	let random_type_partition = generate_random_partition(val_size);
	let mut offset = 0i64;

	let mut acc_val = fb.ins().iconst(val_ty, 0);
	for ty in random_type_partition {
		let pv = fb.ins().ushr_imm(val, offset);
		let pv = fb.ins().ireduce(ty, pv);
		let pv = match ty {
			types::I8 => {
				let olevel = heavy();
				if olevel == 0 {
					let (a0, b0, a1, b1) = generate_linear_maps!(i8);
					let pv = fb.ins().imul_imm(pv, a0 as i64);
					let pv = fb.ins().iadd_imm(pv, b0 as i64);
					let pv = fb.ins().imul_imm(pv, a1 as i64);
					let pv = fb.ins().iadd_imm(pv, b1 as i64);
					pv
				} else {
					let (coeffs, inv_coeffs) = generate_polynomial_maps!(i8, olevel);
					for i in 0..=olevel {
						let mut x_pow_i = pv;
						for j in 0..i {
							x_pow_i = fb.ins().imul(x_pow_i, pv)
						}
						x_pow_i = fb.ins().imul_imm(x_pow_i, coeffs[i as usize] as i64);
					}
					todo!()
				}
			}

			types::I16 => {
				let (a0, b0, a1, b1) = generate_linear_maps!(i16);
				let pv = fb.ins().imul_imm(pv, a0 as i64);
				let pv = fb.ins().iadd_imm(pv, b0 as i64);
				let pv = fb.ins().imul_imm(pv, a1 as i64);
				let pv = fb.ins().iadd_imm(pv, b1 as i64);
				pv
			}

			types::I32 => {
				let (a0, b0, a1, b1) = generate_linear_maps!(i32);
				let pv = fb.ins().imul_imm(pv, a0 as i64);
				let pv = fb.ins().iadd_imm(pv, b0 as i64);
				let pv = fb.ins().imul_imm(pv, a1 as i64);
				let pv = fb.ins().iadd_imm(pv, b1 as i64);
				pv
			}

			_ => pv,
		};

		let pv = fb.ins().uextend(val_ty, pv);
		let pv = fb.ins().ishl_imm(pv, offset);
		acc_val = blur_bor(fb, acc_val, pv);

		offset += ty.bits() as i64
	}

	acc_val
}

fn create_entry_block(fb: &'_ mut FunctionBuilder, param_ty: &[Type], pointer_ty: Type) -> Block {
	let trampoline_ebb = fb.create_block();
	fb.append_block_params_for_function_params(trampoline_ebb);

	fb.switch_to_block(trampoline_ebb);
	let mut param_vals = Vec::new();
	for (i, ty) in param_ty.iter().enumerate() {
		let val = {
			let val = fb.block_params(trampoline_ebb)[i];
			let val = blur_value(fb, val);

			if ty.bytes() < pointer_ty.bytes() {
				let ss = fb.create_stack_slot(StackSlotData::new(
					StackSlotKind::ExplicitSlot,
					pointer_ty.bytes(),
				));
				fb.ins().stack_store(val, ss, 0);

				let ss_addr = fb.ins().stack_addr(pointer_ty, ss, 0);
				let ss_addr = blur_value(fb, ss_addr);
				fb.ins().load(*ty, MemFlags::new(), ss_addr, 0)
			} else {
				val
			}
		};
		param_vals.push(val);
	}

	let entry_ebb = fb.create_block();
	for ty in param_ty {
		fb.append_block_param(entry_ebb, *ty);
	}
	fb.ins().jump(entry_ebb, &param_vals);
	fb.seal_block(trampoline_ebb);

	fb.switch_to_block(entry_ebb);
	fb.seal_block(entry_ebb);
	entry_ebb
}

fn declare_parameter_variables<'tcx>(
	func_def: &'_ FunctionDefinition<'tcx>, fb: &'_ mut FunctionBuilder, entry_ebb: Block,
	pointer_ty: Type, name_env: &'_ mut NameBindingEnvironment<'tcx>,
	type_env: &'_ TypeBindingEnvironment<'tcx>,
) {
	use EffectiveType::*;
	use TypeSpecifier::*;

	let FunctionDefinition { declarator: FunctionDeclarator { parameters, .. }, .. } = func_def;

	for (i, Declaration { declarator, specifier }) in parameters.iter().enumerate() {
		let Declarator { ident: Identifier(var_name), derived, .. } =
			checked_unwrap_option!(declarator.as_ref());
		let param_val = fb.block_params(entry_ebb)[i];

		match specifier {
			VoidTy => todo!(),

			CharTy | ShortTy | IntTy | LongTy => {
				if let Some(derived_decl) = derived {
					match derived_decl {
						DerivedDeclarator::Pointer => {
							let new_var = declare_variable(fb, pointer_ty, Some(param_val));

							name_env.bind(
								var_name,
								SimpleTypedIdentifier::PointerIdent(PointerIdentifer {
									ident: new_var,
									ty: PointerTy(Box::new(PrimitiveTy(specifier.into()))),
								}),
							);
						}
					}
				} else {
					let new_var = declare_variable(fb, specifier.into(), Some(param_val));

					name_env.bind(
						var_name,
						SimpleTypedIdentifier::PrimitiveIdent(PrimitiveIdentifier {
							ident: new_var,
							ty: EffectiveType::PrimitiveTy(specifier.into()),
						}),
					);
				}
			}

			StructTy(StructType { identifier: Identifier(sname), .. }) => {
				if let Some(derived_decl) = derived {
					match derived_decl {
						DerivedDeclarator::Pointer => {
							let new_var = declare_variable(fb, pointer_ty, Some(param_val));

							let aggre_ty = checked_unwrap_option!(type_env.get(sname));

							name_env.bind(
								var_name,
								SimpleTypedIdentifier::PointerIdent(PointerIdentifer {
									ident: new_var,
									ty: PointerTy(Box::new(aggre_ty.clone())),
								}),
							);
						}
					}
				} else {
					todo!()
				}
			}
		}
	}
}

fn optimize_function(ctxt: &'_ mut Context) {
	let isa = {
		let flag_builder = {
			let mut fb = settings::builder();
			checked_unwrap_result!(fb.enable("is_pic"));
			fb
		};

		let isa_bulder = checked_unwrap_result!(isa::lookup(triple!("x86_64-unknown-linux-elf")));
		isa_bulder.finish(settings::Flags::new(flag_builder))
	};
	optimize(ctxt, isa.as_ref()).unwrap();
}

pub fn translate_function<'clif, 'tcx>(
	func_def: &'tcx FunctionDefinition<'tcx>, return_ty: Option<Type>, param_ty: &'_ [Type],
	pointer_ty: Type, ctxt: &'clif mut Context, module: &'clif mut Module<impl Backend>,
	outer_name_env: &'_ NameBindingEnvironment<'tcx>,
	outer_type_env: &'_ TypeBindingEnvironment<'tcx>,
) {
	let FunctionDefinition { body, .. } = func_def;

	let mut func_builder_ctxt = FunctionBuilderContext::new();
	let mut func_builder = FunctionBuilder::new(&mut ctxt.func, &mut func_builder_ctxt);

	let mut name_env = outer_name_env.inherit();

	let entry_ebb = create_entry_block(&mut func_builder, &param_ty, pointer_ty);
	declare_parameter_variables(
		func_def,
		&mut func_builder,
		entry_ebb,
		pointer_ty,
		&mut name_env,
		outer_type_env,
	);

	let mut func_translator =
		FunctionTranslator::new(func_builder, module, return_ty, name_env, outer_type_env);
	func_translator.translate_statement(body, entry_ebb);
	func_translator.func_builder.get_mut().finalize();
}

pub fn finalize_function_translation<'clif>(
	func_id: FuncId, ctxt: &'clif mut Context, module: &'clif mut Module<impl Backend>,
) -> u32 {
	optimize_function(ctxt);
	if verbose() {
		println!("{:?}", ctxt.func);
	}
	let func_len = module.define_function(func_id, ctxt).expect("failed to define function");
	module.clear_context(ctxt);
	func_len
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
		func_builder: FunctionBuilder<'clif>, module: &'clif mut Module<B>,
		return_ty: Option<Type>, name_env: NameBindingEnvironment<'tcx>,
		outer_type_env: &'_ TypeBindingEnvironment<'tcx>,
	) -> Self {
		let func_builder = RefCell::new(func_builder);
		let pointer_ty = module.target_config().pointer_type();

		Self {
			func_builder,
			module,
			imported_sigs: RefCell::new(HashMap::new()),
			name_env,
			type_env: outer_type_env.clone(),
			pointer_ty,
			return_ty,
		}
	}

	fn split_and_merge_value(&'_ self, val: Value) -> Value {
		let val_ty = self.value_type(val);
		let val_size = val_ty.bytes();

		let random_type_partition = generate_random_partition(val_size);
		let mut offset = 0i32;
		let mut partitioned_values = Vec::new();
		for ty in random_type_partition {
			let pv = self.logical_shr_imm(val, offset);
			let pv = checked_unwrap_option!(self.ireduce(ty, pv));
			let pv = match ty {
				types::I8 => {
					let (a0, b0, a1, b1) = generate_linear_maps!(i8);
					self.blur_iadd_imm(
						self.blur_imul_imm(self.blur_iadd_imm(self.blur_imul_imm(pv, a0), b0), a1),
						b1,
					)
				}

				types::I16 => {
					let (a0, b0, a1, b1) = generate_linear_maps!(i16);
					self.blur_iadd_imm(
						self.blur_imul_imm(self.blur_iadd_imm(self.blur_imul_imm(pv, a0), b0), a1),
						b1,
					)
				}

				types::I32 => {
					let (a0, b0, a1, b1) = generate_linear_maps!(i32);
					self.blur_iadd_imm(
						self.blur_imul_imm(self.blur_iadd_imm(self.blur_imul_imm(pv, a0), b0), a1),
						b1,
					)
				}

				_ => pv,
			};

			let pv = checked_unwrap_option!(self.uextend(val_ty, pv));
			partitioned_values.push(self.shl_imm(pv, offset));

			offset += ty.bits() as i32;
		}

		partitioned_values.into_iter().fold(self.iconst(val_ty, 0), |acc, v| self.blur_bor(acc, v))
	}

	fn blur_value(&'_ self, val: Value) -> Value {
		if light() {
			return val;
		}

		let val_ty = self.value_type(val);
		let val_size = val_ty.bytes();

		let ss = self.create_stack_slot(val_size as _);
		let ss_addr = self.stack_addr(ss, 0);

		let random_type_partition = generate_random_partition(val_size);
		let mut offset = 0i32;
		for ty in random_type_partition {
			let pval = {
				let pval = self.logical_shr_imm(val, offset * 8);
				let pval = checked_unwrap_option!(self.ireduce(ty, pval));
				match ty {
					types::I8 => {
						let (a0, b0, a1, b1) = generate_linear_maps!(i8);
						self.blur_iadd_imm(
							self.blur_imul_imm(
								self.blur_iadd_imm(self.blur_imul_imm(pval, a0), b0),
								a1,
							),
							b1,
						)
					}

					types::I16 => {
						let (a0, b0, a1, b1) = generate_linear_maps!(i16);
						self.blur_iadd_imm(
							self.blur_imul_imm(
								self.blur_iadd_imm(self.blur_imul_imm(pval, a0), b0),
								a1,
							),
							b1,
						)
					}

					types::I32 => {
						let (a0, b0, a1, b1) = generate_linear_maps!(i32);
						self.blur_iadd_imm(
							self.blur_imul_imm(
								self.blur_iadd_imm(self.blur_imul_imm(pval, a0), b0),
								a1,
							),
							b1,
						)
					}

					_ => pval,
				}
			};
			self.store(pval, self.split_and_merge_value(ss_addr), offset);

			offset += ty.bytes() as i32;
		}

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
		&'_ mut self, Declaration { specifier, declarator }: &'_ Declaration<'tcx>,
	) {
		use ConcreteValue::*;
		use EffectiveType::*;
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
							self.name_env.bind(
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
						VoidTy => semantically_unreachable!(),
						_ => {
							new_var_ty = specifier.into();
							new_var =
								declare_variable(self.func_builder.get_mut(), new_var_ty, None);

							self.name_env.bind(
								var_name,
								SimpleTypedIdentifier::PrimitiveIdent(PrimitiveIdentifier {
									ident: new_var,
									ty: EffectiveType::PrimitiveTy(new_var_ty),
								}),
							);
						}
					}
				}

				if let Some(initializer) = initializer.as_ref() {
					let SimpleTypedConcreteValue { val, .. } =
						self.translate_expression(initializer);
					let init_val = match val {
						ConstantTy(val) => self.iconst(new_var_ty, val),
						ValueTy(val) => self.cast_value(new_var_ty, val),
						_ => semantically_unreachable!(),
					};
					self.def_var(new_var, init_val);
				}
			}

			StructTy(struct_ty) => {
				let StructType { identifier: Identifier(sname), declarations } = struct_ty;
				if declarations.is_some() {
					let struct_ty: AggregateType = struct_ty.into();
					self.type_env.insert(sname, EffectiveType::AggregateTy(struct_ty));
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
								self.name_env.bind(
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
								struct_ty.bytes()
							});

						let stack_slot = self.create_stack_slot(struct_len);
						self.name_env.bind(
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
		_current_ebb: Block,
	) -> Option<Block> {
		use ConcreteValue::*;

		let loop_ebb = self.new_block();
		let exit_ebb = self.new_block();

		self.insert_jmp(loop_ebb);

		self.switch_to_ebb(loop_ebb);
		self.translate_statement(statement.as_ref(), loop_ebb);
		let SimpleTypedConcreteValue { val, .. } = self.translate_expression(condition);
		let cond = match val {
			ConstantTy(c) => self.iconst(types::I64, c),
			ValueTy(v) => v,
			_ => semantically_unreachable!(),
		};
		self.insert_brz(cond, exit_ebb);
		self.insert_jmp(loop_ebb);
		self.seal_ebb(loop_ebb);

		self.switch_to_ebb(exit_ebb);
		self.seal_ebb(exit_ebb);

		Some(exit_ebb)
	}

	fn translate_while_statement(
		&'_ mut self, WhileStatement { condition, statement }: &'_ WhileStatement<'tcx>,
		_current_ebb: Block,
	) -> Option<Block> {
		use ConcreteValue::*;

		let header_ebb = self.new_block();
		let loop_ebb = self.new_block();
		let exit_ebb = self.new_block();

		self.insert_jmp(header_ebb);

		// header EBB
		self.switch_to_ebb(header_ebb);
		let SimpleTypedConcreteValue { val, .. } = self.translate_expression(condition);
		let cond = match val {
			ConstantTy(c) => self.iconst(types::I64, c),
			ValueTy(v) => v,
			_ => semantically_unreachable!(),
		};
		self.insert_brz(cond, exit_ebb);
		self.insert_jmp(loop_ebb);

		// loop EBB
		self.switch_to_ebb(loop_ebb);
		self.seal_ebb(loop_ebb);
		self.translate_statement(statement.as_ref(), loop_ebb);
		self.insert_jmp(header_ebb);

		self.seal_ebb(header_ebb);

		self.switch_to_ebb(exit_ebb);
		self.seal_ebb(exit_ebb);

		Some(exit_ebb)
	}

	fn translate_compound_statements(
		&'_ mut self, stmts: &'_ [Statement<'tcx>], current_ebb: Block,
	) -> Option<Block> {
		let original_name_env = self.name_env.clone();
		let original_type_env = self.type_env.clone();

		let local_name_env = self.name_env.inherit();
		self.name_env = local_name_env;
		let mut ebb = Some(current_ebb);
		for stmt in stmts {
			ebb = self.translate_statement(stmt, ebb.unwrap());
			if ebb.is_none() {
				break;
			}
		}
		self.name_env = original_name_env;
		self.type_env = original_type_env;

		ebb
	}

	fn translate_for_statement(
		&'_ mut self,
		ForStatement { initializer, condition, step, statement }: &'_ ForStatement<'tcx>,
		_current_ebb: Block,
	) -> Option<Block> {
		use ConcreteValue::*;

		if let Some(initializer) = initializer.as_ref() {
			self.translate_expression(initializer);
		}

		let header_ebb = self.new_block();
		let loop_ebb = self.new_block();
		let exit_ebb = self.new_block();

		self.insert_jmp(header_ebb);

		// header EBB
		self.switch_to_ebb(header_ebb);
		let SimpleTypedConcreteValue { val, .. } = self.translate_expression(condition);
		let cond = match val {
			ConstantTy(c) => self.iconst(types::I64, c),
			ValueTy(v) => v,
			_ => semantically_unreachable!(),
		};
		self.insert_brz(cond, exit_ebb);
		self.insert_jmp(loop_ebb);

		// loop EBB
		self.switch_to_ebb(loop_ebb);
		self.seal_ebb(loop_ebb);
		self.translate_statement(statement.as_ref(), loop_ebb);
		if let Some(step) = step.as_ref() {
			self.translate_expression(step);
		}
		self.insert_jmp(header_ebb);
		self.seal_ebb(header_ebb);

		self.switch_to_ebb(exit_ebb);
		self.seal_ebb(exit_ebb);

		Some(exit_ebb)
	}

	fn translate_if_statement(
		&'_ mut self,
		IfStatement { condition, then_statement, else_statement }: &'_ IfStatement<'tcx>,
		_current_ebb: Block,
	) -> Option<Block> {
		use ConcreteValue::*;

		let SimpleTypedConcreteValue { val, .. } = self.translate_expression(condition);
		let cond = match val {
			ConstantTy(c) => self.iconst(types::I64, c),
			ValueTy(v) => v,
			_ => semantically_unreachable!(),
		};

		let then_ebb = self.new_block();
		let merge_ebb = self.new_block();
		if let Some(else_stmt) = else_statement.as_ref() {
			let else_ebb = self.new_block();
			self.insert_brz(cond, else_ebb);
			self.insert_jmp(then_ebb);

			// else EBB
			self.switch_to_ebb(else_ebb);
			self.seal_ebb(else_ebb);
			if self.translate_statement(else_stmt.as_ref(), else_ebb).is_some() {
				self.insert_jmp(merge_ebb);
			}
		} else {
			self.insert_brz(cond, merge_ebb);
			self.insert_jmp(then_ebb);
		}

		// then EBB
		self.switch_to_ebb(then_ebb);
		self.seal_ebb(then_ebb);

		if self.translate_statement(then_statement.as_ref(), then_ebb).is_some() {
			self.insert_jmp(merge_ebb);
		}

		self.switch_to_ebb(merge_ebb);
		self.seal_ebb(merge_ebb);

		Some(merge_ebb)
	}

	fn translate_statement(
		&'_ mut self, stmt: &'_ Statement<'tcx>, current_ebb: Block,
	) -> Option<Block> {
		use ConcreteValue::*;
		use Statement::*;

		match stmt {
			DoWhileStmt(stmt) => self.translate_do_while_statement(stmt, current_ebb),

			WhileStmt(stmt) => self.translate_while_statement(stmt, current_ebb),

			ForStmt(stmt) => self.translate_for_statement(stmt, current_ebb),

			IfStmt(stmt) => self.translate_if_statement(stmt, current_ebb),

			ReturnStmt(expr) => {
				if let Some(expr) = expr {
					let val = {
						let SimpleTypedConcreteValue { val, .. } = self.translate_expression(expr);
						let return_ty = checked_unwrap_option!(self.return_ty);
						match val {
							ConstantTy(c) => self.iconst(return_ty, c),
							ValueTy(v) => v,
							_ => todo!(),
						}
					};
					let ret_val = checked_unwrap_option!(self.uextend(self.pointer_ty, val));
					self.insert_return(ret_val);
				}
				None
			}

			CompoundStmt(stmts) => {
				self.translate_compound_statements(stmts.as_slice(), current_ebb)
			}

			ExpressionStmt(expr) => {
				if let Some(expr) = expr {
					// C11 Standard: 6.8.3 Expression and null statements
					// A statement expression is an expression but its type is void, i.e. it is evaluated for side-effect
					// E.g. x = 5 is a binary expression where the operator is assignment
					self.translate_expression(expr);
				}
				Some(current_ebb)
			}

			DeclarationStmt(decl) => {
				self.translate_declaration(decl);
				Some(current_ebb)
			}
		}
	}

	fn translate_unary_operator_expression(
		&'_ mut self,
		UnaryOperatorExpression { operator, operand }: &'_ UnaryOperatorExpression<'tcx>,
	) -> SimpleTypedConcreteValue<'tcx> {
		use ConcreteValue::*;
		use EffectiveType::*;
		use Expression::*;
		use MemberOperator::*;
		use SimpleTypedIdentifier::*;
		use UnaryOperator::*;

		match operator {
			Negation => {
				let SimpleTypedConcreteValue { val, ty } =
					self.translate_expression(operand.as_ref());
				SimpleTypedConcreteValue {
					val: match val {
						ConstantTy(rhs) => ConstantTy(-rhs),
						ValueTy(rhs) => ValueTy(self.ineg(rhs)),
						_ => semantically_unreachable!(),
					},
					ty,
				}
			}

			// e.g. ++i
			PreIncrement => checked_if_let!(IdentifierExpr(var_name), operand.as_ref(), {
				let var_name: &str = var_name.into();
				let ident_var = self.name_env.get_unchecked(var_name);
				match ident_var {
					PrimitiveIdent(PrimitiveIdentifier { ident, ty }) => {
						let ident_val = self.use_var(*ident);
						let ident_new_val = self.iadd_imm(ident_val, 1);
						self.def_var(*ident, ident_new_val);
						SimpleTypedConcreteValue { val: ValueTy(ident_new_val), ty: ty.clone() }
					}

					PointerIdent(PointerIdentifer { ident, ty }) => {
						checked_if_let!(PointerTy(pty), ty, {
							match pty.as_ref() {
								PrimitiveTy(t) => {
									let ident_val = self.use_var(*ident);
									let ident_new_val = self.iadd_imm(ident_val, t.bytes());
									self.def_var(*ident, ident_new_val);
									SimpleTypedConcreteValue {
										val: ValueTy(ident_new_val),
										ty: ty.clone(),
									}
								}

								_ => todo!(),
							}
						})
					}

					_ => semantically_unreachable!(),
				}
			}),

			// e.g. i++
			PostIncrement => checked_if_let!(IdentifierExpr(var_name), operand.as_ref(), {
				let var_name: &str = var_name.into();
				let ident_var = self.name_env.get_unchecked(var_name);
				match ident_var {
					PrimitiveIdent(PrimitiveIdentifier { ident, ty }) => {
						let ident_val = self.use_var(*ident);
						let ident_new_val = self.iadd_imm(ident_val, 1);
						self.def_var(*ident, ident_new_val);
						SimpleTypedConcreteValue { val: ValueTy(ident_val), ty: ty.clone() }
					}

					PointerIdent(PointerIdentifer { ident, ty }) => {
						checked_if_let!(PointerTy(pty), ty, {
							match pty.as_ref() {
								PrimitiveTy(t) => {
									let ident_val = self.use_var(*ident);
									let ident_new_val = self.iadd_imm(ident_val, t.bytes());
									self.def_var(*ident, ident_new_val);
									SimpleTypedConcreteValue {
										val: ValueTy(ident_val),
										ty: ty.clone(),
									}
								}

								_ => todo!(),
							}
						})
					}

					_ => semantically_unreachable!(),
				}
			}),

			Address => match operand.as_ref() {
				IdentifierExpr(ident) => {
					let var_name: &str = ident.into();
					let typed_ident = self.name_env.get_unchecked(var_name);
					match typed_ident {
						AggregateIdent(AggregateIdentifier { ident, ty }) => {
							SimpleTypedConcreteValue {
								val: ValueTy(self.stack_addr(*ident, 0)),
								ty: ty.clone(),
							}
						}

						_ => todo!(),
					}
				}

				// calculate address of a field given struct (or pointer to struct)
				MemberExpr(MemberExpression { expression, identifier, operator }) => {
					match expression.as_ref() {
						IdentifierExpr(struct_name) => {
							let field_name: &str = identifier.into();
							let struct_name: &str = struct_name.into();
							let typed_ident = self.name_env.get_unchecked(struct_name);
							match typed_ident {
								// e.g. s.i
								AggregateIdent(AggregateIdentifier {
									ident,
									ty: AggregateTy(aggre_ty),
								}) => checked_match!(operator, Direct, {
									let offset =
										checked_unwrap_option!(aggre_ty.field_offset(field_name));
									SimpleTypedConcreteValue {
										val: ValueTy(self.stack_addr(*ident, offset as i32)),
										ty: AggregateTy(aggre_ty.clone()),
									}
								}),

								// e.g. ps->i
								PointerIdent(PointerIdentifer { ident, ty }) => {
									checked_match!(operator, Indirect, {
										checked_match!(ty, AggregateTy(aggre_ty), {
											let ident_addr = self.use_var(*ident);
											let offset = checked_unwrap_option!(
												aggre_ty.field_offset(field_name)
											);
											SimpleTypedConcreteValue {
												val: ValueTy(
													self.iadd_imm(ident_addr, offset as i64),
												),
												ty: ty.clone(),
											}
										})
									})
								}

								_ => semantically_unreachable!(),
							}
						}

						_ => todo!(),
					}
				}

				_ => semantically_unreachable!(),
			},

			Indirection => match operand.as_ref() {
				IdentifierExpr(ident) => {
					let var_name: &str = ident.into();
					let typed_ident = self.name_env.get_unchecked(var_name);
					checked_if_let!(PointerIdent(PointerIdentifer { ident, ty }), typed_ident, {
						let ident_val = self.use_var(*ident);
						checked_if_let!(PointerTy(ty), ty, {
							match ty.as_ref() {
								PrimitiveTy(pty) => SimpleTypedConcreteValue {
									val: ValueTy(self.load(pty.clone(), ident_val, 0)),
									ty: ty.as_ref().clone(),
								},

								_ => todo!(),
							}
						})
					})
				}

				_ => todo!(),
			},
		}
	}

	fn translate_binary_operator_expression(
		&'_ mut self,
		BinaryOperatorExpression { operator, lhs, rhs }: &'_ BinaryOperatorExpression<'tcx>,
	) -> SimpleTypedConcreteValue<'tcx> {
		use BinaryOperator::*;
		use ConcreteValue::*;
		use EffectiveType::*;
		use Expression::*;
		use MemberOperator::*;
		use SimpleTypedIdentifier::*;

		let lhs_val = self.translate_expression(lhs.as_ref());
		let rhs_val = self.translate_expression(rhs.as_ref());

		match (lhs_val, rhs_val) {
			(
				SimpleTypedConcreteValue { val: ConstantTy(lhs), ty: PrimitiveTy(lhs_ty) },
				SimpleTypedConcreteValue { val: ConstantTy(rhs), ty: PrimitiveTy(rhs_ty) },
			) => {
				let val = match operator {
					Multiplication => ConstantTy(lhs * rhs),
					Division => ConstantTy(lhs / rhs),
					Remainder => ConstantTy(lhs % rhs),
					Addition => ConstantTy(lhs + rhs),
					Subtraction => ConstantTy(lhs - rhs),

					BitwiseAnd => ConstantTy(lhs & rhs),
					BitwiseXor => ConstantTy(lhs ^ rhs),
					BitwiseOr => ConstantTy(lhs | rhs),
					BitwiseLeftShift => ConstantTy(lhs << rhs),
					BitwiseRightShift => ConstantTy(lhs >> rhs),

					Less => ValueTy(self.bconst(types::B64, lhs < rhs)),
					LessOrEqual => ValueTy(self.bconst(types::B64, lhs <= rhs)),
					Greater => ValueTy(self.bconst(types::I64, lhs > rhs)),
					GreaterOrEqual => ValueTy(self.bconst(types::I64, lhs >= rhs)),
					Equal => ValueTy(self.bconst(types::I64, lhs == rhs)),
					NotEqual => ValueTy(self.bconst(types::I64, lhs != rhs)),

					Assignment
					| AdditionAssignment
					| SubtractionAssignment
					| MultiplicationAssignment
					| DivisionAssignment => semantically_unreachable!(),
				};
				let ty = PrimitiveTy(if lhs_ty.bytes() > rhs_ty.bytes() { lhs_ty } else { rhs_ty });
				SimpleTypedConcreteValue { val, ty }
			}

			(
				SimpleTypedConcreteValue { val: ConstantTy(lhs_val), .. },
				SimpleTypedConcreteValue { val: ValueTy(rhs_val), ty: rhs_ty },
			) => {
				let val = match operator {
					Multiplication => ValueTy(self.imul_imm(rhs_val, lhs_val)),

					Division => {
						let rhs_ty = self.value_type(rhs_val);
						let lhs = self.iconst(rhs_ty, lhs_val);
						ValueTy(self.idiv(lhs, rhs_val))
					}

					Remainder => {
						let rhs_ty = self.value_type(rhs_val);
						let lhs = self.iconst(rhs_ty, lhs_val);
						ValueTy(self.srem(lhs, rhs_val))
					}

					Addition => match &rhs_ty {
						PrimitiveTy(_) => ValueTy(self.iadd_imm(rhs_val, lhs_val)),

						PointerTy(pty) => match pty.as_ref() {
							PrimitiveTy(ty) => {
								ValueTy(self.iadd_imm(rhs_val, lhs_val * ty.bytes() as i64))
							}
							_ => todo!(),
						},

						_ => semantically_unreachable!(),
					},

					Subtraction => checked_if_let!(PrimitiveTy(_), &rhs_ty, {
						let ty = self.value_type(rhs_val);
						let lhs = self.iconst(ty, lhs_val);
						ValueTy(self.isub(lhs, rhs_val))
					}),

					BitwiseAnd => checked_if_let!(PrimitiveTy(_), &rhs_ty, {
						ValueTy(self.band_imm(rhs_val, lhs_val))
					}),
					BitwiseXor => checked_if_let!(PrimitiveTy(_), &rhs_ty, {
						ValueTy(self.bxor_imm(rhs_val, lhs_val))
					}),
					BitwiseOr => checked_if_let!(PrimitiveTy(_), &rhs_ty, {
						ValueTy(self.bor_imm(rhs_val, lhs_val))
					}),

					BitwiseLeftShift => {
						ValueTy(self.shl(self.iconst(types::I64, lhs_val), rhs_val))
					}
					BitwiseRightShift => {
						ValueTy(self.arithmetic_shr(self.iconst(types::I64, lhs_val), rhs_val))
					}

					Less => ValueTy(self.icmp_imm(IntCC::SignedGreaterThan, rhs_val, lhs_val)),
					LessOrEqual => {
						ValueTy(self.icmp_imm(IntCC::SignedGreaterThanOrEqual, rhs_val, lhs_val))
					}
					Greater => ValueTy(self.icmp_imm(IntCC::SignedLessThan, rhs_val, lhs_val)),
					GreaterOrEqual => {
						ValueTy(self.icmp_imm(IntCC::SignedLessThanOrEqual, rhs_val, lhs_val))
					}
					Equal => ValueTy(self.icmp_imm(IntCC::Equal, rhs_val, lhs_val)),
					NotEqual => ValueTy(self.icmp_imm(IntCC::NotEqual, rhs_val, lhs_val)),

					Assignment
					| AdditionAssignment
					| SubtractionAssignment
					| MultiplicationAssignment
					| DivisionAssignment => semantically_unreachable!(),
				};

				SimpleTypedConcreteValue { val, ty: rhs_ty }
			}

			(
				SimpleTypedConcreteValue { val: ValueTy(lhs_val), ty: lhs_ty },
				SimpleTypedConcreteValue { val: ConstantTy(rhs_val), .. },
			) => {
				let val = match operator {
					Multiplication => ValueTy(self.blur_imul_imm(lhs_val, rhs_val)),
					Division => ValueTy(self.idiv_imm(lhs_val, rhs_val)),
					Remainder => ValueTy(self.srem_imm(lhs_val, rhs_val)),

					Addition => match &lhs_ty {
						PrimitiveTy(_) => ValueTy(self.blur_iadd_imm(lhs_val, rhs_val)),

						PointerTy(pty) => match pty.as_ref() {
							PrimitiveTy(ty) => {
								ValueTy(self.blur_iadd_imm(lhs_val, rhs_val * ty.bytes() as i64))
							}

							_ => todo!(),
						},

						_ => semantically_unreachable!(),
					},

					Subtraction => {
						let ty = self.value_type(lhs_val);
						match &lhs_ty {
							PrimitiveTy(_) => {
								let rhs = self.iconst(ty, rhs_val);
								ValueTy(self.isub(lhs_val, rhs))
							}

							PointerTy(_) => {
								let rhs = self.iconst(ty, rhs_val * ty.bytes() as i64);
								ValueTy(self.isub(lhs_val, rhs))
							}

							_ => todo!(),
						}
					}

					BitwiseAnd => checked_if_let!(PrimitiveTy(_), &lhs_ty, {
						ValueTy(self.band_imm(lhs_val, rhs_val))
					}),
					BitwiseXor => checked_if_let!(PrimitiveTy(_), &lhs_ty, {
						ValueTy(self.bxor_imm(lhs_val, rhs_val))
					}),
					BitwiseOr => checked_if_let!(PrimitiveTy(_), &lhs_ty, {
						ValueTy(self.bor_imm(lhs_val, rhs_val))
					}),
					BitwiseLeftShift => checked_if_let!(PrimitiveTy(_), &lhs_ty, {
						ValueTy(self.shl_imm(lhs_val, rhs_val))
					}),
					BitwiseRightShift => checked_if_let!(PrimitiveTy(_), &lhs_ty, {
						ValueTy(self.arithmetic_shr_imm(lhs_val, rhs_val))
					}),

					Less => ValueTy(self.icmp_imm(IntCC::SignedLessThan, lhs_val, rhs_val)),
					LessOrEqual => {
						ValueTy(self.icmp_imm(IntCC::SignedLessThanOrEqual, lhs_val, rhs_val))
					}
					Greater => ValueTy(self.icmp_imm(IntCC::SignedGreaterThan, lhs_val, rhs_val)),
					GreaterOrEqual => {
						ValueTy(self.icmp_imm(IntCC::SignedGreaterThanOrEqual, lhs_val, rhs_val))
					}
					Equal => ValueTy(self.icmp_imm(IntCC::Equal, lhs_val, rhs_val)),
					NotEqual => ValueTy(self.icmp_imm(IntCC::NotEqual, lhs_val, rhs_val)),

					Assignment
					| AdditionAssignment
					| SubtractionAssignment
					| MultiplicationAssignment
					| DivisionAssignment => {
						match lhs.as_ref() {
							IdentifierExpr(Identifier(var_name)) => {
								let lhs_var = self.name_env.get_unchecked(var_name);
								match lhs_var {
									PrimitiveIdent(PrimitiveIdentifier { ident, .. }) => {
										let lhs_ty = self.value_type(lhs_val);
										let new_lhs_val = match operator {
											Assignment => self.iconst(lhs_ty, rhs_val),
											AdditionAssignment => {
												self.blur_iadd_imm(lhs_val, rhs_val)
											}
											SubtractionAssignment => {
												self.isub(lhs_val, self.iconst(lhs_ty, rhs_val))
											}
											MultiplicationAssignment => {
												self.blur_imul_imm(lhs_val, rhs_val)
											}
											DivisionAssignment => self.idiv_imm(lhs_val, rhs_val),
											_ => semantically_unreachable!(),
										};
										self.blur_def_var(*ident, new_lhs_val);
									}

									PointerIdent(PointerIdentifer {
										ident,
										ty: PointerTy(pty),
									}) => {
										let new_lhs_val = match operator {
											AdditionAssignment => match pty.as_ref() {
												PrimitiveTy(ty) => self.blur_iadd_imm(
													lhs_val,
													rhs_val * ty.bytes() as i64,
												),
												_ => todo!(),
											},

											SubtractionAssignment => match pty.as_ref() {
												PrimitiveTy(ty) => self.blur_iadd_imm(
													lhs_val,
													rhs_val * ty.bytes() as i64,
												),
												_ => todo!(),
											},

											_ => semantically_unreachable!(),
										};
										self.blur_def_var(*ident, new_lhs_val);
									}

									_ => semantically_unreachable!(),
								}
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
										let typed_ident = self.name_env.get_unchecked(var_name);
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

											_ => semantically_unreachable!(),
										}
									}
								);
							}

							_ => semantically_unreachable!(),
						}

						Unit
					}
				};

				SimpleTypedConcreteValue { val, ty: lhs_ty }
			}

			(
				SimpleTypedConcreteValue { val: ValueTy(lhs_val), ty: lhs_ty },
				SimpleTypedConcreteValue { val: ValueTy(rhs_val), ty: rhs_ty },
			) => {
				let lhs_val = self.blur_value(lhs_val);
				let rhs_val = self.blur_value(rhs_val);
				let val = match operator {
					Multiplication => ValueTy(self.imul(lhs_val, rhs_val)),
					Division => ValueTy(self.idiv(lhs_val, rhs_val)),
					Remainder => ValueTy(self.srem(lhs_val, rhs_val)),

					Addition => match (&lhs_ty, &rhs_ty) {
						(PrimitiveTy(_), PrimitiveTy(_)) => {
							ValueTy(self.blur_iadd(lhs_val, rhs_val))
						}

						(PointerTy(pty), PrimitiveTy(_)) => match pty.as_ref() {
							PrimitiveTy(ty) => ValueTy(self.blur_iadd(
								lhs_val,
								self.blur_imul_imm(rhs_val, ty.bytes() as i64),
							)),
							_ => todo!(),
						},

						(PrimitiveTy(_), PointerTy(pty)) => match pty.as_ref() {
							PrimitiveTy(ty) => ValueTy(self.blur_iadd(
								rhs_val,
								self.blur_imul_imm(lhs_val, ty.bytes() as i64),
							)),
							_ => todo!(),
						},

						_ => semantically_unreachable!(),
					},

					Subtraction => match (&lhs_ty, &rhs_ty) {
						(PrimitiveTy(_), PrimitiveTy(_)) => ValueTy(self.isub(lhs_val, rhs_val)),

						(PointerTy(pty), PrimitiveTy(_)) => match pty.as_ref() {
							PrimitiveTy(ty) => ValueTy(
								self.isub(lhs_val, self.blur_imul_imm(rhs_val, ty.bytes() as i64)),
							),
							_ => todo!(),
						},

						_ => semantically_unreachable!(),
					},

					BitwiseAnd => ValueTy(self.band(lhs_val, rhs_val)),
					BitwiseOr => ValueTy(self.bor(lhs_val, rhs_val)),
					BitwiseXor => ValueTy(self.bxor(lhs_val, rhs_val)),
					BitwiseLeftShift => ValueTy(self.shl(lhs_val, rhs_val)),
					BitwiseRightShift => ValueTy(self.arithmetic_shr(lhs_val, rhs_val)),

					Less => ValueTy(self.icmp(IntCC::SignedLessThan, lhs_val, rhs_val)),
					LessOrEqual => {
						ValueTy(self.icmp(IntCC::SignedLessThanOrEqual, lhs_val, rhs_val))
					}
					Greater => ValueTy(self.icmp(IntCC::SignedGreaterThan, lhs_val, rhs_val)),
					GreaterOrEqual => {
						ValueTy(self.icmp(IntCC::SignedGreaterThanOrEqual, lhs_val, rhs_val))
					}
					Equal => ValueTy(self.icmp(IntCC::Equal, lhs_val, rhs_val)),
					NotEqual => ValueTy(self.icmp(IntCC::NotEqual, lhs_val, rhs_val)),

					Assignment
					| AdditionAssignment
					| SubtractionAssignment
					| MultiplicationAssignment
					| DivisionAssignment => {
						match lhs.as_ref() {
							IdentifierExpr(Identifier(lhs_var_name)) => {
								let lhs_var = self.name_env.get_unchecked(lhs_var_name);
								match lhs_var {
									PrimitiveIdent(PrimitiveIdentifier {
										ident: lhs_ident,
										ty: PrimitiveTy(ty),
									}) => {
										let new_lhs_val = match operator {
											Assignment => self.cast_value(*ty, rhs_val),
											AdditionAssignment => self.blur_iadd(lhs_val, rhs_val),
											SubtractionAssignment => self.isub(lhs_val, rhs_val),
											MultiplicationAssignment => {
												self.blur_imul(lhs_val, rhs_val)
											}
											DivisionAssignment => self.idiv(lhs_val, rhs_val),
											_ => semantically_unreachable!(),
										};
										self.blur_def_var(*lhs_ident, new_lhs_val);
									}

									PointerIdent(PointerIdentifer {
										ident: lhs_ident,
										ty: PointerTy(lhs_pty),
									}) => {
										let new_lhs_val = match operator {
											Assignment => {
												if lhs_ty == rhs_ty {
													rhs_val
												} else {
													semantically_unreachable!()
												}
											}

											AdditionAssignment => match lhs_pty.as_ref() {
												PrimitiveTy(lhs_pty) => self.blur_iadd(
													lhs_val,
													self.blur_imul_imm(
														rhs_val,
														lhs_pty.bytes() as i64,
													),
												),
												_ => todo!(), // pointer to pointer, etc.
											},

											SubtractionAssignment => match lhs_pty.as_ref() {
												PrimitiveTy(lhs_pty) => self.isub(
													lhs_val,
													self.blur_imul_imm(
														rhs_val,
														lhs_pty.bytes() as i64,
													),
												),
												_ => todo!(), // pointer to pointer, etc.
											},

											_ => semantically_unreachable!(),
										};
										self.blur_def_var(*lhs_ident, new_lhs_val);
									}

									_ => todo!(),
								}
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
										let typed_ident = self.name_env.get_unchecked(var_name);
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
																let ident_val =
																	self.use_var(*ident);
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

											_ => semantically_unreachable!(),
										}
									}
								);
							}

							_ => todo!(),
						}

						Unit
					}
				};

				match operator {
					Assignment
					| AdditionAssignment
					| SubtractionAssignment
					| MultiplicationAssignment
					| DivisionAssignment => SimpleTypedConcreteValue { val, ty: lhs_ty },
					_ => match (&lhs_ty, &rhs_ty) {
						(PrimitiveTy(lty), PrimitiveTy(rty)) => {
							let ty = if lty.bytes() > rty.bytes() { lhs_ty } else { rhs_ty };
							SimpleTypedConcreteValue { val, ty }
						}
						(PointerTy(_), PrimitiveTy(_)) => {
							SimpleTypedConcreteValue { val, ty: lhs_ty }
						}
						(PrimitiveTy(_), PointerTy(_)) => {
							SimpleTypedConcreteValue { val, ty: rhs_ty }
						}
						_ => todo!(),
					},
				}
			}

			_ => todo!(),
		}
	}

	fn translate_member_expression(
		&'_ self,
		MemberExpression { expression, identifier: Identifier(field_name), operator }: &'_ MemberExpression<'tcx>,
	) -> SimpleTypedConcreteValue<'tcx> {
		use ConcreteValue::*;
		use EffectiveType::*;
		use Expression::*;
		use MemberOperator::*;
		use SimpleTypedIdentifier::*;

		if let IdentifierExpr(Identifier(var_name)) = expression.as_ref() {
			let typed_ident = self.name_env.get_unchecked(var_name);
			match typed_ident {
				// e.g. s.i
				AggregateIdent(AggregateIdentifier { ident, ty: AggregateTy(aggre_ty) }) => {
					checked_match!(operator, Direct, {
						let offset = checked_unwrap_option!(aggre_ty.field_offset(field_name));
						let (_, fty) = checked_unwrap_option!(
							aggre_ty.fields.iter().find(|(fname, _)| fname == field_name)
						);
						SimpleTypedConcreteValue {
							val: ValueTy(self.stack_load(*fty, *ident, offset as i32)),
							ty: AggregateTy(aggre_ty.clone()),
						}
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

								let (_, fty) = checked_unwrap_option!(
									aggre_ty.fields.iter().find(|(fname, _)| fname == field_name)
								);

								let ident_val = self.use_var(*ident);
								SimpleTypedConcreteValue {
									val: ValueTy(self.load(*fty, ident_val, offset as i32)),
									ty: PrimitiveTy(*fty),
								}
							})
						})
					})
				}

				_ => semantically_unreachable!(),
			}
		} else {
			unimpl!("unhandled expression for assignment")
		}
	}

	fn translate_call_expression(
		&'_ mut self,
		CallExpression { callee: Identifier(func_name), arguments }: &'_ CallExpression<'tcx>,
	) -> SimpleTypedConcreteValue<'tcx> {
		use ConcreteValue::*;
		use EffectiveType::*;
		use SimpleTypedIdentifier::*;

		let func = self.name_env.get_unchecked(func_name).clone();
		match func {
			FunctionIdent(FunctionIdentifier {
				ty: FunctionTy(FunctionType { return_ty, param_ty }),
				ident,
			}) => {
				let sig = Signature {
					params: param_ty.iter().map(|_| AbiParam::new(self.pointer_ty)).collect(),
					returns: if return_ty.is_some() {
						vec![AbiParam::new(self.pointer_ty)]
					} else {
						vec![]
					},
					call_conv: isa::CallConv::SystemV,
				};
				let sig_ref = self.import_signature(&sig);

				let local_callee = self.func_ref(ident);
				let callee_addr = self.blur_value(self.func_addr(local_callee));

				let arg_values: Vec<_> = arguments
					.iter()
					.zip(param_ty.iter())
					.map(|(arg, param_ty)| {
						let SimpleTypedConcreteValue { val, .. } = self.translate_expression(arg);

						let arg_val = match val {
							ValueTy(val) => self.cast_value(*param_ty, val),
							ConstantTy(val) => self.iconst(*param_ty, val),

							_ => todo!(),
						};
						checked_unwrap_option!(self.uextend(self.pointer_ty, arg_val))
					})
					.collect();

				let call = self.insert_indirect_call(sig_ref, callee_addr, &arg_values);

				let ret_val = if let Some(ty) = return_ty {
					let ret_val = self.inst_result(call);
					ValueTy(checked_unwrap_option!(self.ireduce(ty, ret_val)))
				} else {
					Unit
				};

				SimpleTypedConcreteValue {
					val: ret_val,
					ty: if let Some(ty) = return_ty { PrimitiveTy(ty) } else { UnitTy },
				}
			}

			_ => unimpl!("unsupported call identifier"),
		}
	}

	fn translate_identifier_expression(
		&'_ self, Identifier(var_name): &'_ Identifier<'tcx>,
	) -> SimpleTypedConcreteValue<'tcx> {
		use SimpleTypedIdentifier::*;

		let var = self.name_env.get_unchecked(var_name);
		match var {
			PrimitiveIdent(PrimitiveIdentifier { ident, ty }) => SimpleTypedConcreteValue {
				val: ConcreteValue::ValueTy(self.blur_use_var(*ident)),
				ty: ty.clone(),
			},

			PointerIdent(PointerIdentifer { ident, ty }) => SimpleTypedConcreteValue {
				val: ConcreteValue::ValueTy(self.blur_use_var(*ident)),
				ty: ty.clone(),
			},

			_ => todo!(),
		}
	}

	fn translate_expression(
		&'_ mut self, expr: &'_ Expression<'tcx>,
	) -> SimpleTypedConcreteValue<'tcx> {
		use EffectiveType::*;
		use Expression::*;

		if let Some(val) = evaluate_constant_arithmetic_expression(expr) {
			SimpleTypedConcreteValue {
				val: ConcreteValue::ConstantTy(val),
				ty: PrimitiveTy(types::I64),
			}
		} else {
			match expr {
				CallExpr(expr) => self.translate_call_expression(expr),
				MemberExpr(expr) => self.translate_member_expression(expr),
				IdentifierExpr(ident) => self.translate_identifier_expression(ident),
				UnaryOperatorExpr(expr) => self.translate_unary_operator_expression(expr),
				BinaryOperatorExpr(expr) => self.translate_binary_operator_expression(expr),
				ConstantExpr(_) => semantically_unreachable!(),
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

	fn sextend(&'_ self, ty: Type, val: Value) -> Option<Value> {
		let val_size = self.value_type(val).bytes();
		let ty_size = ty.bytes();
		if ty_size > val_size {
			Some(self.func_builder.borrow_mut().ins().sextend(ty, val))
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

	fn new_block(&'_ self) -> Block { self.func_builder.borrow_mut().create_block() }

	fn switch_to_ebb(&'_ self, ebb: Block) { self.func_builder.borrow_mut().switch_to_block(ebb) }

	fn seal_ebb(&'_ self, ebb: Block) { self.func_builder.borrow_mut().seal_block(ebb) }

	fn value_type(&'_ self, val: Value) -> Type {
		self.func_builder.borrow_mut().func.dfg.value_type(val)
	}

	fn use_var(&'_ self, var: Variable) -> Value { self.func_builder.borrow_mut().use_var(var) }

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

	fn normalize(&'_ self, x: Value, y: Value) -> (Value, Value) {
		let ty_x = self.value_type(x);
		let ty_y = self.value_type(y);
		if ty_x.bytes() <= ty_y.bytes() {
			(checked_unwrap_option!(self.sextend(ty_y, x)), y)
		} else {
			(x, checked_unwrap_option!(self.sextend(ty_x, y)))
		}
	}

	fn iadd(&'_ self, x: Value, y: Value) -> Value {
		let (x, y) = self.normalize(x, y);
		self.func_builder.borrow_mut().ins().iadd(x, y)
	}

	fn blur_iadd(&'_ self, x: Value, y: Value) -> Value {
		let (x, y) = self.normalize(x, y);
		if light() { self.iadd(x, y) } else { self.iadd(self.bor(x, y), self.band(x, y)) }
	}

	fn iadd_imm(&'_ self, x: Value, n: impl Into<i64>) -> Value {
		self.func_builder.borrow_mut().ins().iadd_imm(x, n.into())
	}

	fn blur_iadd_imm(&'_ self, x: Value, y: impl Into<i64> + Copy) -> Value {
		if light() {
			self.iadd_imm(x, y)
		} else {
			self.blur_iadd(self.bor_imm(x, y), self.band_imm(x, y))
		}
	}

	fn isub(&'_ self, x: Value, y: Value) -> Value {
		let (x, y) = self.normalize(x, y);
		self.func_builder.borrow_mut().ins().isub(x, y)
	}

	#[allow(dead_code)]
	fn blur_isub(&'_ self, x: Value, y: Value) -> Value {
		let neg_y = self.ineg(y);
		self.blur_iadd(x, neg_y)
	}

	fn idiv(&'_ self, x: Value, y: Value) -> Value {
		let (x, y) = self.normalize(x, y);
		self.func_builder.borrow_mut().ins().sdiv(x, y)
	}

	fn idiv_imm(&'_ self, x: Value, n: impl Into<i64>) -> Value {
		self.func_builder.borrow_mut().ins().sdiv_imm(x, n.into())
	}

	fn srem(&'_ self, x: Value, y: Value) -> Value {
		let (x, y) = self.normalize(x, y);
		self.func_builder.borrow_mut().ins().srem(x, y)
	}

	fn srem_imm(&'_ self, x: Value, n: impl Into<i64>) -> Value {
		self.func_builder.borrow_mut().ins().srem_imm(x, n.into())
	}

	fn imul(&'_ self, x: Value, y: Value) -> Value {
		self.func_builder.borrow_mut().ins().imul(x, y)
	}

	fn blur_imul(&'_ self, x: Value, y: Value) -> Value {
		if light() {
			self.imul(x, y)
		} else {
			let lhs = self.imul(self.bor(x, y), self.band(x, y));
			let rhs = self.imul(self.band_not(x, y), self.band_not(y, x));
			self.blur_iadd(lhs, rhs)
		}
	}

	fn imul_imm(&'_ self, x: Value, n: impl Into<i64>) -> Value {
		self.func_builder.borrow_mut().ins().imul_imm(x, n.into())
	}

	fn blur_imul_imm(&'_ self, x: Value, y: impl Into<i64> + Copy) -> Value {
		if light() {
			self.imul_imm(x, y)
		} else {
			let lhs = self.imul(self.bor_imm(x, y), self.band_imm(x, y));
			let y = self.iconst(self.value_type(x), y);
			let rhs = self.imul(self.band_not(x, y), self.band_not(y, x));
			self.blur_iadd(lhs, rhs)
		}
	}

	fn ineg(&'_ self, x: Value) -> Value { self.func_builder.borrow_mut().ins().ineg(x) }

	fn bconst(&'_ self, bty: Type, n: impl Into<bool>) -> Value {
		self.func_builder.borrow_mut().ins().bconst(bty, n)
	}

	fn icmp(&'_ self, cond: impl Into<IntCC>, x: Value, y: Value) -> Value {
		self.func_builder.borrow_mut().ins().icmp(cond, x, y)
	}

	fn icmp_imm(&'_ self, cond: impl Into<IntCC>, x: Value, y: impl Into<i64>) -> Value {
		self.func_builder.borrow_mut().ins().icmp_imm(cond, x, y.into())
	}

	fn inst_result(&'_ self, inst: Inst) -> Value {
		self.func_builder.borrow().inst_results(inst)[0]
	}

	#[allow(dead_code)]
	fn logical_shr(&'_ self, x: Value, y: Value) -> Value {
		self.func_builder.borrow_mut().ins().ushr(x, y)
	}

	fn logical_shr_imm(&'_ self, x: Value, y: impl Into<i64>) -> Value {
		self.func_builder.borrow_mut().ins().ushr_imm(x, y.into())
	}

	fn arithmetic_shr(&'_ self, x: Value, y: Value) -> Value {
		self.func_builder.borrow_mut().ins().sshr(x, y)
	}

	fn arithmetic_shr_imm(&'_ self, x: Value, y: impl Into<i64>) -> Value {
		self.func_builder.borrow_mut().ins().sshr_imm(x, y.into())
	}

	fn shl(&'_ self, x: Value, y: Value) -> Value {
		self.func_builder.borrow_mut().ins().ishl(x, y)
	}

	fn shl_imm(&'_ self, x: Value, y: impl Into<i64>) -> Value {
		self.func_builder.borrow_mut().ins().ishl_imm(x, y.into())
	}

	fn band(&'_ self, x: Value, y: Value) -> Value {
		self.func_builder.borrow_mut().ins().band(x, y)
	}

	fn bor(&'_ self, x: Value, y: Value) -> Value { self.func_builder.borrow_mut().ins().bor(x, y) }

	fn blur_bor(&'_ self, x: Value, y: Value) -> Value {
		let x_add_y = self.iadd(x, y);
		let x_and_y = self.band(x, y);
		self.isub(x_add_y, x_and_y)
	}

	fn bxor(&'_ self, x: Value, y: Value) -> Value {
		self.func_builder.borrow_mut().ins().bxor(x, y)
	}

	#[allow(dead_code)]
	fn bnot(&'_ self, x: Value) -> Value { self.func_builder.borrow_mut().ins().bnot(x) }

	#[allow(dead_code)]
	fn band_not(&'_ self, x: Value, y: Value) -> Value {
		self.func_builder.borrow_mut().ins().band_not(x, y)
	}

	#[allow(dead_code)]
	fn bor_not(&'_ self, x: Value, y: Value) -> Value {
		self.func_builder.borrow_mut().ins().bor_not(x, y)
	}

	#[allow(dead_code)]
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

	fn insert_brz(&'_ self, cond: Value, ebb: Block) -> Inst {
		self.func_builder.borrow_mut().ins().brz(cond, ebb, &[])
	}

	#[allow(dead_code)]
	fn insert_br_icmp(&'_ self, cond: impl Into<IntCC>, x: Value, y: Value, ebb: Block) -> Inst {
		self.func_builder.borrow_mut().ins().br_icmp(cond, x, y, ebb, &[])
	}

	fn insert_jmp(&'_ self, ebb: Block) -> Inst {
		self.func_builder.borrow_mut().ins().jump(ebb, &[])
	}

	#[allow(dead_code)]
	fn insert_call(&'_ self, fref: FuncRef, args: &[Value]) -> Inst {
		self.func_builder.borrow_mut().ins().call(fref, args)
	}

	fn insert_indirect_call(&'_ self, sigref: SigRef, callee: Value, args: &[Value]) -> Inst {
		self.func_builder.borrow_mut().ins().call_indirect(sigref, callee, args)
	}

	fn insert_return(&'_ self, val: Value) { self.func_builder.borrow_mut().ins().return_(&[val]); }

	fn import_signature(&'_ self, fsig: &'_ Signature) -> SigRef {
		if self.imported_sigs.borrow().contains_key(fsig) {
			checked_unwrap_option!(self.imported_sigs.borrow().get(fsig)).to_owned()
		} else {
			let fsigref = self.func_builder.borrow_mut().import_signature(fsig.to_owned());
			self.imported_sigs.borrow_mut().insert(fsig.to_owned(), fsigref);
			fsigref
		}
	}

	fn func_ref(&'_ mut self, func_id: FuncId) -> FuncRef {
		self.module.declare_func_in_func(func_id, self.func_builder.get_mut().func)
	}

	fn func_addr(&'_ self, fref: FuncRef) -> Value {
		self.func_builder.borrow_mut().ins().func_addr(self.pointer_ty, fref)
	}
}

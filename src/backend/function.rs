use std::{
	cell::RefCell,
	collections::HashMap,
	hint::unreachable_unchecked,
	i16, i32, i64, i8,
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

use crate::{
	checked_if_let, checked_match, checked_unwrap_option,
	frontend::syntax::{
		BinaryOperator, BinaryOperatorExpression, CallExpression, Declaration, Declarator, DerivedDeclarator,
		DoWhileStatement, Expression, ForStatement, FunctionDeclarator, FunctionDefinition, Identifier, IfStatement,
		MemberExpression, MemberOperator, Statement, StructType, TypeSpecifier, UnaryOperator, UnaryOperatorExpression,
		WhileStatement,
	},
	generate_random_maps, unimpl,
};

use super::support::{
	evaluate_constant_arithmetic_expression, generate_random_partition, AggregateIdentifier, AggregateType, ConcreteValue,
	EffectiveType, FunctionIdentifier, FunctionType, NameBindingEnvironment, PointerIdentifer, PrimitiveIdentifier,
	SimpleTypedConcreteValue, SimpleTypedIdentifier, TypeBindingEnvironment,
};

static NEW_VAR_ID: AtomicUsize = AtomicUsize::new(0);

struct FunctionTranslator<'clif: 'tcx, 'tcx, B: Backend> {
	pub func_builder: RefCell<FunctionBuilder<'clif>>,
	module: &'clif mut Module<B>,
	// func_id: FuncId,
	// func_ref: FuncRef,
	imported_sigs: RefCell<HashMap<Signature, SigRef>>,
	name_env: NameBindingEnvironment<'tcx>,
	type_env: TypeBindingEnvironment<'tcx>,
	pointer_ty: Type,
	return_ty: Option<Type>,
}

pub fn get_function_signature(func_def: &'_ FunctionDefinition<'_>, pointer_ty: Type) -> (Option<Type>, Vec<Type>) {
	use TypeSpecifier::*;

	let FunctionDefinition { specifier, declarator: FunctionDeclarator { parameters, .. }, .. } = func_def;

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
					VoidTy => unsafe { unreachable_unchecked() },
				}
			}
		})
		.collect();

	(return_ty, param_ty)
}

pub fn blur_function_signature(return_ty: Option<Type>, param_ty: &'_ [Type], pointer_ty: Type, ctxt: &'_ mut Context) {
	if return_ty.is_some() {
		ctxt.func.signature.returns.push(AbiParam::new(pointer_ty));
	}
	for _ in param_ty {
		ctxt.func.signature.params.push(AbiParam::new(pointer_ty));
	}
}

// fn blur_function_signature(
// 	func_def: &'_ FunctionDefinition<'_>, ctxt: &'_ mut Context, pointer_ty: Type,
// ) -> (Option<Type>, Vec<Type>) {
// 	use TypeSpecifier::*;

// 	let FunctionDefinition { specifier, declarator: FunctionDeclarator { parameters, .. }, .. } =
// 		func_def;

// 	let return_ty = match specifier {
// 		CharTy | ShortTy | IntTy | LongTy => Some(specifier.into()),

// 		StructTy(_) => todo!(),

// 		VoidTy => None,
// 	};
// 	if return_ty.is_some() {
// 		// blur return type
// 		ctxt.func.signature.returns.push(AbiParam::new(pointer_ty));
// 	}

// 	let mut param_ty = Vec::new();
// 	for Declaration { specifier, declarator } in parameters {
// 		let Declarator { derived, .. } = checked_unwrap_option!(declarator.as_ref());
// 		if let Some(derived_decl) = derived {
// 			match derived_decl {
// 				// some pointer types
// 				DerivedDeclarator::Pointer => {
// 					ctxt.func.signature.params.push(AbiParam::new(pointer_ty));
// 					param_ty.push(pointer_ty);
// 				}
// 			}
// 		} else {
// 			// non pointer types
// 			match specifier {
// 				CharTy | ShortTy | IntTy | LongTy => {
// 					let ty = specifier.into();
// 					// blur param type
// 					ctxt.func.signature.params.push(AbiParam::new(pointer_ty));
// 					param_ty.push(ty)
// 				}

// 				StructTy(_) => todo!(),

// 				VoidTy => unsafe { unreachable_unchecked() },
// 			}
// 		}
// 	}

// 	(return_ty, param_ty)
// }

fn blur_bor(fb: &'_ mut FunctionBuilder, x: Value, y: Value) -> Value {
	let x_add_y = fb.ins().iadd(x, y);
	let x_and_y = fb.ins().band(x, y);
	fb.ins().isub(x_add_y, x_and_y)
}

fn blur_value(fb: &'_ mut FunctionBuilder, val: Value) -> Value {
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
				let (a0, b0, a1, b1) = generate_random_maps!(i8);
				let pv = fb.ins().imul_imm(pv, a0 as i64);
				let pv = fb.ins().iadd_imm(pv, b0 as i64);
				let pv = fb.ins().imul_imm(pv, a1 as i64);
				let pv = fb.ins().iadd_imm(pv, b1 as i64);
				pv
			}

			types::I16 => {
				let (a0, b0, a1, b1) = generate_random_maps!(i16);
				let pv = fb.ins().imul_imm(pv, a0 as i64);
				let pv = fb.ins().iadd_imm(pv, b0 as i64);
				let pv = fb.ins().imul_imm(pv, a1 as i64);
				let pv = fb.ins().iadd_imm(pv, b1 as i64);
				pv
			}

			types::I32 => {
				let (a0, b0, a1, b1) = generate_random_maps!(i32);
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
		// acc_val = fb.ins().bor(acc_val, pv);
		// acc_val = blur_bor(fb, acc_val, val);
		acc_val = blur_bor(fb, acc_val, pv);

		offset += ty.bits() as i64
	}

	acc_val
}

fn create_entry_ebb(fb: &'_ mut FunctionBuilder, param_ty: &[Type], pointer_ty: Type) -> Ebb {
	let trampoline_ebb = fb.create_ebb();
	fb.append_ebb_params_for_function_params(trampoline_ebb);

	fb.switch_to_block(trampoline_ebb);
	let mut param_vals = Vec::new();
	for (i, ty) in param_ty.iter().enumerate() {
		let val = {
			let val = fb.ebb_params(trampoline_ebb)[i];
			let val = blur_value(fb, val);

			if ty.bytes() < pointer_ty.bytes() {
				let ss = fb.create_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, pointer_ty.bytes()));
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

	let entry_ebb = fb.create_ebb();
	for ty in param_ty {
		fb.append_ebb_param(entry_ebb, *ty);
	}
	fb.ins().jump(entry_ebb, &param_vals);
	fb.seal_block(trampoline_ebb);

	fb.switch_to_block(entry_ebb);
	fb.seal_block(entry_ebb);
	entry_ebb
}

fn declare_parameter_variables<'tcx>(
	func_def: &'_ FunctionDefinition<'tcx>, fb: &'_ mut FunctionBuilder, entry_ebb: Ebb, pointer_ty: Type,
	name_env: &'_ mut NameBindingEnvironment<'tcx>, type_env: &'_ TypeBindingEnvironment<'tcx>,
) {
	use EffectiveType::*;
	use TypeSpecifier::*;

	let FunctionDefinition { declarator: FunctionDeclarator { parameters, .. }, .. } = func_def;

	for (i, Declaration { declarator, specifier }) in parameters.iter().enumerate() {
		let Declarator { ident: Identifier(var_name), derived, .. } = checked_unwrap_option!(declarator.as_ref());
		let param_val = fb.ebb_params(entry_ebb)[i];

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

pub fn translate_function<'clif, 'tcx>(
	func_def: &'tcx FunctionDefinition<'tcx>, func_id: FuncId, return_ty: Option<Type>, param_ty: &'_ [Type],
	pointer_ty: Type, ctxt: &'clif mut Context, module: &'clif mut Module<impl Backend>,
	outer_name_env: &'_ NameBindingEnvironment<'tcx>, outer_type_env: &'_ TypeBindingEnvironment<'tcx>,
) -> (FuncId, usize) {
	let FunctionDefinition { body, .. } = func_def;

	// let pointer_ty = module.target_config().pointer_type();

	// // function signature: return type
	// let return_ty = match specifier {
	// 	CharTy | ShortTy | IntTy | LongTy => Some(specifier.into()),

	// 	StructTy(_) => todo!(),

	// 	VoidTy => None,
	// };
	// if let Some(ty) = return_ty {
	// 	// ctxt.func.signature.returns.push(AbiParam::new(ty));
	// 	// blur return type
	// 	ctxt.func.signature.returns.push(AbiParam::new(pointer_ty));
	// }

	// // function signature: param type
	// let mut param_ty = Vec::new();
	// for Declaration { specifier, declarator } in parameters {
	// 	let Declarator { derived, .. } = checked_unwrap_option!(declarator.as_ref());
	// 	if let Some(derived_decl) = derived {
	// 		match derived_decl {
	// 			// some pointer types
	// 			DerivedDeclarator::Pointer => {
	// 				ctxt.func.signature.params.push(AbiParam::new(pointer_ty));
	// 				param_ty.push(pointer_ty);
	// 			}
	// 		}
	// 	} else {
	// 		// non pointer types
	// 		match specifier {
	// 			CharTy | ShortTy | IntTy | LongTy => {
	// 				let ty = specifier.into();
	// 				// ctxt.func.signature.params.push(AbiParam::new(ty));
	// 				// blur param type
	// 				ctxt.func.signature.params.push(AbiParam::new(pointer_ty));
	// 				param_ty.push(ty)
	// 			}

	// 			// simplification: struct definition does not occurs in parameter list
	// 			StructTy(_) => todo!(),

	// 			VoidTy => unsafe { unreachable_unchecked() },
	// 		}
	// 	}
	// }

	// let (return_ty, param_ty) = get_function_signature(func_def, pointer_ty);
	// blur_function_signature(return_ty, &param_ty, ctxt, pointer_ty);

	// let (return_ty, param_ty) = blur_function_signature(func_def, ctxt, pointer_ty);

	// let func_id = checked_unwrap_result!(module.declare_function(
	// 	fname,
	// 	Linkage::Export,
	// 	&ctxt.func.signature
	// ));

	// name_env.bind(
	// 	fname,
	// 	SimpleTypedIdentifier::FunctionIdent(FunctionIdentifier {
	// 		ident: func_id,
	// 		ty: SimpleType::FunctionTy(FunctionType { return_ty, param_ty: param_ty.to_owned() }),
	// 	}),
	// );

	let mut func_builder_ctxt = FunctionBuilderContext::new();
	let mut func_builder = FunctionBuilder::new(&mut ctxt.func, &mut func_builder_ctxt);

	// let entry_ebb = func_builder.create_ebb();
	// func_builder.append_ebb_params_for_function_params(entry_ebb);
	// func_builder.switch_to_block(entry_ebb);
	// let mut param_vals = Vec::new();
	// for (i, ty) in param_ty.iter().enumerate() {
	// 	let val = {
	// 		let val = func_builder.ebb_params(entry_ebb)[i];
	// 		func_builder.ins().ireduce(*ty, val)
	// 	};
	// 	param_vals.push(val);
	// }

	// let real_entry_ebb = func_builder.create_ebb();
	// for ty in &param_ty {
	// 	func_builder.append_ebb_param(real_entry_ebb, *ty);
	// }
	// func_builder.ins().jump(real_entry_ebb, &param_vals);

	// for (i, Declaration { declarator, specifier }) in parameters.iter().enumerate() {
	// 	let Declarator { ident: Identifier(var_name), derived, .. } =
	// 		checked_unwrap_option!(declarator.as_ref()); // checked in syntax analysis
	// 	let param_val = func_builder.ebb_params(entry_ebb)[i];

	// 	match specifier {
	// 		VoidTy => todo!(),

	// 		CharTy | ShortTy | IntTy | LongTy => {
	// 			if let Some(derived_decl) = derived {
	// 				match derived_decl {
	// 					DerivedDeclarator::Pointer => {
	// 						let new_var =
	// 							declare_variable(&mut func_builder, pointer_ty, Some(param_val));

	// 						name_env.insert(
	// 							var_name,
	// 							SimpleTypedIdentifier::PointerIdent(PointerIdentifer {
	// 								ident: new_var,
	// 								ty: PointerTy(Box::new(PrimitiveTy(specifier.into()))),
	// 							}),
	// 						);
	// 					}
	// 				}
	// 			} else {
	// 				let new_var =
	// 					declare_variable(&mut func_builder, specifier.into(), Some(param_val));

	// 				name_env.insert(
	// 					var_name,
	// 					SimpleTypedIdentifier::PrimitiveIdent(PrimitiveIdentifier {
	// 						ident: new_var,
	// 						ty: SimpleType::PrimitiveTy(specifier.into()),
	// 					}),
	// 				);
	// 			}
	// 		}

	// 		StructTy(StructType { identifier: Identifier(sname), .. }) => {
	// 			if let Some(derived_decl) = derived {
	// 				match derived_decl {
	// 					DerivedDeclarator::Pointer => {
	// 						let new_var =
	// 							declare_variable(&mut func_builder, pointer_ty, Some(param_val));

	// 						let aggre_ty = checked_unwrap_option!(type_env.get(sname));

	// 						name_env.insert(
	// 							var_name,
	// 							SimpleTypedIdentifier::PointerIdent(PointerIdentifer {
	// 								ident: new_var,
	// 								ty: PointerTy(Box::new(aggre_ty.clone())),
	// 							}),
	// 						);
	// 					}
	// 				}
	// 			} else {
	// 				// simplification: struct has always MEMORY class
	// 				// (i.e. larger than 8 bytes or  contains unaligned field)
	// 				// System V ABI AMD64: 3.2.3 Parameter Passing
	// 				unimpl!("passing struct by value unsupported")
	// 			}
	// 		}
	// 	}
	// }

	// let body_ebb = func_builder.create_ebb();
	// for ty in param_ty {
	// 	func_builder.append_ebb_param(body_ebb, ty);
	// }

	// func_builder.ins().jump(body_ebb, &[]);
	// func_builder.seal_block(entry_ebb);
	// func_builder.switch_to_block(body_ebb);
	// func_builder.seal_block(body_ebb);
	let mut name_env = outer_name_env.inherit();

	let entry_ebb = create_entry_ebb(&mut func_builder, &param_ty, pointer_ty);
	declare_parameter_variables(func_def, &mut func_builder, entry_ebb, pointer_ty, &mut name_env, outer_type_env);

	let mut func_translator = FunctionTranslator::new(func_builder, module, return_ty, name_env, outer_type_env);
	// func_translator.blur_signature();
	func_translator.translate_statement(body, entry_ebb);
	func_translator.func_builder.get_mut().finalize();
	println!("{:?}", func_translator.func_builder.borrow().func);

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
	if let Some(init_val) = init_val {
		func_builder.def_var(new_var, init_val)
	}
	new_var
}

impl<'clif, 'tcx, B: Backend> FunctionTranslator<'clif, 'tcx, B> {
	pub fn new(
		func_builder: FunctionBuilder<'clif>,
		module: &'clif mut Module<B>,
		// func_id: FuncId,
		return_ty: Option<Type>,
		name_env: NameBindingEnvironment<'tcx>,
		outer_type_env: &'_ TypeBindingEnvironment<'tcx>,
	) -> Self {
		let func_builder = RefCell::new(func_builder);
		let pointer_ty = module.target_config().pointer_type();
		// let func_ref = module.declare_func_in_func(func_id, func_builder.get_mut().func);

		// let name_env = outer_name_env.clone();
		// let type_env = outer_type_env.clone();

		Self {
			func_builder,
			module,
			// func_id,
			// func_ref,
			imported_sigs: RefCell::new(HashMap::new()),
			name_env,
			type_env: outer_type_env.clone(),
			pointer_ty,
			return_ty,
		}
	}

	// pub fn blur_signature(&'_ mut self) {
	// 	let call_conv = isa::CallConv::SystemV;
	// 	let param_vals = {
	// 		let entry_ebb =
	// 			checked_unwrap_option!(self.func_builder.borrow().func.layout.entry_block());
	// 		self.func_builder.borrow().ebb_params(entry_ebb).to_owned()
	// 	};

	// 	for pval in param_vals {
	// 		let sig = Signature {
	// 			params: vec![AbiParam::new(self.value_type(pval)), AbiParam::new(self.pointer_ty)],
	// 			returns: if let Some(return_ty) = self.return_ty {
	// 				vec![AbiParam::new(return_ty)]
	// 			} else {
	// 				vec![]
	// 			},
	// 			call_conv,
	// 		};
	// 		let sigref = self.import_signature(&sig);

	// 		let pval_blurred = self.blur_value(pval);
	// 		let faddr = self.func_addr(self.func_ref);

	// 		// opaque predicate: x != y
	// 		let pval2 = self.imul(pval, pval_blurred);
	// 		// let pval2 = self.blur_value(pval2);
	// 		let x = self.iadd_imm(pval2, 1); // x^2 + 2
	// 		let y = self.imul(pval_blurred, pval2); // x^3

	// 		let merge_ebb = self.new_ebb();
	// 		let never_ebb = self.new_ebb();
	// 		let x = self.cast_value(self.pointer_ty, x);
	// 		let y = self.cast_value(self.pointer_ty, y);
	// 		self.insert_br_icmp(IntCC::NotEqual, x, y, merge_ebb);
	// 		self.insert_jmp(never_ebb);

	// 		self.switch_to_ebb(never_ebb);
	// 		let func = self.cast_value(self.pointer_ty, pval);
	// 		self.insert_indirect_call(sigref, func, &[pval, faddr]);
	// 		self.insert_jmp(merge_ebb);
	// 		self.seal_ebb(never_ebb);

	// 		self.switch_to_ebb(merge_ebb);
	// 		self.seal_ebb(merge_ebb);
	// 	}
	// }

	fn split_and_merge_value(&'_ self, val: Value) -> Value {
		let val_ty = self.value_type(val);
		let val_size = val_ty.bytes();

		let random_type_partition = generate_random_partition(val_size);
		let mut offset = 0i32;
		let mut partitioned_values = Vec::new();
		// let mut merged_val = self.iconst(val_ty, 0);
		for ty in random_type_partition {
			let pv = self.logical_shr_imm(val, offset);
			let pv = checked_unwrap_option!(self.ireduce(ty, pv));
			let pv = match ty {
				types::I8 => {
					let (a0, b0, a1, b1) = generate_random_maps!(i8);
					self.blur_iadd_imm(self.blur_imul_imm(self.blur_iadd_imm(self.blur_imul_imm(pv, a0), b0), a1), b1)
				}

				types::I16 => {
					let (a0, b0, a1, b1) = generate_random_maps!(i16);
					self.blur_iadd_imm(self.blur_imul_imm(self.blur_iadd_imm(self.blur_imul_imm(pv, a0), b0), a1), b1)
				}

				types::I32 => {
					let (a0, b0, a1, b1) = generate_random_maps!(i32);
					self.blur_iadd_imm(self.blur_imul_imm(self.blur_iadd_imm(self.blur_imul_imm(pv, a0), b0), a1), b1)
				}

				_ => pv,
			};

			let pv = checked_unwrap_option!(self.uextend(val_ty, pv));
			partitioned_values.push(self.logical_shl_imm(pv, offset));

			offset += ty.bits() as i32;
		}

		partitioned_values.into_iter().fold(self.iconst(val_ty, 0), |acc, v| self.blur_bor(acc, v))
	}

	fn blur_value(&'_ self, val: Value) -> Value {
		let val_ty = self.value_type(val);
		let val_size = val_ty.bytes();

		// let ss = self.create_stack_slot(val_size as _);
		// let ss_addr = self.stack_addr(ss, 0);

		// let random_type_partition = generate_random_partition(val_size);
		// let mut offset = 0i32;
		// for ty in random_type_partition {
		// 	let partitioned_val = {
		// 		let pval = self.logical_shr_imm(val, offset * 8);
		// 		let pval = checked_unwrap_option!(self.ireduce(ty, pval));
		// 		match ty {
		// 			types::I8 => {
		// 				let (a0, b0, a1, b1) = generate_random_maps!(i8);
		// 				self.iadd_imm(
		// 					self.blur_imul_imm(
		// 						self.blur_iadd_imm(self.blur_imul_imm(pval, a0), b0),
		// 						a1,
		// 					),
		// 					b1,
		// 				)
		// 			}

		// 			types::I16 => {
		// 				let (a0, b0, a1, b1) = generate_random_maps!(i16);
		// 				self.iadd_imm(
		// 					self.blur_imul_imm(
		// 						self.blur_iadd_imm(self.blur_imul_imm(pval, a0), b0),
		// 						a1,
		// 					),
		// 					b1,
		// 				)
		// 			}

		// 			types::I32 => {
		// 				let (a0, b0, a1, b1) = generate_random_maps!(i32);
		// 				self.iadd_imm(
		// 					self.blur_imul_imm(
		// 						self.blur_iadd_imm(self.blur_imul_imm(pval, a0), b0),
		// 						a1,
		// 					),
		// 					b1,
		// 				)
		// 			}

		// 			_ => pval,
		// 		}
		// 	};
		// 	self.store(partitioned_val, self.split_and_merge_value(ss_addr), offset);

		// 	offset += ty.bytes() as i32;
		// }

		// self.load(val_ty, ss_addr, 0)

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
						let (a0, b0, a1, b1) = generate_random_maps!(i8);
						self.blur_iadd_imm(self.blur_imul_imm(self.blur_iadd_imm(self.blur_imul_imm(pval, a0), b0), a1), b1)
					}

					types::I16 => {
						let (a0, b0, a1, b1) = generate_random_maps!(i16);
						self.blur_iadd_imm(self.blur_imul_imm(self.blur_iadd_imm(self.blur_imul_imm(pval, a0), b0), a1), b1)
					}

					types::I32 => {
						let (a0, b0, a1, b1) = generate_random_maps!(i32);
						self.blur_iadd_imm(self.blur_imul_imm(self.blur_iadd_imm(self.blur_imul_imm(pval, a0), b0), a1), b1)
					}

					_ => pval,
				}
			};
			// self.stack_store(pval, ss, offset);
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

	fn translate_declaration(&'_ mut self, Declaration { specifier, declarator }: &'_ Declaration<'tcx>) {
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
							new_var = declare_variable(self.func_builder.get_mut(), self.pointer_ty, None);
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
						VoidTy => unsafe { unreachable_unchecked() },
						_ => {
							new_var_ty = specifier.into();
							new_var = declare_variable(self.func_builder.get_mut(), new_var_ty, None);

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
					// let init_val = self.translate_expression(initializer);
					let SimpleTypedConcreteValue { val, .. } = self.translate_expression(initializer);
					let init_val = match val {
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
					// let stack_slot = self.create_stack_slot(struct_ty.bytes());
					// if let Some(Declarator { ident: Identifier(var_name), .. }) = declarator {
					// 	self.name_env.bind(
					// 		var_name,
					// 		SimpleTypedIdentifier::AggregateIdent(AggregateIdentifier {
					// 			ident: stack_slot,
					// 			ty: SimpleType::AggregateTy(struct_ty.clone()),
					// 		}),
					// 	);
					// }

					self.type_env.insert(sname, EffectiveType::AggregateTy(struct_ty));
				}

				if let Some(Declarator { ident: Identifier(var_name), derived, .. }) = declarator {
					let struct_simple_ty = checked_unwrap_option!(self.type_env.get(sname));
					let struct_simple_ty = struct_simple_ty.to_owned();

					if let Some(derived_decl) = derived {
						match derived_decl {
							DerivedDeclarator::Pointer => {
								let new_var = declare_variable(self.func_builder.get_mut(), self.pointer_ty, None);
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
						let struct_len = checked_if_let!(AggregateTy(struct_ty), &struct_simple_ty, { struct_ty.bytes() });

						let stack_slot = self.create_stack_slot(struct_len);
						self.name_env
							.bind(var_name, AggregateIdent(AggregateIdentifier { ident: stack_slot, ty: struct_simple_ty }));
					}
				}
			}
		}
	}

	fn translate_do_while_statement(
		&'_ mut self, DoWhileStatement { statement, condition }: &'_ DoWhileStatement<'tcx>, current_ebb: Ebb,
	) -> Option<Ebb> {
		use ConcreteValue::*;

		let loop_ebb = self.new_ebb();
		let exit_ebb = self.new_ebb();

		self.insert_jmp(loop_ebb);

		self.switch_to_ebb(loop_ebb);
		self.translate_statement(statement.as_ref(), loop_ebb);
		// let cond = self.translate_expression(condition);
		let SimpleTypedConcreteValue { val, .. } = self.translate_expression(condition);
		let cond = match val {
			ConstantTy(c) => self.iconst(types::I64, c),
			ValueTy(v) => v,
			_ => unsafe { unreachable_unchecked() },
		};
		self.insert_brz(cond, exit_ebb);
		self.insert_jmp(loop_ebb);
		self.seal_ebb(loop_ebb);

		self.switch_to_ebb(exit_ebb);
		self.seal_ebb(exit_ebb);

		Some(exit_ebb)
	}

	fn translate_while_statement(
		&'_ mut self, WhileStatement { condition, statement }: &'_ WhileStatement<'tcx>, current_ebb: Ebb,
	) -> Option<Ebb> {
		use ConcreteValue::*;

		let header_ebb = self.new_ebb();
		let loop_ebb = self.new_ebb();
		let exit_ebb = self.new_ebb();

		self.insert_jmp(header_ebb);

		// header EBB
		self.switch_to_ebb(header_ebb);
		// let cond = self.translate_expression(condition);
		let SimpleTypedConcreteValue { val, .. } = self.translate_expression(condition);
		let cond = match val {
			ConstantTy(c) => self.iconst(types::I64, c),
			ValueTy(v) => v,
			_ => unsafe { unreachable_unchecked() },
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

	fn translate_compound_statements(&'_ mut self, stmts: &'_ [Statement<'tcx>], current_ebb: Ebb) -> Option<Ebb> {
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
		&'_ mut self, ForStatement { initializer, condition, step, statement }: &'_ ForStatement<'tcx>, current_ebb: Ebb,
	) -> Option<Ebb> {
		use ConcreteValue::*;

		if let Some(initializer) = initializer.as_ref() {
			self.translate_expression(initializer);
		}

		let header_ebb = self.new_ebb();
		let loop_ebb = self.new_ebb();
		let exit_ebb = self.new_ebb();

		self.insert_jmp(header_ebb);

		// header EBB
		self.switch_to_ebb(header_ebb);
		// let cond = self.translate_expression(condition);
		let SimpleTypedConcreteValue { val, .. } = self.translate_expression(condition);
		let cond = match val {
			ConstantTy(c) => self.iconst(types::I64, c),
			ValueTy(v) => v,
			_ => unsafe { unreachable_unchecked() },
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
		&'_ mut self, IfStatement { condition, then_statement, else_statement }: &'_ IfStatement<'tcx>, current_ebb: Ebb,
	) -> Option<Ebb> {
		use ConcreteValue::*;

		// let cond = self.translate_expression(condition);
		let SimpleTypedConcreteValue { val, .. } = self.translate_expression(condition);
		let cond = match val {
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
			if self.translate_statement(else_stmt.as_ref(), else_ebb).is_some() {
				println!("insert jmp");
				self.insert_jmp(merge_ebb);
			}
		} else {
			self.insert_brz(cond, merge_ebb);
			self.insert_jmp(then_ebb);
		}

		println!("switch to then ebb");

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

	fn translate_statement(&'_ mut self, stmt: &'_ Statement<'tcx>, current_ebb: Ebb) -> Option<Ebb> {
		use ConcreteValue::*;
		use Statement::*;

		println!("{:?}", stmt);
		match stmt {
			DoWhileStmt(stmt) => self.translate_do_while_statement(stmt, current_ebb),

			WhileStmt(stmt) => self.translate_while_statement(stmt, current_ebb),

			ForStmt(stmt) => self.translate_for_statement(stmt, current_ebb),

			IfStmt(stmt) => self.translate_if_statement(stmt, current_ebb),

			ReturnStmt(expr) => {
				if let Some(expr) = expr {
					let val = {
						// let val = self.translate_expression(expr);
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

			CompoundStmt(stmts) => self.translate_compound_statements(stmts.as_slice(), current_ebb),

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
		&'_ mut self, UnaryOperatorExpression { operator, operand }: &'_ UnaryOperatorExpression<'tcx>,
	) -> SimpleTypedConcreteValue<'tcx> {
		use ConcreteValue::*;
		use EffectiveType::*;
		use Expression::*;
		use MemberOperator::*;
		use SimpleTypedIdentifier::*;
		use UnaryOperator::*;

		match operator {
			Negation => {
				// let rhs = self.translate_expression(operand.as_ref());
				let SimpleTypedConcreteValue { val, ty } = self.translate_expression(operand);
				SimpleTypedConcreteValue {
					val: match val {
						ConstantTy(rhs) => ConstantTy(-rhs),
						ValueTy(rhs) => ValueTy(self.ineg(rhs)),
						_ => unsafe { unreachable_unchecked() },
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

					PointerIdent(PointerIdentifer { ident, ty }) => checked_if_let!(PointerTy(pty), ty, {
						match pty.as_ref() {
							PrimitiveTy(t) => {
								let ident_val = self.use_var(*ident);
								let ident_new_val = self.iadd_imm(ident_val, t.bytes());
								self.def_var(*ident, ident_new_val);
								SimpleTypedConcreteValue { val: ValueTy(ident_new_val), ty: ty.clone() }
							}

							_ => todo!(),
						}
					}),

					_ => unsafe { unreachable_unchecked() },
				}

				// checked_if_let!(PrimitiveIdent(PrimitiveIdentifier { ident, ty }), ident_var, {})
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

					PointerIdent(PointerIdentifer { ident, ty }) => checked_if_let!(PointerTy(pty), ty, {
						match pty.as_ref() {
							PrimitiveTy(t) => {
								let ident_val = self.use_var(*ident);
								let ident_new_val = self.iadd_imm(ident_val, t.bytes());
								self.def_var(*ident, ident_new_val);
								SimpleTypedConcreteValue { val: ValueTy(ident_val), ty: ty.clone() }
							}

							_ => todo!(),
						}
					}),

					_ => unsafe { unreachable_unchecked() },
				}
			}),

			Address => match operand.as_ref() {
				IdentifierExpr(ident) => {
					let var_name: &str = ident.into();
					let typed_ident = self.name_env.get_unchecked(var_name);
					match typed_ident {
						AggregateIdent(AggregateIdentifier { ident, ty }) => {
							SimpleTypedConcreteValue { val: ValueTy(self.stack_addr(*ident, 0)), ty: ty.clone() }
						}

						// _ => unimpl!("address operator on unsupported type"),
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
								AggregateIdent(AggregateIdentifier { ident, ty: AggregateTy(aggre_ty) }) => {
									checked_match!(operator, Direct, {
										let offset = checked_unwrap_option!(aggre_ty.field_offset(field_name));
										SimpleTypedConcreteValue {
											val: ValueTy(self.stack_addr(*ident, offset as i32)),
											ty: AggregateTy(aggre_ty.clone()),
										}
									})
								}

								// e.g. ps->i
								PointerIdent(PointerIdentifer { ident, ty }) => checked_match!(operator, Indirect, {
									checked_match!(ty, AggregateTy(aggre_ty), {
										let ident_addr = self.use_var(*ident);
										let offset = checked_unwrap_option!(aggre_ty.field_offset(field_name));
										SimpleTypedConcreteValue {
											val: ValueTy(self.iadd_imm(ident_addr, offset as i64)),
											ty: ty.clone(),
										}
									})
								}),

								_ => unsafe { unreachable_unchecked() },
							}
						}

						_ => todo!(),
					}
				}

				_ => unsafe { unreachable_unchecked() },
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
		&'_ mut self, BinaryOperatorExpression { operator, lhs, rhs }: &'_ BinaryOperatorExpression<'tcx>,
	) -> SimpleTypedConcreteValue<'tcx> {
		use BinaryOperator::*;
		use ConcreteValue::*;
		use EffectiveType::*;
		use Expression::*;
		use MemberOperator::*;
		use SimpleTypedIdentifier::*;

		let lhs_val = self.translate_expression(lhs.as_ref());
		let rhs_val = self.translate_expression(rhs.as_ref());

		println!("lhs: {:?}, rhs: {:?}", lhs.as_ref(), rhs.as_ref());
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
					| DivisionAssignment => unsafe { unreachable_unchecked() },
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
							PrimitiveTy(ty) => ValueTy(self.iadd_imm(rhs_val, lhs_val * ty.bytes() as i64)),

							_ => todo!(),
						},

						_ => unsafe { unreachable_unchecked() },
					},

					Subtraction => match &rhs_ty {
						PrimitiveTy(_) => {
							let ty = self.value_type(rhs_val);
							let lhs = self.iconst(ty, lhs_val);
							ValueTy(self.isub(lhs, rhs_val))
						}

						_ => todo!(),
					},

					Less => ValueTy(self.icmp_imm(IntCC::SignedGreaterThan, rhs_val, lhs_val)),
					LessOrEqual => ValueTy(self.icmp_imm(IntCC::SignedGreaterThanOrEqual, rhs_val, lhs_val)),
					Greater => ValueTy(self.icmp_imm(IntCC::SignedLessThan, rhs_val, lhs_val)),
					GreaterOrEqual => ValueTy(self.icmp_imm(IntCC::SignedLessThanOrEqual, rhs_val, lhs_val)),
					Equal => ValueTy(self.icmp_imm(IntCC::Equal, rhs_val, lhs_val)),
					NotEqual => ValueTy(self.icmp_imm(IntCC::NotEqual, rhs_val, lhs_val)),

					Assignment
					| AdditionAssignment
					| SubtractionAssignment
					| MultiplicationAssignment
					| DivisionAssignment => unsafe { unreachable_unchecked() },
				};

				SimpleTypedConcreteValue { val, ty: rhs_ty }
			}

			(
				SimpleTypedConcreteValue { val: ValueTy(lhs_val), ty: lhs_ty },
				SimpleTypedConcreteValue { val: ConstantTy(rhs_val), .. },
			) => {
				let val = match operator {
					Multiplication => ValueTy(self.imul_imm(lhs_val, rhs_val)),

					Division => ValueTy(self.idiv_imm(lhs_val, rhs_val)),

					Remainder => ValueTy(self.srem_imm(lhs_val, rhs_val)),

					Addition => {
						println!("lhs_ty: {:?}", lhs_ty);
						match &lhs_ty {
							PrimitiveTy(_) => ValueTy(self.iadd_imm(lhs_val, rhs_val)),

							PointerTy(pty) => match pty.as_ref() {
								PrimitiveTy(ty) => ValueTy(self.iadd_imm(lhs_val, rhs_val * ty.bytes() as i64)),

								_ => todo!(),
							},

							_ => unsafe { unreachable_unchecked() },
						}
					}

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

					Less => ValueTy(self.icmp_imm(IntCC::SignedLessThan, lhs_val, rhs_val)),
					LessOrEqual => ValueTy(self.icmp_imm(IntCC::SignedLessThanOrEqual, lhs_val, rhs_val)),
					Greater => ValueTy(self.icmp_imm(IntCC::SignedGreaterThan, lhs_val, rhs_val)),
					GreaterOrEqual => ValueTy(self.icmp_imm(IntCC::SignedGreaterThanOrEqual, lhs_val, rhs_val)),
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
								checked_if_let!(PrimitiveIdent(PrimitiveIdentifier { ident, .. }), lhs_var, {
									let lhs_ty = self.value_type(lhs_val);
									let new_lhs_val = match operator {
										Assignment => self.iconst(lhs_ty, rhs_val),
										AdditionAssignment => self.iadd_imm(lhs_val, rhs_val),
										SubtractionAssignment => self.isub(lhs_val, self.iconst(lhs_ty, rhs_val)),
										MultiplicationAssignment => self.imul_imm(lhs_val, rhs_val),
										DivisionAssignment => self.idiv_imm(lhs_val, rhs_val),
										_ => unsafe { unreachable_unchecked() },
									};
									self.def_var(*ident, new_lhs_val);
								});
							}

							MemberExpr(MemberExpression { expression, identifier: Identifier(field_name), operator }) => {
								checked_match!(expression.as_ref(), IdentifierExpr(Identifier(var_name)), {
									let typed_ident = self.name_env.get_unchecked(var_name);
									match typed_ident {
										// e.g. s.x
										AggregateIdent(AggregateIdentifier { ident, ty: AggregateTy(aggre_ty) }) => {
											checked_match!(operator, Direct, {
												let field_offset = checked_unwrap_option!(aggre_ty.field_offset(field_name));
												let field_ty = checked_unwrap_option!(aggre_ty.field_type(field_name));
												let rhs_val = self.iconst(field_ty, rhs_val);
												self.stack_store(rhs_val, *ident, field_offset as i32);
											});
										}

										// e.g. ps->x
										PointerIdent(PointerIdentifer { ident, ty }) => {
											checked_match!(operator, Indirect, {
												checked_match!(ty, PointerTy(pty), {
													checked_match!(pty.as_ref(), AggregateTy(aggre_ty), {
														let field_offset =
															checked_unwrap_option!(aggre_ty.field_offset(field_name));
														let field_ty =
															checked_unwrap_option!(aggre_ty.field_type(field_name));
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
					Multiplication => ValueTy(self.iadd(lhs_val, rhs_val)),
					Division => ValueTy(self.idiv(lhs_val, rhs_val)),
					Remainder => ValueTy(self.srem(lhs_val, rhs_val)),
					Addition => ValueTy(self.blur_iadd(lhs_val, rhs_val)),
					Subtraction => ValueTy(self.isub(lhs_val, rhs_val)),

					Less => ValueTy(self.icmp(IntCC::SignedLessThan, lhs_val, rhs_val)),
					LessOrEqual => ValueTy(self.icmp(IntCC::SignedLessThanOrEqual, lhs_val, rhs_val)),
					Greater => ValueTy(self.icmp(IntCC::SignedGreaterThan, lhs_val, rhs_val)),
					GreaterOrEqual => ValueTy(self.icmp(IntCC::SignedGreaterThanOrEqual, lhs_val, rhs_val)),
					Equal => ValueTy(self.icmp(IntCC::Equal, lhs_val, rhs_val)),
					NotEqual => ValueTy(self.icmp(IntCC::NotEqual, lhs_val, rhs_val)),

					Assignment
					| AdditionAssignment
					| SubtractionAssignment
					| MultiplicationAssignment
					| DivisionAssignment => {
						match lhs.as_ref() {
							IdentifierExpr(Identifier(var_name)) => {
								let lhs_var = self.name_env.get_unchecked(var_name);
								checked_if_let!(PrimitiveIdent(PrimitiveIdentifier { ident, .. }), lhs_var, {
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
								});
							}

							MemberExpr(MemberExpression { expression, identifier: Identifier(field_name), operator }) => {
								checked_match!(expression.as_ref(), IdentifierExpr(Identifier(var_name)), {
									let typed_ident = self.name_env.get_unchecked(var_name);
									match typed_ident {
										// e.g. s.x
										AggregateIdent(AggregateIdentifier { ident, ty: AggregateTy(aggre_ty) }) => {
											checked_match!(operator, Direct, {
												let field_offset = checked_unwrap_option!(aggre_ty.field_offset(field_name));
												self.stack_store(rhs_val, *ident, field_offset as i32);
											});
										}

										// e.g. ps->x
										PointerIdent(PointerIdentifer { ident, ty }) => {
											checked_match!(operator, Indirect, {
												checked_match!(ty, PointerTy(pty), {
													checked_match!(pty.as_ref(), AggregateTy(aggre_ty), {
														let field_offset =
															checked_unwrap_option!(aggre_ty.field_offset(field_name));
														let ident_val = self.use_var(*ident);
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

						Unit
					}
				};

				// let ty = PrimitiveTy(if lhs_ty.bytes() > rhs_ty.bytes() { lhs_ty } else { rhs_ty });
				match (&lhs_ty, &rhs_ty) {
					(PrimitiveTy(lty), PrimitiveTy(rty)) => {
						let ty = if lty.bytes() > rty.bytes() { lhs_ty } else { rhs_ty };
						SimpleTypedConcreteValue { val, ty }
					}
					_ => todo!(),
				}
				// SimpleTypedConcreteValue { val, ty: lhs_ty }
			}

			_ => todo!(),
		}
	}

	fn translate_member_expression(
		&'_ self, MemberExpression { expression, identifier: Identifier(field_name), operator }: &'_ MemberExpression<'tcx>,
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
						let (_, fty) = checked_unwrap_option!(aggre_ty.fields.iter().find(|(fname, _)| fname == field_name));
						// ValueTy(self.stack_load(*ty, *ident, offset as i32))
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
								let offset = checked_unwrap_option!(aggre_ty.field_offset(field_name));

								let (_, fty) =
									checked_unwrap_option!(aggre_ty.fields.iter().find(|(fname, _)| fname == field_name));

								let ident_val = self.use_var(*ident);
								// ValueTy(self.load(*fty, ident_val, offset as i32))
								SimpleTypedConcreteValue {
									val: ValueTy(self.load(*fty, ident_val, offset as i32)),
									ty: PrimitiveTy(*fty),
								}
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
	) -> SimpleTypedConcreteValue<'tcx> {
		use ConcreteValue::*;
		use EffectiveType::*;
		use SimpleTypedIdentifier::*;

		// let func_name: &str = callee.into();
		let func = self.name_env.get_unchecked(func_name).clone();
		match func {
			FunctionIdent(FunctionIdentifier { ty: FunctionTy(FunctionType { return_ty, param_ty }), ident }) => {
				// let mut sig = self.module.make_signature();
				// if return_ty.is_some() {
				// 	// sig.returns.push(AbiParam::new(return_ty));
				// 	sig.returns.push(AbiParam::new(self.pointer_ty));
				// }
				// for _ in &param_ty {
				// 	// sig.params.push(AbiParam::new(*pty));
				// 	sig.params.push(AbiParam::new(self.pointer_ty));
				// }
				// let SimpleType::FunctionTy(FunctionType { return_ty, param_ty }) = ty;
				let sig = Signature {
					params: param_ty.iter().map(|_| AbiParam::new(self.pointer_ty)).collect(),
					returns: if return_ty.is_some() { vec![AbiParam::new(self.pointer_ty)] } else { vec![] },
					call_conv: isa::CallConv::SystemV,
				};
				let sig_ref = self.import_signature(&sig);

				// let callee = checked_unwrap_result!(self.module.declare_function(
				// 	func_name,
				// 	Linkage::Import,
				// 	&sig
				// ));
				// let local_callee =
				// 	self.module.declare_func_in_func(callee, self.func_builder.get_mut().func);
				let local_callee = self.func_ref(ident);
				let callee_addr = self.blur_value(self.func_addr(local_callee));
				// let callee_addr = self.func_addr(local_callee);

				let arg_values: Vec<_> = arguments
					.iter()
					.zip(param_ty.iter())
					.map(|(arg, param_ty)| {
						let SimpleTypedConcreteValue { val, .. } = self.translate_expression(arg);
						// let arg_val = self.translate_expression(arg);

						let arg_val = match val {
							ValueTy(val) => self.cast_value(*param_ty, val),
							ConstantTy(val) => self.iconst(*param_ty, val),

							// _ => unsafe { unreachable_unchecked() },
							_ => todo!(),
						};
						checked_unwrap_option!(self.uextend(self.pointer_ty, arg_val))
					})
					.collect();

				// let call = self.insert_call(local_callee, &arg_values);
				let call = self.insert_indirect_call(sig_ref, callee_addr, &arg_values);

				let ret_val = if let Some(ty) = return_ty {
					// ValueTy(self.func_builder.borrow_mut().inst_results(call)[0])
					let ret_val = self.inst_result(call);
					ValueTy(checked_unwrap_option!(self.ireduce(ty, ret_val)))
				} else {
					Unit
				};

				SimpleTypedConcreteValue {
					val: ret_val,
					// ty: FunctionTy(FunctionType { return_ty, param_ty }),
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
			PrimitiveIdent(PrimitiveIdentifier { ident, ty }) => {
				SimpleTypedConcreteValue { val: ConcreteValue::ValueTy(self.blur_use_var(*ident)), ty: ty.clone() }
			}

			PointerIdent(PointerIdentifer { ident, ty }) => {
				SimpleTypedConcreteValue { val: ConcreteValue::ValueTy(self.blur_use_var(*ident)), ty: ty.clone() }
			}

			_ => todo!(),
		}

		// checked_match!(
		// 	var,
		// 	SimpleTypedIdentifier::PrimitiveIdent(PrimitiveIdentifier { ident, .. }),
		// 	{
		// 		// SimpleConcreteType::ValueTy(self.use_var(*ident))
		// 		SimpleConcreteType::ValueTy(self.blur_use_var(*ident))
		// 	}
		// )
	}

	fn translate_expression(&'_ mut self, expr: &'_ Expression<'tcx>) -> SimpleTypedConcreteValue<'tcx> {
		use EffectiveType::*;
		use Expression::*;

		if let Some(val) = evaluate_constant_arithmetic_expression(expr) {
			SimpleTypedConcreteValue { val: ConcreteValue::ConstantTy(val), ty: PrimitiveTy(types::I64) }
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
		self.iadd(self.bor(x, y), self.band(x, y))
	}

	fn iadd_imm(&'_ self, x: Value, n: impl Into<i64>) -> Value {
		self.func_builder.borrow_mut().ins().iadd_imm(x, n.into())
	}

	fn blur_iadd_imm(&'_ self, x: Value, y: impl Into<i64> + Copy) -> Value {
		self.iadd(self.bor_imm(x, y), self.band_imm(x, y))
	}

	fn isub(&'_ self, x: Value, y: Value) -> Value {
		let (x, y) = self.normalize(x, y);
		self.func_builder.borrow_mut().ins().isub(x, y)
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

	fn logical_shl_imm(&'_ self, x: Value, y: impl Into<i64>) -> Value {
		self.func_builder.borrow_mut().ins().ishl_imm(x, y.into())
	}

	fn band(&'_ self, x: Value, y: Value) -> Value {
		self.func_builder.borrow_mut().ins().band(x, y)
	}

	fn bor(&'_ self, x: Value, y: Value) -> Value {
		self.func_builder.borrow_mut().ins().bor(x, y)
	}

	fn blur_bor(&'_ self, x: Value, y: Value) -> Value {
		let x_add_y = self.iadd(x, y);
		let x_and_y = self.band(x, y);
		self.isub(x_add_y, x_and_y)
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

	fn insert_return(&'_ self, val: Value) {
		self.func_builder.borrow_mut().ins().return_(&[val]);
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

	fn func_ref(&'_ mut self, func_id: FuncId) -> FuncRef {
		self.module.declare_func_in_func(func_id, self.func_builder.get_mut().func)
	}

	fn func_addr(&'_ self, fref: FuncRef) -> Value {
		self.func_builder.borrow_mut().ins().func_addr(self.pointer_ty, fref)
	}
}

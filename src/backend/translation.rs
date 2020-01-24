use std::hint::unreachable_unchecked;

use cranelift_module::{Backend, FuncId, Linkage, Module};

use crate::{
	checked_match, checked_unwrap_result,
	frontend::syntax::{Declaration, ExternalDeclaration, FunctionDeclarator, FunctionDefinition, Identifier, StructType, TranslationUnit, TypeSpecifier},
	semantically_unreachable,
};

use super::{
	function::{blur_function_signature, get_function_signature, translate_function},
	support::{AggregateType, EffectiveType, FunctionIdentifier, FunctionType, NameBindingEnvironment, SimpleTypedIdentifier, TypeBindingEnvironment},
};

pub fn compile<'clif, 'tcx>(
	tu: &'tcx TranslationUnit, module: &'clif mut Module<impl Backend>, name_env: &'_ mut NameBindingEnvironment<'tcx>, type_env: &'_ mut TypeBindingEnvironment<'tcx>,
) -> Vec<(FuncId, usize)> {
	use ExternalDeclaration::*;
	use TypeSpecifier::*;

	let pointer_ty = module.target_config().pointer_type();

	let TranslationUnit(extern_decs) = tu;

	let mut ctxt = module.make_context();
	let mut sfuncs = Vec::new();

	for dec in extern_decs {
		match dec {
			FunctionDefinitionDecl(func_def) => {
				let FunctionDefinition { declarator: FunctionDeclarator { identifier: Identifier(fname), .. }, .. } = func_def;

				let (return_ty, param_ty) = get_function_signature(func_def, pointer_ty);
				blur_function_signature(return_ty, &param_ty, pointer_ty, &mut ctxt);

				let func_id = checked_unwrap_result!(module.declare_function(fname, Linkage::Export, &ctxt.func.signature));

				name_env.bind(
					fname,
					SimpleTypedIdentifier::FunctionIdent(FunctionIdentifier {
						ident: func_id,
						ty: EffectiveType::FunctionTy(FunctionType { return_ty, param_ty: param_ty.clone() }),
					}),
				);

				let func = translate_function(func_def, func_id, return_ty, &param_ty, pointer_ty, &mut ctxt, module, name_env, type_env);
				sfuncs.push(func);
			}

			Decl(Declaration { specifier, .. }) => {
				// TODO: check in semantics analysis (global declaration)
				checked_match!(specifier, StructTy(struct_ty), {
					let StructType { identifier: Identifier(sname), .. } = struct_ty;
					let aggre_ty: AggregateType = struct_ty.into();
					type_env.insert(sname, EffectiveType::AggregateTy(aggre_ty))
				});
			}
		}
	}

	module.finalize_definitions();
	sfuncs
}

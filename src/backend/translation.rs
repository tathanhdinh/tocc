use std::hint::unreachable_unchecked;

use cranelift_module::{Backend, FuncId, Module};

use crate::{
	checked_match,
	frontend::syntax::{
		Declaration, ExternalDeclaration, Identifier, StructType, TranslationUnit, TypeSpecifier,
	},
};

use super::{
	function::translate_function,
	support::{AggregateType, NameBindingEnvironment, SimpleType, TypeBindingEnvironment},
};

pub fn compile<'clif, 'tcx>(
	tu: &'tcx TranslationUnit, module: &'clif mut Module<impl Backend>,
	name_env: &'_ mut NameBindingEnvironment<'tcx>, type_env: &'_ mut TypeBindingEnvironment<'tcx>,
) -> Vec<(FuncId, usize)> {
	use ExternalDeclaration::*;
	use TypeSpecifier::*;

	let TranslationUnit(extern_decs) = tu;

	let mut ctxt = module.make_context();
	let mut sfuncs = Vec::new();

	for dec in extern_decs {
		match dec {
			FunctionDefinitionDecl(func_def) => {
				let func = translate_function(func_def, &mut ctxt, module, name_env, type_env);
				sfuncs.push(func);
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

	module.finalize_definitions();
	sfuncs
}

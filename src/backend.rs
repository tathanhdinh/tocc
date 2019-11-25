// Back-end:
//  - ir translation
//  - machine code generation

use cranelift_codegen::ir::Function;
use cranelift_module::FuncId;
use cranelift_simplejit::SimpleJITBuilder;

mod support;
mod translation;

use crate::frontend::syntax::TranslationUnit;
use support::{
	BackedModule, FunctionIdentifier, NameBindingEnvironment, SimpleTypedIdentifier,
	TypeBindingEnvironment,
};

// an abstract machine that runs Cranelift IR
pub struct AbstractMachine<'s> {
	module: BackedModule,
	name_env: NameBindingEnvironment<'s>,
	compiled_funcs: Vec<(Function, FuncId, usize)>,
}

impl<'s> AbstractMachine<'s> {
	pub fn new(tu: &'s TranslationUnit) -> Self {
		let builder = SimpleJITBuilder::new(cranelift_module::default_libcall_names());
		let mut module = BackedModule::new(builder);
		let mut name_env = NameBindingEnvironment::new();
		let mut type_env = TypeBindingEnvironment::new();
		let compiled_funcs = translation::compile(tu, &mut module, &mut name_env, &mut type_env);

		AbstractMachine { module, name_env, compiled_funcs }
	}

	pub fn compiled_function(&mut self, fname: &'_ str) -> Option<(&Function, &[u8])> {
		let ident = self.name_env.get(fname)?;
		if let SimpleTypedIdentifier::FunctionIdent(FunctionIdentifier { ident, .. }) = ident {
			let (fclif, fid, flen) = self.compiled_funcs.iter().find(|(_, fid, _)| fid == ident)?;
			let fptr = translation::compiled_function(*fid, *flen, &mut self.module);
			Some((fclif, fptr))
		} else {
			None
		}
	}
}

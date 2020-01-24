// Back-end:
//  - ir translation
//  - machine code generation

use cranelift_module::{Backend, FuncId, Module};

mod function;
mod support;
mod translation;

use crate::frontend::syntax::TranslationUnit;
use support::{FunctionIdentifier, NameBindingEnvironment, SimpleTypedIdentifier, TypeBindingEnvironment};

// an abstract machine that runs Cranelift IR
pub struct AbstractMachine<'s, B: Backend> {
	module: Module<B>,
	name_env: NameBindingEnvironment<'s>,
	compiled_funcs: Vec<(FuncId, usize)>,
}

impl<'s, B: Backend> AbstractMachine<'s, B> {
	pub fn new(tu: &'s TranslationUnit, builder: B::Builder) -> Self {
		// let builder = SimpleJITBuilder::new(cranelift_module::default_libcall_names());
		let mut module = Module::new(builder);
		let mut name_env = NameBindingEnvironment::new();
		let mut type_env = TypeBindingEnvironment::new();
		let compiled_funcs = translation::compile(tu, &mut module, &mut name_env, &mut type_env);

		AbstractMachine { module, name_env, compiled_funcs }
	}

	pub fn compiled_function(&mut self, fname: &'_ str) -> Option<(B::FinalizedFunction, usize)> {
		let ident = self.name_env.get(fname);
		if let SimpleTypedIdentifier::FunctionIdent(FunctionIdentifier { ident, .. }) = ident {
			let (fid, flen) = self.compiled_funcs.iter().find(|(fid, _)| fid == ident)?;
			// let fptr = translation::jitted_function(*fid, *flen, &mut self.module);
			let fptr = self.module.get_finalized_function(*fid);
			Some((fptr, *flen))
		} else {
			None
		}
	}

	pub fn finish(self) -> B::Product { self.module.finish() }
}

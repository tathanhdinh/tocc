// Back-end:
//  - ir translation
//  - machine code generation

use cranelift_codegen::ir::Function;
use cranelift_module::FuncId;
use cranelift_simplejit::{SimpleJITBackend, SimpleJITBuilder};

mod ir;

use crate::frontend::syntax::{function_name, TranslationUnit};
use ir::{BackedModule, Environment, FunctionIdentifier, SimpleTypedIdentifier};

// an abstract machine that runs Cranelift IR
pub struct AbstractMachine<'s> {
	module: BackedModule,
	env: Environment<'s>,
	compiled_funcs: Vec<(Function, FuncId, usize)>,
}

impl<'s> AbstractMachine<'s> {
	pub fn new(tu: &'s TranslationUnit) -> Self {
		let builder = SimpleJITBuilder::new(cranelift_module::default_libcall_names());
		let mut module = BackedModule::new(builder);
		let mut env = Environment::new();
		let compiled_funcs = ir::compile(tu, &mut module, &mut env);

		AbstractMachine {
			module,
			env,
			compiled_funcs,
		}
	}

	// pub fn compile(&mut self, tu: &'s TranslationUnit) {
	// 	let compiled_funcs = ir::compile(tu, &mut self.module, &mut self.env);
	// 	self.compiled_funcs = compiled_funcs;
	// }

	pub fn compiled_function(&mut self, fname: &'_ str) -> Option<(&Function, &[u8])> {
		let ident = self.env.get(fname)?;
		if let SimpleTypedIdentifier::Function(FunctionIdentifier { function_id, .. }) = ident {
			let (fclif, fid, flen) = self
				.compiled_funcs
				.iter()
				.find(|(_, fid, _)| fid == function_id)?;
			let fptr = ir::compiled_function(*fid, *flen, &mut self.module);
			Some((fclif, fptr))
		} else {
			None
		}
	}
}

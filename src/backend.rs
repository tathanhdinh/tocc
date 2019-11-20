// Back-end:
//  - ir translation
//  - machine code generation

use cranelift_codegen::ir::Function;
use cranelift_codegen::Context;
use cranelift_module::Module;
use cranelift_simplejit::{SimpleJITBackend, SimpleJITBuilder};

use crate::frontend::syntax::{function_name, TranslationUnit};

mod ir;

// an abstract machine that runs Cranelift IR
pub struct AbstractMachine {
	module: Module<SimpleJITBackend>,
	context: Context,
}

impl AbstractMachine {
	pub fn new() -> Self {
		let builder = SimpleJITBuilder::new(cranelift_module::default_libcall_names());
		let module = Module::<SimpleJITBackend>::new(builder);
		let context = module.make_context();
		AbstractMachine { module, context }
	}

	pub fn evaluate<'a>(&mut self, tu: &'a TranslationUnit) -> (&'a str, &Function) {
		let func = ir::evaluate(tu, &mut self.module, &mut self.context);
		let fname = function_name(tu);
		(fname, func)
	}

	pub fn compile(&mut self, fname: &'_ str) -> &[u8] {
		ir::compile_function(fname, &mut self.module, &mut self.context)
	}
}

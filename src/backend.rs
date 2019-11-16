// Back-end:
//  - ir translation
//  - machine code generation

use cranelift_module::Module;
use cranelift_simplejit::{SimpleJITBackend, SimpleJITBuilder};

use crate::frontend::syntax::TranslationUnit;

mod ir;

// an abstract machine that runs Cranelift IR
pub struct AbstractMachine {
	module: Module<SimpleJITBackend>,
}

impl AbstractMachine {
	pub fn new() -> Self {
		let builder = SimpleJITBuilder::new(cranelift_module::default_libcall_names());
		let module = Module::<SimpleJITBackend>::new(builder);
		AbstractMachine { module }
	}

	pub fn generate(&mut self, tu: &TranslationUnit) -> &[u8] {
		ir::evaluate(tu, &mut self.module)
	}
}

use std::mem;

use cranelift::prelude::*;
use cranelift_module::{Linkage, Module};
use cranelift_simplejit::{SimpleJITBackend, SimpleJITBuilder};

fn main() {
	let builder =
		SimpleJITBuilder::new(cranelift_module::default_libcall_names());
	let mut module = Module::<SimpleJITBackend>::new(builder);
	let mut context = module.make_context();
	let mut func_builder_context = FunctionBuilderContext::new();

	// signature of main
	context
		.func
		.signature
		.returns
		.push(AbiParam::new(types::I64));

	// build main
	let mut func_builder =
		FunctionBuilder::new(&mut context.func, &mut func_builder_context);
	let entry_block = func_builder.create_ebb();
	func_builder.switch_to_block(entry_block);
	let zero_value = func_builder.ins().iconst(types::I64, 0);
	func_builder.ins().return_(&[zero_value]);
	func_builder.seal_block(entry_block);
	func_builder.finalize();

    // push main into module
	let func_id = module
		.declare_function("main", Linkage::Export, &context.func.signature)
		.expect("Failed to declare main function");
	module
		.define_function(func_id, &mut context)
		.expect("Failed to define main function");

    module.clear_context(&mut context);
    module.finalize_definitions();

    let jitted_func = unsafe {
        mem::transmute::<_,fn() -> i64>(module.get_finalized_function(func_id))
    };

    jitted_func();
}

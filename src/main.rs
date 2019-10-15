use std::mem;

use cranelift::prelude::*;
use cranelift_module::{Linkage, Module};
use cranelift_simplejit::{SimpleJITBackend, SimpleJITBuilder};

use zydis::{
	Formatter, Decoder, FormatterStyle, MachineMode, AddressWidth, OutputBuffer,
};

const PAGE_SIZE: usize = 1024;

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
	let func_len = module
		.define_function(func_id, &mut context)
		.expect("Failed to define main function");

	module.clear_context(&mut context);
	// SELinux would not allow that, temporarily disable with "sudo setenforce 0"
	module.finalize_definitions();

	let func_addr = module.get_finalized_function(func_id);
	let jitted_func = unsafe {
		mem::transmute::<_, fn() -> i64>(func_addr)
	};

	// run
	assert_eq!(0, jitted_func());

	// print assembly code

	// let func_addr = module.get_finalized_function(func_id) as usize;
	// let page_addr = func_addr & !(PAGE_SIZE - 1);
	// let page_addr_up =
	// 	((func_addr + func_len as usize) & !(PAGE_SIZE - 1)) + PAGE_SIZE;

	// let jitted_func = unsafe {
	// 	use libc::{mprotect, PROT_EXEC, PROT_READ};
	// 	let i = mprotect(
	// 		page_addr as _,
	// 		page_addr_up - page_addr,
	// 		PROT_READ,
	// 	);
	// 	println!("i = {}", i);
	// 	mem::transmute::<_, fn() -> i64>(func_addr)
	// };
}

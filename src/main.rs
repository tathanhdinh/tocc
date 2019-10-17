use std::{mem, slice};

use cranelift::prelude::*;
use cranelift_module::{Linkage, Module};
use cranelift_simplejit::{SimpleJITBackend, SimpleJITBuilder};

use zydis::{
	AddressWidth, Decoder, Formatter, FormatterStyle, MachineMode, OutputBuffer,
};

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

	let func_ptr = module.get_finalized_function(func_id);
	let jitted_func = unsafe { mem::transmute::<_, fn() -> i64>(func_ptr) };

	// run & check
	assert_eq!(0, jitted_func());

	// print assembly code
	let asm_formatter = Formatter::new(FormatterStyle::INTEL)
		.expect("Failed to create assembly formatter");
	let asm_decoder = Decoder::new(MachineMode::LONG_64, AddressWidth::_64)
		.expect("Failed to create assembly decoder");
	let func_code = unsafe { slice::from_raw_parts(func_ptr, func_len as _) };

	let mut decoded_inst_buffer = [0u8; 200];
	let mut decoded_inst_buffer =
		OutputBuffer::new(&mut decoded_inst_buffer[..]);

	for (inst, ip) in asm_decoder.instruction_iterator(func_code, 0) {
		asm_formatter
			.format_instruction(&inst, &mut decoded_inst_buffer, Some(ip), None)
			.expect("Failed to format instruction");
		println!("0x{:x}\t{}", ip, decoded_inst_buffer);
	}
}

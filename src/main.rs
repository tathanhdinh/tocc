use std::{mem, slice};

use cranelift::prelude::*;
use cranelift_module::{Linkage, Module};
use cranelift_simplejit::{SimpleJITBackend, SimpleJITBuilder};

use zydis::{
	AddressWidth, Decoder, Formatter, FormatterProperty, FormatterStyle,
	MachineMode, OutputBuffer,
};

use structopt::StructOpt;

mod frontend;
use frontend::{arithmetic, Expr};

#[derive(StructOpt)]
#[structopt(name = "tocc", about = "A type-obfuscated C compiler")]
struct Opt {
	#[structopt(
		name = "input",
		short = "i",
		long = "input",
		help = "Arithmetic expression"
	)]
	expr: String,
}

fn compile(expr: &Expr, fb: &mut FunctionBuilder) -> Value {
	match expr {
		Expr::Add(lhs, rhs) => {
			let lhs = compile(lhs, fb);
			let rhs = compile(rhs, fb);
			fb.ins().iadd(lhs, rhs)
		}

		Expr::Sub(lhs, rhs) => {
			let lhs = compile(lhs, fb);
			let rhs = compile(rhs, fb);
			fb.ins().isub(lhs, rhs)
		}

		Expr::Val(v) => fb.ins().iconst(types::I64, *v),
	}
}

fn main() {
	let input_expr = {
		let opt = Opt::from_args();
		opt.expr
	};

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

	// layout of main function
	let mut func_builder =
		FunctionBuilder::new(&mut context.func, &mut func_builder_context);
	let entry_block = func_builder.create_ebb();
	func_builder.switch_to_block(entry_block);

	// compile input arithmetic expression
	let expr = arithmetic::evaluate(&input_expr)
		.expect("Failed to parse input expression");
	let expr_value = compile(&expr, &mut func_builder);
	func_builder.ins().return_(&[expr_value]);

	// finalize main
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

	// call jitted function
	println!("result: {}", jitted_func());

	// print assembly code
	let asm_formatter = {
		let mut fm = Formatter::new(FormatterStyle::INTEL)
			.expect("Failed to create assembly formatter");
		fm.set_property(FormatterProperty::HexUppercase(false))
			.expect("Failed to set assembly formatter property");
		fm
	};

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

use std::{mem, slice};

use cranelift::prelude::*;
use cranelift_codegen::Context;
use cranelift_module::{Linkage, Module};
use cranelift_simplejit::{SimpleJITBackend, SimpleJITBuilder};

use zydis::{
	AddressWidth, Decoder, Formatter, FormatterProperty, FormatterStyle,
	MachineMode, OutputBuffer,
};

use structopt::StructOpt;

mod frontend;
use frontend::{parser, ArithmeticExpr, Stmt};

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

fn compile(
	input: &str,
	name: &str,
	module: &mut Module<SimpleJITBackend>,
	context: &mut Context,
	function_builder_context: &mut FunctionBuilderContext,
) -> (Box<unsafe extern "C" fn() -> i64>, usize) {
	// signature of function
	context
		.func
		.signature
		.returns
		.push(AbiParam::new(types::I64));

	// layout
	let mut func_builder =
		FunctionBuilder::new(&mut context.func, function_builder_context);
	let entry_block = func_builder.create_ebb();
	func_builder.switch_to_block(entry_block);

	// compile input arithmetic expression
	let Stmt::Ret(expr) = parser::stmt(&input).expect("Failed to parse input expression");
	// let expr =
	// 	parser::arithmetic_expr(&input).expect("Failed to parse input expression");
	let expr_value = translate(&expr, &mut func_builder);
	func_builder.ins().return_(&[expr_value]);

	// finalize function
	func_builder.seal_block(entry_block);
	func_builder.finalize();

	// push function into module
	let func_id = module
		.declare_function(name, Linkage::Export, &context.func.signature)
		.expect("Failed to declare main function");
	let func_len = module
		.define_function(func_id, context)
		.expect("Failed to define main function");

	module.clear_context(context);
	// SELinux may not allow that, if it is the case,
	// temporarily disable with "sudo setenforce 0"
	module.finalize_definitions();

	let func_ptr = module.get_finalized_function(func_id);
	// this is really a function pointer, not closure
	let func_ptr = unsafe { mem::transmute::<_, _>(func_ptr) };

	(Box::new(func_ptr), func_len as _)
}

fn translate(expr: &ArithmeticExpr, fb: &mut FunctionBuilder) -> Value {
	use ArithmeticExpr::*;
	match expr {
		Add(lhs, rhs) => {
			let lhs = translate(lhs, fb);
			let rhs = translate(rhs, fb);
			fb.ins().iadd(lhs, rhs)
		}

		Sub(lhs, rhs) => {
			let lhs = translate(lhs, fb);
			let rhs = translate(rhs, fb);
			fb.ins().isub(lhs, rhs)
		}

		Mul(lhs, rhs) => {
			let lhs = translate(lhs, fb);
			let rhs = translate(rhs, fb);
			fb.ins().imul(lhs, rhs)
		}

		Div(lhs, rhs) => {
			let lhs = translate(lhs, fb);
			let rhs = translate(rhs, fb);
			fb.ins().sdiv(lhs, rhs)
		}

		ArithmeticExpr::Val(v) => fb.ins().iconst(types::I64, *v),
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
	let mut builder_context = FunctionBuilderContext::new();

	let (func_ptr, func_len) = compile(
		&input_expr,
		"main",
		&mut module,
		&mut context,
		&mut builder_context,
	);
	let func_ptr = *func_ptr;

	// call jitted function
	println!("result: {}", unsafe { func_ptr() });

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
	let func_code = unsafe {
		slice::from_raw_parts(
			mem::transmute::<_, *const u8>(func_ptr),
			func_len as _,
		)
	};

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

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn expr_simple() {
		let builder =
			SimpleJITBuilder::new(cranelift_module::default_libcall_names());
		let mut module = Module::<SimpleJITBackend>::new(builder);
		let mut context = module.make_context();
		let mut builder_context = FunctionBuilderContext::new();

		let (func_ptr, _) = compile(
			"return 1 + 5 - 3;",
			"test0",
			&mut module,
			&mut context,
			&mut builder_context,
		);
		assert_eq!(unsafe { func_ptr() }, 3);

		let (func_ptr, _) = compile(
			"return 2 - 3 - 7;",
			"test1",
			&mut module,
			&mut context,
			&mut builder_context,
		);
		assert_eq!(unsafe { func_ptr() }, -8);
	}

	#[test]
	fn expr_with_parens() {
		let builder =
			SimpleJITBuilder::new(cranelift_module::default_libcall_names());
		let mut module = Module::<SimpleJITBackend>::new(builder);
		let mut context = module.make_context();
		let mut builder_context = FunctionBuilderContext::new();

		let (func_ptr, _) = compile(
			"return -(5 - 9) + 10 + (4 - 27);",
			"test0",
			&mut module,
			&mut context,
			&mut builder_context,
		);
		assert_eq!(unsafe { func_ptr() }, -9);

		let (func_ptr, _) = compile(
			"return (3 + 4) - (10 - (7 - 1));",
			"test1",
			&mut module,
			&mut context,
			&mut builder_context,
		);
		assert_eq!(unsafe { func_ptr() }, 3);
	}

	#[test]
	fn expr_with_mul_div() {
		let builder =
			SimpleJITBuilder::new(cranelift_module::default_libcall_names());
		let mut module = Module::<SimpleJITBackend>::new(builder);
		let mut context = module.make_context();
		let mut builder_context = FunctionBuilderContext::new();

		let (func_ptr, _) = compile(
			"return (1 + 5) * (9 - 6);",
			"test0",
			&mut module,
			&mut context,
			&mut builder_context,
		);
		assert_eq!(unsafe { func_ptr() }, 18);

		let (func_ptr, _) = compile(
			"return (7 / 2) + (9 - 6 * 3);",
			"test1",
			&mut module,
			&mut context,
			&mut builder_context,
		);
		assert_eq!(unsafe { func_ptr() }, -6);
	}
}

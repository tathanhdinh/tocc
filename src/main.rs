use std::path::PathBuf;

use zydis::{AddressWidth, Decoder, Formatter, FormatterProperty, FormatterStyle, MachineMode, OutputBuffer};

use structopt::StructOpt;

mod backend;
mod frontend;

#[derive(StructOpt)]
#[structopt(name = "tocc", about = "A type-obfuscated C compiler")]
struct Opt {
	/// Source code file
	#[structopt(name = "input", parse(from_os_str))]
	src: PathBuf,
}

fn main() {
	let src_file = {
		let opt = Opt::from_args();
		opt.src
	};

	let tu = frontend::syntax::parse(&src_file);
	frontend::semantics::check(&tu);

	let mut builder = backend::AbstractMachine::new();
	let fptr = builder.generate(&tu);

	let asm_formatter = {
		let mut fm = Formatter::new(FormatterStyle::INTEL).expect("Failed to create assembly formatter");
		fm.set_property(FormatterProperty::HexUppercase(false)).expect("Failed to set assembly formatter property");
		fm
	};

	let asm_decoder = Decoder::new(MachineMode::LONG_64, AddressWidth::_64).expect("Failed to create assembly decoder");

	let mut decoded_inst_buffer = [0u8; 200];
	let mut decoded_inst_buffer = OutputBuffer::new(&mut decoded_inst_buffer[..]);

	for (inst, ip) in asm_decoder.instruction_iterator(fptr, 0) {
		asm_formatter
			.format_instruction(&inst, &mut decoded_inst_buffer, Some(ip), None)
			.expect("Failed to format instruction");
		println!("0x{:02x}\t{}", ip, decoded_inst_buffer);
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use std::{mem, path::Path};

	fn compile_and_run_void_to_int(file: impl AsRef<Path>) -> i32 {
		let tu = frontend::syntax::parse(file);
		frontend::semantics::check(&tu);

		let mut am = backend::AbstractMachine::new();
		let fptr = am.generate(&tu);

		let fptr = unsafe { mem::transmute::<_, unsafe extern "C" fn() -> i32>(fptr.as_ptr()) };
		unsafe { fptr() }
	}

	#[test]
	fn compile_0() {
		assert_eq!(compile_and_run_void_to_int("tests/0.c"), 12);
	}

	#[test]
	fn compile_1() {
		assert_eq!(compile_and_run_void_to_int("tests/1.c"), -17);
	}

	#[test]
	fn compile_2() {
		assert_eq!(compile_and_run_void_to_int("tests/2.c"), -1);
	}

	#[test]
	fn compile_3() {
		assert_eq!(compile_and_run_void_to_int("tests/3.c"), -6);
	}

	#[test]
	fn compile_4() {
		assert_eq!(compile_and_run_void_to_int("tests/4.c"), 10);
	}

	fn compile_and_run_int_to_int(file: impl AsRef<Path>, i: i32) -> i32 {
		let tu = frontend::syntax::parse(file);
		frontend::semantics::check(&tu);

		let mut am = backend::AbstractMachine::new();
		let fptr = am.generate(&tu);

		let fptr = unsafe { mem::transmute::<_, unsafe extern "C" fn(i32) -> i32>(fptr.as_ptr()) };
		unsafe { fptr(i) }
	}

	#[test]
	fn compile_5() {
		assert_eq!(compile_and_run_int_to_int("tests/5.c", 10), 11);
	}
}

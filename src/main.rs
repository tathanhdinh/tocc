use std::{fs, path::PathBuf};

use zydis::{
	AddressWidth, Decoder, Formatter, FormatterProperty, FormatterStyle, MachineMode, OutputBuffer,
	Signedness,
};

use structopt::StructOpt;

mod backend;
mod frontend;
mod helper;

#[derive(StructOpt)]
#[structopt(name = "tocc", about = "A type-obfuscated C compiler")]
struct Opt {
	/// Source code file
	#[structopt(name = "source", parse(from_os_str))]
	src: PathBuf,

	/// Function
	#[structopt(name = "function", short = "f")]
	fname: String,
}

fn main() {
	let opt = Opt::from_args();
	let (src, fname) = { (opt.src.as_path(), opt.fname.as_str()) };

	let src_code = fs::read_to_string(src).expect("Failed to read source code file");
	let tu = frontend::syntax::parse(src_code.as_str());
	frontend::semantics::check(&tu);

	let mut am = backend::AbstractMachine::new(&tu);
	if let Some(fptr) = am.compiled_function(fname) {
		// println!("{}", &fclif);

		let asm_formatter = {
			let mut fm =
				Formatter::new(FormatterStyle::INTEL).expect("failed to create assembly formatter");
			fm.set_property(FormatterProperty::HexUppercase(false))
				.expect("failed to disable hex uppercase");
			fm.set_property(FormatterProperty::DisplacementSignedness(
				Signedness::SIGNED,
			))
			.expect("failed to set displacement signedness");
			fm.set_property(FormatterProperty::ImmediateSignedness(Signedness::SIGNED))
				.expect("failed to set immediate signedness");
			fm.set_property(FormatterProperty::ForceRelativeRiprel(true))
				.expect("failed to force relative RIP");
			fm.set_property(FormatterProperty::AddressSignedness(Signedness::SIGNED))
				.expect("failed to set address signedness");
			fm.set_property(FormatterProperty::ForceRelativeBranches(true))
				.expect("failed to set relative branches");
			fm
		};

		let asm_decoder = Decoder::new(MachineMode::LONG_64, AddressWidth::_64)
			.expect("Failed to create assembly decoder");

		let mut decoded_inst_buffer = [0u8; 200];
		let mut decoded_inst_buffer = OutputBuffer::new(&mut decoded_inst_buffer[..]);

		for (inst, ip) in asm_decoder.instruction_iterator(fptr, 0) {
			asm_formatter
				.format_instruction(&inst, &mut decoded_inst_buffer, Some(ip), None)
				.expect("Failed to format instruction");
			println!("0x{:02x}\t{}", ip, decoded_inst_buffer);
		}
	} else {
		println!("Function {} not found", fname)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use std::{mem, path::Path};

	// tests 0, 1, 2, 3, 4, 6, 7, 8, 9, 10
	fn compile_and_run_void_to_int(file: impl AsRef<Path>, fname: &str) -> i32 {
		let src = fs::read_to_string(file).expect("failed to read source code file");
		let tu = frontend::syntax::parse(src.as_str());
		frontend::semantics::check(&tu);

		let mut am = backend::AbstractMachine::new(&tu);
		// let (_, fptr) = am.compiled_function(fname).unwrap();
		let fptr = am.compiled_function(fname).unwrap();

		let fptr = unsafe { mem::transmute::<_, unsafe extern "C" fn() -> i32>(fptr.as_ptr()) };
		unsafe { fptr() }
	}

	// tests 5
	fn compile_and_run_int_to_int(file: impl AsRef<Path>, fname: &str, i: i32) -> i32 {
		let src = fs::read_to_string(file).expect("failed to read source code file");
		let tu = frontend::syntax::parse(src.as_str());
		frontend::semantics::check(&tu);

		let mut am = backend::AbstractMachine::new(&tu);
		// let (_, fptr) = am.compiled_function(fname).unwrap();
		let fptr = am.compiled_function(fname).unwrap();

		let fptr = unsafe { mem::transmute::<_, unsafe extern "C" fn(i32) -> i32>(fptr.as_ptr()) };
		unsafe { fptr(i) }
	}

	#[test]
	fn compile_0() {
		assert_eq!(compile_and_run_void_to_int("tests/0.c", "main"), 12);
	}

	#[test]
	fn compile_1() {
		assert_eq!(compile_and_run_void_to_int("tests/1.c", "foo"), -17);
	}

	#[test]
	fn compile_2() {
		assert_eq!(compile_and_run_void_to_int("tests/2.c", "bar"), -1);
	}

	#[test]
	fn compile_3() {
		assert_eq!(compile_and_run_void_to_int("tests/3.c", "foo"), -6);
	}

	#[test]
	fn compile_4() {
		assert_eq!(compile_and_run_void_to_int("tests/4.c", "foo"), 10);
	}

	#[test]
	fn compile_5() {
		assert_eq!(compile_and_run_int_to_int("tests/5.c", "foo", 10), 11);
	}

	#[test]
	fn compile_6() {
		assert_eq!(compile_and_run_void_to_int("tests/6.c", "bar"), 17);
	}

	#[test]
	fn compile_7() {
		assert_eq!(compile_and_run_void_to_int("tests/7.c", "bar"), 70);
	}

	#[test]
	fn compile_8() {
		assert_eq!(compile_and_run_void_to_int("tests/8.c", "bar"), 3);
	}

	#[test]
	fn compile_9() {
		assert_eq!(compile_and_run_void_to_int("tests/9.c", "bar"), 11);
	}

	#[test]
	fn compile_10() {
		assert_eq!(compile_and_run_void_to_int("tests/10.c", "bar"), 16);
	}

	#[test]
	fn compile_11() {
		assert_eq!(compile_and_run_void_to_int("tests/11.c", "foo"), 14);
	}

	#[test]
	fn compile_12() {
		assert_eq!(compile_and_run_void_to_int("tests/12.c", "foo"), 61);
	}

	#[test]
	fn compile_13() {
		assert_eq!(compile_and_run_void_to_int("tests/13.c", "foo"), 18);
	}
}

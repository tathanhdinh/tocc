use std::path::PathBuf;

use zydis::{
	AddressWidth, Decoder, Formatter, FormatterProperty, FormatterStyle, MachineMode, OutputBuffer,
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
	let (src, fname) = {
		(opt.src.as_path(), opt.fname.as_str())
	};

	let tu = frontend::syntax::parse(src);
	frontend::semantics::check(&tu);

	let mut am = backend::AbstractMachine::new(&tu);
	if let Some((fclif, fptr)) = am.compiled_function(fname) {
		println!("{}", &fclif);

		let asm_formatter = {
			let mut fm =
				Formatter::new(FormatterStyle::INTEL).expect("Failed to create assembly formatter");
			fm.set_property(FormatterProperty::HexUppercase(false))
				.expect("Failed to set assembly formatter property");
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

	// tests 0, 1, 2, 3, 4
	fn compile_and_run_void_to_int(file: impl AsRef<Path>, fname: &str) -> i32 {
		let tu = frontend::syntax::parse(file);
		frontend::semantics::check(&tu);

		let mut am = backend::AbstractMachine::new(&tu);
		let (_, fptr) = am.compiled_function(fname).unwrap();

		let fptr = unsafe { mem::transmute::<_, unsafe extern "C" fn() -> i32>(fptr.as_ptr()) };
		unsafe { fptr() }
	}

	// tests 5
	fn compile_and_run_int_to_int(file: impl AsRef<Path>, fname: &str, i: i32) -> i32 {
		let tu = frontend::syntax::parse(file);
		frontend::semantics::check(&tu);

		let mut am = backend::AbstractMachine::new(&tu);
		let (_, fptr) = am.compiled_function(fname).unwrap();

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
}

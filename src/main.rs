use std::{
	fs::{self, File},
	hint::unreachable_unchecked,
	mem,
	path::PathBuf,
	slice,
	str::FromStr,
};

use cranelift::prelude::*;
use cranelift_faerie::{FaerieBackend, FaerieBuilder, FaerieTrapCollection};
use cranelift_simplejit::{SimpleJITBackend, SimpleJITBuilder};
use target_lexicon::triple;

use gumdrop::Options;
use once_cell::sync::OnceCell;
use zydis::{
	AddressWidth, Decoder, Formatter, FormatterProperty, FormatterStyle, MachineMode, OutputBuffer,
	Signedness,
};

mod backend;
mod frontend;
mod helper;

#[derive(Options)]
struct Opt {
	#[options(help = "print usage")]
	help: bool,

	#[options(free, help = "source code file")]
	src: String,

	#[options(help = "output object file", meta = "output", no_long)]
	out: Option<String>,

	#[options(help = "lightweight obfuscation", no_long)]
	light: bool,

	#[options(
		help = "heavyweight obfuscation",
		meta = "level",
		short = "w",
		no_long,
		default = "0"
	)]
	heavy: u8,

	#[options(help = "verbose", no_long)]
	verbose: bool,

	#[options(help = "function to jit", meta = "function", no_long)]
	fname: Option<String>,

	#[options(help = "jit", no_long)]
	jit: bool,
}

static HEAVY_BLUR: OnceCell<u8> = OnceCell::new();
pub fn heavy() -> u8 { *HEAVY_BLUR.get_or_init(|| 3) }

static LIGHT_BLUR: OnceCell<bool> = OnceCell::new();
pub fn light() -> bool { *LIGHT_BLUR.get_or_init(|| false) }

static VERBOSE: OnceCell<bool> = OnceCell::new();
pub fn verbose() -> bool { *VERBOSE.get_or_init(|| false) }

fn main() {
	let opt = Opt::parse_args_default_or_exit();
	HEAVY_BLUR.set(opt.heavy).unwrap();
	LIGHT_BLUR.set(opt.light).unwrap();
	VERBOSE.set(opt.verbose).unwrap();

	let src_code = fs::read_to_string(&opt.src).expect("failed to read source code file");
	let tu = frontend::syntax::parse(src_code.as_str());
	frontend::semantics::check(&tu);

	if opt.jit {
		let builder = SimpleJITBuilder::new(cranelift_module::default_libcall_names());
		let mut am = backend::AbstractMachine::<'_, SimpleJITBackend>::new(&tu, builder);
		if let Some(fname) = &opt.fname {
			if let Some((fptr, flen)) = am.compiled_function(fname.as_str()) {
				let fptr = unsafe {
					slice::from_raw_parts(mem::transmute::<_, *const u8>(fptr), flen as _)
				};

				let asm_formatter = {
					let mut fm = Formatter::new(FormatterStyle::INTEL)
						.expect("failed to create assembly formatter");
					fm.set_property(FormatterProperty::HexUppercase(false))
						.expect("failed to disable hex uppercase");
					fm.set_property(FormatterProperty::DisplacementSignedness(Signedness::SIGNED))
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
					.expect("failed to create assembly decoder");

				let mut decoded_inst_buffer = [0u8; 200];
				let mut decoded_inst_buffer = OutputBuffer::new(&mut decoded_inst_buffer[..]);

				for (inst, ip) in asm_decoder.instruction_iterator(fptr, 0) {
					asm_formatter
						.format_instruction(&inst, &mut decoded_inst_buffer, Some(ip), None)
						.expect("failed to format instruction");
					println!("0x{:02x}\t{}", ip, decoded_inst_buffer);
				}
			} else {
				println!("function {} not found", fname)
			}
		}
	} else {
		let output = {
			if let Some(out) = opt.out {
				out
			} else {
				let mut src = PathBuf::from(opt.src);
				src.set_extension("o");
				let output = checked_unwrap_option!(src.file_name());
				checked_unwrap_option!(output.to_str()).to_owned()
			}
		};

		let isa = {
			let flag_builder = {
				let mut fb = settings::builder();
				checked_unwrap_result!(fb.enable("is_pic"));
				fb
			};

			let isa_bulder =
				checked_unwrap_result!(isa::lookup(triple!("x86_64-unknown-linux-elf")));
			isa_bulder.finish(settings::Flags::new(flag_builder))
		};

		let builder = FaerieBuilder::new(
			isa,
			output,
			FaerieTrapCollection::Disabled,
			cranelift_module::default_libcall_names(),
		)
		.expect("cannot create backend builder");
		let am = backend::AbstractMachine::<'_, FaerieBackend>::new(&tu, builder);

		let product = am.finish();
		let file = File::create(product.name()).expect("failed to create output file");
		product.write(file).expect("failed to write output file");
	}
}

#[cfg(test)]
mod compilation_tests {
	use super::*;
	use std::{mem, path::Path};

	// fn() -> i32
	fn compile_and_run_void_to_int(file: impl AsRef<Path>, fname: &str) -> i32 {
		let src = fs::read_to_string(file).expect("failed to read source code file");
		let tu = frontend::syntax::parse(src.as_str());
		frontend::semantics::check(&tu);

		let builder = SimpleJITBuilder::new(cranelift_module::default_libcall_names());
		let mut am = backend::AbstractMachine::<'_, SimpleJITBackend>::new(&tu, builder);
		let (fptr, _) = am.compiled_function(fname).unwrap();

		let fptr = unsafe { mem::transmute::<_, unsafe extern "C" fn() -> i32>(fptr) };
		unsafe { fptr() }
	}

	// fn(i32) -> i32
	fn compile_and_run_int_to_int(file: impl AsRef<Path>, fname: &str, i: i32) -> i32 {
		let src = fs::read_to_string(file).expect("failed to read source code file");
		let tu = frontend::syntax::parse(src.as_str());
		frontend::semantics::check(&tu);

		let builder = SimpleJITBuilder::new(cranelift_module::default_libcall_names());
		let mut am = backend::AbstractMachine::<'_, SimpleJITBackend>::new(&tu, builder);
		let (fptr, _) = am.compiled_function(fname).unwrap();

		let fptr = unsafe { mem::transmute::<_, unsafe extern "C" fn(i32) -> i32>(fptr) };
		let i = unsafe { fptr(i) };
		i
	}

	fn compile_and_run_int_int_to_int(file: impl AsRef<Path>, fname: &str, i: i32, j: i32) -> i32 {
		let src = fs::read_to_string(file).expect("failed to read source code file");
		let tu = frontend::syntax::parse(src.as_str());
		frontend::semantics::check(&tu);

		let builder = SimpleJITBuilder::new(cranelift_module::default_libcall_names());
		let mut am = backend::AbstractMachine::<'_, SimpleJITBackend>::new(&tu, builder);
		let (fptr, _) = am.compiled_function(fname).unwrap();

		let fptr = unsafe { mem::transmute::<_, unsafe extern "C" fn(i32, i32) -> i32>(fptr) };
		unsafe { fptr(i, j) }
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

	#[test]
	fn compile_14() {
		assert_eq!(compile_and_run_int_int_to_int("tests/14.c", "foo", 7, 8), 3);
	}

	#[test]
	fn compile_15() {
		assert_eq!(compile_and_run_int_to_int("tests/15.c", "foobar", 17), 452);
	}

	#[test]
	fn compile_16() {
		assert_eq!(compile_and_run_int_to_int("tests/16.c", "foo", 0), 4);
	}

	#[test]
	fn compile_17() {
		assert_eq!(compile_and_run_int_to_int("tests/17.c", "fibo", 6), 8);
	}

	#[test]
	fn compile_18() {
		assert_eq!(compile_and_run_int_to_int("tests/18.c", "sum_0n", 4), 10);
	}

	#[test]
	fn compile_19() {
		assert_eq!(compile_and_run_int_to_int("tests/19.c", "collatz", 5), 4);
	}
}

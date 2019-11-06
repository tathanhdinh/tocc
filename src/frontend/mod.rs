// Front-end:
//  - lexer/parser
//  - semantics analysis

use std::{fs, path::Path};

pub mod ast;
use ast::{parser, TranslationUnit};

pub fn ast(src_file: impl AsRef<Path>) -> TranslationUnit {
	let src_code =
		fs::read_to_string(src_file).expect("Failed to read source code file");
	if let Ok(tu) = parser::parse(&src_code) {
		tu
	} else {
		panic!("Failed to parse source code")
	}
}

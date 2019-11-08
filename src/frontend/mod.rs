// Front-end:
//  - syntax analysis
//  - semantics analysis

use std::{fs, path::Path};

mod sem;
pub mod syntax;

use syntax::{parser, TranslationUnit};

pub fn parse(src_file: impl AsRef<Path>) -> TranslationUnit {
	let src_code =
		fs::read_to_string(src_file).expect("Failed to read source code file");
	if let Ok(tu) = parser::parse(&src_code) {
		tu
	} else {
		panic!("Failed to parse source code")
	}
}

pub fn semantic_analysis(tu: &TranslationUnit) {
	sem::check_binding(tu);
	sem::check_kind(tu);
}

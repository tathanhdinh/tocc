use std::{collections::HashMap, hint::unreachable_unchecked};

use cranelift::prelude::*;
use cranelift_codegen::ir::entities::StackSlot;
use cranelift_module::{FuncId, Module};
use cranelift_simplejit::SimpleJITBackend;

use crate::{
	checked_if_let, checked_unwrap,
	frontend::syntax::{Declaration, Declarator, Identifier, StructType, TypeSpecifier},
};

// Engineering a Compiler: 7.7.1 Understanding Structure Layout
// Dragon Book: 6.3.4 Storage Layouts for Local Names
#[derive(Clone)]
pub struct AggregateType<'a> {
	pub fields: Vec<(&'a str, Type)>,
}

impl AggregateType<'_> {
	pub fn field_offset(&self, field_name: &str) -> Option<usize> {
		let mut os = 0usize;
		for (fname, fty) in &self.fields {
			if *fname == field_name {
				return Some(os);
			} else {
				os += fty.bytes() as usize;
			}
		}
		None
	}

	pub fn field_type(&self, field_name: &str) -> Option<Type> {
		let (_, fty) = self.fields.iter().find(|(fname, _)| *fname == field_name)?;
		Some(*fty)
	}

	pub fn bytes(&self) -> usize {
		self.fields.iter().fold(0usize, |sum, (_, fty)| sum + fty.bytes() as usize)
	}
}

impl<'a> Into<AggregateType<'a>> for &'_ StructType<'a> {
	fn into(self) -> AggregateType<'a> {
		// struct type definition: each declaration is a field declaration
		let StructType { declarations, .. } = self;
		let declarations = checked_unwrap!(declarations.as_ref());
		let fields: Vec<(&str, Type)> = declarations
			.iter()
			.map(|Declaration { specifier, declarator }| {
				checked_if_let!(Some(Declarator { ident: Identifier(ident), .. }), declarator, {
					(*ident, specifier.into())
				})
			})
			.collect();
		AggregateType { fields }
	}
}

#[derive(Clone)]
pub struct FunctionType {
	pub return_ty: Type,
	pub param_ty: Vec<Type>,
}

#[derive(Clone)]
pub enum SimpleType<'a> {
	PrimitiveTy(Type),
	AggregateTy(AggregateType<'a>),
	FunctionTy(FunctionType),
	PointerTy(Box<SimpleType<'a>>),
}

#[derive(Clone)]
pub struct PrimitiveIdentifier<'a> {
	pub ident: Variable,
	pub ty: SimpleType<'a>,
}

#[derive(Clone)]
pub struct FunctionIdentifier<'a> {
	pub ident: FuncId,
	pub ty: SimpleType<'a>,
}

#[derive(Clone)]
pub struct AggregateIdentifier<'a> {
	pub ident: StackSlot,
	pub ty: SimpleType<'a>,
}

#[derive(Clone)]
pub struct PointerIdentifer<'a> {
	pub ident: Variable,
	pub ty: SimpleType<'a>,
}

#[derive(Clone)]
pub enum SimpleTypedIdentifier<'a> {
	PrimitiveIdent(PrimitiveIdentifier<'a>),
	AggregateIdent(AggregateIdentifier<'a>),
	FunctionIdent(FunctionIdentifier<'a>),
	PointerIdent(PointerIdentifer<'a>),
}

impl Into<Type> for &TypeSpecifier<'_> {
	fn into(self) -> Type {
		use TypeSpecifier::*;
		match self {
			CharTy => types::I8,
			ShortTy => types::I16,
			IntTy => types::I32,
			LongTy => types::I64,
			_ => unsafe { unreachable_unchecked() },
		}
	}
}

// binding context
pub type NameBindingEnvironment<'a> = HashMap<&'a str, SimpleTypedIdentifier<'a>>;

// visible types
pub type TypeBindingEnvironment<'a> = HashMap<&'a str, SimpleType<'a>>;

// backend-ed module
pub type ConcreteModule = Module<SimpleJITBackend>;

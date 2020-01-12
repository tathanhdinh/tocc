use std::{
	collections::HashMap,
	hint::unreachable_unchecked,
	ops::{Add, Rem},
};

use cranelift::prelude::*;
use cranelift_codegen::ir::entities::StackSlot;
use cranelift_module::FuncId;

use rand::{thread_rng, Rng};

use crate::{
	checked_if_let, checked_unwrap_option,
	frontend::syntax::{
		BinaryOperator, BinaryOperatorExpression, Constant, Declaration, Declarator, Expression,
		Identifier, StructType, TypeSpecifier, UnaryOperator, UnaryOperatorExpression,
	},
};

pub enum SimpleConcreteType {
	ConstantTy(i64),
	ValueTy(Value),
	StackSlotTy(StackSlot),
	UnitTy,
}
// EaC 7.7.1 Understanding Structure Layout
// DRAGON 6.3.4 Storage Layouts for Local Names
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
		let declarations = checked_unwrap_option!(declarations.as_ref());
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
	pub return_ty: Option<Type>,
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
// pub type JitModule = Module<SimpleJITBackend>;

pub fn evaluate_constant_arithmetic_expression(expr: &'_ Expression) -> Option<i64> {
	use Expression::*;

	match expr {
		ConstantExpr(Constant::IntegerConst(i)) => Some(i.into()),

		UnaryOperatorExpr(UnaryOperatorExpression { operator, operand }) => {
			use UnaryOperator::*;

			let val = evaluate_constant_arithmetic_expression(operand.as_ref())?;
			match operator {
				Negation => Some(-val),
				PreIncrement => Some(val + 1),
				PostIncrement => Some(val),
				Address => None,
			}
		}

		BinaryOperatorExpr(BinaryOperatorExpression { operator, lhs, rhs }) => {
			use BinaryOperator::*;

			let lval = evaluate_constant_arithmetic_expression(lhs.as_ref())?;
			let rval = evaluate_constant_arithmetic_expression(rhs.as_ref())?;
			match operator {
				Multiplication => Some(lval * rval),
				Division => Some(lval / rval),
				Addition => Some(lval + rval),
				Subtraction => Some(lval - rval),
				_ => None,
			}
		}

		_ => None,
	}
}

pub fn generate_random_partition(sum: u32) -> Vec<Type> {
	let mut partition = Vec::new();
	let mut rng = thread_rng();
	let mut current_sum = sum;
	loop {
		if current_sum == 0 {
			break;
		}

		let num = rng.gen_range(1, current_sum + 1);
		match num {
			1 => partition.push(types::I8),
			2 => partition.push(types::I16),
			4 => partition.push(types::I32),
			_ => {
				continue;
			}
		}

		current_sum -= num;
	}

	partition
}

pub fn generate_random_maps_bv8() -> (u8, u8, u8, u8) {
	let mut rng = thread_rng();
	let a0 = {
		let a: u8 = rng.gen();
		if a % 2 == 0 {
			a + 1
		} else {
			a
		}
	};
	let a1 = {
		let mut a1 = a0;
		loop {
			if a1.wrapping_mul(a0) == 1 {
				break;
			}
			a1 = a1.wrapping_mul(a0);
		}
		a1
	};
	let b0: u8 = rng.gen();
	let b1 = a1.wrapping_mul(b0).wrapping_neg();

	(a0, b0, a1, b1)
}

pub fn generate_random_maps_bv16() -> (u16, u16, u16, u16) {
	let mut rng = thread_rng();
	let a0 = {
		let a: u16 = rng.gen();
		if a % 2 == 0 {
			a + 1
		} else {
			a
		}
	};
	let a1 = {
		let mut a1 = a0;
		loop {
			if a1.wrapping_mul(a0) == 1 {
				break;
			}
			a1 = a1.wrapping_mul(a0);
		}
		a1
	};
	let b0: u16 = rng.gen();
	let b1 = a1.wrapping_mul(b0).wrapping_neg();

	(a0, b0, a1, b1)
}

pub fn generate_random_maps_bv32() -> (u32, u32, u32, u32) {
	let mut rng = thread_rng();
	let a0 = {
		let a: u32 = rng.gen();
		if a % 2 == 0 {
			a + 1
		} else {
			a
		}
	};
	let a1 = {
		let mut a1 = a0;
		loop {
			if a1.wrapping_mul(a0) == 1 {
				break;
			}
			a1 = a1.wrapping_mul(a0);
		}
		a1
	};
	let b0: u32 = rng.gen();
	let b1 = a1.wrapping_mul(b0).wrapping_neg();

	(a0, b0, a1, b1)
}

#[macro_export]
macro_rules! generate_random_maps {
	($ty:ty) => {
		{
			use rand::{thread_rng, Rng};
			let mut rng = thread_rng();
			let a0 = {
				let a: $ty = rng.gen();
				if a % 2 == 0 {
					a + 1
				} else {
					a
				}
			};
			let a1 = {
				let mut a1 = a0;
				loop {
					if a1.wrapping_mul(a0) == 1 {
						break;
					}
					a1 = a1.wrapping_mul(a0);
				}
				a1
			};
			let b0: $ty = rng.gen();
			let b1 = a1.wrapping_mul(b0).wrapping_neg();

			(a0, b0, a1, b1)
		}
	}
}

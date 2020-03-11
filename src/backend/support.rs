use std::{collections::HashMap, hint::unreachable_unchecked};

use cranelift::prelude::*;
use cranelift_codegen::ir::entities::StackSlot;
use cranelift_module::FuncId;

use rand::{thread_rng, Rng};

use crate::{
	checked_if_let, checked_unwrap_option,
	frontend::{
		semantics::Environment,
		syntax::{
			BinaryOperator, BinaryOperatorExpression, Constant, Declaration, Declarator,
			Expression, Identifier, StructType, TypeSpecifier, UnaryOperator,
			UnaryOperatorExpression,
		},
	},
};

#[derive(Debug)]
pub enum ConcreteValue {
	ConstantTy(i64),
	ValueTy(Value),
	#[allow(unused)]
	StackSlotTy(StackSlot),
	Unit,
}

#[derive(Debug)]
pub struct SimpleTypedConcreteValue<'a> {
	pub ty: EffectiveType<'a>,
	pub val: ConcreteValue,
}
// EaC 7.7.1 Understanding Structure Layout
// DRAGON 6.3.4 Storage Layouts for Local Names
#[derive(Clone, Debug, PartialEq, Eq)]
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

#[derive(Clone, Debug, PartialEq)]
pub enum CType {
	Signed(Type),
	Unsigned(Type),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionType {
	pub return_ty: Option<CType>,
	pub param_ty: Vec<CType>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum EffectiveType<'a> {
	PrimitiveTy(CType),
	AggregateTy(AggregateType<'a>),
	FunctionTy(FunctionType),
	PointerTy(Box<EffectiveType<'a>>),
	UnitTy,
}

#[derive(Clone, Debug)]
pub struct PrimitiveIdentifier<'a> {
	pub ident: Variable,
	pub ty: EffectiveType<'a>,
}

#[derive(Clone, Debug)]
pub struct FunctionIdentifier<'a> {
	pub ident: FuncId,
	pub ty: EffectiveType<'a>,
}

#[derive(Clone, Debug)]
pub struct AggregateIdentifier<'a> {
	pub ident: StackSlot,
	pub ty: EffectiveType<'a>,
}

#[derive(Clone, Debug)]
pub struct PointerIdentifer<'a> {
	pub ident: Variable,
	pub ty: EffectiveType<'a>,
}

#[derive(Clone, Debug)]
pub enum SimpleTypedIdentifier<'a> {
	PrimitiveIdent(PrimitiveIdentifier<'a>),
	AggregateIdent(AggregateIdentifier<'a>),
	FunctionIdent(FunctionIdentifier<'a>),
	PointerIdent(PointerIdentifer<'a>),
}

impl Into<CType> for &TypeSpecifier<'_> {
	fn into(self) -> CType {
		use TypeSpecifier::*;
		use CType::*;
		match self {
			CharTy => Signed(types::I8),
			UCharTy => Unsigned(types::I8),
			ShortTy => Signed(types::I16),
			UShortTy => Unsigned(types::I16),
			IntTy => Signed(types::I32),
			UIntTy => Unsigned(types::I32),
			LongTy | ULongTy => types::I64,
			_ => unsafe { unreachable_unchecked() },
		}
	}
}

// binding context
pub type NameBindingEnvironment<'a> = Environment<'a, &'a str, SimpleTypedIdentifier<'a>>;

// visible types
pub type TypeBindingEnvironment<'a> = HashMap<&'a str, EffectiveType<'a>>;

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
				Indirection => unsafe { unreachable_unchecked() },
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
			// 8 => partition.push(types::I64),
			// 4 => {
			// 	if heavy() != 0 {
			// 		partition.push(types::I32)
			// 	} else {
			// 		continue;
			// 	}
			// }
			_ => {
				continue;
			}
		}

		current_sum -= num;
	}

	partition
}

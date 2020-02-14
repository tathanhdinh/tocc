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
	heavy,
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionType {
	pub return_ty: Option<Type>,
	pub param_ty: Vec<Type>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum EffectiveType<'a> {
	PrimitiveTy(Type),
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
			4 => {
				if heavy() {
					partition.push(types::I32)
				} else {
					continue;
				}
			}
			_ => {
				continue;
			}
		}

		current_sum -= num;
	}

	partition
}

// P(x) = a0 * x + b0
// Q(x) = a1 *x + b1
// Q(P(x)) = x (i.e. Q = P^(-1))
// #[macro_export]
// macro_rules! generate_linear_maps {
// 	($ty:ty) => {{
// 		use rand::{thread_rng, Rng};
// 		let mut rng = thread_rng();
// 		let a0 = {
// 			let a: $ty = rng.gen();
// 			if a % 2 == 0 { a + 1 } else { a }
// 			};
// 		let a1 = {
// 			let mut a1 = a0;
// 			loop {
// 				let a1a0 = a1.wrapping_mul(a0);
// 				if a1a0 == 1 {
// 					break;
// 				}
// 				a1 = a1a0;
// 				}
// 			a1
// 			};
// 		let b0: $ty = rng.gen();
// 		let b1 = a1.wrapping_mul(b0).wrapping_neg();

// 		(a0, b0, a1, b1)
// 		}};
// }

// Back-end:
//  - register allocation
//  - machine code generation

use std::mem;

use cranelift::prelude::*;
use cranelift_module::{Linkage, Module};
use cranelift_simplejit::{SimpleJITBackend, SimpleJITBuilder};

use crate::frontend::ast::{
	BinaryOperator, BinaryOperatorExpression, Constant, Expression,
	FunctionDefinition, Identifier, Integer, Statement, TranslationUnit,
	TypeSpecifier,
};

fn translate(expr: &Expression, fb: &mut FunctionBuilder) -> Value {
	use Expression::*;
	match expr {
		BinaryOperatorExpr(BinaryOperatorExpression { op, lhs, rhs }) => {
			let lhs = translate(lhs, fb);
			let rhs = translate(rhs, fb);

			use BinaryOperator::*;
			match op {
				Mul => fb.ins().imul(lhs, rhs),

				Div => fb.ins().sdiv(lhs, rhs),

				Add => fb.ins().iadd(lhs, rhs),

				Sub => fb.ins().isub(lhs, rhs),
			}
		}

		ConstantExpr(Constant::IntegerConst(Integer(i))) => {
			fb.ins().iconst(types::I64, *i)
		}
	}
}

pub fn compile(
	tu: &TranslationUnit,
) -> (Box<unsafe extern "C" fn() -> i64>, usize) {
	use Statement::*;
	if let TranslationUnit::FunctionDefinition(FunctionDefinition {
		specifier: TypeSpecifier::Int,
		declarator: Identifier(i),
		body: Statement::CompoundStmt(s),
	}) = tu
	{
		if let ReturnStmt(Some(expr)) = &s[0] {
			let builder = SimpleJITBuilder::new(
				cranelift_module::default_libcall_names(),
			);
			let mut module = Module::<SimpleJITBackend>::new(builder);
			let mut context = module.make_context();
			context
				.func
				.signature
				.returns
				.push(AbiParam::new(types::I64));

			// layout
			let mut fbc = FunctionBuilderContext::new();
			let mut fb = FunctionBuilder::new(&mut context.func, &mut fbc);
			let ebb = fb.create_ebb();
			fb.switch_to_block(ebb);

			let return_value = translate(expr, &mut fb);
			fb.ins().return_(&[return_value]);

			// finalize function
			fb.seal_block(ebb);
			fb.finalize();

			let fid = module
				.declare_function(i, Linkage::Export, &context.func.signature)
				.expect("Failed to declare function");
			let flen = module
				.define_function(fid, &mut context)
				.expect("Failed to define function");

			module.clear_context(&mut context);
			// SELinux workaround: "sudo setenforce 0"
			module.finalize_definitions();

			let fptr = module.get_finalized_function(fid);
			let fptr = unsafe { mem::transmute::<_, _>(fptr) };

			(Box::new(fptr), flen as _)
		} else {
			panic!("Failed to compile compound statement");
		}
	} else {
		panic!("Failed to compile translation unit");
	}
}


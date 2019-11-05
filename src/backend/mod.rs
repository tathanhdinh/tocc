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
	TypeSpecifier, UnaryOperator, UnaryOperatorExpression,
};

fn translate_expression(expr: &Expression, fb: &mut FunctionBuilder) -> Value {
	use Expression::*;
	match expr {
		UnaryOperatorExpr(UnaryOperatorExpression { op, rhs }) => {
			let rhs = translate_expression(rhs, fb);

			use UnaryOperator::*;
			match op {
				Neg => {
					let lhs = fb.ins().iconst(types::I64, 0);
					fb.ins().isub(lhs, rhs)
				}
			}
		}

		BinaryOperatorExpr(BinaryOperatorExpression { op, lhs, rhs }) => {
			let lhs = translate_expression(lhs, fb);
			let rhs = translate_expression(rhs, fb);

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

fn translate_statement(stmt: &Statement, fb: &mut FunctionBuilder) {
	use Statement::*;
	match stmt {
		CompoundStmt(stmts) => {
			for s in stmts.iter() {
				translate_statement(s, fb);
			}
		}

		ReturnStmt(opt_expr) => {
			if let Some(expr) = opt_expr {
				let v = translate_expression(expr, fb);
				fb.ins().return_(&[v]);
			}
		}
	}
}

pub fn compile(
	tu: &TranslationUnit,
) -> (Box<unsafe extern "C" fn() -> i64>, usize) {
	let TranslationUnit::FunctionDefinition(FunctionDefinition {
		specifier: TypeSpecifier::Int,
		declarator: Identifier(i),
		// body: Statement::CompoundStmt(s),
		body,
	}) = tu;
	let builder =
		SimpleJITBuilder::new(cranelift_module::default_libcall_names());
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

	translate_statement(body, &mut fb);

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
}

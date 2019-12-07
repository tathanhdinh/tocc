// semantics analysis

use std::{
	collections::{HashMap, HashSet},
	hint::unreachable_unchecked,
	sync::atomic::{AtomicUsize, Ordering},
};

use super::syntax::{
	BinaryOperator, BinaryOperatorExpression, Declaration, Declarator, Expression,
	ExternalDeclaration, FunctionDeclarator, FunctionDefinition, Identifier, IfStatement,
	Statement, StructType, TranslationUnit, TypeSpecifier, UnaryOperatorExpression,
};

use crate::{checked_if_let, checked_match, checked_unwrap, error, unimpl};

type NameBindingEnvironment<'a> = HashMap<&'a str, bool>;
type TypeBindingEnvironment<'a> = HashMap<&'a str, bool>;

fn check_binding_declaration<'a>(
	decl: &'a Declaration<'a>, name_env: &'_ mut NameBindingEnvironment<'a>,
	type_env: &'_ mut TypeBindingEnvironment<'a>,
) {
	let Declaration { specifier, declarator } = decl;
	if let Some(Declarator { ident: Identifier(var_name), .. }) = declarator {
		if name_env.contains_key(var_name) {
			if name_env[var_name] {
				// cannot rebound by an identifer in the same scope
				error!("variable {} already exists in the same scope", var_name)
			} else {
				// rebound the identifier in the outer scope
				*name_env.get_mut(var_name).unwrap() = true;
			}
		} else {
			name_env.insert(var_name, false);
		}
	} else {
		// should be some struct type declaration
		use TypeSpecifier::*;
		match specifier {
			StructTy(StructType { identifier: Identifier(ty_name), declarations }) => {
				if type_env.contains_key(ty_name) {
					if declarations.is_some() {
						*type_env.get_mut(ty_name).unwrap() = true;
					}
				} else {
					if declarations.is_none() {
						error!("struct {}'s definition not found", ty_name)
					} else {
						type_env.insert(ty_name, false);
					}
				}
			}
			_ => error!("identifier not found"),
		}
	}
}

fn check_binding_at_expression(expr: &'_ Expression, env: &'_ NameBindingEnvironment) {
	use Expression::*;
	match expr {
		IdentifierExpr(Identifier(i)) => {
			if !env.contains_key(i) {
				error!("variable {} doesn't exist", i)
			}
		}

		UnaryOperatorExpr(UnaryOperatorExpression { rhs, .. }) => {
			check_binding_at_expression(rhs.as_ref(), env);
		}

		BinaryOperatorExpr(BinaryOperatorExpression { rhs, lhs, .. }) => {
			check_binding_at_expression(lhs.as_ref(), env);
			check_binding_at_expression(rhs.as_ref(), env);
		}

		_ => {}
	}
}

fn check_binding_at_statement<'a>(
	stmt: &'a Statement, name_env: &'_ mut NameBindingEnvironment<'a>,
	type_env: &'_ mut TypeBindingEnvironment<'a>,
) {
	use Statement::*;
	match stmt {
		CompoundStmt(stmts) => {
			let mut local_name_env = name_env.clone();
			for (_, val) in local_name_env.iter_mut() {
				*val = false;
			}

			let mut local_type_env = type_env.clone();
			for (_, val) in local_type_env.iter_mut() {
				*val = false;
			}

			for stmt in stmts {
				check_binding_at_statement(stmt, &mut local_name_env, &mut local_type_env);
			}
		}

		IfStmt(IfStatement { condition, then_statement, else_statement }) => {
			check_binding_at_expression(condition, name_env);
			check_binding_at_statement(then_statement.as_ref(), name_env, type_env);
			if let Some(stmt) = else_statement {
				check_binding_at_statement(stmt.as_ref(), name_env, type_env);
			}
		}

		ReturnStmt(expr) => {
			if let Some(expr) = expr {
				check_binding_at_expression(expr, name_env);
			}
		}

		DeclarationStmt(decl) => check_binding_declaration(decl, name_env, type_env),

		ExpressionStmt(expr) => {
			if let Some(expr) = expr {
				check_binding_at_expression(expr, name_env);
			}
		}
	}
}

// C11 Standard: 6.2.1 Scope of identifiers
// Tiger book: 5.1 Symbol tables
//
// Functional style environment (i.e. symbol table) checking
// Initialize a global environment as a HashMap: identifier -> bool, all value set to false
// In a scope:
//   - for each binding, check if the identifer is in the symbol table,
//   - no: add it into the map, set its value to false (i.e. no rebind yet)
//   - yes: check if it is fresh:
//       - yes: set its value to true, i.e. rebound some identifier from the outer scope
//       - no: error, an identifer cannot rebound by some identifer in the same scope
// Before going to a nested scope:
//   - duplicate the outer environment, all value set to true
fn check_binding(tu: &'_ TranslationUnit) {
	// global contexts
	let mut name_env = NameBindingEnvironment::new();
	let mut type_env = TypeBindingEnvironment::new();

	let TranslationUnit(eds) = tu;
	for ed in eds {
		use ExternalDeclaration::*;
		match ed {
			FunctionDefinitionDecl(FunctionDefinition {
				declarator: FunctionDeclarator { identifier: Identifier(fname), parameters },
				body,
				..
			}) => {
				// check name binding context
				if name_env.contains_key(fname) {
					error!("function {} already exists in the same scope", fname);
				} else {
					name_env.insert(fname, false);
					for decl in parameters {
						check_binding_declaration(decl, &mut name_env, &mut type_env);
					}
				}
				check_binding_at_statement(body, &mut name_env, &mut type_env)
			}

			Decl(decl) => {
				check_binding_declaration(decl, &mut name_env, &mut type_env);
			}
		}
	}
}

fn check_lr_value_statement<'a>(
	stmt: &'a Statement<'a>, bounded_identifiers: &'_ mut HashSet<&'a str>,
) {
	use Statement::*;
	match stmt {
		CompoundStmt(stmts) => {
			let mut local_bounded_identifiers = bounded_identifiers.clone();
			for stmt in stmts {
				check_lr_value_statement(stmt, &mut local_bounded_identifiers);
			}
		}

		DeclarationStmt(Declaration { declarator, .. }) => {
			if let Some(Declarator { ident: Identifier(i), .. }) = declarator {
				bounded_identifiers.insert(i);
			}
		}

		ExpressionStmt(Some(expr)) => {
			use Expression::*;
			match expr {
				BinaryOperatorExpr(BinaryOperatorExpression {
					op: BinaryOperator::Assignment,
					lhs,
					..
				}) => match lhs.as_ref() {
					IdentifierExpr(Identifier(ident)) => {
						if !bounded_identifiers.contains(ident) {
							error!("failed to assign, {} is not a lvalue", ident)
						}
					}
					_ => {}
				},
				_ => {}
			}
		}

		_ => {}
	}
}

fn check_lr_value_function<'a>(
	func: &'a FunctionDefinition<'a>, bounded_identifiers: &'_ HashSet<&str>,
) {
	let FunctionDefinition {
		declarator: FunctionDeclarator {
			parameters,
			// function is not denoted
			..
		},
		body,
		..
	} = func;

	let mut local_bounded_identifiers = bounded_identifiers.clone();
	for Declaration { declarator, .. } in parameters {
		checked_if_let!(Some(Declarator { ident: Identifier(pname), .. }), declarator, {
			local_bounded_identifiers.insert(pname);
		});
	}
	check_lr_value_statement(body, &mut local_bounded_identifiers);
}

// C11 Standard: 6.3.2.1 Lvalue, arrays, and function designators
// Modern Compiler Design: 11.1.2.5 Kind checking
// Dragon book: 2.8.3 Static checking: L-values and R-values
// Essentials of Programming Languages: 3.2.2
fn check_lr_value<'a>(TranslationUnit(eds): &'a TranslationUnit<'a>) {
	use ExternalDeclaration::*;

	// The most simple possible check for denoted (i.e. having location) and expressed values (c.f. EoPL 3.2.2):
	//   - any bounded identifier is denoted
	//   - otherwise it isn't
	let mut bounded_identifiers = HashSet::new();
	for ed in eds {
		match ed {
			FunctionDefinitionDecl(fd) => {
				check_lr_value_function(fd, &bounded_identifiers);
			}

			Decl(Declaration { declarator, .. }) => {
				if let Some(Declarator { ident: Identifier(ident), .. }) = declarator {
					bounded_identifiers.insert(ident);
				}
			}
		}
	}
}

fn check_type<'a>(TranslationUnit(eds): &'a TranslationUnit<'a>) {
	use ExternalDeclaration::*;

	for ed in eds {
		match ed {
			FunctionDefinitionDecl(_) => {}

			Decl(_) => {}
		}
	}
}

pub fn check<'a>(tu: &'a TranslationUnit<'a>) {
	check_binding(tu);
	check_lr_value(tu);
	check_type(tu);
}

static NEW_VAR_INDEX: AtomicUsize = AtomicUsize::new(0);

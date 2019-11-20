// semantics analysis

use std::{
	collections::{HashMap, HashSet},
	hint::unreachable_unchecked,
	sync::atomic::{AtomicUsize, Ordering},
};

use super::syntax::{
	BinaryOperator, BinaryOperatorExpression, Declaration, Expression, ExternalDeclaration,
	FunctionDeclarator, FunctionDefinition, Identifier, Statement, TranslationUnit,
	UnaryOperatorExpression,
};

fn check_binding_declaration_statement<'a>(stmt: &'a Statement, env: &mut HashMap<&'a str, bool>) {
	use Statement::*;
	match stmt {
		DeclarationStmt(Declaration {
			declarator: Identifier(i),
			..
		}) => {
			let i = i.as_str();
			if env.contains_key(i) {
				if env[i] {
					// cannot rebound by an identifer in the same scope
					panic!(format!("Variable {} already exists in the same scope", i))
				} else {
					// rebound the identifier in the outer scope
					*env.get_mut(i).unwrap() = true;
				}
			} else {
				env.insert(i, false);
			}
		}

		_ => unsafe { unreachable_unchecked() },
	}
}

fn check_binding_at_expression(expr: &Expression, env: &HashMap<&str, bool>) {
	use Expression::*;
	match expr {
		IdentifierExpr(Identifier(i)) => {
			if !env.contains_key(i.as_str()) {
				panic!(format!("Variable {} doesn't exist", i))
			}
		}

		UnaryOperatorExpr(UnaryOperatorExpression { rhs, .. }) => {
			check_binding_at_expression(&**rhs, env);
		}

		BinaryOperatorExpr(BinaryOperatorExpression { rhs, lhs, .. }) => {
			check_binding_at_expression(&**lhs, env);
			check_binding_at_expression(&**rhs, env);
		}

		_ => {}
	}
}

fn check_binding_expression_statement(stmt: &Statement, env: &HashMap<&str, bool>) {
	use Statement::*;
	match stmt {
		ExpressionStmt(Some(expr)) => {
			check_binding_at_expression(expr, env);
		}

		_ => unsafe { unreachable_unchecked() },
	}
}

fn check_binding_return_statement(stmt: &Statement, env: &HashMap<&str, bool>) {
	use Statement::*;
	match stmt {
		ReturnStmt(stmt) => {
			if let Some(expr) = stmt {
				check_binding_at_expression(expr, env)
			}
		}

		_ => unsafe { unreachable_unchecked() },
	}
}

fn check_binding_statement<'a>(stmt: &'a Statement, env: &mut HashMap<&'a str, bool>) {
	use Statement::*;
	match stmt {
		CompoundStmt(stmts) => {
			let mut local_env = env.clone();
			for (_, val) in local_env.iter_mut() {
				*val = false;
			}

			for stmt in stmts.iter() {
				match stmt {
					CompoundStmt(_) => check_binding_statement(stmt, &mut local_env),

					ReturnStmt(_) => check_binding_return_statement(stmt, &local_env),

					DeclarationStmt(_) => check_binding_declaration_statement(stmt, &mut local_env),

					ExpressionStmt(_) => check_binding_expression_statement(stmt, &local_env),
				}
			}
		}
		ReturnStmt(_) => check_binding_return_statement(stmt, env),
		DeclarationStmt(_) => check_binding_declaration_statement(stmt, env),
		ExpressionStmt(_) => check_binding_expression_statement(stmt, env),
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
fn check_binding(tu: &TranslationUnit) {
	// global environment
	let mut env = HashMap::new();

	let TranslationUnit(eds) = tu;
	for ed in eds.iter() {
		use ExternalDeclaration::*;
		match ed {
			FunctionDefinitionDecl(FunctionDefinition {
				declarator:
					FunctionDeclarator {
						identifier: Identifier(fname),
						parameters,
					},
				body,
				..
			}) => {
				let fname = fname.as_str();
				if env.contains_key(fname) {
					panic!(format!(
						"Function {} already exists in the same scope",
						fname
					));
				} else {
					env.insert(fname, false);
					for param in parameters.iter() {
						let Declaration {
							declarator: Identifier(pname),
							..
						} = param;
						let pname = pname.as_str();
						if env.contains_key(pname) {
							if env[pname] {
								// cannot rebound by an identifer in the same scope
								panic!(format!(
									"Parameter {} already exists in the same scope",
									pname
								))
							} else {
								// rebound the identifier in the outer scope
								*env.get_mut(pname).unwrap() = true;
							}
						} else {
							env.insert(pname, false);
						}
					}
				}

				check_binding_statement(body, &mut env)
			}

			_ => panic!("Unsupported external declaration"),
		}
	}
}

fn check_value_statement<'a>(stmt: &'a Statement, env: &mut HashSet<&'a str>) {
	use Statement::*;
	match stmt {
		CompoundStmt(stmts) => {
			let mut nested_env = env.clone();
			for stmt in stmts.iter() {
				check_value_statement(stmt, &mut nested_env);
			}
		}

		DeclarationStmt(Declaration {
			declarator: Identifier(i),
			..
		}) => {
			env.insert(i.as_str());
		}

		ExpressionStmt(Some(expr)) => {
			use Expression::*;
			match expr {
				BinaryOperatorExpr(BinaryOperatorExpression {
					op: BinaryOperator::Asg,
					lhs,
					..
				}) => match &**lhs {
					IdentifierExpr(Identifier(ident)) => {
						if !env.contains(ident.as_str()) {
							panic!(format!("Failed to assign since {} is not a lvalue", ident))
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

fn check_value_function(func: &ExternalDeclaration, env: &HashSet<&str>) {
	use ExternalDeclaration::*;
	if let FunctionDefinitionDecl(FunctionDefinition {
		declarator: FunctionDeclarator {
			parameters,
			// TODO: check function
			..
		},
		body,
		..
	}) = func
	{
		let mut env = env.clone();
		for param in parameters.iter() {
			let Declaration {
				declarator: Identifier(pname),
				..
			} = param;
			env.insert(pname.as_str());
		}
		check_value_statement(body, &mut env);
	}
}

// C11 Standard: 6.3.2.1 Lvalue, arrays, and function designators
// Modern Compiler Design: 11.1.2.5 Kind checking
// Dragon book: 2.8.3 Static checking: L-values and R-values
// Essentials of Programming Languages: 3.2.2
fn check_value(tu: &TranslationUnit) {
	// The most simple possible check for denoted (i.e. having location) and expressed values (c.f. EoPL 3.2.2):
	//   - any bounded identifier is denoted
	//   - otherwise it isn't
	let TranslationUnit(eds) = tu;
	for ed in eds.iter() {
		use ExternalDeclaration::*;
		match ed {
			FunctionDefinitionDecl(_) => {
				let env = HashSet::new();
				check_value_function(ed, &env);
			}

			_ => panic!("Unsupported external declaration"),
		}
	}
}

pub fn check(tu: &TranslationUnit) {
	check_binding(tu);
	check_value(tu);
}

static NEW_VAR_INDEX: AtomicUsize = AtomicUsize::new(0);

// semantics analysis

use std::{
	borrow::Borrow,
	cmp,
	collections::{HashMap, HashSet},
	hash::Hash,
	hint::unreachable_unchecked,
	i16, i32, i64, i8,
	marker::PhantomData,
	sync::atomic::{AtomicUsize, Ordering},
};

use super::syntax::{
	BinaryOperator, BinaryOperatorExpression, CallExpression, Constant, Declaration, Declarator,
	DerivedDeclarator, Expression, ExternalDeclaration, FunctionDeclarator, FunctionDefinition,
	Identifier, IfStatement, Integer, MemberExpression, MemberOperator, Statement, StructType,
	TranslationUnit, TypeSpecifier, UnaryOperator, UnaryOperatorExpression,
};

use crate::{checked_if_let, checked_match, checked_unwrap, error, unimpl};

pub struct Environment<'a, K, Ty>
where
	K: 'a + Copy + Eq + Hash,
	Ty: 'a + Clone,
{
	pub env: HashMap<K, BoundedType<Ty>>,
	phantom: PhantomData<&'a K>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct IdentifierName<'a>(&'a str);
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeName<'a>(&'a str);

impl Borrow<str> for &'_ IdentifierName<'_> {
	fn borrow(&self) -> &str {
		self.0
	}
}

impl Borrow<str> for &'_ TypeName<'_> {
	fn borrow(&self) -> &str {
		self.0
	}
}

impl<'a> From<&'a str> for IdentifierName<'a> {
	fn from(i: &'a str) -> Self {
		IdentifierName(i)
	}
}

impl<'a> From<&'_ &'a str> for IdentifierName<'a> {
	fn from(i: &'_ &'a str) -> Self {
		(*i).into()
	}
}

impl<'a> AsRef<str> for IdentifierName<'a> {
	fn as_ref(&self) -> &str {
		self.0
	}
}

impl<'a> From<Identifier<'a>> for IdentifierName<'a> {
	fn from(i: Identifier<'a>) -> Self {
		i.0.into()
	}
}

impl<'a> From<&'_ Identifier<'a>> for IdentifierName<'a> {
	fn from(i: &'_ Identifier<'a>) -> Self {
		(*i).0.into()
	}
}

impl<'a> From<&'a str> for TypeName<'a> {
	fn from(i: &'a str) -> Self {
		TypeName(i)
	}
}

impl<'a> From<&'_ &'a str> for TypeName<'a> {
	fn from(i: &'_ &'a str) -> Self {
		(*i).into()
	}
}

impl<'a> From<&'_ Identifier<'a>> for TypeName<'a> {
	fn from(i: &'_ Identifier<'a>) -> Self {
		(*i).0.into()
	}
}

impl<'a> AsRef<str> for TypeName<'a> {
	fn as_ref(&self) -> &str {
		self.0
	}
}

impl<'a> Into<&'a str> for &'_ Identifier<'a> {
	fn into(self) -> &'a str {
		self.0
	}
}

impl<'a> AsRef<str> for Identifier<'a> {
	fn as_ref(&self) -> &str {
		self.0
	}
}

impl<'a, K, T> Environment<'a, K, T>
where
	K: 'a + Clone + Copy + Eq + Hash + AsRef<str>,
	T: 'a + Clone,
{
	pub fn new() -> Self {
		Self { env: HashMap::new(), phantom: PhantomData }
	}

	pub fn inherit(&self) -> Self {
		let mut inherited_env = self.env.clone();
		for (name, _) in &self.env {
			inherited_env.get_mut(name).unwrap().rebind = false
		}
		Self { env: inherited_env, phantom: PhantomData }
	}

	pub fn bind(&mut self, name: K, ty: T) {
		if self.env.contains_key(&name) && self.env[&name].rebind {
			error!("name already bound in current scope");
		} else {
			self.env.insert(name, BoundedType { ty, rebind: true });
		}
	}

	pub fn get(&self, name: K) -> &T {
		self.env
			.get(&name)
			.map(|BoundedType { ty, .. }| ty)
			.unwrap_or_else(|| error!("name not found in current scope"))
	}
}

// map from indentifier to its type
type BindingEnvironment<'a> = Environment<'a, IdentifierName<'a>, QualifiedSimpleType<'a>>;

// map from type name to type
type TypingEnvironment<'a> = Environment<'a, TypeName<'a>, SimpleType<'a>>;

#[derive(Clone)]
pub struct BoundedType<T: Clone> {
	pub ty: T,
	pub rebind: bool, // false if it's inherited from outer scope
}

#[derive(Clone)]
pub struct BoundedIdentifier<'a> {
	pub ty: QualifiedSimpleType<'a>,
	pub rebind: bool, // false if it's inherited from outer scope
}

#[derive(Clone)]
pub struct QualifiedSimpleType<'a> {
	qualifier: ValueQualifier,
	ty: SimpleType<'a>,
}

#[derive(Clone, PartialEq, Eq)]
pub enum ValueQualifier {
	Denoted,   // lvalue
	Expressed, // rvalue
}

#[derive(Clone)]
pub enum SimpleType<'a> {
	UnitTy,
	PrimitiveTy(PrimitiveType),
	FunctionTy(FunctionType<'a>),
	AggregateTy(AggregateType<'a>),
	PointerTy(Box<SimpleType<'a>>),
}

impl PartialEq for SimpleType<'_> {
	fn eq(&self, other: &'_ Self) -> bool {
		use SimpleType::*;
		match (self, other) {
			(UnitTy, UnitTy)
			| (PrimitiveTy(_), PrimitiveTy(_))
			| (FunctionTy(_), FunctionTy(_))
			| (AggregateTy(_), AggregateTy(_))
			| (PointerTy(_), PointerTy(_)) => true,

			_ => false,
		}
	}
}

impl Eq for SimpleType<'_> {}

impl<'a> SimpleType<'a> {
	pub fn size(&self) -> Option<usize> {
		use SimpleType::*;
		match self {
			UnitTy => None,
			PrimitiveTy(ty) => ty.size(),
			FunctionTy(ty) => ty.size(),
			AggregateTy(ty) => ty.size(),
			PointerTy(_) => Some(8),
		}
	}

	// anything in env is already well-typed, so no need to check again
	pub fn synthesize_expression(
		expr: &'_ Expression<'a>, env: &'_ BindingEnvironment<'a>,
	) -> Self {
		use BinaryOperator::*;
		use Expression::*;
		use MemberOperator::*;
		use SimpleType::*;
		use UnaryOperator::*;

		match expr {
			CallExpr(CallExpression { callee, arguments }) => {
				let QualifiedSimpleType { ty, .. } = env.get(callee.into());
				if let FunctionTy(FunctionType { return_ty, param_ty }) = ty {
					if arguments.len() != param_ty.len() {
						error!("incorrect number of arguments")
					} else {
						for (a_expr, pty) in arguments.iter().zip(param_ty.iter()) {
							if SimpleType::synthesize_expression(a_expr, env) != *pty {
								error!("ill-typed argument")
							}
						}

						return_ty.as_ref().clone()
					}
				} else {
					error!("callee is not of function type")
				}
			}

			MemberExpr(MemberExpression { expression, identifier, operator }) => match expression
				.as_ref()
			{
				IdentifierExpr(ident) => {
					let QualifiedSimpleType { ty, .. } = env.get(ident.into());
					let field_name: &str = identifier.into();
					match operator {
						Direct => match ty {
							AggregateTy(AggregateType { fields }) => {
								if let Some((_, fty)) =
									fields.iter().find(|(fname, _)| *fname == field_name)
								{
									fty.clone()
								} else {
									error!("unknown field name in member expression")
								}
							}

							_ => error!("direct member operator applied on a non-aggregate type"),
						},

						Indirect => match ty {
							PointerTy(ty) => match ty.as_ref() {
								AggregateTy(AggregateType { fields }) => {
									if let Some((_, fty)) =
										fields.iter().find(|(fname, _)| *fname == field_name)
									{
										fty.clone()
									} else {
										error!("unknown field name in member expression")
									}
								}

								_ => error!("pointer's base is not a aggregate type"),
							},

							_ => error!("indirect member operator applied on a non-pointer type"),
						},
					}
				}

				_ => error!("ill-typed expression in member expression"),
			},

			ConstantExpr(c) => {
				// actually, type of a constant depends on the context
				use Constant::*;
				match c {
					IntegerConst(i) => {
						let i: i64 = i.into();
						if i >= i8::MIN as i64 && i <= i8::MAX as i64 {
							Self::PrimitiveTy(PrimitiveType::Char)
						} else if i >= i16::MIN as i64 && i <= i16::MAX as i64 {
							Self::PrimitiveTy(PrimitiveType::Short)
						} else if i >= i32::MIN as i64 && i <= i32::MAX as i64 {
							Self::PrimitiveTy(PrimitiveType::Int)
						} else {
							Self::PrimitiveTy(PrimitiveType::Long)
						}
					}
				}
			}

			IdentifierExpr(ident) => {
				let QualifiedSimpleType { ty, .. } = env.get(ident.into());
				ty.clone()
			}

			UnaryOperatorExpr(UnaryOperatorExpression { operand, operator }) => {
				let operand_ty = Self::synthesize_expression(operand.as_ref(), env);
				match operator {
					Negation | PostIncrement | PreIncrement => match &operand_ty {
						PrimitiveTy(_) => operand_ty,
						FunctionTy(_) | AggregateTy(_) | PointerTy(_) | UnitTy => {
							error!("negation cannot applied on operand")
						}
					},

					Address => {
						match operand.as_ref() {
							IdentifierExpr(_) | MemberExpr(_) => {}
							_ => error!("expression is not a lvalue"),
						}
						Self::PointerTy(Box::new(operand_ty))
					}
				}
			}

			BinaryOperatorExpr(BinaryOperatorExpression { operator, lhs, rhs }) => {
				let lhs_ty = Self::synthesize_expression(lhs.as_ref(), env);
				let rhs_ty = Self::synthesize_expression(rhs.as_ref(), env);
				if lhs_ty == UnitTy || rhs_ty == UnitTy {
					error!("lhs or rhs is of unit type")
				}

				match operator {
					Multiplication | Division | Addition | Subtraction => {
						let lhs_ty: PrimitiveType = if let PrimitiveTy(ty) = lhs_ty {
							ty
						} else {
							error!("operator cannot applied on lhs")
						};
						let rhs_ty: PrimitiveType = if let PrimitiveTy(ty) = rhs_ty {
							ty
						} else {
							error!("operator cannot applied on rhs")
						};

						// type promotion
						PrimitiveTy(cmp::max(lhs_ty, rhs_ty))
					}

					Less | LessOrEqual | Greater | GreaterOrEqual | Equal => {
						let lhs_ty: PrimitiveType = if let PrimitiveTy(ty) = lhs_ty {
							ty
						} else {
							error!("operator cannot applied on lhs")
						};
						let rhs_ty: PrimitiveType = if let PrimitiveTy(ty) = rhs_ty {
							ty
						} else {
							error!("operator cannot applied on rhs")
						};

						PrimitiveTy(cmp::max(lhs_ty, rhs_ty))
					}

					Assignment
					| AdditionAssignment
					| SubtractionAssignment
					| MultiplicationAssignment
					| DivisionAssignment => {
						if lhs_ty == rhs_ty {
							UnitTy
						} else {
							error!("lhs and rhs are not of the same type")
						}
					}
				}
			}
		}
	}

	pub fn from_type_specifier(
		ty: &'_ TypeSpecifier<'a>, env: &'_ mut TypingEnvironment<'a>,
	) -> Self {
		use TypeSpecifier::*;
		match ty {
			CharTy | ShortTy | IntTy | LongTy => Self::PrimitiveTy(ty.into()),

			StructTy(StructType { identifier, declarations }) => {
				if let Some(declarations) = declarations {
					// new struct definition
					let fields: Vec<_> = declarations
						.iter()
						.map(|decl| {
							let (fname, fty) = Self::parse_declaration(decl, env, None);
							(checked_unwrap!(fname), fty)
						})
						.collect();

					// let sname = sname.into();
					env.bind(identifier.into(), Self::AggregateTy(AggregateType { fields }));
				}

				env.get(identifier.into()).clone()
			}
		}
	}

	pub fn parse_declaration(
		decl: &'_ Declaration<'a>, type_env: &'_ mut TypingEnvironment<'a>,
		bind_env: Option<&'_ BindingEnvironment>,
	) -> (Option<&'a str>, Self) {
		let Declaration { specifier, declarator } = decl;
		let base_ty = Self::from_type_specifier(&specifier, type_env);
		if let Some(Declarator { derived, ident: Identifier(name), initializer }) =
			declarator.as_ref()
		{
			let ident_ty = if let Some(derived) = derived {
				match derived {
					DerivedDeclarator::Pointer => Self::PointerTy(Box::new(base_ty)),
				}
			} else {
				base_ty
			};

			if let Some(bind_env) = bind_env {
				if let Some(initializer) = initializer.as_ref() {
					let init_ty = SimpleType::synthesize_expression(initializer, bind_env);
					if init_ty != ident_ty {
						error!("initializer and variable are not the same type")
					}
				}
			}

			(Some(*name), ident_ty)
		} else {
			(None, base_ty)
		}
	}
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum PrimitiveType {
	Char,
	Short,
	Int,
	Long,
}

impl PrimitiveType {
	pub fn size(&self) -> Option<usize> {
		use PrimitiveType::*;
		match self {
			Char => Some(1),
			Short => Some(2),
			Int => Some(4),
			Long => Some(8),
		}
	}
}

impl Into<PrimitiveType> for &'_ TypeSpecifier<'_> {
	fn into(self) -> PrimitiveType {
		use PrimitiveType::*;
		use TypeSpecifier::*;
		match self {
			CharTy => Char,
			ShortTy => Short,
			IntTy => Int,
			LongTy => Long,
			StructTy(_) => unsafe { unreachable_unchecked() },
		}
	}
}

#[derive(Clone)]
pub struct FunctionType<'a> {
	pub return_ty: Box<SimpleType<'a>>,
	pub param_ty: Vec<SimpleType<'a>>,
}

impl FunctionType<'_> {
	pub fn size(&self) -> Option<usize> {
		None
	}
}

#[derive(Clone)]
pub struct AggregateType<'a> {
	pub fields: Vec<(&'a str, SimpleType<'a>)>,
}

impl AggregateType<'_> {
	pub fn size(&self) -> Option<usize> {
		let sizes: Option<Vec<usize>> = self.fields.iter().map(|(_, sty)| sty.size()).collect();
		sizes.map(|sizes| sizes.iter().sum())
	}
}

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

		UnaryOperatorExpr(UnaryOperatorExpression { operand, .. }) => {
			check_binding_at_expression(operand.as_ref(), env);
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

		ForStmt(_) => {
			// TODO
		}

		WhileStmt(_) => {
			// TODO
		}

		DoWhileStmt(_) => {
			// TODO
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
					operator: BinaryOperator::Assignment,
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

	// The most simple possible check for denoted (i.e. having location)
	// and expressed values (c.f. EoPL 3.2.2):
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

pub fn check_statement<'a>(
	stmt: &'_ Statement<'a>, bind_env: &'_ mut BindingEnvironment<'a>,
	type_env: &'_ mut TypingEnvironment<'a>, return_ty: &'_ SimpleType<'a>,
) {
	use BinaryOperator::*;
	use Expression::*;
	use SimpleType::*;
	use Statement::*;
	use ValueQualifier::*;

	match stmt {
		ExpressionStmt(expr) => {
			if let Some(expr) = expr {
				if SimpleType::synthesize_expression(expr, bind_env) != UnitTy {
					error!("unit type expected for expression statement")
				}

				// check also value qualifier
				match expr {
					BinaryOperatorExpr(BinaryOperatorExpression { operator, lhs, .. }) => {
						match operator {
							Assignment
							| AdditionAssignment
							| SubtractionAssignment
							| MultiplicationAssignment
							| DivisionAssignment => match lhs.as_ref() {
								IdentifierExpr(lhs_ident) => {
									let QualifiedSimpleType { qualifier, .. } =
										bind_env.get(lhs_ident.into());
									if *qualifier == Expressed {
										error!("lhs must be a denoted value")
									}
								}

								MemberExpr(MemberExpression { expression, .. }) => {
									match expression.as_ref() {
										IdentifierExpr(lhs_ident) => {
											let QualifiedSimpleType { qualifier, .. } =
												bind_env.get(lhs_ident.into());
											if *qualifier == Expressed {
												error!("lhs must be a denoted value")
											}
										}

										_ => error!("lhs must be a denoted value"),
									}
								}

								_ => unimpl!("unsupported lhs"),
							},

							_ => unsafe { unreachable_unchecked() },
						}
					}

					_ => {}
				}
			}
		}

		ReturnStmt(expr) => {
			// return some expression, so return type must not unit, event if
			// the returned expression has type unit (because of C)
			if let Some(expr) = expr {
				if *return_ty == UnitTy {
					error!("return type is unit, but return statement has some expression")
				} else {
					let expr_ty = SimpleType::synthesize_expression(expr, bind_env);
					if *return_ty != expr_ty {
						error!("returned expression ill-typed")
					}
				}
			}
		}

		DeclarationStmt(declaration) => {
			let Declaration { specifier, declarator } = declaration;
			if declarator.is_some() {
				let (ident_name, ident_ty) =
					SimpleType::parse_declaration(declaration, type_env, Some(bind_env));
				if let Some(ident_name) = ident_name {
					bind_env.bind(
						ident_name.into(),
						QualifiedSimpleType { qualifier: Denoted, ty: ident_ty },
					)
				}
			} else {
				// some new struct definition
				SimpleType::from_type_specifier(specifier, type_env);
			}
		}

		IfStmt(IfStatement { condition, .. }) => {
			let cond_ty = SimpleType::synthesize_expression(condition, bind_env);
			match cond_ty {
				PrimitiveTy(_) => {}

				_ => error!("condition expression ill-typed"),
			}
		}

		ForStmt(_) => {}

		WhileStmt(_) => {}

		DoWhileStmt(_) => {}

		CompoundStmt(stmts) => {
			let mut bind_env = bind_env.inherit();
			let mut type_env = type_env.inherit();
			for stmt in stmts {
				check_statement(stmt, &mut bind_env, &mut type_env, return_ty);
			}
		}
	}
}

pub fn check<'a>(tu: &'a TranslationUnit<'a>) {
	check_binding(tu);
	check_lr_value(tu);
	// check_type(tu);
	use ExternalDeclaration::*;
	use ValueQualifier::*;

	let mut bind_env = BindingEnvironment::new();
	let mut type_env = TypingEnvironment::new();

	let TranslationUnit(eds) = tu;
	for extern_decl in eds {
		match extern_decl {
			FunctionDefinitionDecl(FunctionDefinition {
				declarator: FunctionDeclarator { identifier, parameters },
				body,
				specifier,
			}) => {
				let return_ty = SimpleType::from_type_specifier(specifier, &mut type_env);
				let mut param_ty = Vec::new();
				for param in parameters {
					let (pname, pty) = SimpleType::parse_declaration(param, &mut type_env, None);
					param_ty.push(pty.clone());

					bind_env.bind(
						checked_unwrap!(pname).into(),
						QualifiedSimpleType { qualifier: Denoted, ty: pty },
					);
				}

				let fty = SimpleType::FunctionTy(FunctionType {
					return_ty: Box::new(return_ty.clone()),
					param_ty,
				});

				bind_env
					.bind(identifier.into(), QualifiedSimpleType { qualifier: Expressed, ty: fty });

				checked_match!(body, Statement::CompoundStmt(_), {
					check_statement(body, &mut bind_env, &mut type_env, &return_ty);
				});
			}

			Decl(declaration) => {
				let Declaration { specifier, declarator } = declaration;
				if declarator.is_some() {
					let (ident_name, ident_ty) =
						SimpleType::parse_declaration(declaration, &mut type_env, Some(&bind_env));
					if let Some(ident_name) = ident_name {
						bind_env.bind(
							ident_name.into(),
							QualifiedSimpleType { qualifier: Denoted, ty: ident_ty },
						)
					}
				} else {
					// some new struct definition
					SimpleType::from_type_specifier(specifier, &mut type_env);
				}
			}
		}
	}
}

static NEW_VAR_INDEX: AtomicUsize = AtomicUsize::new(0);

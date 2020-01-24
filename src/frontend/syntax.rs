// syntax analysis
use std::hint::unreachable_unchecked;

use crate::error;

const KEYWORDS: &'_ [&'_ str] = &["if", "else", "for", "while", "do", "char", "short", "int", "long", "return", "struct", "void"];

#[derive(Clone, Debug)]
pub enum UnaryOperator {
	Negation,
	PostIncrement,
	PreIncrement,
	Address,
	Indirection,
}

#[derive(Clone, Debug)]
pub struct UnaryOperatorExpression<'a> {
	pub operator: UnaryOperator,
	pub operand: Box<Expression<'a>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BinaryOperator {
	Multiplication,
	Division,
	Remainder,
	Addition,
	Subtraction,
	Less,
	LessOrEqual,
	Greater,
	GreaterOrEqual,
	Equal,
	NotEqual,
	Assignment,
	AdditionAssignment,
	SubtractionAssignment,
	MultiplicationAssignment,
	DivisionAssignment,
	BitwiseAnd,
	BitwiseXor,
	BitwiseOr,
}

#[derive(Clone, Debug)]
pub enum MemberOperator {
	Direct,
	Indirect,
}

#[derive(Clone, Debug)]
pub struct Integer(pub i64);

impl Into<i64> for &'_ Integer {
	fn into(self) -> i64 { self.0 }
}

impl Into<i64> for Integer {
	fn into(self) -> i64 { self.0 }
}

#[derive(Clone, Debug)]
pub enum Constant {
	IntegerConst(Integer),
}

#[derive(Clone, Debug)]
pub struct BinaryOperatorExpression<'a> {
	pub operator: BinaryOperator,
	pub lhs: Box<Expression<'a>>,
	pub rhs: Box<Expression<'a>>,
}

#[derive(Clone, Debug)]
pub struct MemberExpression<'a> {
	pub operator: MemberOperator,
	pub expression: Box<Expression<'a>>,
	pub identifier: Identifier<'a>,
}

// Simplified function calls (C11 6.5.5.2 Function calls)
#[derive(Clone, Debug)]
pub struct CallExpression<'a> {
	pub callee: Identifier<'a>,
	pub arguments: Vec<Expression<'a>>,
}

#[derive(Clone, Debug)]
pub enum Expression<'a> {
	UnaryOperatorExpr(UnaryOperatorExpression<'a>),
	BinaryOperatorExpr(BinaryOperatorExpression<'a>),
	ConstantExpr(Constant),
	IdentifierExpr(Identifier<'a>),
	MemberExpr(MemberExpression<'a>),
	CallExpr(CallExpression<'a>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DerivedDeclarator {
	Pointer,
}

// Simplified declarators
// C11 6.7.6 Declarators
#[derive(Clone, Debug)]
pub struct Declarator<'a> {
	pub ident: Identifier<'a>,
	pub derived: Option<DerivedDeclarator>,
	pub initializer: Option<Expression<'a>>,
}

// Simplified declaration
// C11 6.7 Declarations
#[derive(Clone, Debug)]
pub struct Declaration<'a> {
	pub specifier: TypeSpecifier<'a>,
	pub declarator: Option<Declarator<'a>>,
}

#[derive(Clone, Debug)]
pub struct IfStatement<'a> {
	pub condition: Expression<'a>,
	pub then_statement: Box<Statement<'a>>,
	pub else_statement: Option<Box<Statement<'a>>>,
}

// C11 6.8.5.3 The for statement
// Simplification: initializer is expression
#[derive(Clone, Debug)]
pub struct ForStatement<'a> {
	pub initializer: Option<Expression<'a>>,
	pub condition: Expression<'a>,
	pub step: Option<Expression<'a>>,
	pub statement: Box<Statement<'a>>,
}

// C11 6.8.5.1 The while statement
#[derive(Clone, Debug)]
pub struct WhileStatement<'a> {
	pub condition: Expression<'a>,
	pub statement: Box<Statement<'a>>,
}

#[derive(Clone, Debug)]
pub struct DoWhileStatement<'a> {
	pub condition: Expression<'a>,
	pub statement: Box<Statement<'a>>,
}

#[derive(Clone, Debug)]
pub enum Statement<'a> {
	CompoundStmt(Vec<Statement<'a>>),

	// e.g. return 1 + 2; or just return;
	ReturnStmt(Option<Expression<'a>>),

	// e.g. int i;
	DeclarationStmt(Declaration<'a>),

	// e.g. i = 10; or just ; (i.e. null statement)
	ExpressionStmt(Option<Expression<'a>>),

	IfStmt(IfStatement<'a>),

	ForStmt(ForStatement<'a>),

	WhileStmt(WhileStatement<'a>),

	DoWhileStmt(DoWhileStatement<'a>),
}

#[derive(Clone, Copy, Debug)]
pub struct Identifier<'a>(pub &'a str);

#[derive(Clone, Debug)]
pub struct StructType<'a> {
	pub identifier: Identifier<'a>,
	pub declarations: Option<Vec<Declaration<'a>>>,
}

// Plain signed types
// ABI: 3.1.2 Data Representation
// C11: 6.2.5 Types
#[derive(Clone, Debug)]
pub enum TypeSpecifier<'a> {
	CharTy,
	ShortTy,
	IntTy,
	LongTy,
	StructTy(StructType<'a>),
	VoidTy,
}

// Simplified function declarator
// C11: 6.7.6.3
#[derive(Clone)]
pub struct FunctionDeclarator<'a> {
	pub identifier: Identifier<'a>,
	pub parameters: Vec<Declaration<'a>>,
}

#[derive(Clone)]
pub struct FunctionDefinition<'a> {
	pub specifier: TypeSpecifier<'a>,
	pub declarator: FunctionDeclarator<'a>,
	pub body: Statement<'a>, // actually Statement::CompoundStmt
}

#[derive(Clone)]
pub enum ExternalDeclaration<'a> {
	FunctionDefinitionDecl(FunctionDefinition<'a>),
	Decl(Declaration<'a>),
}

pub struct TranslationUnit<'a>(pub Vec<ExternalDeclaration<'a>>);

//  IP10 paper, and mostly https://github.com/vickenty/lang-c
peg::parser! {grammar parser() for str {
	rule blank() = [' ' | '\t' | '\n']
	rule digit() = ['0'..='9']
	rule letter() = ['a'..='z' | 'A'..='Z' | '_']

	rule identifier() -> Identifier<'input>
		= i:$(letter() (letter() / digit())*) {?
			if KEYWORDS.contains(&i) {
				Err("identifier is a keyword")
			} else {
				Ok(Identifier(i))
			}
		}

	rule type_specifier() -> TypeSpecifier<'input>
		= "char" { TypeSpecifier::CharTy }
		/ "short" { TypeSpecifier::ShortTy }
		/ "int" { TypeSpecifier::IntTy }
		/ "long" { TypeSpecifier::LongTy }
		/ "void" { TypeSpecifier::VoidTy }
		/ "struct" blank()+ i:identifier() blank()* "{" blank()* dss:declaration_stmt()* blank()* "}" {
			let ds: Vec<_> = dss.iter().map(|s| {
				use Statement::*;
				match s {
					DeclarationStmt(d) => {
						let Declaration { declarator, .. } = d;
						if declarator.is_none() {
							error!("incomplelete struct field declaration")
						} else {
							d.clone()
						}
					}
					_ => unsafe { unreachable_unchecked() }
			}}).collect();
			TypeSpecifier::StructTy(StructType {
				identifier: i,
				declarations: Some(ds)
			})
		}
		/ "struct" blank()+ i:identifier() {
			TypeSpecifier::StructTy(StructType {
				identifier: i,
				declarations: None
			})
		}

	rule integer_literal() -> Constant
		= i:$("_"? blank()* digit()+) {
			Constant::IntegerConst(Integer(i.parse().unwrap()))
		}

	// https://en.cppreference.com/w/c/language/operator_precedence
	rule expression() -> Expression<'input> = precedence!{
		a:@ blank()* "=" blank()* b:(@) {
			Expression::BinaryOperatorExpr(BinaryOperatorExpression {
				operator: BinaryOperator::Assignment,
				lhs: Box::new(a),
				rhs: Box::new(b),
			})
		}
		a:@ blank()* "+=" blank()* b:(@) {
			Expression::BinaryOperatorExpr(BinaryOperatorExpression {
				operator: BinaryOperator::AdditionAssignment,
				lhs: Box::new(a),
				rhs: Box::new(b),
			})
		}
		a:@ blank()* "-=" blank()* b:(@) {
			Expression::BinaryOperatorExpr(BinaryOperatorExpression {
				operator: BinaryOperator::SubtractionAssignment,
				lhs: Box::new(a),
				rhs: Box::new(b),
			})
		}
		a:@ blank()* "*=" blank()* b:(@) {
			Expression::BinaryOperatorExpr(BinaryOperatorExpression {
				operator: BinaryOperator::MultiplicationAssignment,
				lhs: Box::new(a),
				rhs: Box::new(b),
			})
		}
		a:@ blank()* "/=" blank()* b:(@) {
			Expression::BinaryOperatorExpr(BinaryOperatorExpression {
				operator: BinaryOperator::DivisionAssignment,
				lhs: Box::new(a),
				rhs: Box::new(b),
			})
		}
		--
		a:(@) blank()* "&" blank()* b:@ {
			Expression::BinaryOperatorExpr(BinaryOperatorExpression {
				operator: BinaryOperator::BitwiseAnd,
				lhs: Box::new(a),
				rhs: Box::new(b)
			})
		}
		a:(@) blank()* "^" blank()* b:@ {
			Expression::BinaryOperatorExpr(BinaryOperatorExpression {
				operator: BinaryOperator::BitwiseXor,
				lhs: Box::new(a),
				rhs: Box::new(b)
			})
		}
		a:(@) blank()* "|" blank()* b:@ {
			Expression::BinaryOperatorExpr(BinaryOperatorExpression {
				operator: BinaryOperator::BitwiseOr,
				lhs: Box::new(a),
				rhs: Box::new(b)
			})
		}
		--
		a:(@) blank()* "<" blank()* b:@ {
			Expression::BinaryOperatorExpr(BinaryOperatorExpression {
				operator: BinaryOperator::Less,
				lhs: Box::new(a),
				rhs: Box::new(b)
			})
		}
		a:(@) blank()* "<=" blank()* b:@ {
			Expression::BinaryOperatorExpr(BinaryOperatorExpression {
				operator: BinaryOperator::LessOrEqual,
				lhs: Box::new(a),
				rhs: Box::new(b)
			})
		}
		a:(@) blank()* ">" blank()* b:@ {
			Expression::BinaryOperatorExpr(BinaryOperatorExpression {
				operator: BinaryOperator::Greater,
				lhs: Box::new(a),
				rhs: Box::new(b)
			})
		}
		a:(@) blank()* ">=" blank()* b:@ {
			Expression::BinaryOperatorExpr(BinaryOperatorExpression {
				operator: BinaryOperator::GreaterOrEqual,
				lhs: Box::new(a),
				rhs: Box::new(b)
			})
		}
		a:(@) blank()* "==" blank()* b:@ {
			Expression::BinaryOperatorExpr(BinaryOperatorExpression {
				operator: BinaryOperator::Equal,
				lhs: Box::new(a),
				rhs: Box::new(b)
			})
		}
		a:(@) blank()* "!=" blank()* b:@ {
			Expression::BinaryOperatorExpr(BinaryOperatorExpression {
				operator: BinaryOperator::NotEqual,
				lhs: Box::new(a),
				rhs: Box::new(b)
			})
		}
		--
		a:(@) blank()* "+" blank()* b:@ {
			Expression::BinaryOperatorExpr(BinaryOperatorExpression {
				operator: BinaryOperator::Addition,
				lhs: Box::new(a),
				rhs: Box::new(b),
			})
		}
		a:(@) blank()* "-" blank()* b:@ {
			Expression::BinaryOperatorExpr(BinaryOperatorExpression {
				operator: BinaryOperator::Subtraction,
				lhs: Box::new(a),
				rhs: Box::new(b),
			})
		}
		--
		a:(@) blank()* "*" blank()* b:@ {
			Expression::BinaryOperatorExpr(BinaryOperatorExpression {
				operator: BinaryOperator::Multiplication,
				lhs: Box::new(a),
				rhs: Box::new(b),
			})
		}
		a:(@) blank()* "/" blank()* b:@ {
			Expression::BinaryOperatorExpr(BinaryOperatorExpression {
				operator: BinaryOperator::Division,
				lhs: Box::new(a),
				rhs: Box::new(b),
			})
		}
		a:(@) blank()* "%" blank()* b:@ {
			Expression::BinaryOperatorExpr(BinaryOperatorExpression {
				operator: BinaryOperator::Remainder,
				lhs: Box::new(a),
				rhs: Box::new(b),
			})
		}
		--
		i:identifier() "(" blank()* es:expression() ** "," blank()* ")" {
			Expression::CallExpr(CallExpression {
				callee: i,
				arguments: es,
			})
		}
		--
		"-" blank()* a:@ {
			Expression::UnaryOperatorExpr(UnaryOperatorExpression {
				operator: UnaryOperator::Negation,
				operand: Box::new(a),
			})
		}
		"&" blank()* a:@ {
			Expression::UnaryOperatorExpr(UnaryOperatorExpression {
				operator: UnaryOperator::Address,
				operand: Box::new(a),
			})
		}
		"*" blank()* a:@ {
			Expression::UnaryOperatorExpr(UnaryOperatorExpression {
				operator: UnaryOperator::Indirection,
				operand: Box::new(a),
			})
		}
		--
		a:identifier() "++" {
			Expression::UnaryOperatorExpr(UnaryOperatorExpression {
				operator: UnaryOperator::PostIncrement,
				operand: Box::new(Expression::IdentifierExpr(a)),
			})
		}
		"++" a:identifier() {
			Expression::UnaryOperatorExpr(UnaryOperatorExpression {
				operator: UnaryOperator::PreIncrement,
				operand: Box::new(Expression::IdentifierExpr(a)),
			})
		}
		--
		a:(@) "." b:identifier() {
			Expression::MemberExpr(MemberExpression {
				operator: MemberOperator::Direct,
				expression: Box::new(a),
				identifier: b,
			})
		}
		a:(@) "->" b:identifier() {
			Expression::MemberExpr(MemberExpression {
				operator: MemberOperator::Indirect,
				expression: Box::new(a),
				identifier: b,
			})
		}
		--
		i:identifier() blank()* {
			Expression::IdentifierExpr(i)
		}
		--
		blank()+ e:expression() { e }
		"(" e:expression() ")" { e }
		i:integer_literal() { Expression::ConstantExpr(i) }
	}

	rule derived_declarator() -> DerivedDeclarator
		= "*" {
			DerivedDeclarator::Pointer
		}

	rule declarator() -> Declarator<'input>
		= d:derived_declarator()? blank()* i:identifier() blank()* "=" blank()* e:expression() {
			Declarator {
				ident: i,
				derived: d,
				initializer: Some(e),
			}
		}
		/ d:derived_declarator()? blank()* i:identifier() {
			Declarator {
				ident: i,
				derived: d,
				initializer: None,
			}
		}

	rule declaration() -> Declaration<'input>
		= blank()+ d:declaration() { d }
		/ t:type_specifier() blank()+ d:declarator() blank()* {
			Declaration {
				specifier: t,
				declarator: Some(d),
			}
		}
		/ t:type_specifier() blank()* {?
			match t {
				TypeSpecifier::StructTy(_) => {
					Ok(Declaration {
						specifier: t,
						declarator: None,
					})
				}

				_ => Err("declarator is obliged for primitive types")
			}
		}

	rule declaration_stmt() -> Statement<'input>
		= blank()+ s:declaration_stmt() { s }
		/ d:declaration() blank()* ";" {
			Statement::DeclarationStmt(d)
		}

	rule expression_stmt() -> Statement<'input>
		= blank()+ s:expression_stmt() { s }
		/ e:expression() blank()* ";" { Statement::ExpressionStmt(Some(e)) }
		/ ";" { Statement::ExpressionStmt(None) }

	rule return_stmt() -> Statement<'input>
		= blank()+ s:return_stmt() { s }
		/ "return" blank()+ e:expression() blank()* ";" {
			Statement::ReturnStmt(Some(e))
		}
		/ "return" blank()* ";" { Statement::ReturnStmt(None) }

	rule compound_stmt() -> Statement<'input>
		= blank()+ s:compound_stmt() { s }
		/ "{" ss:statement()* blank()* "}" {
			Statement::CompoundStmt(ss)
		}

	rule if_stmt() -> Statement<'input>
		= blank()+ s:if_stmt() { s }
		/ "if" blank()* "(" e:expression() blank()* ")" ts:statement() blank()* "else" es:statement() {
			Statement::IfStmt(IfStatement {
				condition: e,
				then_statement: Box::new(ts),
				else_statement: Some(Box::new(es)),
			})
		}
		/ "if" blank()* "(" e:expression() blank()* ")" ts:statement() blank()* {
			Statement::IfStmt(IfStatement {
				condition: e,
				then_statement: Box::new(ts),
				else_statement: None,
			})
		}

	rule for_stmt() -> Statement<'input>
		= blank()+ s:for_stmt() { s }
		/ "for" blank()* "(" i:expression()? ";" c:expression() ";" s:expression()? blank()* ")" st:statement() {
			Statement::ForStmt(ForStatement {
				initializer: i,
				condition: c,
				step: s,
				statement: Box::new(st),
			})
		}

	rule while_stmt() -> Statement<'input>
		= blank()+ s:while_stmt() { s }
		/ "while" blank()* "(" c:expression() blank()* ")" blank()* st:statement() {
			Statement::WhileStmt(WhileStatement {
				condition: c,
				statement: Box::new(st),
			})
		}

	rule do_while_stmt() -> Statement<'input>
		= blank()+ s:do_while_stmt() { s }
		/ "do" blank()* st:compound_stmt() blank()* "while" blank()* "(" c:expression() blank()* ")" blank()* ";" {
			Statement::DoWhileStmt(DoWhileStatement {
				condition:c,
				statement: Box::new(st)
			})
		}
		/ "do" blank()+ st:statement() blank()* "while" blank()* "(" c:expression() blank()* ")" blank()* ";" {
			Statement::DoWhileStmt(DoWhileStatement {
				condition:c,
				statement: Box::new(st)
			})
		}

	rule statement() -> Statement<'input>
		= compound_stmt()
		/ if_stmt()
		/ do_while_stmt()
		/ while_stmt()
		/ for_stmt()
		/ return_stmt()
		/ declaration_stmt()
		/ expression_stmt()

	rule function_declarator() -> FunctionDeclarator<'input>
		= i:identifier() blank()* "(" blank()* ds:declaration() ** "," blank()* ")" {?
			if ds.iter().any(|Declaration { declarator, .. }| declarator.is_none() || {
				let Declarator { initializer, .. } = declarator.clone().unwrap();
				initializer.is_some()
			}) {
				Err("parameter name not found (or found but with initializer)")
			} else {
				Ok(FunctionDeclarator {
					identifier: i,
					parameters: ds,
				})
			}
		}

	rule function_definition() -> FunctionDefinition<'input>
		= blank()+ f:function_definition() { f }
		/ t:type_specifier() blank()+ blank()* d:function_declarator() b:compound_stmt() {
			FunctionDefinition {
				specifier: t,
				declarator: d,
				body: b
			}
		}

	rule external_declaration() -> ExternalDeclaration<'input>
		= blank()+ e:external_declaration() { e }
		/ f:function_definition() {
			ExternalDeclaration::FunctionDefinitionDecl(f)
		}
		/ d:declaration_stmt() {
			if let Statement::DeclarationStmt(d) = d {
				ExternalDeclaration::Decl(d)
			} else {
				unsafe { unreachable_unchecked() }
			}
		}

	pub rule translation_unit() -> TranslationUnit<'input>
		= blank()+ tu:translation_unit() { tu }
		/ eds:external_declaration()* blank()* {
			TranslationUnit(eds)
		}
}}

// pub fn parse(src_file: impl AsRef<Path>) -> TranslationUnit {
pub fn parse(src_code: &str) -> TranslationUnit {
	// let src_code = fs::read_to_string(src_file).expect("Failed to read source code file");
	if let Ok(tu) = parser::translation_unit(&src_code) { tu } else { panic!("failed to parse source code") }
}

// pub fn function_name(tu: &TranslationUnit) -> &str {
// 	let TranslationUnit(extern_decs) = tu;

// 	for dec in extern_decs.iter() {
// 		use ExternalDeclaration::*;
// 		if let FunctionDefinitionDecl(FunctionDefinition {
// 			declarator: FunctionDeclarator {
// 				identifier: Identifier(fname),
// 				..
// 			},
// 			..
// 		}) = dec
// 		{
// 			return fname.as_str();
// 		}
// 	}

// 	panic!("No function in the translation unit")
// }

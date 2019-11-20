// syntax analysis
use std::{fs, hint::unreachable_unchecked, path::Path};

const KEYWORDS: &'static [&'static str] = &["if", "else", "while", "do", "int", "return", "struct"];

pub enum UnaryOperator {
	Neg,
}

pub struct UnaryOperatorExpression {
	pub op: UnaryOperator,
	pub rhs: Box<Expression>,
}

pub enum BinaryOperator {
	Mul,
	Div,
	Add,
	Sub,
	Asg,
}

pub enum MemberOperator {
	Direct,
	Indirect,
}

pub struct Integer(pub i32);

pub enum Constant {
	IntegerConst(Integer),
}

pub struct BinaryOperatorExpression {
	pub op: BinaryOperator,
	pub lhs: Box<Expression>,
	pub rhs: Box<Expression>,
}

pub struct MemberExpression {
	pub operator: MemberOperator,
	pub expression: Box<Expression>,
	pub identifier: Identifier,
}

pub enum Expression {
	UnaryOperatorExpr(UnaryOperatorExpression),
	BinaryOperatorExpr(BinaryOperatorExpression),
	ConstantExpr(Constant),
	IdentifierExpr(Identifier),
	MemberExpr(MemberExpression),
}

// Simplified declaration (C11 6.7)
#[derive(Debug, Clone)]
pub struct Declaration {
	pub specifier: TypeSpecifier,
	pub declarator: Identifier,
}

pub enum Statement {
	CompoundStmt(Vec<Statement>),

	// e.g. return 1 + 2; or just return;
	ReturnStmt(Option<Expression>),

	// e.g. int i;
	DeclarationStmt(Declaration),

	// e.g. i = 10; or just ; (i.e. null statement)
	ExpressionStmt(Option<Expression>),
}

#[derive(Debug, Clone)]
pub struct Identifier(pub String);

#[derive(Debug, Clone)]
pub struct StructType {
	pub identifier: Identifier,
	pub declarations: Option<Vec<Declaration>>,
}
#[derive(Debug, Clone)]
pub enum TypeSpecifier {
	Int,
	Struct(StructType),
}

// Simplified function declarator (C11 6.7.6.3)
#[derive(Debug, Clone)]
pub struct FunctionDeclarator {
	pub identifier: Identifier,
	pub parameters: Vec<Declaration>,
}

pub struct FunctionDefinition {
	pub specifier: TypeSpecifier,
	pub declarator: FunctionDeclarator,
	pub body: Statement, // actually Statement::CompoundStmt
}

pub enum ExternalDeclaration {
	FunctionDefinitionDecl(FunctionDefinition),
	None,
}

pub struct TranslationUnit(pub Vec<ExternalDeclaration>);

//  DOI 10.1145/1942793.1942796
//  https://github.com/vickenty/lang-c
peg::parser! {grammar parser() for str {
	rule blank() = [' ' | '\t' | '\n']
	rule digit() = ['0'..='9']
	rule letter() = ['a'..='z' | 'A'..='Z' | '_']

	rule identifier() -> Identifier
		= i:$(letter() (letter() / digit())*) {?
			if KEYWORDS.contains(&i) {
				Err("identifier is a keyword")
			} else {
				Ok(Identifier(i.to_owned()))
			}
		}

	rule type_specifier() -> TypeSpecifier
		= "int" { TypeSpecifier::Int }
		/ "struct" blank()+ i:identifier() blank()* "{" blank()* dss:declaration_stmt()* blank()* "}" {
			let ds: Vec<_> = dss.iter().map(|s| {
				use Statement::*;
				match s {
					DeclarationStmt(d) => d.clone(),
					_ => unsafe { unreachable_unchecked() }
			}}).collect();
			TypeSpecifier::Struct(StructType {
				identifier: i,
				declarations: Some(ds)
			})
		}
		/ "struct" blank()+ i:identifier() {
			TypeSpecifier::Struct(StructType {
				identifier: i,
				declarations: None
			})
		}

	rule integer_literal() -> Constant
		= i:$(digit()+) {
			Constant::IntegerConst(Integer(i.parse().unwrap()))
		}

	rule expression() -> Expression = precedence!{
		a:@ blank()* "=" blank()* b:(@) {
			Expression::BinaryOperatorExpr(BinaryOperatorExpression {
				op: BinaryOperator::Asg,
				lhs: Box::new(a),
				rhs: Box::new(b),
			})
		}
		--
		a:(@) blank()* "+" blank()* b:@ {
			Expression::BinaryOperatorExpr(BinaryOperatorExpression {
				op: BinaryOperator::Add,
				lhs: Box::new(a),
				rhs: Box::new(b)
			})
		}
		a:(@) blank()* "-" blank()* b:@ {
			Expression::BinaryOperatorExpr(BinaryOperatorExpression {
				op: BinaryOperator::Sub,
				lhs: Box::new(a),
				rhs: Box::new(b)
			})
		}
		"-" blank()* a:@ {
			Expression::UnaryOperatorExpr(UnaryOperatorExpression {
				op: UnaryOperator::Neg,
				rhs: Box::new(a),
			})
		}
		--
		a:(@) blank()* "*" blank()* b:@ {
			Expression::BinaryOperatorExpr(BinaryOperatorExpression {
				op: BinaryOperator::Mul,
				lhs: Box::new(a),
				rhs: Box::new(b)
			})
		}
		a:(@) blank()* "/" blank()* b:@ {
			Expression::BinaryOperatorExpr(BinaryOperatorExpression {
				op: BinaryOperator::Div,
				lhs: Box::new(a),
				rhs: Box::new(b)
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
		a:(@) "->" b:identifier() @ {
			Expression::MemberExpr(MemberExpression {
				operator: MemberOperator::Indirect,
				expression: Box::new(a),
				identifier: b,
			})
		}
		--
		i:identifier() {
			Expression::IdentifierExpr(i)
		}
		--
		blank()+ e:expression() { e }
		"(" e:expression() ")" { e }
		i:integer_literal() { Expression::ConstantExpr(i) }
	}

	rule declaration() -> Declaration
		= blank()+ d:declaration() { d }
		/ t:type_specifier() blank()+ i:identifier() {
			Declaration {
				specifier: t,
				declarator: i,
			}
		}

	rule declaration_stmt() -> Statement
		= blank()+ s:declaration_stmt() { s }
		/ d:declaration() blank()* ";" {
			Statement::DeclarationStmt(d)
		}

	rule expression_stmt() -> Statement
		= blank()+ s:expression_stmt() { s }
		/ e:expression() blank()* ";" { Statement::ExpressionStmt(Some(e)) }
		/ ";" { Statement::ExpressionStmt(None) }

	rule return_stmt() -> Statement
		= blank()+ s:return_stmt() { s }
		/ "return" blank()+ e:expression() blank()* ";" {
			Statement::ReturnStmt(Some(e))
		}
		/ "return" blank()* ";" { Statement::ReturnStmt(None) }

	rule compound_stmt() -> Statement
		= blank()+ s:compound_stmt() { s }
		/ "{" ss:statement()* blank()* "}" {
			Statement::CompoundStmt(ss)
		}

	rule statement() -> Statement
		= compound_stmt()
		/ return_stmt()
		/ declaration_stmt()
		/ expression_stmt()

	rule function_declarator() -> FunctionDeclarator
		= i:identifier() blank()* "(" blank()* ds:declaration() ** "," blank()* ")" {
			FunctionDeclarator {
				identifier: i,
				parameters: ds,
			}
		}

	rule function_definition() -> FunctionDefinition
		= t:type_specifier() blank()+ blank()* d:function_declarator() b:compound_stmt() {
			FunctionDefinition {
				specifier: t,
				declarator: d,
				body: b
			}
		}

	pub rule translation_unit() -> TranslationUnit
		= f:function_definition() {
			TranslationUnit(vec![ExternalDeclaration::FunctionDefinitionDecl(f)])
		}
}}

pub fn parse(src_file: impl AsRef<Path>) -> TranslationUnit {
	let src_code = fs::read_to_string(src_file).expect("Failed to read source code file");
	if let Ok(tu) = parser::translation_unit(&src_code) {
		tu
	} else {
		panic!("Failed to parse source code")
	}
}

pub fn function_name(tu: &TranslationUnit) -> &str {
	let TranslationUnit(extern_decs) = tu;

	for dec in extern_decs.iter() {
		use ExternalDeclaration::*;
		if let FunctionDefinitionDecl(FunctionDefinition {
			declarator: FunctionDeclarator {
				identifier: Identifier(fname),
				..
			},
			..
		}) = dec
		{
			return fname.as_str();
		}
	}

	panic!("No function in the translation unit")
}

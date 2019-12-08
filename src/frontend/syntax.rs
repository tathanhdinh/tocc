// syntax analysis
use std::hint::unreachable_unchecked;

const KEYWORDS: &'static [&'static str] =
	&["if", "else", "while", "do", "char", "short", "int", "long", "return", "struct"];

#[derive(Clone)]
pub enum UnaryOperator {
	Negation,
	Address,
}

#[derive(Clone)]
pub struct UnaryOperatorExpression<'a> {
	pub op: UnaryOperator,
	pub rhs: Box<Expression<'a>>,
}

#[derive(Clone)]
pub enum BinaryOperator {
	Multiplication,
	Division,
	Addition,
	Subtraction,
	Less,
	LessOrEqual,
	Greater,
	GreaterOrEqual,
	Equal,
	Assignment,
}

#[derive(Clone)]
pub enum MemberOperator {
	Direct,
	Indirect,
}

#[derive(Clone)]
pub struct Integer(pub i32);

#[derive(Clone)]
pub enum Constant {
	IntegerConst(Integer),
}

#[derive(Clone)]
pub struct BinaryOperatorExpression<'a> {
	pub op: BinaryOperator,
	pub lhs: Box<Expression<'a>>,
	pub rhs: Box<Expression<'a>>,
}

#[derive(Clone)]
pub struct MemberExpression<'a> {
	pub operator: MemberOperator,
	pub expression: Box<Expression<'a>>,
	pub identifier: Identifier<'a>,
}

// Simplified function calls (C11 6.5.5.2 Function calls)
#[derive(Clone)]
pub struct CallExpression<'a> {
	pub callee: Identifier<'a>,
	pub arguments: Vec<Expression<'a>>,
}

#[derive(Clone)]
pub enum Expression<'a> {
	UnaryOperatorExpr(UnaryOperatorExpression<'a>),
	BinaryOperatorExpr(BinaryOperatorExpression<'a>),
	ConstantExpr(Constant),
	IdentifierExpr(Identifier<'a>),
	MemberExpr(MemberExpression<'a>),
	CallExpr(CallExpression<'a>),
}

#[derive(Clone)]
pub enum DerivedDeclarator {
	Pointer,
}

// Simplified declarators
// C11 Standard: 6.7.6 Declarators
#[derive(Clone)]
pub struct Declarator<'a> {
	pub ident: Identifier<'a>,
	pub derived: Option<DerivedDeclarator>,
}

// Simplified declaration
// C11 Standard 6.7 Declarations
#[derive(Clone)]
pub struct Declaration<'a> {
	pub specifier: TypeSpecifier<'a>,
	pub declarator: Option<Declarator<'a>>,
}

#[derive(Clone)]
pub struct IfStatement<'a> {
	pub condition: Expression<'a>,
	pub then_statement: Box<Statement<'a>>,
	pub else_statement: Option<Box<Statement<'a>>>,
}

#[derive(Clone)]
pub enum Statement<'a> {
	CompoundStmt(Vec<Statement<'a>>),

	// e.g. return 1 + 2; or just return;
	ReturnStmt(Option<Expression<'a>>),

	// e.g. int i;
	DeclarationStmt(Declaration<'a>),

	// e.g. i = 10; or just ; (i.e. null statement)
	ExpressionStmt(Option<Expression<'a>>),

	IfStmt(IfStatement<'a>),
}

#[derive(Clone)]
pub struct Identifier<'a>(pub &'a str);

#[derive(Clone)]
pub struct StructType<'a> {
	pub identifier: Identifier<'a>,
	pub declarations: Option<Vec<Declaration<'a>>>,
}

// Plain signed types
// System V ABI: 3.1.2 Data Representation
// C11 Standard: 6.2.5 Types
#[derive(Clone)]
pub enum TypeSpecifier<'a> {
	CharTy,
	ShortTy,
	IntTy,
	LongTy,
	StructTy(StructType<'a>),
}

// Simplified function declarator
// C11 Standard: 6.7.6.3
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

//  DOI 10.1145/1942793.1942796
//  https://github.com/vickenty/lang-c
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
		/ "struct" blank()+ i:identifier() blank()* "{" blank()* dss:declaration_stmt()* blank()* "}" {
			let ds: Vec<_> = dss.iter().map(|s| {
				use Statement::*;
				match s {
					DeclarationStmt(d) => d.clone(),
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
		= i:$(digit()+) {
			Constant::IntegerConst(Integer(i.parse().unwrap()))
		}

	// https://en.cppreference.com/w/c/language/operator_precedence
	rule expression() -> Expression<'input> = precedence!{
		a:@ blank()* "=" blank()* b:(@) {
			Expression::BinaryOperatorExpr(BinaryOperatorExpression {
				op: BinaryOperator::Assignment,
				lhs: Box::new(a),
				rhs: Box::new(b),
			})
		}
		--
		a:(@) blank()* "<" blank()* b:@ {
			Expression::BinaryOperatorExpr(BinaryOperatorExpression {
				op: BinaryOperator::Less,
				lhs: Box::new(a),
				rhs: Box::new(b)
			})
		}
		a:(@) blank()* "<=" blank()* b:@ {
			Expression::BinaryOperatorExpr(BinaryOperatorExpression {
				op: BinaryOperator::LessOrEqual,
				lhs: Box::new(a),
				rhs: Box::new(b)
			})
		}
		a:(@) blank()* ">" blank()* b:@ {
			Expression::BinaryOperatorExpr(BinaryOperatorExpression {
				op: BinaryOperator::Greater,
				lhs: Box::new(a),
				rhs: Box::new(b)
			})
		}
		a:(@) blank()* ">=" blank()* b:@ {
			Expression::BinaryOperatorExpr(BinaryOperatorExpression {
				op: BinaryOperator::GreaterOrEqual,
				lhs: Box::new(a),
				rhs: Box::new(b)
			})
		}
		a:(@) blank()* "==" blank()* b:@ {
			Expression::BinaryOperatorExpr(BinaryOperatorExpression {
				op: BinaryOperator::Equal,
				lhs: Box::new(a),
				rhs: Box::new(b)
			})
		}
		--
		a:(@) blank()* "+" blank()* b:@ {
			Expression::BinaryOperatorExpr(BinaryOperatorExpression {
				op: BinaryOperator::Addition,
				lhs: Box::new(a),
				rhs: Box::new(b),
			})
		}
		a:(@) blank()* "-" blank()* b:@ {
			Expression::BinaryOperatorExpr(BinaryOperatorExpression {
				op: BinaryOperator::Subtraction,
				lhs: Box::new(a),
				rhs: Box::new(b),
			})
		}
		--
		a:(@) blank()* "*" blank()* b:@ {
			Expression::BinaryOperatorExpr(BinaryOperatorExpression {
				op: BinaryOperator::Multiplication,
				lhs: Box::new(a),
				rhs: Box::new(b),
			})
		}
		a:(@) blank()* "/" blank()* b:@ {
			Expression::BinaryOperatorExpr(BinaryOperatorExpression {
				op: BinaryOperator::Division,
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
				op: UnaryOperator::Negation,
				rhs: Box::new(a),
			})
		}
		"&" blank()* a:@ {
			Expression::UnaryOperatorExpr(UnaryOperatorExpression {
				op: UnaryOperator::Address,
				rhs: Box::new(a),
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
		i:identifier() {
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
		= d:derived_declarator()? blank()* i:identifier() {
			Declarator {
				ident: i,
				derived: d,
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

				_ => {
					Err("declarator is obliged for primitive types")
				}
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

	rule statement() -> Statement<'input>
		= compound_stmt()
		/ if_stmt()
		/ return_stmt()
		/ declaration_stmt()
		/ expression_stmt()

	rule function_declarator() -> FunctionDeclarator<'input>
		= i:identifier() blank()* "(" blank()* ds:declaration() ** "," blank()* ")" {?
			if ds.iter().any(|Declaration { declarator, .. }| declarator.is_none()) {
				Err("parameter name not found")
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
	if let Ok(tu) = parser::translation_unit(&src_code) {
		tu
	} else {
		panic!("failed to parse source code")
	}
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

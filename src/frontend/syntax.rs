// syntax analysis

const KEYWORDS: &'static [&'static str] = &["if", "else", "while", "do", "int"];

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

pub struct Integer(pub i64);

pub enum Constant {
	IntegerConst(Integer),
}

pub struct BinaryOperatorExpression {
	pub op: BinaryOperator,
	pub lhs: Box<Expression>,
	pub rhs: Box<Expression>,
}

pub enum Expression {
	UnaryOperatorExpr(UnaryOperatorExpression),
	BinaryOperatorExpr(BinaryOperatorExpression),
	ConstantExpr(Constant),
	IdentifierExpr(Identifier),
}

pub struct Declaration {
	pub specifier: TypeSpecifier,
	pub declarator: Identifier,
}

pub enum Statement {
	CompoundStmt(Box<Vec<Statement>>),

	// e.g. return 1 + 2; or just return;
	ReturnStmt(Option<Box<Expression>>),

	// e.g. int i;
	DeclarationStmt(Declaration),

	// e.g. i = 10; or just ; (i.e. null statement)
	ExpressionStmt(Option<Box<Expression>>),
}

pub struct Identifier(pub String);

pub enum TypeSpecifier {
	Int,
}

pub struct FunctionDefinition {
	pub specifier: TypeSpecifier,
	pub declarator: Identifier,
	pub body: Statement, // actually Statement::CompoundStmt
}

pub enum ExternalDeclaration {
	FunctionDefinitionDecl(FunctionDefinition),
}

pub struct TranslationUnit(pub Vec<ExternalDeclaration>);

//  10.1145/1942793.1942796
//  https://github.com/vickenty/lang-c
peg::parser! {pub grammar parser() for str {
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
		i:identifier() {
			Expression::IdentifierExpr(i)
		}
		--
		blank()+ e:expression() { e }
		"(" e:expression() ")" { e }
		i:integer_literal() { Expression::ConstantExpr(i) }
	}

	rule declaration_stmt() -> Statement
		= blank()+ s:declaration_stmt() { s }
		/ t:type_specifier() blank()+ i:identifier() blank()* ";" {
			Statement::DeclarationStmt(Declaration {
				specifier: t,
				declarator: i,
			})
		}

	rule expression_stmt() -> Statement
		= blank()+ s:expression_stmt() { s }
		/ e:expression() blank()* ";" { Statement::ExpressionStmt(Some(Box::new(e))) }
		/ ";" { Statement::ExpressionStmt(None) }

	rule return_stmt() -> Statement
		= blank()+ s:return_stmt() { s }
		/ "return" blank()+ e:expression() blank()* ";" {
			Statement::ReturnStmt(Some(Box::new(e)))
		}
		/ "return" blank()* ";" { Statement::ReturnStmt(None) }

	rule compound_stmt() -> Statement
		= blank()+ s:compound_stmt() { s }
		/ "{" s:statement()* blank()* "}" {
			Statement::CompoundStmt(Box::new(s))
		}

	rule statement() -> Statement
		= compound_stmt()
		/ return_stmt()
		/ declaration_stmt()
		/ expression_stmt()

	rule function_definition() -> FunctionDefinition
		= t:type_specifier() blank()+ d:identifier() blank()* "(" blank()* ")" b:compound_stmt() {
			FunctionDefinition {
				specifier: t,
				declarator: d,
				body: b
			}
		}

	pub rule parse() -> TranslationUnit
		= f:function_definition() {
			TranslationUnit(vec![ExternalDeclaration::FunctionDefinitionDecl(f)])
		}
}}

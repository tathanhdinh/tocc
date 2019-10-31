pub enum BinaryOperator {
	Mul,
	Div,
	Add,
	Sub,
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
	BinaryOperatorExpr(BinaryOperatorExpression),
	ConstantExpr(Constant),
}

pub enum Statement {
	CompoundStmt(Box<Vec<Statement>>),
	ReturnStmt(Option<Box<Expression>>),
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

pub enum TranslationUnit {
	FunctionDefinition(FunctionDefinition),
}

// References:
//  - 10.1145/1942793.1942796
//  - https://github.com/vickenty/lang-c
peg::parser! {pub grammar parser() for str {
	rule blank() = [' ' | '\t' | '\n']
	rule digit() = ['0'..='9']
	rule letter() = ['a'..='z' | 'A'..='Z' | '_']

	rule identifier() -> Identifier
		= i:$(letter() (letter() / digit())*) {
			Identifier(i.to_owned())
		}

	rule type_specifier() -> TypeSpecifier
		= "int" { TypeSpecifier::Int }

	rule integer_literal() -> Constant
		= i:$(digit()+) {
			Constant::IntegerConst(Integer(i.parse().unwrap()))
		}

	rule expression() -> Expression = precedence!{
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
		blank()+ e:expression() blank()* { e }
		"(" e:expression() ")" { e }
		i:integer_literal() { Expression::ConstantExpr(i) }
	}

	rule return_stmt() -> Statement
		= blank()+ s:return_stmt() blank()* { s }
		/ "return" blank()+ e:expression() ";" { Statement::ReturnStmt(Some(Box::new(e))) }
		/ "return" blank()* ";" { Statement::ReturnStmt(None) }

	rule compound_stmt() -> Statement
		= blank()+ s:compound_stmt() blank()* { s }
		/ "{" s:statement()* "}" { Statement::CompoundStmt(Box::new(s)) }

	rule statement() -> Statement
		 = compound_stmt() / return_stmt()

	rule function_definition() -> FunctionDefinition
		= t:type_specifier() blank()+ d:identifier() blank()* "(" blank()* ")" b:compound_stmt() {
			FunctionDefinition {
				specifier: t,
				declarator: d,
				body: b
			}
		}

	pub rule parse() -> TranslationUnit
		= f:function_definition() { TranslationUnit::FunctionDefinition(f) }
}}

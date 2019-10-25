// Frontend:
//  - lexical analysis
//  - syntax analysis
//  - type checking

// AST
pub enum BinaryOperator {
	Mul,
	Div,
	Add,
	Sub,
}

pub struct Integer(i64);

pub enum Constant {
	Integer(Integer),
}

pub struct BinaryOperatorExpression {
	op: BinaryOperator,
	lhs: Box<Expression>,
	rhs: Box<Expression>,
}

pub enum Expression {
	BinaryOperator(BinaryOperatorExpression),
	Constant(Constant),
}

pub enum Statement {
	Compound(Box<Vec<Statement>>),
	Return(Option<Box<Expression>>),
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

pub enum Stmt {
	Return(ArithmeticExpr),
}

pub enum ArithmeticExpr {
	Add(Box<ArithmeticExpr>, Box<ArithmeticExpr>),
	Sub(Box<ArithmeticExpr>, Box<ArithmeticExpr>),
	Mul(Box<ArithmeticExpr>, Box<ArithmeticExpr>),
	Div(Box<ArithmeticExpr>, Box<ArithmeticExpr>),
	Val(i64),
}

peg::parser! {pub grammar parser() for str {
	rule blanks() = [' '|'\t']*

	rule literal() -> ArithmeticExpr
		= blanks() v:$(['0'..='9']+) blanks() { ArithmeticExpr::Val(v.parse().unwrap()) }

	pub rule arithmetic_expr() -> ArithmeticExpr = precedence!{
		a:(@) "+" b:@ { ArithmeticExpr::Add(Box::new(a), Box::new(b)) }
		a:(@) "-" b:@ { ArithmeticExpr::Sub(Box::new(a), Box::new(b)) }
		blanks() "-" blanks() b:@ { ArithmeticExpr::Sub(Box::new(ArithmeticExpr::Val(0)), Box::new(b)) }
		--
		a:(@) "*" b:@ { ArithmeticExpr::Mul(Box::new(a), Box::new(b)) }
		a:(@) "/" b:@ { ArithmeticExpr::Div(Box::new(a), Box::new(b)) }
		--
		blanks() "(" blanks() e:arithmetic_expr() blanks() ")" blanks() { e }
		v:literal() { v }
	}

	pub rule stmt() -> Stmt
		= blanks() "return" blanks() a:arithmetic_expr() ";" { Stmt::Return(a) }
}}

peg::parser! {pub grammar c11() for str {
	rule blank() = [' ' | '\t' | '\n']

	rule identifier() -> Identifier
		= i:$(['a'..='z' | 'A'..='Z' | '_']['a'..='z' | 'A'..='Z' | '0'..='9' | '_']*) {
			Identifier(i.to_owned())
		}

	rule type_specifier() -> TypeSpecifier
		= "int" { TypeSpecifier::Int }

	rule integer_literal() -> Constant
		= i:$(['0'..='9']+) {
			Constant::Integer(Integer(i.parse().unwrap()))
		}

	rule expression() -> Expression = precedence!{
		a:(@) blank()* "+" blank()* b:@ {
			Expression::BinaryOperator(BinaryOperatorExpression {
				op: BinaryOperator::Add,
				lhs: Box::new(a),
				rhs: Box::new(b)
			})
		}
		a:(@) blank()* "-" blank()* b:@ {
			Expression::BinaryOperator(BinaryOperatorExpression {
				op: BinaryOperator::Sub,
				lhs: Box::new(a),
				rhs: Box::new(b)
			})
		}
		--
		a:(@) blank()* "*" blank()* b:@ {
			Expression::BinaryOperator(BinaryOperatorExpression {
				op: BinaryOperator::Mul,
				lhs: Box::new(a),
				rhs: Box::new(b)
			})
		}
		a:(@) blank()* "/" blank()* b:@ {
			Expression::BinaryOperator(BinaryOperatorExpression {
				op: BinaryOperator::Div,
				lhs: Box::new(a),
				rhs: Box::new(b)
			})
		}
		--
		blank()+ e:expression() blank()* { e }
		"(" e:expression() ")" { e }
		i:integer_literal() { Expression::Constant(i) }
	}

	rule return_stmt() -> Statement
		= blank()+ s:return_stmt() blank()* { s }
		/ "return" blank()+ e:expression() ";" { Statement::Return(Some(Box::new(e))) }
		/ "return" blank()* ";" { Statement::Return(None) }

	rule compound_stmt() -> Statement
		= blank()+ s:compound_stmt() blank()* { s }
		/ "{" s:statement()* "}" { Statement::Compound(Box::new(s)) }

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

// AST
pub enum Stmt {
	Ret(ArithmeticExpr),
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
		= blanks() "return" blanks() a:arithmetic_expr() ";" { Stmt::Ret(a) }
}}

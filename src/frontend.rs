// AST
pub enum Expr {
	Add(Box<Expr>, Box<Expr>),
	Sub(Box<Expr>, Box<Expr>),
	Mul(Box<Expr>, Box<Expr>),
	Div(Box<Expr>, Box<Expr>),
	Val(i64),
}

peg::parser! {pub grammar arithmetic() for str {
	rule blanks() = [' '|'\t']*

	rule literal() -> Expr
		= blanks() v:$(['0'..='9']+) blanks() { Expr::Val(v.parse().unwrap()) }

	pub rule evaluate() -> Expr = precedence!{
		a:(@) "+" b:@ { Expr::Add(Box::new(a), Box::new(b)) }
		a:(@) "-" b:@ { Expr::Sub(Box::new(a), Box::new(b)) }
		blanks() "-" blanks() b:@ { Expr::Sub(Box::new(Expr::Val(0)), Box::new(b)) }
		--
		a:(@) "*" b:@ { Expr::Mul(Box::new(a), Box::new(b)) }
		a:(@) "/" b:@ { Expr::Div(Box::new(a), Box::new(b)) }
		--
		blanks() "(" blanks() e:evaluate() blanks() ")" blanks() { e }
		v:literal() { v }
	}
}}

#[macro_export]
macro_rules! error {
    ($($tt:tt)*) => {
        panic!(format!($($tt)*))
    }
}

#[macro_export]
macro_rules! unimpl {
    ($($tt:tt)*) => {
        panic!(format!($($tt)*))
    }
}

#[macro_export]
macro_rules! semantically_unreachable {
	() => {
		unsafe { unreachable_unchecked() }
	};
}

#[macro_export]
macro_rules! checked_unwrap_option {
	($expr:expr) => {
		$expr.unwrap_or_else(|| unsafe { unreachable_unchecked() })
	};
}

#[macro_export]
macro_rules! checked_unwrap_result {
	($expr:expr) => {
		$expr.unwrap_or_else(|_| unsafe { unreachable_unchecked() })
	};
}

#[macro_export]
macro_rules! checked_if_let {
	($pat:pat, $expr:expr, $block:block) => {
		if let $pat = $expr { $block } else { unsafe { unreachable_unchecked() } }
	};
}

#[macro_export]
macro_rules! checked_match {
	($expr:expr, $pat:pat, $block:block) => {
		match $expr {
			$pat => $block,
			// _ => unsafe { unreachable_unchecked() },
			_ => semantically_unreachable!(),
			}
	};
}

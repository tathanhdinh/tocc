// P(x) = a0 * x + b0
// Q(x) = a1 *x + b1
// Q(P(x)) = x (i.e. Q = P^(-1))
#[macro_export]
macro_rules! generate_linear_maps {
	($ty:ty) => {{
		use rand::{thread_rng, Rng};
		let mut rng = thread_rng();
		let a0 = {
			let a: $ty = rng.gen();
			if a % 2 == 0 { a + 1 } else { a }
			};
		// let a1 = {
		// 	let mut a1 = a0;
		// 	loop {
		// 		let a1a0 = a1.wrapping_mul(a0);
		// 		if a1a0 == 1 {
		// 			break;
		// 		}
		// 		a1 = a1a0;
		// 		}
		// 	a1
		// 	};
		let a1 = {
			inverse!($ty);
			inverse(a0)
			};
		let b0: $ty = rng.gen();
		let b1 = a1.wrapping_mul(b0).wrapping_neg();

		(a0, b0, a1, b1)
		}};
}

#[macro_export]
macro_rules! generate_polynomial_maps {
	($ty:ty, $m:expr) => {{
		use rand::{thread_rng, Rng};
		use std::mem::size_of;
		let mut rng = thread_rng();
		generate_random_invertible_polynomial!($ty);
		generate_combinations!($ty);
		inverse!($ty);
		generate_master_coefficients!($ty);
		generate_inverted_polynomial!($ty);
		let coeffs = generate_random_invertible_polynomial($m as u8);
		let inv_coeffs = generate_inverted_polynomial(&coeffs);
		(coeffs, inv_coeffs)
		}};
}

#[macro_export]
macro_rules! inverse {
	($ty:ty) => {
		fn inverse(a: $ty) -> $ty {
			let mut inv = 1 as $ty;
			loop {
				let inv_a = inv.wrapping_mul(a);
				if inv_a == 1 {
					break;
				}
				inv = inv_a;
			}
			inv
		}
	};
}

#[macro_export]
macro_rules! generate_random_invertible_polynomial {
	($ty:ty) => {
		fn generate_random_invertible_polynomial(m: u8) -> Vec<$ty> {
			let m = m as usize;
			let mut coeffs = vec![0; m + 1];

			let mut rng = thread_rng();

			coeffs[0] = (1 as $ty)
				<< (rng.gen_range(size_of::<$ty>() as u8 / 2, size_of::<$ty>() as u8) * 8);

			coeffs[1] = {
				let a: $ty = rng.gen();
				if a % 2 == 0 { a + 1 } else { a }
			};

			for i in 2..=m {
				coeffs[i] = (1 as $ty)
					<< (rng.gen_range(size_of::<$ty>() as u8 / 2, size_of::<$ty>() as u8) * 8);
			}

			coeffs
		}
	};
}

#[macro_export]
macro_rules! generate_combinations {
	($ty:ty) => {
		fn generate_combinations(m: u8) -> Vec<Vec<$ty>> {
			let m = m as usize;
			let mut combs = vec![vec![0; m + 1]; m + 1];

			for n in 0..=m {
				// C(0, n)
				combs[0][n] = 1;
			}
			for m in 1..=m {
				for n in m..=m {
					// C(m, n) = C(m - 1, n) + C(m - 1, n - 1)
					combs[m][n] = combs[m - 1][n] + combs[m - 1][n - 1];
				}
			}

			combs
		}
	};
}

#[macro_export]
macro_rules! generate_master_coefficients {
	($ty:ty) => {
		fn generate_master_coefficients(coeff: &[$ty]) -> Vec<$ty> {
			let mut master_coeffs = vec![0; coeff.len()];
			let m = coeff.len() - 1;

			// Am = -a1^(-m) * am
			master_coeffs[m] =
				inverse(coeff[1].wrapping_pow(m as u32)).wrapping_mul(coeff[m]).wrapping_neg();

			let combs = generate_combinations(m as u8);
			for k in (2..m).rev() {
				// Ak = -a1^(-k) * ak - ...
				master_coeffs[k] =
					inverse(coeff[1].wrapping_pow(k as u32)).wrapping_mul(coeff[k]).wrapping_neg();
				for j in (k + 1)..=m {
					master_coeffs[k] = master_coeffs[k].wrapping_sub(
						combs[k][j]
							.wrapping_mul(coeff[0].wrapping_pow((j - k) as u32))
							.wrapping_mul(master_coeffs[j]),
					);
				}
			}

			master_coeffs
		}
	};
}

#[macro_export]
macro_rules! generate_inverted_polynomial {
	($ty:ty) => {
		fn generate_inverted_polynomial(coeff: &[$ty]) -> Vec<$ty> {
			let m = coeff.len() - 1;
			let mut inv_coeffs = vec![0; m + 1];

			let inv_a1 = inverse(coeff[1]);

			// bm = -a1^(-(m + 1)) * am
			inv_coeffs[m] = inv_a1.wrapping_pow(m as u32 + 1).wrapping_mul(coeff[m]).wrapping_neg();

			let combs = generate_combinations(m as u8);
			let master_coeffs = generate_master_coefficients(coeff);
			for k in 2..m {
				inv_coeffs[k] =
					inv_a1.wrapping_pow(k as u32 + 1).wrapping_mul(coeff[k]).wrapping_neg();
				for j in (k + 1)..=m {
					inv_coeffs[k] = inv_coeffs[k].wrapping_sub(
						inv_a1.wrapping_mul(
							combs[k][j]
								.wrapping_mul(coeff[0].wrapping_pow((j - k) as u32))
								.wrapping_mul(master_coeffs[j]),
						),
					)
				}
			}

			inv_coeffs[1] = inv_a1;
			for j in 2..=m {
				inv_coeffs[1] = inv_coeffs[1].wrapping_sub(
					inv_a1.wrapping_mul(
						(j as $ty)
							.wrapping_mul(coeff[0].wrapping_pow(j as u32 + 1))
							.wrapping_mul(master_coeffs[j]),
					),
				);
			}

			inv_coeffs[0] = 0;
			for j in 1..=m {
				inv_coeffs[0] = inv_coeffs[0]
					.wrapping_add(coeff[0].wrapping_pow(j as u32).wrapping_mul(inv_coeffs[j]));
			}
			inv_coeffs[0] = inv_coeffs[0].wrapping_neg();

			inv_coeffs
		}
	};
}

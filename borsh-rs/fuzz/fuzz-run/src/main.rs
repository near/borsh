use borsh::BorshDeserialize;

#[macro_use]
extern crate honggfuzz;

macro_rules! fuzz_types {
	(
		$data:ident;
		$first:ty,
		$( $rest:ty, )*
	) => {
		fuzz_types! {
			@INTERNAL
			$data;
			1u8;
			{ $first; 0u8 }
			$( $rest, )*
		}
	};
	(@INTERNAL
		$data:ident;
		$counter:expr;
		{ $( $parsed:ty; $index:expr ),* }
		$current:ty,
		$( $rest:ty, )*
	) => {
		fuzz_types! {
			@INTERNAL
			$data;
			$counter + 1u8;
			{ $current; $counter $(, $parsed; $index )* }
			$( $rest, )*
		}
	};
	(@INTERNAL
		$data:ident;
		$counter:expr;
		{ $( $parsed:ty; $index:expr ),* }
	) => {
		let num = $counter;
		$(
			if $data[0] % num == $index {
				// Check that decode doesn't panic.
				let _ = <$parsed>::deserialize(&mut &$data[1..]);
				return
			}
		)*

		unreachable!()
	};
}

fn main() {
    loop {
        fuzz!(|data: &[u8]| {
            fuzz_types!(
                data;
                u32,
                u64,
                i32,
                i64,
                f32,
                f64,
                String,);
        });
    }
}

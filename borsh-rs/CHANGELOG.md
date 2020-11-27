# Changelog

## 0.8.0
- Add no_std support.

## 0.7.2
- Implement `BorshSerialize` for reference fields (`&T`)

## 0.7.1
- Implement `BorshSerialize` for `&T` if `T` implements `BorshSerialize`.

## 0.7.0

- Extended `Box<T>` implementation for `?Sized` types (`[T]`, `str`, ...).
- Added support for `std::borrow::Cow`
- Avoid silent integer casts since they can lead to hidden security issues.
- Removed `Cargo.lock` as it is advised for lib crates.


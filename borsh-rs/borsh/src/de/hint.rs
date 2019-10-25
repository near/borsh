#[inline]
pub fn cautious<T>(remaining_len: u32, hint: u32) -> usize {
    let el_size = std::mem::size_of::<T>() as u32;
    let max_len = std::cmp::min(4096/el_size, remaining_len/el_size);
    std::cmp::max(std::cmp::min(hint, max_len), 1u32) as _
}

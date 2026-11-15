#![allow(arithmetic_overflow)]

pub fn checked_add(value: usize) -> usize {
    value + 1
}

pub fn indexed(values: &[u8], index: usize) -> u8 {
    values[index]
}

pub fn explicit() {
    panic!("test panic");
}

pub fn call_explicit() {
    explicit();
}

pub fn helper(value: usize) -> usize {
    value
}

pub fn call_helper(value: usize) -> usize {
    helper(value)
}

pub fn call_indirect(callback: fn(usize) -> usize, value: usize) -> usize {
    callback(value)
}

pub unsafe fn raw_value(pointer: *const u8) -> u8 {
    unsafe { *pointer }
}

unsafe extern "C" {
    fn crash();
}

pub unsafe fn call_c_crash() {
    unsafe { crash() }
}

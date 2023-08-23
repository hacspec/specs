#[cfg(not(feature = "hacspec"))]
use crate::*;

use hacspec_lib::*;

#[cfg(not(feature = "hacspec"))]
pub fn coerce_rust_to_hacspec_public_byte_seq(buf: &[u8]) -> PublicByteSeq {
    PublicByteSeq::from_native_slice(buf)
}

// TODO: Make creusot friendly version
#[cfg(not(feature = "hacspec"))]
pub fn coerce_hacspec_to_rust_public_byte_seq(buf: PublicByteSeq) -> Vec<u8> {
    // buf.native_slice().iter().collect();
    let mut temp_vec: Vec<u8> = Vec::new();
    for i in 0..buf.len() {
        temp_vec.push(buf.index(i).clone())
    }
    temp_vec
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
    pub(crate) fn accept() -> u32;
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn accept_creusot() -> u32 {
    unsafe { accept() }
}

#[cfg(feature = "hacspec")]
pub(crate) fn accept_hacspec() -> u32 {
    1u32
}

#[cfg(not(feature = "hacspec"))]
pub(crate) fn accept_hacspec() -> u32 {
    accept_creusot()
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
  // Basic action to send tokens to an account.
  pub(crate) fn simple_transfer(addr_bytes: *const u8, amount: u64) -> u32;
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn simple_transfer_creusot(addr_bytes: *const u8, amount: u64) -> u32 {
    unsafe { simple_transfer(addr_bytes, amount) }
}

#[cfg(feature = "hacspec")]
pub(crate) fn simple_transfer_hacspec(buf: PublicByteSeq, amount: u64) -> u32 {
    1u32
}

#[cfg(not(feature = "hacspec"))]
pub(crate) fn simple_transfer_hacspec(buf: PublicByteSeq, amount: u64) -> u32 {
    let temp = &mut coerce_hacspec_to_rust_public_byte_seq(buf.clone())[..];
    simple_transfer_creusot(temp.as_ptr(), amount)
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
  // Send a message to a smart contract.
  pub(crate) fn send(
      addr_index: u64,
      addr_subindex: u64,
      receive_name: *const u8,
      receive_name_len: u32,
      amount: u64,
      parameter: *const u8,
      parameter_len: u32,
  ) -> u32;
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn send_creusot(
      addr_index: u64,
      addr_subindex: u64,
      receive_name: *const u8,
      receive_name_len: u32,
      amount: u64,
      parameter: *const u8,
      parameter_len: u32,
  ) -> u32 {
    unsafe { send(addr_index, addr_subindex, receive_name, receive_name_len, amount, parameter, parameter_len) }
}

#[cfg(feature = "hacspec")]
pub(crate) fn send_hacspec(
      addr_index: u64,
      addr_subindex: u64,
      receive_name: PublicByteSeq,
      amount: u64,
      parameter: PublicByteSeq,
  ) -> u32 {
    1u32
}

#[cfg(not(feature = "hacspec"))]
pub(crate) fn send_hacspec(
      addr_index: u64,
      addr_subindex: u64,
      receive_name: PublicByteSeq,
      amount: u64,
      parameter: PublicByteSeq,
  ) -> u32 {
    let temp_receive_name = &mut coerce_hacspec_to_rust_public_byte_seq(receive_name.clone())[..];
    let temp_parameter = &mut coerce_hacspec_to_rust_public_byte_seq(parameter.clone())[..];
    send_creusot(addr_index, addr_subindex, temp_receive_name.as_ptr(), receive_name.len() as u32, amount, temp_parameter.as_ptr(), parameter.len() as u32)
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
  // Combine two actions using normal sequencing. This is using the stack of
  // actions already produced.
  pub(crate) fn combine_and(l: u32, r: u32) -> u32;
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn combine_and_creusot(l: u32, r: u32) -> u32 {
    unsafe { combine_and(l, r) }
}

#[cfg(feature = "hacspec")]
pub(crate) fn combine_and_hacspec(l: u32, r: u32) -> u32 {
    1u32
}

#[cfg(not(feature = "hacspec"))]
pub(crate) fn combine_and_hacspec(l: u32, r: u32) -> u32 {
    combine_and_creusot(l,r)
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
  // Combine two actions using normal sequencing. This is using the stack of
  // actions already produced.
  pub(crate) fn combine_or(l: u32, r: u32) -> u32;
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn combine_or_creusot(l: u32, r: u32) -> u32 {
    unsafe { combine_or(l, r) }
}

#[cfg(feature = "hacspec")]
pub(crate) fn combine_or_hacspec(l: u32, r: u32) -> u32 {
    1u32
}

#[cfg(not(feature = "hacspec"))]
pub(crate) fn combine_or_hacspec(l: u32, r: u32) -> u32 {
    combine_or_creusot(l,r)
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
    // Get the size of the parameter to the method (either init or receive).
    pub(crate) fn get_parameter_size() -> u32;
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn get_parameter_size_creusot() -> u32 {
    unsafe { get_parameter_size() }
}

#[cfg(feature = "hacspec")]
pub(crate) fn get_parameter_size_hacspec() -> u32 {
    1u32
}

#[cfg(not(feature = "hacspec"))]
pub(crate) fn get_parameter_size_hacspec() -> u32 {
    get_parameter_size_creusot()
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
    // Write a section of the parameter to the given location. Return the number
    // of bytes written. The location is assumed to contain enough memory to
    // write the requested length into.
    pub(crate) fn get_parameter_section(param_bytes: *mut u8, length: u32, offset: u32) -> u32;
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn get_parameter_section_creusot(start: *mut u8, length: u32, offset: u32) -> u32 {
    unsafe { get_parameter_section(start, length, offset) }
}

#[cfg(feature = "hacspec")]
pub(crate) fn get_parameter_section_hacspec(buf: PublicByteSeq, offset: u32) -> (PublicByteSeq, u32) {
    (buf, 1u32)
}

#[cfg(not(feature = "hacspec"))]
pub(crate) fn get_parameter_section_hacspec(buf: PublicByteSeq, offset: u32) -> (PublicByteSeq, u32) {
    let temp = &mut coerce_hacspec_to_rust_public_byte_seq(buf.clone())[..];
    let result = get_parameter_section_creusot(temp.as_mut_ptr(), buf.len() as u32, offset);
    (
        coerce_rust_to_hacspec_public_byte_seq(&temp),
        result,
    )
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
  // Write a section of the policy to the given location. Return the number
  // of bytes written. The location is assumed to contain enough memory to
  // write the requested length into.
  pub(crate) fn get_policy_section(policy_bytes: *mut u8, length: u32, offset: u32) -> u32;
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn get_policy_section_creusot(policy_bytes: *mut u8, length: u32, offset: u32) -> u32 {
    unsafe { get_policy_section(policy_bytes, length, offset) }
}

#[cfg(feature = "hacspec")]
pub(crate) fn get_policy_section_hacspec(policy_bytes: PublicByteSeq, offset: u32) -> (PublicByteSeq, u32) {
    (policy_bytes, 1u32)
}

#[cfg(not(feature = "hacspec"))]
pub(crate) fn get_policy_section_hacspec(policy_bytes: PublicByteSeq, offset: u32) -> (PublicByteSeq, u32) {
    let temp = &mut coerce_hacspec_to_rust_public_byte_seq(policy_bytes.clone())[..];
    let result = get_policy_section_creusot(temp.as_mut_ptr(), policy_bytes.len() as u32, offset);
    (
        coerce_rust_to_hacspec_public_byte_seq(&temp),
        result,
    )
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
    // Add a log item. Return values are
    // - -1 if logging failed due to the message being too long
    // - 0 if the log is already full
    // - 1 if data was successfully logged.
    pub(crate) fn log_event(start: *const u8, length: u32) -> i32;
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn log_event_creusot(start: *const u8, length: u32) -> i32 {
    unsafe { log_event(start, length) }
}

#[cfg(feature = "hacspec")]
pub(crate) fn log_event_hacspec(start: PublicByteSeq) -> (PublicByteSeq, i32) {
    (start, 1i32)
}

#[cfg(not(feature = "hacspec"))]
pub(crate) fn log_event_hacspec(start: PublicByteSeq) -> (PublicByteSeq, i32) {
    let temp = &mut coerce_hacspec_to_rust_public_byte_seq(start.clone())[..];
    let result = log_event_creusot(temp.as_ptr(), start.len() as u32);
    (coerce_rust_to_hacspec_public_byte_seq(&temp), result)
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
    pub(crate) fn load_state(start: *mut u8, length: u32, offset: u32) -> u32;
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn load_state_creusot(start: *mut u8, length: u32, offset: u32) -> u32 {
    unsafe { load_state(start, length, offset) }
}

#[cfg(feature = "hacspec")]
pub(crate) fn load_state_hacspec(buf: PublicByteSeq, offset: u32) -> (PublicByteSeq, u32) {
    (buf, 1u32)
}

#[cfg(not(feature = "hacspec"))]
pub(crate) fn load_state_hacspec(buf: PublicByteSeq, offset: u32) -> (PublicByteSeq, u32) {
    let temp = &mut coerce_hacspec_to_rust_public_byte_seq(buf.clone())[..];
    let result = load_state_creusot(temp.as_mut_ptr(), buf.len() as u32, offset);
    (coerce_rust_to_hacspec_public_byte_seq(&temp), result)
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
    pub(crate) fn write_state(start: *mut u8, length: u32, offset: u32) -> u32;
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn write_state_creusot(start: *mut u8, length: u32, offset: u32) -> u32 {
    unsafe { write_state(start, length, offset) }
}

#[cfg(feature = "hacspec")]
pub(crate) fn write_state_hacspec(buf: PublicByteSeq, offset: u32) -> (PublicByteSeq, u32) {
    (buf, 1u32)
}

#[cfg(not(feature = "hacspec"))]
pub(crate) fn write_state_hacspec(buf: PublicByteSeq, offset: u32) -> (PublicByteSeq, u32) {
    let temp = &mut coerce_hacspec_to_rust_public_byte_seq(buf.clone())[..];
    let result = write_state_creusot(temp.as_mut_ptr(), buf.len() as u32, offset);
    (coerce_rust_to_hacspec_public_byte_seq(&temp), result)
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
    // Resize state to the new value (truncate if new size is smaller). Return 0 if
    // this was unsuccesful (new state too big), or 1 if successful.
    pub(crate) fn resize_state(new_size: u32) -> u32; // returns 0 or 1.
                                                      // get current state size in bytes.
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn resize_state_creusot(new_size: u32) -> u32 {
    unsafe { resize_state(new_size) }
}

#[cfg(feature = "hacspec")]
pub(crate) fn resize_state_hacspec(new_size: u32) -> u32 {
    1u32
}

#[cfg(not(feature = "hacspec"))]
pub(crate) fn resize_state_hacspec(new_size: u32) -> u32 {
    resize_state_creusot(new_size)
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
    pub(crate) fn state_size() -> u32;
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn state_size_creusot() -> u32 {
    unsafe { state_size() }
}

#[cfg(feature = "hacspec")]
pub(crate) fn state_size_hacspec() -> u32 {
    1u32
}

#[cfg(not(feature = "hacspec"))]
pub(crate) fn state_size_hacspec() -> u32 {
    state_size_creusot()
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
  // Getter for the init context.
  /// Address of the sender, 32 bytes
  pub(crate) fn get_init_origin(start: *mut u8);
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn get_init_origin_creusot(start: *mut u8) {
    unsafe { get_init_origin(start) }
}

#[cfg(feature = "hacspec")]
pub(crate) fn get_init_origin_hacspec(start: PublicByteSeq) -> PublicByteSeq {
    start
}

#[cfg(not(feature = "hacspec"))]
pub(crate) fn get_init_origin_hacspec(start: PublicByteSeq) -> PublicByteSeq {
    let temp = &mut coerce_hacspec_to_rust_public_byte_seq(start.clone())[..];
    get_init_origin_creusot(temp.as_mut_ptr());
    coerce_rust_to_hacspec_public_byte_seq(&temp)
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
  /// Invoker of the top-level transaction, AccountAddress.
  pub(crate) fn get_receive_invoker(start: *mut u8);
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn get_receive_invoker_creusot(start: *mut u8) {
    unsafe { get_receive_invoker(start) }
}

#[cfg(feature = "hacspec")]
pub(crate) fn get_receive_invoker_hacspec(start: PublicByteSeq) -> PublicByteSeq {
    start
}

#[cfg(not(feature = "hacspec"))]
pub(crate) fn get_receive_invoker_hacspec(start: PublicByteSeq) -> PublicByteSeq {
    let temp = &mut coerce_hacspec_to_rust_public_byte_seq(start.clone())[..];
    get_receive_invoker_creusot(temp.as_mut_ptr());
    coerce_rust_to_hacspec_public_byte_seq(&temp)
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
  /// Address of the contract itself, ContractAddress.
  pub(crate) fn get_receive_self_address(start: *mut u8);
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn get_receive_self_address_creusot(start: *mut u8) {
    unsafe { get_receive_self_address(start) }
}

#[cfg(feature = "hacspec")]
pub(crate) fn get_receive_self_address_hacspec(start: PublicByteSeq) -> PublicByteSeq {
    start
}

#[cfg(not(feature = "hacspec"))]
pub(crate) fn get_receive_self_address_hacspec(start: PublicByteSeq) -> PublicByteSeq {
    let temp = &mut coerce_hacspec_to_rust_public_byte_seq(start.clone())[..];
    get_receive_self_address_creusot(temp.as_mut_ptr());
    coerce_rust_to_hacspec_public_byte_seq(&temp)
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
  /// Self-balance of the contract, returns the amount
  pub(crate) fn get_receive_self_balance() -> u64;
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn get_receive_self_balance_creusot() -> u64 {
    unsafe { get_receive_self_balance() }
}

#[cfg(feature = "hacspec")]
pub(crate) fn get_receive_self_balance_hacspec() -> u64 {
    1u64
}

#[cfg(not(feature = "hacspec"))]
pub(crate) fn get_receive_self_balance_hacspec() -> u64 {
    get_receive_self_balance_creusot()
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
  /// Immediate sender of the message (either contract or account).
  pub(crate) fn get_receive_sender(start: *mut u8);
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn get_receive_sender_creusot(start: *mut u8) {
    unsafe { get_receive_sender(start) }
}

#[cfg(feature = "hacspec")]
pub(crate) fn get_receive_sender_hacspec(start: PublicByteSeq) -> PublicByteSeq {
    start
}

#[cfg(not(feature = "hacspec"))]
pub(crate) fn get_receive_sender_hacspec(start: PublicByteSeq) -> PublicByteSeq {
    let temp = &mut coerce_hacspec_to_rust_public_byte_seq(start.clone())[..];
    get_receive_sender_creusot(temp.as_mut_ptr());
    coerce_rust_to_hacspec_public_byte_seq(&temp)
}

#[cfg(not(feature = "hacspec"))]
extern "C" {
  // Getters for the chain meta data
  /// Slot time (in milliseconds) from chain meta data
  pub(crate) fn get_slot_time() -> u64;
}

#[cfg(not(feature = "hacspec"))]
#[trusted]
pub(crate) fn get_slot_time_creusot() -> u64 {
    unsafe { get_slot_time() }
}

#[cfg(feature = "hacspec")]
pub(crate) fn get_slot_time_hacspec() -> u64 {
    1u64
}

#[cfg(not(feature = "hacspec"))]
pub(crate) fn get_slot_time_hacspec() -> u64 {
    get_slot_time_creusot()
}

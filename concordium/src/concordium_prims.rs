#![feature(register_tool)]
#![register_tool(hax)]

#[hax_lib_macros::exclude]
extern crate hax_lib_macros;
#[hax_lib_macros::exclude]
use hax_lib_macros::*;

#[exclude]
use crate::*;

extern "C" {
    pub(crate) fn accept() -> u32;
}

extern "C" {
  // Basic action to send tokens to an account.
  pub(crate) fn simple_transfer(addr_bytes: *const u8, amount: u64) -> u32;
}

extern "C" {
  // Send a message to a smart contract.
  pub// (crate)
    fn send(
      addr_index: u64,
      addr_subindex: u64,
      receive_name: *const u8,
      receive_name_len: u32,
      amount: u64,
      parameter: *const u8,
      parameter_len: u32,
  ) -> u32;
}

extern "C" {
  // Combine two actions using normal sequencing. This is using the stack of
  // actions already produced.
  pub(crate) fn combine_and(l: u32, r: u32) -> u32;
}

extern "C" {
  // Combine two actions using normal sequencing. This is using the stack of
  // actions already produced.
  pub(crate) fn combine_or(l: u32, r: u32) -> u32;
}

extern "C" {
    // Get the size of the parameter to the method (either init or receive).
    pub(crate) fn get_parameter_size() -> u32;
}

extern "C" {
    // Write a section of the parameter to the given location. Return the number
    // of bytes written. The location is assumed to contain enough memory to
    // write the requested length into.
    pub(crate) fn get_parameter_section(param_bytes: *mut u8, length: u32, offset: u32) -> u32;
}

extern "C" {
  // Write a section of the policy to the given location. Return the number
  // of bytes written. The location is assumed to contain enough memory to
  // write the requested length into.
  pub(crate) fn get_policy_section(policy_bytes: *mut u8, length: u32, offset: u32) -> u32;
}

extern "C" {
    // Add a log item. Return values are
    // - -1 if logging failed due to the message being too long
    // - 0 if the log is already full
    // - 1 if data was successfully logged.
    pub(crate) fn log_event(start: *const u8, length: u32) -> i32;
}

extern "C" {
    pub(crate) fn load_state(start: *mut u8, length: u32, offset: u32) -> u32;
}

extern "C" {
    pub(crate) fn write_state(start: *mut u8, length: u32, offset: u32) -> u32;
}

extern "C" {
    // Resize state to the new value (truncate if new size is smaller). Return 0 if
    // this was unsuccesful (new state too big), or 1 if successful.
    pub(crate) fn resize_state(new_size: u32) -> u32; // returns 0 or 1.
                                                      // get current state size in bytes.
}

extern "C" {
    pub(crate) fn state_size() -> u32;
}

extern "C" {
  // Getter for the init context.
  /// Address of the sender, 32 bytes
  pub(crate) fn get_init_origin(start: *mut u8);
}

extern "C" {
  /// Invoker of the top-level transaction, AccountAddress.
  pub(crate) fn get_receive_invoker(start: *mut u8);
}

extern "C" {
  /// Address of the contract itself, ContractAddress.
  pub(crate) fn get_receive_self_address(start: *mut u8);
}

extern "C" {
  /// Self-balance of the contract, returns the amount
  pub(crate) fn get_receive_self_balance() -> u64;
}

extern "C" {
  /// Immediate sender of the message (either contract or account).
  pub(crate) fn get_receive_sender(start: *mut u8);
}

extern "C" {
  // Getters for the chain meta data
  /// Slot time (in milliseconds) from chain meta data
  pub(crate) fn get_slot_time() -> u64;
}

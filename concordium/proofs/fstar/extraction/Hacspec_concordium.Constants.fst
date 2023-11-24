module Hacspec_concordium.Constants
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let v_MAX_CONTRACT_STATE_SIZE: u32 = 16384ul

let v_MAX_LOG_SIZE: usize = sz 512

let v_MAX_NUM_LOGS: usize = sz 64
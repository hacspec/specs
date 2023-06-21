mod hacspec_helper;
use hacspec_helper::*;

type State = [u32; 16];
type Block = [u8; 64];
type ChaChaIV = [u8; 12];
type ChaChaKey = [u8; 32];

// #[derive(Copy, Clone)]
// pub struct StateIdx(usize);

// impl std::ops::Index<StateIdx> for State {
//     type Output = u32;
//     fn index(&self, StateIdx(i): StateIdx) -> &u32 {
//         self.index(i)
//     }
// }
// impl std::ops::IndexMut<StateIdx> for State {
//     fn index_mut(&mut self, StateIdx(i): StateIdx) -> &mut u32 {
//         self.index_mut(i)
//     }
// }

type StateIdx = usize;
fn _StateIdx(x: usize) -> usize {x}

fn chacha20_line(a: StateIdx, b: StateIdx, d: StateIdx, s: u32, m: State) -> State {
    let mut state = m;
    state[a] = state[a].wrapping_add(state[b]);
    state[d] = state[d] ^ state[a];
    state[d] = state[d].rotate_left(s);
    state
}

pub fn chacha20_quarter_round(a: StateIdx, b: StateIdx, c: StateIdx, d: StateIdx, state: State) -> State {
    let state = chacha20_line(a, b, d, 16, state);
    let state = chacha20_line(c, d, b, 12, state);
    let state = chacha20_line(a, b, d, 8, state);
    chacha20_line(c, d, b, 7, state)
}

fn chacha20_double_round(state: State) -> State {
    let state = chacha20_quarter_round(_StateIdx(0), _StateIdx(4), _StateIdx(8), _StateIdx(12), state);
    let state = chacha20_quarter_round(_StateIdx(1), _StateIdx(5), _StateIdx(9), _StateIdx(13), state);
    let state = chacha20_quarter_round(_StateIdx(2), _StateIdx(6), _StateIdx(10), _StateIdx(14), state);
    let state = chacha20_quarter_round(_StateIdx(3), _StateIdx(7), _StateIdx(11), _StateIdx(15), state);

    let state = chacha20_quarter_round(_StateIdx(0), _StateIdx(5), _StateIdx(10), _StateIdx(15), state);
    let state = chacha20_quarter_round(_StateIdx(1), _StateIdx(6), _StateIdx(11), _StateIdx(12), state);
    let state = chacha20_quarter_round(_StateIdx(2), _StateIdx(7), _StateIdx(8), _StateIdx(13), state);
    chacha20_quarter_round(_StateIdx(3), _StateIdx(4), _StateIdx(9), _StateIdx(14), state)
}

pub fn chacha20_rounds(state: State) -> State {
    let mut st = state;
    for _i in 0usize..10usize {
        st = chacha20_double_round(st);
    }
    st
}

pub fn chacha20_core(ctr: u32, st0: State) -> State {
    let mut state = st0;
    state[12] = state[12].wrapping_add(ctr);
    let k = chacha20_rounds(state);
    add_state(state, k)
}

pub fn chacha20_init(key: &ChaChaKey, iv: &ChaChaIV, ctr: u32) -> State {
    let key_u32: [u32; 8] = to_le_u32s_8(key);
    let iv_u32: [u32; 3] = to_le_u32s_3(iv);
    [
        0x6170_7865,
        0x3320_646e,
        0x7962_2d32,
        0x6b20_6574,
        key_u32[0],
        key_u32[1],
        key_u32[2],
        key_u32[3],
        key_u32[4],
        key_u32[5],
        key_u32[6],
        key_u32[7],
        ctr,
        iv_u32[0],
        iv_u32[1],
        iv_u32[2],
    ]
}

pub fn chacha20_key_block(state: State) -> Block {
    let state = chacha20_core(0u32, state);
    u32s_to_le_bytes(&state)
}

pub fn chacha20_key_block0(key: &ChaChaKey, iv: &ChaChaIV) -> Block {
    let state = chacha20_init(key, iv, 0u32);
    chacha20_key_block(state)
}

pub fn chacha20_encrypt_block(st0: State, ctr: u32, plain: &Block) -> Block {
    let st = chacha20_core(ctr, st0);
    let pl: State = to_le_u32s_16(plain);
    let encrypted = xor_state(st, pl);
    u32s_to_le_bytes(&encrypted)
}

pub fn chacha20_encrypt_last(st0: State, ctr: u32, plain: &[u8]) -> Vec<u8> {
    let mut b: Block = [0; 64];
    b = update_array(b, plain);
    b = chacha20_encrypt_block(st0, ctr, &b);
    b[..plain.len()].to_vec()
}

pub fn chacha20_update(st0: State, m: &[u8]) -> Vec<u8> {
    let mut blocks_out = Vec::new();
    let num_blocks = m.len() / 64;
    let remainder_len = m.len() % 64;
    // for (i, msg_block) in m.chunks(64).enumerate() {
    for i in 0..num_blocks {
        // if msg_block.len() != 64 {
        // } else {
        // Full block
        let b =
            chacha20_encrypt_block(st0, i as u32, &m[64 * i..(64 * i + 64)].try_into().unwrap());
        blocks_out.extend_from_slice(&b);
        // }
    }
    if remainder_len != 0 {
        // Last block
        let b = chacha20_encrypt_last(st0, num_blocks as u32, &m[64 * num_blocks..]);
        blocks_out.extend_from_slice(&b);
    }
    blocks_out
}

pub fn chacha20(m: &[u8], key: &ChaChaKey, iv: &ChaChaIV, ctr: u32) -> Vec<u8> {
    let state = chacha20_init(key, iv, ctr);
    chacha20_update(state, m)
}


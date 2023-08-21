use hacspec_lib::*;

mod schnorr;
use schnorr::*;

// (Exec_i i j m) ∘ (par ((P_i i b) ∘ (Sigma1.Sigma.Fiat_Shamir ∘ RO1.RO)) (Sigma1.Sigma.Fiat_Shamir ∘ RO1.RO))

// Init, construct, vote:
//
// Definition P_i (i : pid) (b : bool):
//     package (P_i_locs i)
//       Sigma1_I
//       P_i_E :=
//     [package
//         #def #[ INIT ] (_ : 'unit) : 'public_key
//         {
//           #import {sig #[ Sigma1.Sigma.RUN ] : chRelation1 → chTranscript1} as ZKP ;;
//           #import {sig #[ Sigma1.Sigma.VERIFY ] : chTranscript1 → 'bool} as VER ;;
//           x ← sample uniform i_secret ;;
//           #put (skey_loc i) := x ;;
//           let y := (fto (g ^+ (otf x))) : public in
//             zkp ← ZKP (y, x) ;;
//             ret (y, zkp)
//         }
//         ;
//         #def #[ CONSTRUCT ] (m : 'public_keys) : 'unit
//         {
//           #import {sig #[ Sigma1.Sigma.VERIFY ] : chTranscript1 → 'bool} as VER ;;
//           #assert (size (domm m) == n) ;;
//           let key := fto (compute_key m i) in
//           #put (ckey_loc i) := key ;;
//           @ret 'unit Datatypes.tt
//         }
//         ;
//         #def #[ VOTE ] (v : 'bool) : 'public
//         {
//           skey ← get (skey_loc i) ;;
//           ckey ← get (ckey_loc i) ;;
//           if b then
//             let vote := (otf ckey ^+ skey * g ^+ v) in
//             @ret 'public (fto vote)
//           else
//             let vote := (otf ckey ^+ skey * g ^+ (negb v)) in
//             @ret 'public (fto vote)
//         }
//     ].

type Secret = schnorr::random_oracle::Q; // Zp_finComRingType (Zp_trunc #[g]);
// pub fn sample_uniform () -> Secret {
//     schnorr::random_oracle::Q{v: 1} // Secret::ONE()
// }

type public = schnorr::random_oracle::G;
type public_key = (public, schnorr::Transcript); // (public, (schnorr::random_oracle::Message , schnorr::random_oracle::Challenge , schnorr::random_oracle::Response))
fn p_i_init(_: (), uniform_sample : Secret, uniform_sample_R1 : schnorr::random_oracle::Random, uniform_sample_R2 : schnorr::random_oracle::Random) -> public_key {
    // #import {sig #[ Sigma1.Sigma.RUN ] : chRelation1 → chTranscript1} as ZKP ;;
    // #import {sig #[ Sigma1.Sigma.VERIFY ] : chTranscript1 → 'bool} as VER ;;
    // x ← sample uniform i_secret ;;
    let x = uniform_sample; // sample_uniform();
    // #put (skey_loc i) := x ;;
    // let y := (fto (g ^+ (otf x))) : public in
    let y = schnorr::random_oracle::G::ONE() // {v: 1}
    ; // public::ONE();
    // zkp ← ZKP (y, x) ;;
    let zkp = schnorr::fiat_shamir_run((y, x), uniform_sample_R1, uniform_sample_R2);
    (y, zkp)
}

// fn compute_key (m : chMap pid (chProd public choiceTranscript1), i : pid) {
//     let low := \prod_(k <- domm m | (k < i)%ord) (get_value m k);
//     let high := \prod_(k <- domm m | (i < k)%ord) (get_value m k);
//     low * invg high
//     }

// Order of G
public_nat_mod!( //Custom Macro - defining a newtype with some functions - well defined macro's have library functions built in
    type_name: N,
    type_of_canvas: NCanvas,
    bit_size_of_field: 384, //381 with 3 extra bits
    modulo_value: "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab" //0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
);

type pid = N;
use std::collections::HashMap;

type public_keys = HashMap<pid, (public, schnorr::Transcript)>; // TODO
fn p_i_construct(m: public_keys) -> () {
    // #import {sig #[ Sigma1.Sigma.VERIFY ] : chTranscript1 → 'bool} as VER ;;
    // #assert (size (domm m) == n) ;;
    // let key := fto (compute_key m i) in
    // #put (ckey_loc i) := key ;;
    // @ret 'unit Datatypes.tt
    ()
}

fn p_i_vote(v: bool) -> public {
    // skey ← get (skey_loc i) ;;
    // ckey ← get (ckey_loc i) ;;
    // if b then
    //     let vote := (otf ckey ^+ skey * g ^+ v) in
    //     @ret 'public (fto vote)
    // else
    //     let vote := (otf ckey ^+ skey * g ^+ (negb v)) in
    //     @ret 'public (fto vote)
    schnorr::random_oracle::G::ONE()// {v: 1}
    // public::ONE()
}

// Exec_i
// [package
//         #def #[ Exec i ] (v : 'bool) : 'public
//         {
//           #import {sig #[ INIT ] : 'unit → 'public_key} as Init ;;
//           #import {sig #[ CONSTRUCT ] : 'public_keys → 'unit} as Construct ;;
//           #import {sig #[ VOTE ] : 'bool → 'public} as Vote ;;
//           #import {sig #[ Sigma1.Sigma.RUN ] : chRelation1 → chTranscript1} as ZKP ;;
//           pk ← Init Datatypes.tt ;;
//           x ← sample uniform i_secret ;;
//           let y := (fto (g ^+ (otf x))) : public in
//             zkp ← ZKP (y, x) ;;
//             let m' := setm (setm m j (y, zkp)) i pk in
//               Construct m' ;;
//               vote ← Vote v ;;
//               @ret 'public vote
//         }
//     ]

fn exec(v : bool,uniform_sample : Secret, uniform_sample_R1 : schnorr::random_oracle::Random, uniform_sample_R2 : schnorr::random_oracle::Random) -> public {
    // #import {sig #[ INIT ] : 'unit → 'public_key} as Init ;;
    // #import {sig #[ CONSTRUCT ] : 'public_keys → 'unit} as Construct ;;
    // #import {sig #[ VOTE ] : 'bool → 'public} as Vote ;;
    // #import {sig #[ Sigma1.Sigma.RUN ] : chRelation1 → chTranscript1} as ZKP ;;
    // pk ← Init Datatypes.tt ;;
    // x ← sample uniform i_secret ;;
    let x = uniform_sample;
    // let y := (fto (g ^+ (otf x))) : public in
    let y = schnorr::random_oracle::G::ONE()// {v: 1}
    ; // public::ONE();
    //     zkp ← ZKP (y, x) ;;
    let zkp = schnorr::fiat_shamir_run((y, x),uniform_sample_R1,uniform_sample_R2);
    // let m' := setm (setm m j (y, zkp)) i pk in
    //     Construct m' ;;
    // vote ← Vote v ;;
    let vote = p_i_vote (v);
    // @ret 'public vote
    vote
}

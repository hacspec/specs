/**************************/
/*** Random Oracle file ***/
/**************************/

use hacspec_lib::*;

// INIT , QUERY (RO (RandomOracle) OracleParams)
// Definition RO : package RO_locs [interface] RO_exports :=
//   [package
//     #def #[ INIT ] (_ : 'unit) : 'unit
//     {
//       #put queries_loc := emptym ;;
//       ret Datatypes.tt
//     } ;
//     #def #[ QUERY ] (q : 'query) : 'random
//     {
//       queries ← get queries_loc ;;
//       match queries q with
//       | Some r =>
//         ret r
//       | None =>
//         r ← sample uniform i_random ;;
//         #put queries_loc := setm queries q r ;;
//         ret r
//       end
//     }
//   ].

pub fn random_oracle_init(_ : ()) -> () {
    ()
}

// #[derive(PartialEq, Eq, Clone, Copy)]
// pub struct G{
//     pub v : u32
// }
public_nat_mod!( //Custom Macro - defining a newtype with some functions - well defined macro's have library functions built in
    type_name: G,
    type_of_canvas: GCanvas,
    bit_size_of_field: 384, //381 with 3 extra bits
    modulo_value: "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab" //0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
);

// #[derive(PartialEq, Eq, Clone, Copy, Hash)]
// pub struct Q {
//     pub v : u32
// }
// Order of G
public_nat_mod!( //Custom Macro - defining a newtype with some functions - well defined macro's have library functions built in
    type_name: Q,
    type_of_canvas: QCanvas,
    bit_size_of_field: 384, //381 with 3 extra bits
    modulo_value: "2566" // TODO Order of group G!
);

pub type Witness = Q;
pub type Statement = G;
pub type Message = G;
pub type Challenge = Q;
pub type Response =  Q;

pub type Random = Challenge; // (Statement, Message);
pub type Query = Challenge;

// pub fn sample_uniform () -> Random {
//     uniform_sample
//     // (G{v: 1}, G{v: 1})// (Statement::ONE(), Message::ONE())
// }

use std::collections::HashMap;

use std::hash::*;
// use std::hash::{Hash, Hasher};
impl Hash for Query {
    fn hash<H: Hasher> (&self, state: &mut H) {

    }
}


pub type QueriesType = HashMap<Query, Random>;
// static ref QUERIES : HashMap<Query, Random> = HashMap::new();
// chQuery  := 'fin #|Query|
// chRandom := 'fin #|Random|
pub fn random_oracle_query(mut QUERIES : QueriesType, q : Query, uniform_sample : Random) -> (QueriesType, Random) {
    match QUERIES.get(&q)
                 {
        Some (r) => (QUERIES.clone(), r.clone()),
        None => {
            let r = uniform_sample;
            QUERIES.insert(q, r);
            (QUERIES, r)
        }
    }
}

/********************/
/*** Schnorr file ***/
/********************/

// use hacspec_lib::*;
// use std::collections::HashMap;

// pub mod random_oracle;
// use random_oracle::*;
// type Transcript = (Message, Challenge, Response);

// Sigma1.Sigma.RUN and Sigma1.Sigma.VERIFY: (Schnorr, RO (RandomOracle) OracleParams)
// Definition Fiat_Shamir :
//   package Sigma_locs
//     [interface
//       #val #[ INIT ] : 'unit → 'unit ;
//       #val #[ QUERY ] : 'query → 'random
//     ]
//     [interface
//       #val #[ VERIFY ] : chTranscript → 'bool ;
//       #val #[ RUN ] : chRelation → chTranscript
//     ]
//   :=
//   [package
//     #def #[ VERIFY ] (t : chTranscript) : 'bool
//     {
//       #import {sig #[ QUERY ] : 'query → 'random } as RO_query ;;
//       let '(h,a,e,z) := t in
//       e ← RO_query (prod_assoc (h, a)) ;;
//       ret (otf (Verify h a e z))
//     } ;
//     #def #[ RUN ] (hw : chRelation) : chTranscript
//     {
//       #import {sig #[ INIT ] : 'unit → 'unit } as RO_init ;;
//       #import {sig #[ QUERY ] : 'query → 'random } as RO_query ;;
//       let '(h,w) := hw in
//       #assert (R (otf h) (otf w)) ;;
//       a ← Commit h w ;;
//       RO_init Datatypes.tt ;;
//       e ← RO_query (prod_assoc (h, a)) ;;
//       z ← Response h w a e ;;
//       @ret choiceTranscript (h,a,e,z)
//     }
//   ].

pub type Transcript = (Statement , Message , Challenge , Response);

fn prod_assoc (sm : (Statement, Message)) -> // random_oracle::
Query {
    let (statement, message) = sm;
    // Proof.
    //   cbn. intros [statement message].
    //   rewrite !card_prod.
    //   apply mxvec_index. all: assumption.
    // Qed.
    // random_oracle::
    Q::ONE()// {v: 1}
    // random_oracle::Query::ONE()
}

// Verify_schamir
fn verify (h : Statement, a : Message, e : Challenge, z : Response) -> bool {
    // fto (g ^+ (otf z) == (otf a) * (otf h) ^+ (otf e))
    false
}

pub fn fiat_shamir_verify(t : Transcript, uniform_sample : Random) -> bool {
    let QUERIES = HashMap::new();
    let (h,a,e,z) = t;
    let (QUERIES, eu) = // random_oracle::
    random_oracle_query (QUERIES, prod_assoc ((h, a)), uniform_sample);
    // e <- eu;
    // otf (
    verify (h, a, e, z)
    // )
}

pub type Relation = (Statement, Witness);

fn Commit (h : Statement, w : Witness, uniform_sample : Random) -> Message {
    // r ← sample uniform i_witness ;;
    let r = uniform_sample;
    // #put commit_loc := r ;;
    let mut commit = r;
    // ret (fto (g ^+ (otf r)))
    // G{v: 1}
    G::ONE()
    // Message::ONE()
}


fn Response (h : Statement, w : Witness, a : Message, e : Challenge) -> Response {
    // r ← get commit_loc ;;
    // ret (fto (otf r + otf e * otf w))
    Q::ONE()// {v: 1}
    // Response::ONE()
}

pub fn fiat_shamir_run(hw : Relation, uniform_sample_1 : Random, uniform_sample_2 : Random) -> Transcript {
    let QUERIES = HashMap::new();
    // #import {sig #[ INIT ] : 'unit → 'unit } as RO_init ;;
    // #import {sig #[ QUERY ] : 'query → 'random } as RO_query ;;
    let (h,w) = hw;
    // #assert (R (otf h) (otf w)) ;;
    let a = Commit(h, w, uniform_sample_1);
    // random_oracle::
    random_oracle_init(());
    let (QUERIES, eu) = // random_oracle::
    random_oracle_query(QUERIES, prod_assoc((h, a)), uniform_sample_2);
    let e = Q::ONE()// {v: 1}
    ; // Challenge::ONE(); // Should be e <- eu
    let z = Response (h, w, a, e);
    (h,a,e,z)
}

// use hacspec_lib::*;

// mod schnorr;
// use schnorr::*;

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

type Secret = // schnorr::random_oracle::
Q; // Zp_finComRingType (Zp_trunc #[g]);
// pub fn sample_uniform () -> Secret {
//     schnorr::random_oracle::Q{v: 1} // Secret::ONE()
// }

type public = // schnorr::random_oracle::
G;
type public_key = (public, // schnorr::
                   Transcript); // (public, (schnorr::random_oracle::Message , schnorr::random_oracle::Challenge , schnorr::random_oracle::Response))
fn p_i_init(_: (), uniform_sample : Secret, uniform_sample_R1 : // schnorr::random_oracle::
            Random, uniform_sample_R2 : // schnorr::random_oracle::
            Random) -> public_key {
    // #import {sig #[ Sigma1.Sigma.RUN ] : chRelation1 → chTranscript1} as ZKP ;;
    // #import {sig #[ Sigma1.Sigma.VERIFY ] : chTranscript1 → 'bool} as VER ;;
    // x ← sample uniform i_secret ;;
    let x = uniform_sample; // sample_uniform();
    // #put (skey_loc i) := x ;;
    // let y := (fto (g ^+ (otf x))) : public in
    let y = // schnorr::random_oracle::
    G::ONE() // {v: 1}
    ; // public::ONE();
    // zkp ← ZKP (y, x) ;;
    let zkp = // schnorr::
    fiat_shamir_run((y, x), uniform_sample_R1, uniform_sample_R2);
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
// use std::collections::HashMap;

type public_keys = HashMap<pid, (public, // schnorr::
                                 Transcript)>; // TODO
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
    // schnorr::random_oracle::
    G::ONE()// {v: 1}
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

fn exec(v : bool,uniform_sample : Secret, uniform_sample_R1 : // schnorr::random_oracle::
        Random, uniform_sample_R2 : // schnorr::random_oracle::
        Random) -> public {
    // #import {sig #[ INIT ] : 'unit → 'public_key} as Init ;;
    // #import {sig #[ CONSTRUCT ] : 'public_keys → 'unit} as Construct ;;
    // #import {sig #[ VOTE ] : 'bool → 'public} as Vote ;;
    // #import {sig #[ Sigma1.Sigma.RUN ] : chRelation1 → chTranscript1} as ZKP ;;
    // pk ← Init Datatypes.tt ;;
    // x ← sample uniform i_secret ;;
    let x = uniform_sample;
    // let y := (fto (g ^+ (otf x))) : public in
    let y = // schnorr::random_oracle::
    G::ONE()// {v: 1}
    ; // public::ONE();
    //     zkp ← ZKP (y, x) ;;
    let zkp = // schnorr::
    fiat_shamir_run((y, x),uniform_sample_R1,uniform_sample_R2);
    // let m' := setm (setm m j (y, zkp)) i pk in
    //     Construct m' ;;
    // vote ← Vote v ;;
    let vote = p_i_vote (v);
    // @ret 'public vote
    vote
}

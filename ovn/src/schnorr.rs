use hacspec_lib::*;
use std::collections::HashMap;

pub mod random_oracle;
// use random_oracle::*;

pub type Witness = random_oracle::Q;
pub type Statement = random_oracle::G;
pub type Message = random_oracle::G;
pub type Challenge = random_oracle::Q;
pub type Response =  random_oracle::G;
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

fn prod_assoc ((statement, message) : (Statement, Message)) -> random_oracle::Query {
    // Proof.
    //   cbn. intros [statement message].
    //   rewrite !card_prod.
    //   apply mxvec_index. all: assumption.
    // Qed.
    random_oracle::Query::ONE()
}

// Verify_schamir
fn verify (h : Statement, a : Message, e : Challenge, z : Response) -> bool {
    // fto (g ^+ (otf z) == (otf a) * (otf h) ^+ (otf e))
    false
}

pub fn fiat_shamir_verify(t : Transcript) -> bool {
    let QUERIES = HashMap::new();
    let (h,a,e,z) = t;
    let (QUERIES, eu) = random_oracle::random_oracle_query (QUERIES, prod_assoc ((h, a)));
    // e <- eu;
    // otf (
    verify (h, a, e, z)
    // )
}

pub type Relation = (Statement, Witness);

fn Commit (h : Statement, w : Witness) -> Message {
    // r ← sample uniform i_witness ;;
    let r = random_oracle::sample_uniform();
    // #put commit_loc := r ;;
    let mut commit = r;
    // ret (fto (g ^+ (otf r)))
    Message::ONE()
}


fn Response (h : Statement, w : Witness, a : Message, e : Challenge) -> Response {
    // r ← get commit_loc ;;
    // ret (fto (otf r + otf e * otf w))
    Response::ONE()
}

pub fn fiat_shamir_run(hw : Relation) -> Transcript {
    let QUERIES = HashMap::new();
    // #import {sig #[ INIT ] : 'unit → 'unit } as RO_init ;;
    // #import {sig #[ QUERY ] : 'query → 'random } as RO_query ;;
    let (h,w) = hw;
    // #assert (R (otf h) (otf w)) ;;
    let a = Commit(h, w);
    // RO_init Datatypes.tt ;;
    random_oracle::random_oracle_init(());
    // e ← RO_query (prod_assoc (h, a)) ;;
    let (QUERIES, eu) = random_oracle::random_oracle_query(QUERIES, prod_assoc((h, a)));
    let e = Challenge::ONE(); // Should be e <- eu
    // z ← Response h w a e ;;
    let z = Response (h, w, a, e);
    // @ret choiceTranscript (h,a,e,z)
    (h,a,e,z)
}

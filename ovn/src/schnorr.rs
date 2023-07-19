use hacspec_lib::*;
use std::collections::HashMap;

pub mod random_oracle;
use random_oracle::*;
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

fn prod_assoc (sm : (Statement, Message)) -> random_oracle::Query {
    let (statement, message) = sm;
    // Proof.
    //   cbn. intros [statement message].
    //   rewrite !card_prod.
    //   apply mxvec_index. all: assumption.
    // Qed.
    random_oracle::Q{v: 1} // random_oracle::Query::ONE()
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
    G{v: 1} // Message::ONE()
}


fn Response (h : Statement, w : Witness, a : Message, e : Challenge) -> Response {
    // r ← get commit_loc ;;
    // ret (fto (otf r + otf e * otf w))
    Q{v: 1} // Response::ONE()
}

pub fn fiat_shamir_run(hw : Relation) -> Transcript {
    let QUERIES = HashMap::new();
    // #import {sig #[ INIT ] : 'unit → 'unit } as RO_init ;;
    // #import {sig #[ QUERY ] : 'query → 'random } as RO_query ;;
    let (h,w) = hw;
    // #assert (R (otf h) (otf w)) ;;
    let a = Commit(h, w);
    random_oracle::random_oracle_init(());
    let (QUERIES, eu) = random_oracle::random_oracle_query(QUERIES, prod_assoc((h, a)));
    let e = Q{v: 1}; // Challenge::ONE(); // Should be e <- eu
    let z = Response (h, w, a, e);
    (h,a,e,z)
}

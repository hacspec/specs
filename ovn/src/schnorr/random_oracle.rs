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

public_nat_mod!( //Custom Macro - defining a newtype with some functions - well defined macro's have library functions built in
    type_name: G,
    type_of_canvas: GCanvas,
    bit_size_of_field: 384, //381 with 3 extra bits
    modulo_value: "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab" //0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
);

// Order of G
public_nat_mod!( //Custom Macro - defining a newtype with some functions - well defined macro's have library functions built in
    type_name: Q,
    type_of_canvas: QCanvas,
    bit_size_of_field: 384, //381 with 3 extra bits
    modulo_value: "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab" //0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
);

pub type Random = G;
pub type Query = G;

pub fn sample_uniform () -> Random {
    Random::ONE()
}

use std::collections::HashMap;

use std::hash::{Hash, Hasher};
impl Hash for Query {
    fn hash<H: Hasher> (&self, state: &mut H) {

    }
}

// static ref QUERIES : HashMap<Query, Random> = HashMap::new();
// chQuery  := 'fin #|Query|
// chRandom := 'fin #|Random|
pub fn random_oracle_query(mut QUERIES : HashMap<Query, Random>, q : Query) -> (HashMap<Query, Random>, Random) {
    match QUERIES.get(&q) {
        Some (r) => (QUERIES.clone(), r.clone()),
        None => {
            let r = sample_uniform();
            QUERIES.insert(q, r);
            (QUERIES, r)
        }
    }
}

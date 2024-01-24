// #![no_std]
// #![feature(register_tool)]
// #![register_tool(hax)]

// // pub trait Z_Field: core::marker::Copy {
// //     type field_type: PartialEq + Eq + Clone + Copy + hacspec_concordium::Serialize;

// //     const q: usize;

// //     fn random_field_elem(random: u32) -> Self::field_type;

// //     fn field_zero() -> Self::field_type;
// //     fn field_one() -> Self::field_type;

// //     fn add(x: Self::field_type, y: Self::field_type) -> Self::field_type;
// //     fn mul(x: Self::field_type, y: Self::field_type) -> Self::field_type;
// // }

// // /** Interface for group implementation */
// // pub trait Group<Z: Z_Field>: core::marker::Copy {
// //     type group_type: PartialEq + Eq + Clone + Copy + hacspec_concordium::Serialize;

// //     const g: Self::group_type; // Generator (elemnent of group)

// //     fn random_group_elem(random: u32) -> Self::group_type;

// //     fn g_pow(x: Z::field_type) -> Self::group_type;
// //     fn pow(g: Self::group_type, x: Z::field_type) -> Self::group_type; // TODO: Link with q
// //     fn group_one() -> Self::group_type;
// //     fn prod(x: Self::group_type, y: Self::group_type) -> Self::group_type;
// //     fn inv(x: Self::group_type) -> Self::group_type;
// //     fn div(x: Self::group_type, y: Self::group_type) -> Self::group_type;

// //     fn hash(x: G::group_type, y: G::group_type, z: G::group_type) -> Z::field_type;
// // }

// use hacspec_bls12_381::*;

// // pub trait Z_Field: core::marker::Copy {
// //     type field_type: PartialEq + Eq + Clone + Copy + hacspec_concordium::Serialize;

// //     const q: usize;

// //     fn random_field_elem(random: u32) -> Self::field_type;

// //     fn field_zero() -> Self::field_type;
// //     fn field_one() -> Self::field_type;

// //     fn add(x: Self::field_type, y: Self::field_type) -> Self::field_type;
// //     fn mul(x: Self::field_type, y: Self::field_type) -> Self::field_type;
// // }

// impl Z_Field for Scalar {
//     type Field_type = Scalar;

//     // const q = Scalar::modulo;

//     fn random_field_elem(random: u32) {
//         return Scalar::from_literal(random);
//     }
// }

// impl Group<Scalar> for Fp12 {
//     group_type = Fp12;
// }


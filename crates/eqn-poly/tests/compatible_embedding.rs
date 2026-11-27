use eqn_algebra::ring::SemiRing;
use eqn_core::map::Map;
use eqn_poly::finite_field::{
    CompatibleFiniteField, CompatibleFiniteFieldEmbedding, FirstCompatible, Fq,
};

type F4 = CompatibleFiniteField<2, 2>;
type F16 = CompatibleFiniteField<2, 4>;
type E4 = Fq<2, 2, FirstCompatible>;

#[test]
fn the_generator_of_f4_lands_on_a_root_of_the_defining_polynomial_of_f4_inside_f16() {
    let embedding = CompatibleFiniteFieldEmbedding::<2, 2, 4>::new();

    assert_eq!(
        F16::evaluate_base_polynomial(&F4::modulus(), embedding.map(F4::generator())),
        F16::zero()
    );
}

#[test]
fn the_embedding_of_f4_into_f16_is_a_ring_map() {
    let embedding = CompatibleFiniteFieldEmbedding::<2, 2, 4>::new();
    let elements: Vec<E4> = (0..2)
        .flat_map(|a| (0..2).map(move |b| F4::from_values([a, b])))
        .collect();

    assert_eq!(embedding.map(F4::one()), F16::one());
    for a in &elements {
        for b in &elements {
            assert_eq!(
                embedding.map(F4::add(a.clone(), b.clone())),
                F16::add(embedding.map(a.clone()), embedding.map(b.clone()))
            );
            assert_eq!(
                embedding.map(F4::multiply(a.clone(), b.clone())),
                F16::multiply(embedding.map(a.clone()), embedding.map(b.clone()))
            );
        }
    }
}

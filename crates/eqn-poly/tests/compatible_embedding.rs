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
        Fq::zero()
    );
}

#[test]
fn the_embedding_of_f4_into_f16_is_a_ring_map() {
    let embedding = CompatibleFiniteFieldEmbedding::<2, 2, 4>::new();
    let elements: Vec<E4> = (0..2)
        .flat_map(|a| (0..2).map(move |b| E4::from_values([a, b])))
        .collect();

    assert_eq!(embedding.map(E4::one()), Fq::one());
    for &a in &elements {
        for &b in &elements {
            assert_eq!(embedding.map(a + b), embedding.map(a) + embedding.map(b));
            assert_eq!(embedding.map(a * b), embedding.map(a) * embedding.map(b));
        }
    }
}

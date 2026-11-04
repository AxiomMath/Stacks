module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.PolynomialQuotientBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.PolynomialIrreducibility

/-!
# The standard geometrically irreducible model over a principal open

Let `R` be a commutative ring, let `ι` be a type and let `P : MvPolynomial ι R`. If the
coefficientwise image of `P` in `K[xᵢ]` is irreducible for every field-valued specialization
`R ⟶ K`, then `Spec (R[xᵢ] ⧸ (P)) ⟶ Spec R` is geometrically irreducible.

This is step F of Stacks Tag 0559: combined with Tag 0557 it produces, for an absolutely
irreducible polynomial over a domain `A`, a nonzero `a : A` such that the hypersurface cut out by
`P` in affine space over `A_a` has geometrically irreducible fibres over `Spec A_a`, that is, over
the principal open `D(a) ⊆ Spec A`.

The proof is the composite of three identifications. Geometric irreducibility of a morphism to an
affine scheme is tested on the base changes along the field-valued specializations of the base
ring; the base change of `Spec (R[xᵢ] ⧸ (P))` along `R ⟶ K` is the spectrum of
`(R[xᵢ] ⧸ (P)) ⊗[R] K`; and that ring is `K[xᵢ] ⧸ (P^φ)`, a domain as soon as `P^φ` is
irreducible. The spectrum of a domain is irreducible.

## Main results

* `AlgebraicGeometry.geometricallyIrreducible_specMap_mvPolynomialQuotient`: step F.
* `AlgebraicGeometry.exists_away_geometricallyIrreducible_mvPolynomialQuotient`: step F combined
  with Stacks Tag 0557.

## References

* [Stacks Project, Tag 0557](https://stacks.math.columbia.edu/tag/0557)
* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- **Step F of Stacks Tag 0559.** If the coefficientwise image of `P : MvPolynomial ι R` in
`K[xᵢ]` is irreducible for every homomorphism from `R` to a field `K`, then the hypersurface
`Spec (R[xᵢ] ⧸ (P))` is geometrically irreducible over `Spec R`. -/
public theorem geometricallyIrreducible_specMap_mvPolynomialQuotient {R : Type u} [CommRing R]
    {ι : Type u} (P : MvPolynomial ι R)
    (hP : ∀ (K : Type u) [Field K] (φ : R →+* K), Irreducible (P.map φ)) :
    GeometricallyIrreducible (Spec.map (CommRingCat.ofHom
      (algebraMap R (MvPolynomial ι R ⧸ Ideal.span {P})))) := by
  refine ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.mpr fun K _ _ ↦ ?_⟩
  have : IsDomain ((MvPolynomial ι R ⧸ Ideal.span {P}) ⊗[R] K) :=
    MvPolynomial.isDomain_quotientSpan_tensor R ι P (hP K (algebraMap R K))
  exact (pullbackSpecIso R (MvPolynomial ι R ⧸ Ideal.span {P}) K).hom.homeomorph
    |>.irreducibleSpace_iff.mpr inferInstance

/-- **Step F of Stacks Tag 0559**, combined with **Stacks Tag 0557**. Let `A` be a domain with
fraction field `F` and let `P : MvPolynomial ι A` be irreducible over an algebraically closed
extension of `F`. Then there is a nonzero `a : A` such that the hypersurface cut out by `P` in
affine space over `A_a` is geometrically irreducible over `Spec A_a`, that is, has geometrically
irreducible fibres over the principal open `D(a) ⊆ Spec A`. -/
public theorem exists_away_geometricallyIrreducible_mvPolynomialQuotient (A : Type u) [CommRing A]
    [IsDomain A] (F : Type u) [Field F] [Algebra A F] [IsFractionRing A F] (Fbar : Type u)
    [Field Fbar] [Algebra F Fbar] [IsAlgClosed Fbar] (ι : Type u) [Finite ι]
    (P : MvPolynomial ι A)
    (hP : Irreducible (P.map ((algebraMap F Fbar).comp (algebraMap A F)))) :
    ∃ a : A, a ≠ 0 ∧ GeometricallyIrreducible (Spec.map (CommRingCat.ofHom
      (algebraMap (Localization.Away a) (MvPolynomial ι (Localization.Away a) ⧸
        Ideal.span {P.map (algebraMap A (Localization.Away a))})))) := by
  obtain ⟨a, ha, h⟩ := MvPolynomial.exists_away_irreducible_map A F Fbar ι P hP
  refine ⟨a, ha, geometricallyIrreducible_specMap_mvPolynomialQuotient _ fun K _ φ ↦ ?_⟩
  rw [MvPolynomial.map_map]
  exact h K φ

end AlgebraicGeometry

end

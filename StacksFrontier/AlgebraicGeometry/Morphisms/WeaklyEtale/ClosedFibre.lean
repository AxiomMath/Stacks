module

public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.Stalks
public import StacksFrontier.RingTheory.WeaklyEtale.Field

/-!
# The closed fibre of a weakly étale morphism

A weakly étale morphism of schemes has regular local rings as the closed fibres of its stalk
maps: these closed fibres are in fact fields.

## Main results

* `AlgebraicGeometry.isRegularLocalRing_closedFibre_of_weaklyEtale`: the closed fibre of the
  stalk map of a weakly étale morphism is a regular local ring.

## Implementation notes

The closed fibre `B ⧸ m_A B` of a local homomorphism `A → B` is a local ring, and it is a
quotient of the base change `(A ⧸ m_A) ⊗[A] B`, hence weakly étale over the residue field of
`A`. A weakly étale algebra over a field is reduced and integral, so every prime quotient of the
closed fibre is a field; a reduced local ring of Krull dimension `0` is a field, and a field is
a regular local ring.

## References

* [Stacks Project, Tag 094Q](https://stacks.math.columbia.edu/tag/094Q)
* [Stacks Project, Tag 0CKR](https://stacks.math.columbia.edu/tag/0CKR)
-/

@[expose] public section

open CategoryTheory IsLocalRing TensorProduct

universe u

namespace Algebra.WeaklyEtale

/-- The closed fibre `B ⧸ m_A B` of a weakly étale local homomorphism of local rings `A → B`
is a field. -/
private lemma isField_quotient_map_maximalIdeal (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [Algebra.WeaklyEtale A B] :
    IsField (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) := by
  let : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field _
  have hle : Ideal.map (algebraMap A B) (maximalIdeal A) ≤ maximalIdeal B :=
    IsLocalRing.map_maximalIdeal_le (algebraMap A B)
  have : Nontrivial (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) :=
    Ideal.Quotient.nontrivial_iff.mpr <| ne_top_of_le_ne_top (maximalIdeal.isMaximal B).ne_top hle
  have : IsLocalRing (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) :=
    .of_surjective' _ Ideal.Quotient.mk_surjective
  -- The closed fibre is a quotient of the base change `(A ⧸ m_A) ⊗[A] B`.
  have hwe : Algebra.WeaklyEtale (A ⧸ maximalIdeal A)
      (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) := by
    refine (structure_of_weaklyEtale_over_field (A ⧸ maximalIdeal A)
      ((A ⧸ maximalIdeal A) ⊗[A] B) inferInstance).2.2.2.2.1.2 _
      ⟨AlgHom.liftEquiv A (A ⧸ maximalIdeal A) B _
        (Ideal.Quotient.mkₐ A (Ideal.map (algebraMap A B) (maximalIdeal A))), fun z => ?_⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨1 ⊗ₜ b, by simp⟩
  have hstr := structure_of_weaklyEtale_over_field.{u, u, u} (A ⧸ maximalIdeal A)
    (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) hwe
  have : IsReduced (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) := hstr.1
  have : Algebra.IsIntegral (A ⧸ maximalIdeal A)
      (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) := hstr.2.1
  have : Ring.KrullDimLE 0 (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) := by
    rw [Ring.krullDimLE_zero_iff]
    intro P hP
    have : Algebra.IsIntegral (A ⧸ maximalIdeal A)
        ((B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) ⧸ P) := ⟨fun x => by
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact (Algebra.IsIntegral.isIntegral c).map (Ideal.Quotient.mkₐ (A ⧸ maximalIdeal A) P)⟩
    exact Ideal.Quotient.maximal_of_isField P
      (isField_of_isIntegral_of_isField' (Field.toIsField (A ⧸ maximalIdeal A)))
  exact Ring.KrullDimLE.isField_of_isReduced

end Algebra.WeaklyEtale

namespace AlgebraicGeometry

/-- The closed fibre of the stalk map of a weakly étale morphism is a regular local ring. -/
theorem isRegularLocalRing_closedFibre_of_weaklyEtale
    {X Y : Scheme.{u}} (f : Y ⟶ X) [AlgebraicGeometry.WeaklyEtale f] (y : Y) :
    IsRegularLocalRing ((Y.presheaf.stalk y) ⧸
      Ideal.map (f.stalkMap y).hom (IsLocalRing.maximalIdeal (X.presheaf.stalk (f y)))) := by
  have h : IsField ((Y.presheaf.stalk y) ⧸
      Ideal.map (f.stalkMap y).hom (IsLocalRing.maximalIdeal (X.presheaf.stalk (f y)))) := by
    let := (f.stalkMap y).hom.toAlgebra
    have : IsLocalHom (algebraMap (X.presheaf.stalk (f y)) (Y.presheaf.stalk y)) :=
      inferInstanceAs (IsLocalHom (f.stalkMap y).hom)
    have : Algebra.WeaklyEtale (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) :=
      (weaklyEtale_iff_stalkMap_weaklyEtale f).mp inferInstance y
    exact Algebra.WeaklyEtale.isField_quotient_map_maximalIdeal
      (X.presheaf.stalk (f y)) (Y.presheaf.stalk y)
  let := h.toField
  infer_instance

end AlgebraicGeometry

end

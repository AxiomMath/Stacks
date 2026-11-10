module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Artinian.Module
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteOverFieldStalks

/-!
# Global functions on a finite reduced scheme over an algebraically closed field

Let `Z` be a reduced scheme finite over an algebraically closed field `k`. Then
`dim_k Γ(Z, 𝒪_Z)` is at most the number of points of `Z`; in fact it equals that number, but only
the bound is used.

The ring `A = Γ(Z, 𝒪_Z)` is a finite `k`-algebra, so it is Artinian, and it is reduced, so it is
the product `∏_𝔪 A/𝔪` of its residue fields (`IsArtinianRing.equivPi`). Each residue field is
finite over `k`, hence equal to `k`, so `dim_k A` is the number of maximal ideals of `A`. That
number is bounded by the number of prime ideals, which is the number of points of the affine
scheme `Z ≅ Spec A`.

This is the bound `dim_k Γ(Z, ℒ ^⊗ n|_Z) ≤ 2` of the Bertini step of [Stacks, Tag 0FH7] for the
reduced subscheme on two closed points.

## Main results

* `AlgebraicGeometry.finrank_globalSections_le_natCard_of_isReduced`

## References

* [Stacks Project, Tag 0FH7](https://stacks.math.columbia.edu/tag/0FH7)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **On a reduced scheme finite over an algebraically closed field, the dimension of the
global functions is at most the number of points.** -/
theorem finrank_globalSections_le_natCard_of_isReduced (k : Type u) [Field k] [IsAlgClosed k]
    {Z : Scheme.{u}} (g : Z ⟶ Spec (.of k)) [IsFinite g] [IsReduced Z] [Finite Z] :
    letI : Algebra k Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
    Module.finrank k Γ(Z, ⊤) ≤ Nat.card Z := by
  let : Algebra k Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
  have : Module.Finite k Γ(Z, ⊤) := finite_globalSections_of_isFinite_over_field k g
  have : IsArtinianRing Γ(Z, ⊤) := IsArtinianRing.of_finite k Γ(Z, ⊤)
  have : IsAffine Z := isAffine_of_isAffineHom g
  let A := Γ(Z, ⊤)
  have hres : ∀ m : MaximalSpectrum A, Module.finrank k (A ⧸ m.asIdeal) = 1 := by
    intro m
    let : Field (A ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
    have : Module.Finite k (A ⧸ m.asIdeal) := inferInstance
    have : Algebra.IsIntegral k (A ⧸ m.asIdeal) := inferInstance
    have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := A ⧸ m.asIdeal)
    rw [← (AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ m.asIdeal)) hb).toLinearEquiv.finrank_eq,
      Module.finrank_self]
  have : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  have hA : Module.finrank k A = Fintype.card (MaximalSpectrum A) := by
    rw [((IsArtinianRing.equivPi A).restrictScalars k).toLinearEquiv.finrank_eq,
      Module.finrank_pi_fintype]
    simp [hres]
  -- maximal ideals inject into points of `Z ≅ Spec A`
  have hinj : Function.Injective fun m : MaximalSpectrum A =>
      (Z.isoSpec.inv).base m.toPrimeSpectrum :=
    (Z.isoSpec.inv.isOpenEmbedding.injective).comp MaximalSpectrum.toPrimeSpectrum_injective
  change Module.finrank k A ≤ Nat.card Z
  rw [hA, ← Nat.card_eq_fintype_card]
  exact Nat.card_le_card_of_injective _ hinj

end AlgebraicGeometry

end

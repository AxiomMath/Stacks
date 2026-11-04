module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameMultiplicativeGroup.TowerPoints

/-!
# The image of a base point of the Kummer tower is integrally closed

The base point `k₀^{(m)} : 𝔽_{m!}[X]_X → Ω`, `X ↦ t_m`, is injective with image the Laurent
polynomial ring `𝔽_{m!}[t_m, t_m⁻¹]`, whose fraction field is `𝔽_{m!}(t_m) ⊆ Ω`. Since a
localization of the principal ideal domain `𝔽_{m!}[X]` is integrally closed, an element of
`𝔽_{m!}(t_m)` which is integral over the image lies in it.

## Main definitions

* `AlgebraicGeometry.TameMultiplicativeGroup.towerPointAdjoin`: the base point as a ring
  homomorphism into `𝔽_{m!}(t_m)`.

## Main results

* `AlgebraicGeometry.TameMultiplicativeGroup.mem_range_towerPoint_of_isIntegralElem`: an element
  of `𝔽_{m!}(t_m)` integral over the image of the base point lies in that image.
-/

@[expose] public noncomputable section

open Polynomial IntermediateField

universe u

namespace AlgebraicGeometry.TameMultiplicativeGroup

variable (k : Type u) [Field k] [Fintype k]

/-- The base point `k₀^{(m)}` takes values in `𝔽_{m!}(t_m) ⊆ Ω`. -/
theorem towerPoint_mem_adjoin (m : ℕ) (z : Ring (towerField k m)) :
    towerPoint k m z ∈ (towerField k m)⟮towerRoot k m⟯ := by
  obtain ⟨p, s, rfl⟩ := IsLocalization.exists_mk'_eq
    (Submonoid.powers (X : (towerField k m)[X])) z
  have h1 : towerPoint k m (IsLocalization.mk' (Ring (towerField k m)) p s) *
      towerPoint k m (algebraMap _ (Ring (towerField k m)) (s : (towerField k m)[X])) =
        towerPoint k m (algebraMap _ (Ring (towerField k m)) p) := by
    rw [← map_mul, IsLocalization.mk'_spec]
  have hs : towerPoint k m (algebraMap _ (Ring (towerField k m)) (s : (towerField k m)[X])) ≠ 0 :=
    ((IsLocalization.map_units (Ring (towerField k m)) s).map (towerPoint k m)).ne_zero
  have hmem : ∀ r : (towerField k m)[X],
      towerPoint k m (algebraMap _ (Ring (towerField k m)) r) ∈
        (towerField k m)⟮towerRoot k m⟯ := fun r ↦ by
    rw [towerPoint_algebraMap, ← aeval_def]
    exact algebra_adjoin_le_adjoin (towerField k m) {towerRoot k m}
      (Polynomial.aeval_mem_adjoin_singleton _ _)
  rw [← eq_div_iff hs] at h1
  rw [h1]
  exact div_mem (hmem _) (hmem _)

/-- The base point as a map into `𝔽_{m!}(t_m)`. -/
def towerPointAdjoin (m : ℕ) :
    Ring (towerField k m) →+* (towerField k m)⟮towerRoot k m⟯ :=
  (towerPoint k m).codRestrict ((towerField k m)⟮towerRoot k m⟯.toSubfield)
    (towerPoint_mem_adjoin k m)

/-- **The image of a base point is integrally closed in `𝔽_{m!}(t_m)`.** -/
theorem mem_range_towerPoint_of_isIntegralElem (m : ℕ) {z : Omega k}
    (hz : z ∈ (towerField k m)⟮towerRoot k m⟯) (hint : (towerPoint k m).IsIntegralElem z) :
    z ∈ (towerPoint k m).range := by
  set F := towerField k m
  set A := F⟮towerRoot k m⟯
  let : Algebra (Ring F) A := (towerPointAdjoin k m).toAlgebra
  have : FaithfulSMul (Ring F) A := (faithfulSMul_iff_algebraMap_injective _ _).mpr fun a b h ↦
    towerPoint_injective k m (congrArg Subtype.val h)
  have : IsFractionRing (Ring F) A := IsFractionRing.of_field _ _ fun a ↦ by
    obtain ⟨r, s, hrs⟩ := (mem_adjoin_simple_iff F (a : Omega k)).mp a.2
    refine ⟨algebraMap F[X] (Ring F) r, algebraMap F[X] (Ring F) s, Subtype.ext ?_⟩
    show (a : Omega k) = towerPoint k m _ / towerPoint k m _
    rw [towerPoint_algebraMap, towerPoint_algebraMap, ← aeval_def, ← aeval_def, hrs]
  have : IsIntegrallyClosed (Ring F) :=
    isIntegrallyClosed_of_isLocalization (R := F[X]) (S := Ring F) (Submonoid.powers X)
      (powers_le_nonZeroDivisors_of_noZeroDivisors X_ne_zero)
  obtain ⟨p, hpm, hp⟩ := hint
  have hintA : _root_.IsIntegral (Ring F) (⟨z, hz⟩ : A) := ⟨p, hpm, Subtype.ext (by
    show ((eval₂ (towerPointAdjoin k m) ⟨z, hz⟩ p : A) : Omega k) = 0
    exact (hom_eval₂ p (towerPointAdjoin k m) A.toSubfield.subtype ⟨z, hz⟩).trans hp)⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hintA
  exact ⟨y, congrArg Subtype.val hy⟩

end AlgebraicGeometry.TameMultiplicativeGroup

end

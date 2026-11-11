module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.RingTheory.Localization.Basic
import Mathlib.Tactic.LinearCombination
public import StacksCore.Tactic.StacksAttribute

/-!
# Localization in two stages at the product submonoid

Let `S` and `S'` be submonoids of a commutative ring `A`, let `B = S'⁻¹A` and let `S̄` be the
image of `S` in `B`. Then `S̄⁻¹B` is a localization of `A` at the submonoid
`S ⊔ S' = {s * s' | s ∈ S, s' ∈ S'}` (Stacks' `SS'`), so that `(SS')⁻¹A ≅ S̄⁻¹(S'⁻¹A)`.

Mathlib's `IsLocalization.localization_localization_isLocalization` describes a localization
of a localization as a localization at the preimage of the composite submonoid, which can be
strictly larger than `S ⊔ S'`; the statement here names the product submonoid itself.

## Main results

* `IsLocalization.isLocalization_sup_of_isLocalization_map`: `S̄⁻¹(S'⁻¹A)` is a localization of
  `A` at `S ⊔ S'`.
* `IsLocalization.algEquivSupOfIsLocalizationMap`: the resulting `A`-algebra isomorphism
  `(SS')⁻¹A ≃ₐ[A] S̄⁻¹(S'⁻¹A)`.
-/

@[expose] public section

namespace IsLocalization

variable {A : Type*} [CommRing A] (S S' : Submonoid A) (B T : Type*) [CommRing B] [CommRing T]
  [Algebra A B] [Algebra B T] [Algebra A T] [IsScalarTower A B T]

/-- **Localization in two stages.** If `B` is the localization of `A` at `S'` and `T` is the
localization of `B` at the image `S̄` of `S`, then `T` is the localization of `A` at the
product submonoid `S ⊔ S' = SS'`. -/
@[stacks 02C6 "Stated as `IsLocalization (S ⊔ S') T`: in a commutative monoid `S ⊔ S'` is
the set of products `s * s'`, which is Stacks' `SS'`; the isomorphism itself is
`IsLocalization.algEquivSupOfIsLocalizationMap`."]
theorem isLocalization_sup_of_isLocalization_map [IsLocalization S' B]
    [IsLocalization (S.map (algebraMap A B)) T] : IsLocalization (S ⊔ S') T where
  map_units := by
    rintro ⟨x, hx⟩
    obtain ⟨s, hs, s', hs', rfl⟩ := Submonoid.mem_sup.mp hx
    rw [IsScalarTower.algebraMap_apply A B T, map_mul, map_mul]
    exact (IsLocalization.map_units T ⟨algebraMap A B s, Submonoid.mem_map_of_mem _ hs⟩).mul
      ((IsLocalization.map_units B ⟨s', hs'⟩).map (algebraMap B T))
  surj z := by
    obtain ⟨⟨y, _, s, hs, rfl⟩, hy⟩ := IsLocalization.surj (S.map (algebraMap A B)) z
    obtain ⟨⟨x, s', hs'⟩, hx⟩ := IsLocalization.surj S' y
    refine ⟨⟨x, s * s', Submonoid.mul_mem_sup hs hs'⟩, ?_⟩
    simp only at hy hx ⊢
    rw [IsScalarTower.algebraMap_apply A B T, IsScalarTower.algebraMap_apply A B T, map_mul,
      map_mul, ← mul_assoc, hy, ← map_mul, hx]
  exists_of_eq {x y} h := by
    rw [IsScalarTower.algebraMap_apply A B T, IsScalarTower.algebraMap_apply A B T] at h
    obtain ⟨⟨_, s, hs, rfl⟩, hc⟩ := IsLocalization.exists_of_eq (M := S.map (algebraMap A B)) h
    simp only [← map_mul] at hc
    obtain ⟨⟨s', hs'⟩, hc'⟩ := IsLocalization.exists_of_eq (M := S') hc
    refine ⟨⟨s * s', Submonoid.mul_mem_sup hs hs'⟩, ?_⟩
    simp only at hc' ⊢
    linear_combination hc'

/-- The `A`-algebra isomorphism `(SS')⁻¹A ≃ₐ[A] S̄⁻¹(S'⁻¹A)` of Stacks 02C6, where
`S ⊔ S' = SS'` and `S̄` is the image of `S` in `B = S'⁻¹A`. -/
noncomputable def algEquivSupOfIsLocalizationMap [IsLocalization S' B]
    [IsLocalization (S.map (algebraMap A B)) T] : Localization (S ⊔ S') ≃ₐ[A] T :=
  have := isLocalization_sup_of_isLocalization_map S S' B T
  IsLocalization.algEquiv (S ⊔ S') (Localization (S ⊔ S')) T

end IsLocalization

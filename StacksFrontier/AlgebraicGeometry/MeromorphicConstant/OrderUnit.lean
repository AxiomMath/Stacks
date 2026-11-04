module

public import Mathlib.AlgebraicGeometry.OrderOfVanishing

/-!
# The order of vanishing against a generator does not depend on the generator

On a locally Noetherian integral scheme the order of vanishing of a regular meromorphic section
of an invertible module along a prime divisor `Z` is defined by writing the section as
`a · s_ξ` for a generator `s_ξ` of the stalk at the generic point `ξ` of `Z`, and taking the
order of the scalar `a`.  This file proves that the result is independent of the generator: two
generators of a rank-one module over the local ring differ by a unit, and the order of a unit of
the local ring is zero.

## Main results

* `Stacks.AlgebraicGeometry.MeromorphicConstant.ord_algebraMap_of_isUnit`: the order of
  vanishing of the image in the function field of a unit of the local ring at a codimension-one
  point is zero.
* `Stacks.AlgebraicGeometry.MeromorphicConstant.exists_isUnit_smul_eq`: two generators of a
  module over the local ring differ by a unit.
* `Stacks.AlgebraicGeometry.MeromorphicConstant.ord_eq_of_coordinate_eq`: the coordinates of an
  element against two generators have the same order of vanishing.

## References

* [Stacks Project, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF)
* [Stacks Project, Tag 02MD](https://stacks.math.columbia.edu/tag/02MD)
-/

@[expose] public section

open AlgebraicGeometry Order TopologicalSpace CategoryTheory

universe u

namespace Stacks.AlgebraicGeometry.MeromorphicConstant

variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]

/-- At a point `z` of coheight one, the order homomorphism `X.ordHom z hz` is the order
homomorphism `Ring.ordFrac` of the local ring at `z`. -/
theorem ordHom_eq_ordFrac {z : X} (hz : coheight z = 1)
    [Ring.KrullDimLE 1 (X.presheaf.stalk z)] :
    X.ordHom z hz = Ring.ordFrac (X.presheaf.stalk z) := rfl

/-- At a point `z` of coheight one, the image in the function field of a unit of the local ring
at `z` has order of vanishing zero at `z`. -/
theorem ord_algebraMap_of_isUnit {z : X} (hz : coheight z = 1)
    {u : X.presheaf.stalk z} (hu : IsUnit u) :
    X.ord (algebraMap (X.presheaf.stalk z) X.functionField u) z = 0 := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  have hne : algebraMap (X.presheaf.stalk z) X.functionField u ≠ 0 := by
    simpa using fun h ↦ hu.ne_zero
      (IsFractionRing.injective (X.presheaf.stalk z) X.functionField (by simpa using h))
  rw [Scheme.ord_eq_iff hz hne, ordHom_eq_ordFrac X hz]
  simpa using Ring.ordFrac_of_isUnit (R := X.presheaf.stalk z)
    (K := X.functionField) hu

/-- If no nonzero element of the local ring at `z` annihilates a generator of the module `M`, then
any two generators of `M` differ by a unit. -/
theorem exists_isUnit_smul_eq {Y : Scheme.{u}} {z : Y}
    {M : Type*} [AddCommGroup M] [Module (Y.presheaf.stalk z) M]
    (hM : ∀ r : Y.presheaf.stalk z, ∀ x : M,
      Submodule.span (Y.presheaf.stalk z) {x} = ⊤ → r • x = 0 → r = 0)
    {m m' : M} (hm : Submodule.span (Y.presheaf.stalk z) {m} = ⊤)
    (hm' : Submodule.span (Y.presheaf.stalk z) {m'} = ⊤) :
    ∃ u : Y.presheaf.stalk z, IsUnit u ∧ m' = u • m := by
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.1 (hm ▸ Submodule.mem_top (x := m'))
  obtain ⟨v, hv⟩ := Submodule.mem_span_singleton.1 (hm' ▸ Submodule.mem_top (x := m))
  have hvu : (v * u - 1) • m = 0 := by
    rw [sub_smul, mul_smul, hu, hv, one_smul, sub_self]
  have h1 : v * u - 1 = 0 := hM _ _ hm hvu
  exact ⟨u, ⟨⟨u, v, by linear_combination h1, by linear_combination h1⟩, rfl⟩, hu.symm⟩

/-- Let `m` and `m'` generate `M` over the local ring at a point `z` of coheight one, and let
`σ : M → N` be a map into a module over the function field such that no nonzero element of the
function field annihilates `σ m`. If `a • σ m = a' • σ m'`, then `a` and `a'` have the same order
of vanishing at `z`. -/
theorem ord_eq_of_coordinate_eq {z : X} (hz : coheight z = 1)
    {M : Type*} [AddCommGroup M] [Module (X.presheaf.stalk z) M]
    {N : Type*} [AddCommGroup N] [Module X.functionField N]
    [Module (X.presheaf.stalk z) N] [IsScalarTower (X.presheaf.stalk z) X.functionField N]
    (σ : M →ₗ[X.presheaf.stalk z] N)
    (hM : ∀ r : X.presheaf.stalk z, ∀ x : M,
      Submodule.span (X.presheaf.stalk z) {x} = ⊤ → r • x = 0 → r = 0)
    {m m' : M} (hm : Submodule.span (X.presheaf.stalk z) {m} = ⊤)
    (hm' : Submodule.span (X.presheaf.stalk z) {m'} = ⊤)
    (hfaithful : ∀ c : X.functionField, c • σ m = 0 → c = 0)
    {a a' : X.functionField} (h : a • σ m = a' • σ m') :
    X.ord a z = X.ord a' z := by
  obtain ⟨u, hu, rfl⟩ := exists_isUnit_smul_eq hM hm hm'
  set w : X.functionField := algebraMap (X.presheaf.stalk z) X.functionField u with hw
  have hσ : σ (u • m) = w • σ m := by
    rw [map_smul, hw, IsScalarTower.algebraMap_smul]
  have hcoord : a = a' * w := by
    have h0 : (a - a' * w) • σ m = 0 := by
      rw [sub_smul, mul_smul, ← hσ, h, sub_self]
    linear_combination (norm := ring_nf) hfaithful _ h0
  have hwu : IsUnit w := hu.map (algebraMap (X.presheaf.stalk z) X.functionField)
  by_cases ha' : a' = 0
  · simp [hcoord, ha']
  rw [hcoord, Scheme.ord_mul ha' hwu.ne_zero, hw,
    ord_algebraMap_of_isUnit X hz hu, add_zero]

end Stacks.AlgebraicGeometry.MeromorphicConstant

end

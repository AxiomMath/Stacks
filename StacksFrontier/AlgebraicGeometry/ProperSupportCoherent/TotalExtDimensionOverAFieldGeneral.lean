module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.PerfectHomVanishingWindowGeneral
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessUnconditional
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.TotalExtDimensionOverAField

/-!
# The total dimension of the Ext groups on a scheme proper over a field

Let `X` be a scheme proper over a field `k`, let `K` be an object of `D^b_Coh(𝒪_X)` and let `E`
be a perfect object of `D(𝒪_X)`. [Stacks, Tag 0FYC] asserts that

`∑_{i ∈ ℤ} dim_k Ext^i_X(E, K) < ∞`.

The statements below take no hypotheses beyond properness of `X`, perfectness of `E` and
boundedness with coherent cohomology of `K`.

## Main results

* `ProperSupportCoherent.finite_setOf_not_subsingleton_ext_of_isPerfect_general`:
  `Ext^i_X(E, K) = 0` for all but finitely many `i`.
* `Stacks.AlgebraicGeometry.ProperSupportCoherent.cardinalSum_rank_ext_lt_aleph0_general`: the
  finiteness of `∑_{i ∈ ℤ} dim_k Ext^i_X(E, K)`.

## Implementation notes

`RΓ(X, -)` enters as a functor `RΓ` together with its structure morphism `α`, the `k`-module
structure on the Ext groups is
`Stacks.AlgebraicGeometry.ProperSupportCoherent.linearModulesOfOverField`, installed as a local
instance, and the derived category is the standard model.

## References

* [Stacks Project, Tag 0FYC](https://stacks.math.columbia.edu/tag/0FYC)
* [Stacks Project, Tag 0D0D](https://stacks.math.columbia.edu/tag/0D0D)
* [Stacks Project, Tag 09M4](https://stacks.math.columbia.edu/tag/09M4)
* [Stacks Project, Tag 0FXU](https://stacks.math.columbia.edu/tag/0FXU)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 01BW](https://stacks.math.columbia.edu/tag/01BW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.Cohomology (sectionsFunctor)

universe u

namespace Stacks.AlgebraicGeometry.ProperSupportCoherent

attribute [local instance 100000] HasDerivedCategory.standard

attribute [local instance] linearModulesOfOverField

section MainGeneral

variable {k : Type u} [Field k] (X : Over (Spec (.of k))) [IsProper X.hom]
  (RΓ : DerivedCategory X.left.Modules ⥤ DerivedCategory (ModuleCat.{u} Γ(X.left, ⊤)))
  (α : (sectionsFunctor X.left ⊤).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RΓ)
  [RΓ.IsRightDerivedFunctor α (HomotopyCategory.quasiIso X.left.Modules (ComplexShape.up ℤ))]
  (E K : DerivedCategory X.left.Modules)

include α in
/-- **Only finitely many of the Ext modules are nonzero, from perfectness alone.** Let `X` be a
scheme proper over a field `k`, let `E` be a perfect object of `D(𝒪_X)` and let `K` be an object
of `D^b_Coh(𝒪_X)`. Then `Ext^n_X(E, K) = 0` for all but finitely many `n`. The hypotheses are
exactly properness of `X`, perfectness of `E` and boundedness with coherent cohomology of `K`. -/
theorem finite_setOf_not_subsingleton_ext_of_isPerfect_general
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.left.toRingedSpace) E)
    (hK : DerivedCategoryB.derivedCategoryBBounded
      (fun M : X.left.Modules => M.IsCoherent) K) :
    {n : ℤ | ¬ Subsingleton (DerivedCategory.Ext E K n)}.Finite := by
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  have : IsNoetherian X.left := isNoetherian_of_isProper_over_field X
  obtain ⟨c, hc⟩ := hK.1.1
  obtain ⟨d, hd⟩ := hK.1.2
  have hKqc : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor X.left.Modules i).obj K).IsQuasicoherent := fun i =>
    have := hK.2 i
    isQuasicoherent_of_isCoherent _
  exact Stacks.DerivedQCoh.finite_setOf_not_subsingleton_hom_shift_of_isPerfect_general
    X.left RΓ α E hE K hKqc c d ((DerivedCategory.isGE_iff K c).mpr hc)
    ((DerivedCategory.isLE_iff K d).mpr hd)

include α in
/-- **The total dimension of the Ext groups is finite.** Let `X` be a scheme proper over a field
`k`, let `K` be an object of `D^b_Coh(𝒪_X)` and let `E` be a perfect object of `D(𝒪_X)`. Then

`∑_{i ∈ ℤ} dim_k Ext^i_X(E, K) < ∞`,

the dimensions being taken for the canonical `k`-structure induced by the structure morphism
`X ⟶ Spec k`, the sum being the cardinal sum over all of `ℤ` and `< ∞` being `< ℵ₀`. -/
@[stacks 0FYC]
theorem cardinalSum_rank_ext_lt_aleph0_general
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.left.toRingedSpace) E)
    (hK : DerivedCategoryB.derivedCategoryBBounded
      (fun M : X.left.Modules => M.IsCoherent) K) :
    Cardinal.sum (fun n : ℤ => Module.rank k (DerivedCategory.Ext E K n)) <
      Cardinal.aleph0 := by
  have : IsNoetherian X.left := isNoetherian_of_isProper_over_field X
  have hEb : DerivedCategoryB.derivedCategoryBBounded
      (fun M : X.left.Modules => M.IsCoherent) E :=
    PerfectCohomology.isBoundedCoherent_of_isPerfect X.left E hE
  have hExtFinite : ∀ n : ℤ, Module.Finite k (DerivedCategory.Ext E K n) := fun n =>
    moduleFinite_ext_of_proper X E K ⟨hEb.1.2, hEb.2⟩ ⟨hK.1.1, hK.2⟩ n
  exact lt_aleph0_cardinalSum
    ((finite_setOf_not_subsingleton_ext_of_isPerfect_general X RΓ α E K hE hK).subset
      fun n hn hsub => hn (rank_zero_iff.2 hsub))
    fun n => Module.rank_lt_aleph0_iff.2 (hExtFinite n)

end MainGeneral

end Stacks.AlgebraicGeometry.ProperSupportCoherent

end

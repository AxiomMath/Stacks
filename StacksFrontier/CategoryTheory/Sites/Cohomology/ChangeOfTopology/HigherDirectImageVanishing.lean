module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DerivedPushforwardBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.SingleCoveringDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.VanishingConditionAllDegrees
import StacksCore.Tactic.StacksAttribute

/-!
# The higher change-of-topology direct images vanish

In the situation of Stacks 0EZ3 write `ε_X : C_τ/X ⟶ C_{τ'}/X` for the change-of-topology
morphism. This file proves that the condition `(V_n)` — the vanishing of `R^i ε_{X,*} ℱ` for
`1 ≤ i ≤ n`, every object `X` and every `ℱ` of the class `𝒜_X` — holds for every `n`, and the
two consequences of Stacks 0EZF in the derived category.

## Main results

* `Stacks.ComparingTopologies.CohomologyComparison.vanishingCondition_succ`: **Stacks 0EZE**,
  `(V_n) ⇒ (V_{n+1})`.
* `Stacks.ComparingTopologies.CohomologyComparison.vanishingCondition`: the leading assertion of
  **Stacks 0EZF**, `(V_n)` for all `n`.
* `Stacks.ComparingTopologies.isIso_derivedComparisonUnit_app`: **Stacks 0EZF (1)**, the map
  `K' ⟶ Rε_{X,*}(ε_X^{-1}K')` is an isomorphism on `D⁺_{𝒜'_X}`.
* `Stacks.ComparingTopologies.isIso_derivedComparisonBaseChange_app`: the base change half of
  **Stacks 0EZF (2)**, `ε_Y^{-1}(Rf_{τ',*}K') ⟶ Rf_{τ,*}(ε_X^{-1}K')` is an isomorphism on
  `D⁺_{𝒜'_X}`; the membership half is
  `Stacks.ComparingTopologies.rightDerivedPushforward_mem_derivedCategoryBPlus`.

## Implementation notes

Stacks 0EZE is the reduction `vanishingCondition_succ_of_singleCoveringDescent` fed with the
descent statement `CohomologyComparison.singleCoveringDescent`, which is the closing argument of
the source's proof. The two clauses of Stacks 0EZF are the statements
`isIso_derivedComparisonUnit_app_of_vanishingCondition` and
`isIso_derivedComparisonBaseChange_app_of_vanishingCondition` of their own files, which take
`(V_n)` for every `n` as an argument, with that argument now supplied. The base change map is
invertible for every morphism of the site, not only for those of the distinguished class.

## References

* [Stacks Project, Tag 0EZE](https://stacks.math.columbia.edu/tag/0EZE)
* [Stacks Project, Tag 0EZF](https://stacks.math.columbia.edu/tag/0EZF)
-/

@[expose] public section

universe v u

open CategoryTheory

namespace Stacks.ComparingTopologies

open Stacks.Cohomology.Localization

variable {C : Type u} [Category.{v} C]

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 0EZE.** In the comparison situation of Stacks 0EZ3 the vanishing condition `(V_n)`
implies `(V_{n+1})`. -/
@[stacks 0EZE]
theorem CohomologyComparison.vanishingCondition_succ (S : CohomologyComparison C) (n : ℕ)
    (hV : S.vanishingCondition n) : S.vanishingCondition (n + 1) :=
  S.vanishingCondition_succ_of_singleCoveringDescent n hV (S.singleCoveringDescent n hV)

/-- **Stacks 0EZF, the leading assertion.** In the comparison situation of Stacks 0EZ3 the
vanishing condition `(V_n)` holds for every `n`: `(V_0)` is empty and Stacks 0EZE is the
induction step. -/
@[stacks 0EZF "(V_n) holds for all n"]
theorem CohomologyComparison.vanishingCondition_all (S : CohomologyComparison C) (n : ℕ) :
    S.vanishingCondition n := by
  induction n with
  | zero => exact S.vanishingCondition_zero
  | succ n hn => exact S.vanishingCondition_succ n hn

/-- **Stacks 0EZF (1).** For `X` in `C` and `K'` in `D⁺_{𝒜'_X}(C_{τ'}/X)` the canonical map
`K' ⟶ Rε_{X,*}(ε_X^{-1}K')` is an isomorphism. -/
@[stacks 0EZF "(1)"]
theorem isIso_derivedComparisonUnit_app (S : CohomologyComparison C) (X : C)
    (K : DerivedCategory.Plus (AbelianSheaves S.coarseCoverage.toGrothendieck X))
    (hK : ∀ i : ℤ, S.weakSerre X ((DerivedCategory.Plus.homologyFunctor _ i).obj K)) :
    IsIso ((derivedComparisonUnit S X).app K) :=
  isIso_derivedComparisonUnit_app_of_vanishingCondition S S.vanishingCondition_all X K hK

/-- **Stacks 0EZF (2), the base change.** For a morphism `f : X ⟶ Y` of `C` and `K'` in
`D⁺_{𝒜'_X}(C_{τ'}/X)` the base change map `ε_Y^{-1}(Rf_{τ',*}K') ⟶ Rf_{τ,*}(ε_X^{-1}K')` is an
isomorphism. The source states this for `f` in the distinguished class; it holds for every `f`. -/
@[stacks 0EZF "(2), base change"]
theorem isIso_derivedComparisonBaseChange_app (S : CohomologyComparison C) {X Y : C} (f : X ⟶ Y)
    (K : DerivedCategory.Plus (AbelianSheaves S.coarseCoverage.toGrothendieck X))
    (hK : ∀ n : ℤ, S.weakSerre X
      ((DerivedCategory.Plus.homologyFunctor
        (AbelianSheaves S.coarseCoverage.toGrothendieck X) n).obj K)) :
    IsIso ((derivedComparisonBaseChange S f).app K) :=
  isIso_derivedComparisonBaseChange_app_of_vanishingCondition S S.vanishingCondition_all f K hK

end Stacks.ComparingTopologies

end

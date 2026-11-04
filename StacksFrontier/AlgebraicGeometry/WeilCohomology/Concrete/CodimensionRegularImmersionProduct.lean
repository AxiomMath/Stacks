module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.RegularImmersionIntersectionProduct
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionCycleClass
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DimensionClassCodimension

/-!
# Stacks 0FFE in the codimension grading

Let `k` be a field, let `X` be a scheme smooth over `k` and let `i : Y ⟶ X` be a regular closed
immersion with `Y` equidimensional of dimension `e`. Stacks 0FFE says `α · [Y]_e = i_*(i^!α)`
(`Stacks.Chow.intersectionProduct_fundamentalChowClass_eq_pushforward_regularImmersionGysin`,
there with `[Y]_e` graded by dimension). Chapter 45 grades Chow groups of smooth schemes by
codimension, `CH^c(X) = ∏_d CH_{d-c}(X_d)` (`Stacks.Chow.codimensionChowGroup`), and reads `[Y]`
as the class `[Y] ∈ CH^c(X)` of a closed subscheme (`Stacks.WeilCohomology.closedSubschemeClass`).
This file states 0FFE in that grading:

  `[Y] · θ = i_*(i^!θ)`   in   `CH^{c+q}(X)`,   for `θ ∈ CH^q(X)`,

where the right side is the class `i_*(i^!θ) ∈ CH_{e-q}(X)` read in codimension `c + q`
(`Stacks.WeilCohomology.chowGroupToCodimension`). `X` need not be equidimensional, and `c` is
arbitrary. The case of a divisor is `c = 1` with `Y` smooth over `k`
(`Stacks.WeilCohomology.codimensionIntersectionProduct_closedSubschemeClass_one_of_smooth`).

## Main results

* `Stacks.WeilCohomology.chowGroupToCodimension_properChowPushforward_fundamentalChowClass`:
  `i_*[Y]_e` read in codimension `c` is `[Y] ∈ CH^c(X)`.
* `Stacks.WeilCohomology.codimensionIntersectionProduct_closedSubschemeClass`: Stacks 0FFE in the
  codimension grading, `[Y] · θ = i_*(i^!θ)`.
* `Stacks.WeilCohomology.codimensionIntersectionProduct_closedSubschemeClass_one_of_smooth`: the
  case of a smooth divisor.

## References

* [Stacks Project, Tag 0FFE](https://stacks.math.columbia.edu/tag/0FFE)
* [Stacks Project, Tag 0FIH](https://stacks.math.columbia.edu/tag/0FIH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow

universe u

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX]

/-! ### The class of an equidimensional closed subscheme -/

variable {Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i]

omit [Smooth sX] in
/-- The cycle of a closed subscheme `Y` of pure dimension `e` vanishes in every other
dimension. -/
theorem cycleAssociatedToClosedSubscheme_eq_zero_of_relativeDimension [LocallyOfFiniteType sX]
    {e : ℕ} (hY : RelativeDimension (i ≫ sX) e) {m : ℤ} (hm : m ≠ e) :
    cycleAssociatedToClosedSubscheme (fieldChowSituation k) sX i m = 0 := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
  refine cycleAssociatedToClosedSubscheme_apply_eq_zero _ sX i m x ?_
  rintro ⟨ξ, rfl, hξ⟩
  rw [← relativeDimension_comp_closedImmersion,
    relativeDimension_of_mem_irreducibleComponents_of_relativeDimension k (i ≫ sX) e hY ξ.1
      ξ.2] at hξ
  exact hm hξ.symm

/-- `i_*[Y]_e` is the class of the cycle of `Y` in `X`. -/
theorem properChowPushforward_fundamentalChowClass_eq_mk (m : ℤ) :
    properChowPushforward (fieldChowSituation k) (i ≫ sX) sX i rfl m
        (properPushforwardDescends _ _ _ _ _ _)
        (fundamentalChowClass (fieldChowSituation k) (i ≫ sX) m) =
      QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) sX m)
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sX i m) := by
  rw [fundamentalChowClass, properChowPushforward_mk,
    properPushforward_fundamentalCycle_of_isClosedImmersion]

/-- **`i_*[Y]_e` read in codimension `c` is the class `[Y] ∈ CH^c(X)`**, for `Y` of pure
dimension `e`. -/
theorem chowGroupToCodimension_properChowPushforward_fundamentalChowClass {e : ℕ}
    (hY : RelativeDimension (i ≫ sX) e) (c : ℤ) :
    chowGroupToCodimension sX e c
        (properChowPushforward (fieldChowSituation k) (i ≫ sX) sX i rfl e
          (properPushforwardDescends _ _ _ _ _ _)
          (fundamentalChowClass (fieldChowSituation k) (i ≫ sX) e)) =
      closedSubschemeClass sX i c := by
  funext d
  rw [closedSubschemeClass_apply, properChowPushforward_fundamentalChowClass_eq_mk]
  by_cases h : (e : ℤ) = d - c
  · exact eq_of_heq ((chowGroupToCodimension_apply_heq _ _ _ _ _ h).trans
      (chowGroupRestrict_heq_of_heq _ _ _ _ _ h _ _
        (mk_cycleAssociatedToClosedSubscheme_heq _ sX i h)))
  · rw [chowGroupToCodimension_apply_of_ne _ _ _ _ _ h,
      cycleAssociatedToClosedSubscheme_eq_zero_of_relativeDimension sX i hY (Ne.symm h)]
    exact (map_zero _).symm

/-! ### Stacks 0FFE in the codimension grading -/

/-- **Stacks 0FFE in the codimension grading: `[Y] · θ = i_*(i^!θ)`.** Let `X` be a scheme smooth
over a field `k`, of arbitrary and not necessarily constant dimension, and let `i : Y ⟶ X` be a
regular closed immersion with `Y` equidimensional of dimension `e`. For every `c`, every `q` and
every `θ ∈ CH^q(X)`, the intersection product (Stacks 0FC0, part by part) of the class
`[Y] ∈ CH^c(X)` with `θ` is `i_*(i^!θ)`, read in `CH^{c+q}(X)`, where
`i^! : CH^q(X) ⟶ CH_{e-q}(Y)` is the Gysin map of `i` (`Stacks.Chow.regularImmersionGysin`). -/
theorem codimensionIntersectionProduct_closedSubschemeClass
    (hreg : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularImmersion i) (e : ℕ)
    (hY : RelativeDimension (i ≫ sX) e) (c q : ℤ) (θ : codimensionChowGroup k sX q) :
    codimensionIntersectionProduct k sX c q (closedSubschemeClass sX i c) θ =
      chowGroupToCodimension sX (e - q) (c + q)
        (properChowPushforward (fieldChowSituation k) (i ≫ sX) sX i rfl (e - q)
          (properPushforwardDescends _ _ _ _ _ _) (regularImmersionGysin sX i hreg e q θ)) := by
  funext d
  rw [codimensionIntersectionProduct_apply]
  by_cases h : (d : ℤ) - c = e
  · rw [chowGroupToCodimension_apply_of_eq _ _ _ _ _ (by lia),
      ← intersectionProduct_fundamentalChowClass_eq_pushforward_regularImmersionGysin sX i hreg e
        hY q θ,
      chowGroupRestrict_codimensionDimensionIntersectionProduct,
      canonicalDiagonalClassFamily_isSymmetric k _ d _ ((d : ℤ) - c) ((d : ℤ) - q)]
    exact eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans
      ((chowGroupDegreeEquiv_heq _ _ _ _).trans
        ((selfIntersectionProduct_heq_of_heq _ _ _ rfl h HEq.rfl
          (heq_of_eq_of_heq (congrFun
            (chowGroupToCodimension_properChowPushforward_fundamentalChowClass sX i hY c) d).symm
            (chowGroupToCodimension_apply_heq sX _ _ _ _ h.symm))).trans
          ((chowGroupDegreeEquiv_heq _ _ _ _).trans (chowGroupDegreeEquiv_heq _ _ _ _)).symm)))
  · rw [chowGroupToCodimension_apply_of_ne _ _ _ _ _ (by lia),
      closedSubschemeClass_apply,
      cycleAssociatedToClosedSubscheme_eq_zero_of_relativeDimension sX i hY h]
    simp

/-- **Stacks 0FFE for a smooth divisor, in the codimension grading.** Let `X` be a scheme smooth
over a field `k` and let `i : D ⟶ X` be a closed immersion with `D` smooth over `k` of pure
dimension `e` (a closed immersion of smooth schemes is regular, Tag 067U). For every `q` and every
`θ ∈ CH^q(X)`, the product of the class `[D] ∈ CH^1(X)` with `θ` is `i_*(i^!θ)` read in
`CH^{1+q}(X)`. -/
theorem codimensionIntersectionProduct_closedSubschemeClass_one_of_smooth [Smooth (i ≫ sX)]
    (e : ℕ) (hY : RelativeDimension (i ≫ sX) e) (q : ℤ) (θ : codimensionChowGroup k sX q) :
    codimensionIntersectionProduct k sX 1 q (closedSubschemeClass sX i 1) θ =
      chowGroupToCodimension sX (e - q) (1 + q)
        (properChowPushforward (fieldChowSituation k) (i ≫ sX) sX i rfl (e - q)
          (properPushforwardDescends _ _ _ _ _ _)
          (regularImmersionGysin sX i
            (Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_of_smooth i sX) e q θ)) :=
  codimensionIntersectionProduct_closedSubschemeClass sX i _ e hY 1 q θ

end Stacks.WeilCohomology

end

module

public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.ComponentDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicCascade.RegularGenericValue
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicSectionIndependence

/-!
# The component divisor of a restricted section represents the first Chern class component

Let `X` be locally of finite type over the base scheme of chapter 42 of the Stacks Project, let
`ℒ` be an invertible `𝒪_X`-module and let `s` be a regular meromorphic section of `ℒ`. For `η` a
generic point of an irreducible component of `X` of delta-dimension `k + 1`, the divisor
`div_{ℒ|_{Xη}}(sη)` of the restricted section on the component `Xη` is a `k`-cycle on `Xη`
(`Stacks.Chow.componentDivisorCycleOn`), and the component rule of
[Stacks, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO) attached to `ℒ` provides another
one, the divisor of a section it chose for itself. The two agree in the Chow group `A_k(Xη)`.

This is the bridge between the two sides of part (4) of
[Stacks, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW): that part computes a difference of
cycles as a locally finite combination of the `div_{ℒ|_{Xη}}(sη)`, while the cap product of
Tag 02SO is computed from the rule's own choices.

## Main results

* `Stacks.Chow.componentDivisorCycleOn_eq_chernComponentCycle` — the divisor cycle of the
  restricted section is the component cycle of its generic value.
* `Stacks.Chow.rationallyEquivalent_firstChernComponentCycleRule_componentDivisorCycleOn` — the
  component rule of `ℒ` and the divisor of the restricted section are rationally equivalent on the
  component.

## Implementation notes

The two cycles are *not* equal: the component rule of Tag 02SO chooses a nonzero element of the
generic stalk of `ℒ|_{Xη}` by `Stacks.Divisors.exists_ne_zero_genericStalk`, with no reference to
`s`. They agree in `A_k(Xη)` by [Stacks, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
part (2), in the form `Stacks.Chow.firstChernComponentClass_eq_mk_of_ne_zero`, whose hypothesis is
that the comparison section has nonzero generic value;
`Stacks.Divisors.genericValue_ne_zero_of_isRegularMeromorphicSection` discharges that for `sη`,
which is regular by part (2) of [Stacks, Tag 02OY](https://stacks.math.columbia.edu/tag/02OY).

**The two gradings are crossed by `Subtype.ext`.** The divisor cycle of a regular meromorphic
section is graded `n - 1` from `dim_δ = n` while the component cycle of Tag 02SO is graded `k`
from `dim_δ = k + 1`; both are specified by the order of vanishing at the generic point of each
prime divisor and by zero elsewhere, so they have the same underlying algebraic cycle. That
comparison is the `private` lemma below. It also exists, for the same reason and with the same
proof, as `Stacks.Chow.val_meromorphicDivisorCycle_eq_chernComponentCycle` in
`StacksFrontier.AlgebraicGeometry.Chow.ChernCapClosedImmersionInvertible`, which is kept out of the
import surface of this module.

## References

* [Stacks Project, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 02OY](https://stacks.math.columbia.edu/tag/02OY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

/-- The divisor cycle of [Stacks, Tag 02SJ] part (1) and the component cycle of
[Stacks, Tag 02SO] have the same underlying algebraic cycle: both are specified by the order of
vanishing at the generic point of each prime divisor and by zero at every other point. The two
live in different cycle groups, the first graded `n - 1` from `dim_δ = n` and the second graded
`k` from `dim_δ = k + 1`. -/
private theorem val_meromorphicDivisorCycle_eq_val_chernComponentCycle (C : ChowSituation.{u})
    {V : Scheme.{u}} (q : V ⟶ C.S) [LocallyOfFiniteType q] [IsIntegral V]
    [IsLocallyNoetherian V] {m : ℤ}
    (hm : schemeDeltaDimension C q = ((m + 1 : ℤ) : EInt)) {M : V.Modules}
    (hM : ∀ x : V, IsTrivializedNear M x) (t : M.presheaf.stalk (genericPoint V)) :
    ((meromorphicDivisorCycle C q hm hM t).val : AlgebraicCycle V ℤ) =
      ((chernComponentCycle C q hm hM t : CycleGroup C q m) : AlgebraicCycle V ℤ) := by
  refine Function.locallyFinsuppWithin.ext fun x => ?_
  by_cases hx : ∃ Z : Stacks.Divisors.PrimeDivisor V, Z.genericPoint = x
  · obtain ⟨Z, rfl⟩ := hx
    rw [meromorphicDivisorCycle_genericPoint, chernComponentCycle_genericPoint]
  · push Not at hx
    rw [meromorphicDivisorCycle_eq_zero C q hm hM t x hx,
      chernComponentCycle_eq_zero C q hm hM t x hx]

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (L : X.Modules)
  [hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : AlgebraicGeometry.MeromorphicSection X.sheaf L)
  (hs : AlgebraicGeometry.IsRegularMeromorphicSection X.sheaf L s) {k : ℤ} {η : X}
  (hη : η ∈ genericPoints X) (hδ : relativeDimension C.dimensionFunction f η = k + 1)

/-- **The divisor of the restricted section is the component cycle of its generic value.** The
divisor cycle of a regular meromorphic section is by construction the Weil divisor of its generic
value, and the component cycle of [Stacks, Tag 02SO] is the same Weil divisor read in the grading
the component rule uses. -/
theorem componentDivisorCycleOn_eq_chernComponentCycle :
    letI := isIntegral_integralComponentAt η
    letI : IsLocallyNoetherian (integralComponentAt η).subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian ((integralComponentAt η).subschemeι ≫ f)
    componentDivisorCycleOn C f L s hL hs hη hδ =
      chernComponentCycle C ((integralComponentAt η).subschemeι ≫ f)
        (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C f η hδ)
        (fun x =>
          letI := isInvertible_presheaf_modulePullback L (integralComponentAt η).subschemeι
          isTrivializedNear_of_isInvertible
            ((Scheme.Modules.pullback (integralComponentAt η).subschemeι).obj L) x)
        (genericValue ((Scheme.Modules.pullback (integralComponentAt η).subschemeι).obj L)
          (componentMeromorphicSection L s hη)) :=
  let := isIntegral_integralComponentAt η
  let : IsLocallyNoetherian (integralComponentAt η).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((integralComponentAt η).subschemeι ≫ f)
  Subtype.ext (val_meromorphicDivisorCycle_eq_val_chernComponentCycle C _ _ _ _)

/-- **The component rule of `ℒ` and the divisor of the restricted section agree in the Chow group
of the component.** The rule's value is the class of the divisor cycle of *any* nonzero
meromorphic section of `ℒ|_{Xη}`, which is [Stacks, Tag 02SJ] part (2); the generic value of the
restriction `sη` is nonzero because `sη` is regular. -/
theorem rationallyEquivalent_firstChernComponentCycleRule_componentDivisorCycleOn :
    RationallyEquivalent C ((integralComponentAt η).subschemeι ≫ f) k
      (firstChernComponentCycleRule C f k L (integralComponentAt η)
        (isIntegral_integralComponentAt η)
        (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C f η hδ))
      (componentDivisorCycleOn C f L s hL hs hη hδ) := by
  have hWi := isIntegral_integralComponentAt η
  have hWN : IsLocallyNoetherian (integralComponentAt η).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((integralComponentAt η).subschemeι ≫ f)
  have hσ : genericValue ((Scheme.Modules.pullback (integralComponentAt η).subschemeι).obj L)
      (componentMeromorphicSection L s hη) ≠ 0 :=
    genericValue_ne_zero_of_isRegularMeromorphicSection _ _
      (isRegularMeromorphicSection_componentMeromorphicSection L s hL hs hη)
  refine QuotientAddGroup.eq_iff_sub_mem.1 (Eq.trans ?_ (congrArg QuotientAddGroup.mk
    (componentDivisorCycleOn_eq_chernComponentCycle C f L s hs hη hδ).symm))
  exact (firstChernComponentClass_eq_mk C f k L (integralComponentAt η) hWi
      (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C f η hδ)).symm.trans
    (firstChernComponentClass_eq_mk_of_ne_zero C f k L (integralComponentAt η)
      (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C f η hδ) hσ)

end Stacks.Chow

end

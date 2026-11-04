module

public import StacksFrontier.AlgebraicGeometry.AmpleImmersionReduction.EventualGeneration
public import StacksFrontier.AlgebraicGeometry.ChartImmersionFinish.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiProjectiveChartRoute.Basic

/-!
# What `ChartImmersion` being a theorem makes unconditional, and what it does not

`Stacks.ChartImmersionFinish.chartImmersion` proves
`Stacks.AmpleImmersionReduction.ChartImmersion`, which was a named input of [Stacks, Tag 01VS].
This file discharges that input wherever it was hypothesised, and records precisely how far that
gets.

## What becomes unconditional

The **single-degree** form of the conclusion of [Stacks, Tag 01VS] — the one the source remarks
"is enough in virtually all applications". For `L` ample on a scheme locally of finite type over
`S` there are a positive degree `N` and an immersion `i : X ⟶ ℙⁿ_S` over `S` with
`L ^⊗ N ≅ i^* 𝒪(1)`:
`Stacks.ChartImmersionFinish.exists_immersion_projectiveSpaceOver_single_of_isAmple`. The other
input that form needed, `Stacks.AmpleImmersionReduction.TwistPullback`, is
`Stacks.AmpleImmersionReduction.twistPullback`, already unconditional.

Also `Stacks.QuasiProjectiveChartRoute.ChartImmersionUniform`, which is `ChartImmersion` at every
situation, hence everything that file derives from it.

## What does not

**[Stacks, Tag 01VS] itself is not proved and its attribute is not attached.** The tag asserts the
conclusion for *every* `d ≥ d₀`, not at one degree, and the passage from one degree to all of them
is `Stacks.AmpleImmersionReduction.TwistPassage` — steps 6 and 7 of the source, the Segre passage.
No declaration in this repository proves it:
`StacksFrontier/AlgebraicGeometry/ChartImmersionAssembly/SegrePassage.lean` and
`StacksFrontier/AlgebraicGeometry/ExternalTensorPullback/Basic.lean` both measure its residue and
state that they do not discharge it, and the alternative route of
`StacksFrontier/AlgebraicGeometry/ProductFamilyTwist/Basic.lean` replaces it by its own
`ProductFamilyImmersion`, which that file records as unproved. The fourth former input,
`Stacks.AmpleEventualGeneration.IsEventuallyFinGenPowers`, is not an input: it follows from
ampleness by `Stacks.AmpleLocalGeneration.isEventuallyFinGenPowers_of_isAmple`.

So Tag 01VS now stands on **one** named input, `TwistPassage`, where it stood on two;
`Stacks.ChartImmersionFinish.exists_immersion_projectiveSpaceOver_of_isAmple_of_twistPassage` is
the tag's statement carrying exactly that one hypothesis, and it carries no attribute.

## Main results

* `Stacks.ChartImmersionFinish.chartImmersionUniform`:
  `Stacks.QuasiProjectiveChartRoute.ChartImmersionUniform`.
* `Stacks.ChartImmersionFinish.exists_hasImmersionTwistOver_of_isAmple`,
  `exists_immersion_projectiveSpaceOver_single_of_isAmple`: **the single-degree form of
  [Stacks, Tag 01VS], unconditionally.**
* `Stacks.ChartImmersionFinish.immersionTwistGap_of_twistPassage`,
  `exists_immersion_projectiveSpaceOver_of_isAmple_of_twistPassage`: **[Stacks, Tag 01VS] from
  `TwistPassage` alone.**

## References

* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 01VT](https://stacks.math.columbia.edu/tag/01VT)
* [Stacks Project, Tag 07RM](https://stacks.math.columbia.edu/tag/07RM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Ample Stacks.AmpleProjectiveImmersion

universe u

namespace Stacks.ChartImmersionFinish

section Consequences

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
  [Stacks.Ample.IsInvertibleModule X L]

/-- `Stacks.AmpleImmersionReduction.ChartImmersion` at every situation. -/
theorem chartImmersionUniform :
    Stacks.QuasiProjectiveChartRoute.ChartImmersionUniform.{u} :=
  fun _A _B g N _ => chartImmersion g N

/-- **[Stacks, Tag 01VS] at a single degree, unconditionally.** -/
theorem exists_hasImmersionTwistOver_of_isAmple (hL : IsAmple X L)
    (hft : LocallyOfFiniteType f) :
    ∃ N : ℤ, 1 ≤ N ∧ HasImmersionTwistOver f (tensorPowModule X L N) :=
  Stacks.AmpleImmersionReduction.hasImmersionTwistOver_of_isAmple_of_chartImmersion f L
    (chartImmersion f L) hL hft

/-- **The single-degree form of [Stacks, Tag 01VS] written out, unconditionally.** -/
theorem exists_immersion_projectiveSpaceOver_single_of_isAmple (hL : IsAmple X L)
    [hf : LocallyOfFiniteType f] :
    ∃ (N : ℤ) (n : ℕ) (i : X ⟶ projectiveSpaceOver n S), 1 ≤ N ∧ IsImmersion i ∧
      i ≫ pullback.fst (terminal.from S)
        (terminal.from (projectiveSpaceAtUniverse.{u} n)) = f ∧
      Nonempty (tensorPowModule X L N ≅
        (Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf n S)) := by
  obtain ⟨N, hN, n, i, himm, hif, he⟩ := exists_hasImmersionTwistOver_of_isAmple f L hL hf
  exact ⟨N, n, i, hN, himm, hif, he⟩

/-- **The whole of `Stacks.AmpleProjectiveImmersion.ImmersionTwistGap` from
`Stacks.AmpleImmersionReduction.TwistPassage` alone.** -/
theorem immersionTwistGap_of_twistPassage
    (hpass : Stacks.AmpleImmersionReduction.TwistPassage f L) :
    ImmersionTwistGap f L (tensorPowModule X L) :=
  Stacks.AmpleImmersionReduction.immersionTwistGap_of_chartImmersion_twistPassage f L
    (chartImmersion f L) hpass

/-- **[Stacks, Tag 01VS] written out, from
`Stacks.AmpleImmersionReduction.TwistPassage` alone.** -/
theorem exists_immersion_projectiveSpaceOver_of_isAmple_of_twistPassage (hL : IsAmple X L)
    [hf : LocallyOfFiniteType f] (hpass : Stacks.AmpleImmersionReduction.TwistPassage f L) :
    ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
      ∃ (n : ℕ) (i : X ⟶ projectiveSpaceOver n S),
        IsImmersion i ∧
        i ≫ pullback.fst (terminal.from S)
          (terminal.from (projectiveSpaceAtUniverse.{u} n)) = f ∧
        Nonempty (tensorPowModule X L (d : ℤ) ≅
          (Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf n S)) :=
  Stacks.AmpleImmersionReduction.exists_immersion_projectiveSpaceOver_of_isAmple_of_two f L hL
    (chartImmersion f L) hpass

end Consequences

end Stacks.ChartImmersionFinish

end

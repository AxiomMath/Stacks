module

public import StacksFrontier.AlgebraicGeometry.AmpleImmersionReduction.EventualGeneration
public import StacksFrontier.AlgebraicGeometry.ProductFamilyRatio.Basic

/-!
# What the Segre factorization of Stacks Tag 01VS discharges

[Stacks, Tag 01VS] is reduced in
`StacksFrontier/AlgebraicGeometry/AmpleImmersionReduction/Basic.lean` to four named conditions, and
`StacksFrontier/AlgebraicGeometry/ProductFamilyTwist/Basic.lean` restates the reduction on the
source's own route, with `Stacks.AmpleImmersionReduction.TwistPassage` replaced by
`Stacks.ProductFamilyTwist.ProductFamilyImmersion` and
`Stacks.AmpleEventualGeneration.IsEventuallyFinGenPowers` by
`Stacks.ProductFamilyTwist.EventuallyGeneratesStalksPowers`. This file spends the three of those
four that are now theorems.

* `Stacks.AmpleImmersionReduction.TwistPullback f` is
  `Stacks.AmpleImmersionReduction.twistPullback f`, unconditionally.
* `Stacks.AmpleImmersionReduction.ChartImmersion f L` is
  `Stacks.ChartImmersionFinish.chartImmersion f L`, unconditionally.
* `Stacks.ProductFamilyTwist.ProductFamilyImmersion f L` is
  `Stacks.ProductFamilyRatio.productFamilyImmersion f L`, unconditionally — the chart computation
  of the sibling file, which replaces the source's Segre sentence.

What is left in this file is **one** condition,
`Stacks.ProductFamilyTwist.EventuallyGeneratesStalksPowers L`, and it is needed only to pass from
an arithmetic progression of degrees to all sufficiently high degrees: the induction of steps 6
and 7 multiplies two families, so by itself it reaches the degrees `N + d k` and no others. The
progression form, `Stacks.ProductFamilyRatio.hasImmersionTwistOver_multiples_of_isAmple`, is
therefore unconditional here.

That last condition is **also a theorem**, in
`StacksFrontier/AlgebraicGeometry/StalkwiseGeneration/Ample.lean`: clause (7) of [Stacks, Tag 01Q3]
is available from ampleness in the epimorphism form
`Stacks.AmpleEventualGeneration.IsEventuallyFinGenPowers`, and
`Stacks.StalkwiseGeneration.exists_generatesStalks_of_isFinGen` converts that into the stalkwise
form this route consumes. Tag 01VS with no hypothesis beyond ampleness and finite type is
`Stacks.StalkwiseGeneration.exists_immersion_projectiveSpaceOver_of_isAmple`, which carries the
tag attribute; what this file states is the same conclusion with the condition still visible as a
hypothesis.

## Main results

* `Stacks.ProductFamilyRatio.hasImmersionTwistOver_multiples_of_isAmple`: **steps 6 and 7 of
  [Stacks, Tag 01VS] in every degree `N + d k`, with no named input left.**
* `Stacks.ProductFamilyRatio.immersionTwistGap_of_eventuallyGeneratesStalksPowers`:
  **`Stacks.AmpleProjectiveImmersion.ImmersionTwistGap` from the single remaining condition.**
* `Stacks.ProductFamilyRatio.exists_immersion_projectiveSpaceOver_of_isAmple`: **[Stacks, Tag
  01VS] written out, from that same single condition.** It is discharged in
  `StacksFrontier/AlgebraicGeometry/StalkwiseGeneration/Ample.lean`.

## What is not done

**No Stacks attribute is attached here, and in particular not Tag 01VS.** The statement of
that tag is a single assertion, and
`exists_immersion_projectiveSpaceOver_of_isAmple` below carries one hypothesis the tag does not.
The attribute sits on the hypothesis-free form in
`StacksFrontier/AlgebraicGeometry/StalkwiseGeneration/Ample.lean`.

`Stacks.AmpleImmersionReduction.TwistPassage` is **not** proved; it is the Segre-twist form of
steps 6 and 7, which this route does not take. See the sibling file's docstring.

## References

* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 01NE](https://stacks.math.columbia.edu/tag/01NE)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Ample Stacks.ProjectiveFromSections Stacks.AmpleProjectiveImmersion

universe u

namespace Stacks.ProductFamilyRatio

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {X : Scheme.{u}}

/-- **Steps 6 and 7 of [Stacks, Tag 01VS] in every degree `N + d k`, with no named input left.**
All three inputs of `Stacks.ProductFamilyTwist.hasImmersionTwistOver_multiples_of_isAmple` are
theorems: `Stacks.AmpleImmersionReduction.TwistPullback` is
`Stacks.AmpleImmersionReduction.twistPullback`,
`Stacks.AmpleImmersionReduction.ChartImmersion` is
`Stacks.ChartImmersionFinish.chartImmersion`, and
`Stacks.ProductFamilyTwist.ProductFamilyImmersion` is
`Stacks.ProductFamilyRatio.productFamilyImmersion`.

This is the form the source of Tag 01VS calls enough in virtually all applications: for an ample
`L` on a scheme locally of finite type over `S` there are positive `N` and `d` such that every
degree `N + d k` carries an immersion into projective space over `S` pulling `𝒪(1)` back to that
power. What it is *not* is Tag 01VS, which asserts this for **every** sufficiently high degree; the
arithmetic progression is all the source's induction on products of two families gives, and
closing the gap between them is
`Stacks.ProductFamilyTwist.EventuallyGeneratesStalksPowers`. -/
theorem hasImmersionTwistOver_multiples_of_isAmple {S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] (hL : IsAmple X L) (hft : LocallyOfFiniteType f) :
    ∃ N d : ℤ, 1 ≤ N ∧ 1 ≤ d ∧
      ∀ k : ℕ, HasImmersionTwistOver f (tensorPowModule X L (N + d * (k : ℤ))) :=
  Stacks.ProductFamilyTwist.hasImmersionTwistOver_multiples_of_isAmple f L
    (Stacks.AmpleImmersionReduction.twistPullback f)
    (Stacks.ChartImmersionFinish.chartImmersion f L) (productFamilyImmersion f L) hL hft

/-- **`Stacks.AmpleProjectiveImmersion.ImmersionTwistGap` — the whole of [Stacks, Tag 01VS] — from
the single named input `Stacks.ProductFamilyTwist.EventuallyGeneratesStalksPowers`.** -/
theorem immersionTwistGap_of_eventuallyGeneratesStalksPowers {S : Scheme.{u}} (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L]
    (hgen : Stacks.ProductFamilyTwist.EventuallyGeneratesStalksPowers L) :
    ImmersionTwistGap f L (tensorPowModule X L) :=
  Stacks.ProductFamilyTwist.immersionTwistGap_of_productFamilyImmersion f L
    (Stacks.AmpleImmersionReduction.twistPullback f)
    (Stacks.ChartImmersionFinish.chartImmersion f L) hgen (productFamilyImmersion f L)

/-- **[Stacks, Tag 01VS] from one named input**,
`Stacks.ProductFamilyTwist.EventuallyGeneratesStalksPowers`.

**No Tag 01VS attribute is attached here**: this carries one hypothesis the statement of the tag
does
not. The input is discharged for an ample `L` by
`Stacks.StalkwiseGeneration.eventuallyGeneratesStalksPowers_of_isAmple`, and the hypothesis-free
form carrying the attribute is
`Stacks.StalkwiseGeneration.exists_immersion_projectiveSpaceOver_of_isAmple`. -/
theorem exists_immersion_projectiveSpaceOver_of_isAmple {S : Scheme.{u}} (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] (hL : IsAmple X L) [LocallyOfFiniteType f]
    (hgen : Stacks.ProductFamilyTwist.EventuallyGeneratesStalksPowers L) :
    ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
      ∃ (n : ℕ) (i : X ⟶ projectiveSpaceOver n S),
        IsImmersion i ∧
        i ≫ pullback.fst (terminal.from S)
          (terminal.from (projectiveSpaceAtUniverse.{u} n)) = f ∧
        Nonempty (tensorPowModule X L (d : ℤ) ≅
          (Scheme.Modules.pullback i).obj (projectiveSpaceTwistingSheaf n S)) :=
  Stacks.ProductFamilyTwist.exists_immersion_projectiveSpaceOver_of_isAmple f L hL
    (Stacks.AmpleImmersionReduction.twistPullback f)
    (Stacks.ChartImmersionFinish.chartImmersion f L) hgen (productFamilyImmersion f L)

end Stacks.ProductFamilyRatio

end

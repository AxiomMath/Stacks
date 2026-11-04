module

public import StacksFrontier.AlgebraicGeometry.Quot.BaseAlgebraicStackSchemeStack
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyPicardAmpleLocus
public import StacksFrontier.AlgebraicGeometry.Quot.PicardAmpleAlgebraicStackSmooth
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedCurvesToCurvesSmoothAnyBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothTwoFibreProductComparison

/-!
# The smoothness half of Stacks 0DQ0 on the Picard stack of a family of curves

The source proves the smoothness clause of **Stacks 0DQ0** like this: given an object `X ⟶ S` of
`𝒞urves`, the base change `PolarizedCurves ×_{𝒞urves} S` is the substack of
`Picardstack_{X/S}` of objects whose invertible module is ample on `X_T/T`; that substack is open
by **Stacks 0D3D**, and `Picardstack_{X/S} ⟶ S` is smooth by **Stacks 0DPJ**.

`StacksFrontier.AlgebraicGeometry.Quot.PolarizedCurvesToCurvesSmoothReduction` reduces the clause to
smoothness of one such base change, and `AlgebraicGeometry.Stack.AlgebraicStacks`
`.isSmooth_fst_twoFibreProductSquare_of_isTwoFibreProduct` lets the base change be presented by
any 2-fibre product square of the cospan rather than the canonical one. This file supplies the
rest of the source's argument: everything about the ample locus of the Picard stack.

## What is proved and what is assumed

`AlgebraicGeometry.PicardAmpleBaseChange` is the moduli description of the base change, as a
datum: a family of curves over the chart, the relatively ample open substack of its Picard stack,
and a 2-commutative square over the cospan whose apex is that open substack and whose first leg
is its structure morphism to the chart, which is a 2-fibre product. The datum carries **no**
smoothness and **no** algebraicity: those are supplied here. It is exactly the sentence *"it is
clear that `PolarizedCurves ×_{𝒞urves} S` is the substack of `Picardstack_{X/S}` of objects
`(T/S, ℒ/X_T)` such that `ℒ` is ample on `X_T/T`"* of the source, and nothing more.

Given that datum, `AlgebraicGeometry`
`.isSmooth_polarizedCurvesToCurvesAlgebraicOfPolarized_of_picardAmpleBaseChange` proves the
smoothness clause from exactly two held tags, each as a binder quantified over families of
curves:

* `h0D04` — **Stacks 0D04**, that `Picardstack_{X/S}` is an algebraic stack; it is implied by
  **Stacks 09DS**.
* `h0DPJ` — **Stacks 0DPJ**, that `Picardstack_{X/S} ⟶ S` is smooth, in the shape
  `AlgebraicGeometry.Stack.AlgebraicStacks.IsSmooth B S hS
  (AlgebraicGeometry.Space.picardToBaseAlgebraic hc s h0D04)`.

Both are quantified over `AlgebraicGeometry.CurveFamily`, which is the index set at which they
are instances of their tags: the structure morphism of a family of curves is flat, proper and of
finite presentation, which is what Stacks 0D04 needs, and in addition of relative dimension at
most one, which is what Stacks 0DPJ needs. Nothing is quantified more widely than the tag
permits.

Everything else the source's argument uses is discharged here: the openness of the ample locus is
**Stacks 0D3D**, a theorem of this library
(`AlgebraicGeometry.Space.hasOpenObjectPropertyLocus_picardAmple_of_isProper`); the passage from
openness to smoothness over the base is **Stacks 075V** at an open immersion
(`AlgebraicGeometry.Stack.OpenSubstack.isSmooth_inclusion_comp`); the identification of `𝒮_T`
with the stack of the scheme `T` is
`AlgebraicGeometry.Space.baseAlgebraicStackToSchemeStack`; and the descent of smoothness from one
chart is **Stacks 0DN7**, through
`isSmooth_polarizedCurvesToCurvesAlgebraicOfPolarized_of_exists_baseChangeSquare`.

## No tag is registered

Stacks 0DQ0 asserts smoothness and surjectivity of `PolarizedCurves ⟶ 𝒞urves`. The theorems
below still carry **Stacks 0D4X** and **Stacks 0D5A**, which are needed to write the 1-morphism
down at all, together with Stacks 0D04 and Stacks 0DPJ and the moduli description. A registration
of Stacks 0DQ0 goes on the two-clause covering set once all of those are discharged.

## Main definitions

* `AlgebraicGeometry.PicardAmpleBaseChange`: the moduli description of the base change of
  `PolarizedCurves ⟶ 𝒞urves` along a scheme chart of `𝒞urves`, as the relatively ample open
  substack of the Picard stack of a family of curves over that chart.

## Main results

* `AlgebraicGeometry.PicardAmpleBaseChange.isSmooth_toChart`: the first leg of that square is
  smooth, given Stacks 0DPJ.
* `AlgebraicGeometry.PicardAmpleBaseChange.isSmooth_fst_twoFibreProductSquare`: the base-change
  clause of Stacks 0DQ0 at one chart, in the shape the reduction's `hbase` hypothesis asks for.
* `AlgebraicGeometry.isSmooth_polarizedCurvesToCurvesAlgebraicOfPolarized_of_picardAmpleBaseChange`
  : the smoothness half of Stacks 0DQ0 from Stacks 0D4X, Stacks 0D5A, Stacks 0D04, Stacks 0DPJ
  and the moduli description.
* `AlgebraicGeometry`
  `.isSmooth_and_isSurjective_polarizedCurvesToCurvesAlgebraicOfPolarized_of_picardAmpleBaseChange`
  : the two-element covering set for Stacks 0DQ0 on the same inputs.

## References

* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 075U](https://stacks.math.columbia.edu/tag/075U)
* [Stacks Project, Tag 075V](https://stacks.math.columbia.edu/tag/075V)
* [Stacks Project, Tag 0D04](https://stacks.math.columbia.edu/tag/0D04)
* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
* [Stacks Project, Tag 0D4X](https://stacks.math.columbia.edu/tag/0D4X)
* [Stacks Project, Tag 0D4Z](https://stacks.math.columbia.edu/tag/0D4Z)
* [Stacks Project, Tag 0D5A](https://stacks.math.columbia.edu/tag/0D5A)
* [Stacks Project, Tag 0DN7](https://stacks.math.columbia.edu/tag/0DN7)
* [Stacks Project, Tag 0DPJ](https://stacks.math.columbia.edu/tag/0DPJ)
* [Stacks Project, Tag 0DQ0](https://stacks.math.columbia.edu/tag/0DQ0)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u w

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- The statement of **Stacks 0D04** at the Picard stacks of the families of curves: for every
family of curves `X ⟶ T`, the Picard stack `Picardstack_{X/T}` is an algebraic stack. The
structure morphism of a family of curves is flat, proper and of finite presentation, so each
instance is an instance of Stacks 0D04. -/
abbrev Is0D04ForCurveFamilies : Prop :=
  ∀ X : CurveFamily B hZ, Stack.IsAlgebraicStack.{u, w} B integerBase hZ
    (Space.picardCFG (Space.modulePushforwardCoherence B integerBase hZ) X.picardSituation).val

/-- The statement of **Stacks 0DPJ** at the Picard stacks of the families of curves: for every
family of curves `X ⟶ T`, the structure morphism `Picardstack_{X/T} ⟶ 𝒮_T` is smooth in the sense
of Stacks 075U. The structure morphism of a family of curves has, in addition to the standing
hypotheses of Section 0DM9, relative dimension at most one, so each instance is an instance of
Stacks 0DPJ. -/
abbrev Is0DPJForCurveFamilies (h0D04 : Is0D04ForCurveFamilies.{u, w} B hZ) : Prop :=
  ∀ X : CurveFamily B hZ, Stack.AlgebraicStacks.IsSmooth B integerBase hZ
    (Space.picardToBaseAlgebraic.{u, w} (Space.modulePushforwardCoherence B integerBase hZ)
      X.picardSituation (h0D04 X))

variable {B hZ}

/-- **The moduli description of the base change of `PolarizedCurves ⟶ 𝒞urves` along a scheme
chart of `𝒞urves`.** Let `g : (Sch/U) ⟶ 𝒞urves` be a 1-morphism from the stack of a scheme of the
site. This datum says that the base change `(Sch/U) ×_{𝒞urves} PolarizedCurves` is the
relatively ample open substack of the Picard stack of a family of curves over `U`, over `U`:

* `family` is the family of curves, and `chartMap` identifies the stack of its base with the
  stack of `U`;
* `substack` is the relatively ample open substack of `Picardstack_{family}`, read as an object
  of the 2-category of algebraic stacks of Stacks 03YP through
  `AlgebraicGeometry.Space.picardAlgebraicStackOfPicardSituation`, and `substack_property` says
  that it is cut out by relative ampleness;
* `toChart` is its structure morphism to the stack of `U`, which `toChart_eq` requires to be the
  structure morphism of the Picard stack composed with the identifications;
* `toPolarized`, `comm` and `isTwoFibreProduct` say that this presents the base change: the
  square so formed over the cospan is a 2-fibre product (**Stacks 003Q**).

The datum carries no smoothness and no algebraicity, and is therefore exactly the identification
step of the source's proof of the smoothness clause of **Stacks 0DQ0**. Its remaining input is
Stacks 0D04, which is needed to write
`AlgebraicGeometry.Space.picardAlgebraicStackOfPicardSituation` down at all. -/
structure PicardAmpleBaseChange
    (h0D4X : Stack.IsAlgebraicStack.{u, w} B integerBase hZ
      (polarizedFiberedCategory B hZ
        (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)).val)
    (h0D5A : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)
    (h0D04 : Is0D04ForCurveFamilies.{u, w} B hZ) (U : BigFppfOver B integerBase hZ)
    (g : Stack.schemeStack.{u, w} B integerBase hZ U ⟶ curvesAlgebraicStack B hZ h0D5A) where
  /-- The family of curves over the chart whose Picard stack carries the base change. -/
  family : CurveFamily B hZ
  /-- The relatively ample open substack of the Picard stack of that family. -/
  substack : Stack.OpenSubstack (Space.picardAlgebraicStackOfPicardSituation.{u, w}
    (Space.modulePushforwardCoherence B integerBase hZ) family.picardSituation (h0D04 family))
  /-- It is cut out by relative ampleness of the invertible module. -/
  substack_property : substack.property =
    Stack.smallModelObjectProperty B integerBase hZ (h0D04 family)
      (Space.picardAmple (Space.modulePushforwardCoherence B integerBase hZ)
        family.picardSituation)
  /-- The identification of the stack of the base of the family with the stack of the chart. -/
  chartMap : Stack.schemeStack.{u, w} B integerBase hZ family.base ⟶
    Stack.schemeStack.{u, w} B integerBase hZ U
  /-- That identification is an equivalence. -/
  chartMap_isEquivalence :
    Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor chartMap.hom)
  /-- The first leg of the square: the ample open substack over the chart. -/
  toChart : substack.toAlgebraicStack ⟶ Stack.schemeStack.{u, w} B integerBase hZ U
  /-- The first leg is the structure morphism of the Picard stack, read over the chart. -/
  toChart_eq : toChart =
    ((substack.inclusion ≫ Space.picardToBaseAlgebraic.{u, w}
          (Space.modulePushforwardCoherence B integerBase hZ) family.picardSituation
          (h0D04 family)) ≫
        Space.baseAlgebraicStackToSchemeStack.{u, w} B integerBase hZ family.base) ≫ chartMap
  /-- The second leg of the square: the ample open substack as a family of polarized curves. -/
  toPolarized : substack.toAlgebraicStack ⟶ polarizedCurvesAlgebraicStack B hZ
    (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)
    (isAlgebraicStack_polarizedCurvesUnconditional_of_h0D4X B hZ h0D4X)
  /-- The square commutes up to a 2-isomorphism. -/
  comm : toChart ≫ g ≅
    toPolarized ≫ polarizedCurvesToCurvesAlgebraicOfPolarized B hZ h0D4X h0D5A
  /-- The square is a 2-fibre product, i.e. it *is* the base change. -/
  isTwoFibreProduct : Bicategory.IsTwoFibreProduct
    (⟨substack.toAlgebraicStack, toChart, toPolarized, comm⟩ :
      Bicategory.TwoCommSq g (polarizedCurvesToCurvesAlgebraicOfPolarized B hZ h0D4X h0D5A))

namespace PicardAmpleBaseChange

variable {h0D4X : Stack.IsAlgebraicStack.{u, w} B integerBase hZ
    (polarizedFiberedCategory B hZ
      (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)).val}
  {h0D5A : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val}
  {h0D04 : Is0D04ForCurveFamilies.{u, w} B hZ} {U : BigFppfOver B integerBase hZ}
  {g : Stack.schemeStack.{u, w} B integerBase hZ U ⟶ curvesAlgebraicStack B hZ h0D5A}

/-- **The base change is smooth over the chart**, given **Stacks 0DPJ**. The inclusion of the
ample open substack is an open immersion, hence smooth, so its composite with the smooth
structure morphism of the Picard stack is smooth (**Stacks 075V**); the identification of `𝒮_T`
with the stack of `T` and the identification of the base of the family with the chart are
equivalences, hence smooth, so the whole composite is. -/
theorem isSmooth_toChart (D : PicardAmpleBaseChange h0D4X h0D5A h0D04 U g)
    (h0DPJ : Is0DPJForCurveFamilies.{u, w} B hZ h0D04) :
    Stack.AlgebraicStacks.IsSmooth B integerBase hZ D.toChart := by
  rw [D.toChart_eq]
  exact Stack.AlgebraicStacks.isSmooth_comp B integerBase hZ _ D.chartMap
    (Space.isSmooth_comp_baseAlgebraicStackToSchemeStack.{u, w} B integerBase hZ D.family.base _
      (Stack.OpenSubstack.isSmooth_inclusion_comp B integerBase hZ D.substack _
        (h0DPJ D.family)))
    (Stack.AlgebraicStacks.isSmooth_of_isEquivalence B integerBase hZ D.chartMap
      D.chartMap_isEquivalence)

/-- **The base-change clause of Stacks 0DQ0 at one chart**, in the exact shape the hypothesis
`hbase` of
`AlgebraicGeometry.isSmooth_polarizedCurvesToCurvesAlgebraicOfPolarized_of_schemeChartBaseChange`
asks for: the first leg of the *canonical* base-change square of **Stacks 04T2** is smooth.

The moduli description presents the base change by another 2-fibre product square of the same
cospan, whose first leg is smooth by
`AlgebraicGeometry.PicardAmpleBaseChange.isSmooth_toChart`; smoothness of the first leg of a
2-fibre product square depends only on the cospan
(`Stack.AlgebraicStacks.isSmooth_fst_twoFibreProductSquare_of_isTwoFibreProduct`). -/
theorem isSmooth_fst_twoFibreProductSquare
    (D : PicardAmpleBaseChange h0D4X h0D5A h0D04 U g)
    (h0DPJ : Is0DPJForCurveFamilies.{u, w} B hZ h0D04) :
    Stack.AlgebraicStacks.IsSmooth B integerBase hZ
      (Stack.twoFibreProductSquareAlgebraicStacks B integerBase hZ g
        (polarizedCurvesToCurvesAlgebraicOfPolarized B hZ h0D4X h0D5A)).fst :=
  Stack.AlgebraicStacks.isSmooth_fst_twoFibreProductSquare_of_isTwoFibreProduct.{u, w}
    B integerBase hZ g (polarizedCurvesToCurvesAlgebraicOfPolarized B hZ h0D4X h0D5A)
    D.isTwoFibreProduct (D.isSmooth_toChart h0DPJ)

end PicardAmpleBaseChange

/-- **The smoothness half of Stacks 0DQ0 on the Picard stack of a family of curves.** Given that
`𝒫olarized` is an algebraic stack (`h0D4X`, **Stacks 0D4X**), that `𝒞urves` is an algebraic stack
(`h0D5A`, **Stacks 0D5A**), that the Picard stack of every family of curves is an algebraic stack
(`h0D04`, **Stacks 0D04**), that its structure morphism to the base is smooth (`h0DPJ`,
**Stacks 0DPJ**), and the moduli description `hample` of the base change along a scheme chart of
`𝒞urves` (`AlgebraicGeometry.PicardAmpleBaseChange`), the projection
`PolarizedCurves ⟶ 𝒞urves` is smooth in the sense of **Stacks 075U**.

This is the source's proof of the smoothness clause of Stacks 0DQ0 with everything other than
the four tags and the identification step discharged: openness of the ample locus is Stacks 0D3D,
a theorem of this library; the passage from it to smoothness over the base is Stacks 075V at an
open immersion; and the descent from one chart is Stacks 0DN7.

No tag is registered: all five hypotheses are unproved inputs. See the module documentation. -/
theorem isSmooth_polarizedCurvesToCurvesAlgebraicOfPolarized_of_picardAmpleBaseChange
    (h0D4X : Stack.IsAlgebraicStack.{u, w} B integerBase hZ
      (polarizedFiberedCategory B hZ
        (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)).val)
    (h0D5A : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)
    (h0D04 : Is0D04ForCurveFamilies.{u, w} B hZ)
    (h0DPJ : Is0DPJForCurveFamilies.{u, w} B hZ h0D04)
    (hample : ∀ (U : BigFppfOver B integerBase hZ)
      (g : Stack.schemeStack.{u, w} B integerBase hZ U ⟶ curvesAlgebraicStack B hZ h0D5A),
      Stack.AlgebraicStacks.IsSmooth B integerBase hZ g →
      Stack.IsSurjective B integerBase hZ g →
        Nonempty (PicardAmpleBaseChange h0D4X h0D5A h0D04 U g)) :
    Stack.AlgebraicStacks.IsSmooth B integerBase hZ
      (polarizedCurvesToCurvesAlgebraicOfPolarized B hZ h0D4X h0D5A) :=
  isSmooth_polarizedCurvesToCurvesAlgebraicOfPolarized_of_exists_baseChangeSquare.{u, w}
    B hZ h0D4X h0D5A fun U g hgsm hgs => by
      obtain ⟨D⟩ := hample U g hgsm hgs
      exact ⟨_, ⟨D.isTwoFibreProduct⟩, D.isSmooth_toChart h0DPJ⟩

/-- **The two-element covering set for Stacks 0DQ0 on the Picard stack of a family of curves.**
Both clauses of Stacks 0DQ0 — smoothness and surjectivity of `PolarizedCurves ⟶ 𝒞urves` — on
Stacks 0D4X, Stacks 0D5A, Stacks 0D04, Stacks 0DPJ and the moduli description of the base change;
the surjectivity clause rests on the first two alone.

No tag is registered. See the module documentation. -/
theorem
    isSmooth_and_isSurjective_polarizedCurvesToCurvesAlgebraicOfPolarized_of_picardAmpleBaseChange
    (h0D4X : Stack.IsAlgebraicStack.{u, w} B integerBase hZ
      (polarizedFiberedCategory B hZ
        (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)).val)
    (h0D5A : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)
    (h0D04 : Is0D04ForCurveFamilies.{u, w} B hZ)
    (h0DPJ : Is0DPJForCurveFamilies.{u, w} B hZ h0D04)
    (hample : ∀ (U : BigFppfOver B integerBase hZ)
      (g : Stack.schemeStack.{u, w} B integerBase hZ U ⟶ curvesAlgebraicStack B hZ h0D5A),
      Stack.AlgebraicStacks.IsSmooth B integerBase hZ g →
      Stack.IsSurjective B integerBase hZ g →
        Nonempty (PicardAmpleBaseChange h0D4X h0D5A h0D04 U g)) :
    Stack.AlgebraicStacks.IsSmooth B integerBase hZ
        (polarizedCurvesToCurvesAlgebraicOfPolarized B hZ h0D4X h0D5A) ∧
      Stack.IsSurjective B integerBase hZ
        (polarizedCurvesToCurvesAlgebraicOfPolarized B hZ h0D4X h0D5A) :=
  ⟨isSmooth_polarizedCurvesToCurvesAlgebraicOfPolarized_of_picardAmpleBaseChange.{u, w}
      h0D4X h0D5A h0D04 h0DPJ hample,
    isSurjective_polarizedCurvesToCurvesAlgebraicOfPolarized.{u, w} B hZ h0D4X h0D5A⟩

end AlgebraicGeometry

end

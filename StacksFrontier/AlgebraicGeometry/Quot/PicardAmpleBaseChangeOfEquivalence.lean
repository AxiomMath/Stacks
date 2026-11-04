module

public import StacksFrontier.AlgebraicGeometry.Quot.C1783.PolarizedCurvesRemark
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedCurvesToCurvesSmoothPicardAmple
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductUniversalProperty
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence
public import StacksFrontier.CategoryTheory.TwoFibreProduct.PrecomposeLegs

/-!
# The moduli description of the base change, from one equivalence of categories

`AlgebraicGeometry.PicardAmpleBaseChange` identifies the base change of `PolarizedCurves ⟶ 𝒞urves`
along a scheme chart `(Sch/U) ⟶ 𝒞urves` with the relatively ample open substack of the Picard
stack of a family of curves over `U`, as in the smoothness half of **Stacks 0DQ0**. Its last field
asserts that a 2-commutative square over the cospan is a 2-fibre product in the 2-category of
algebraic stacks.

This file shows that the whole datum follows from

* a comparison 1-morphism `p` from the ample open substack to the apex of the *canonical* 2-fibre
  product of the cospan, at the level of categories fibred in groupoids, whose underlying functor
  is an equivalence of categories, and
* two 2-isomorphisms saying that `p` followed by the two projections of the canonical square is
  the ample substack's structure morphism to the chart, respectively the 1-morphism to
  `PolarizedCurves`.

The algebraicity of `𝒫olarized` (Stacks 0D4X) is the first conjunct of clause (2) of
`AlgebraicGeometry.polarizedCurvesToCurves_isAlgebraic_smooth_surjective` (Stacks 0D5C);
Stacks 0D5A (`h0D5A`) and Stacks 0D04 (`h0D04`) are hypotheses.

## Main definitions

* `AlgebraicGeometry.picardAmpleCanonicalSquare`: the canonical 2-fibre product square of the
  cospan of the chart and of `PolarizedCurves ⟶ 𝒞urves`, read between the underlying categories
  fibred in groupoids.

## Main results

* `AlgebraicGeometry.picardAmpleBaseChangeOfEquivalence`: the moduli identification from the
  comparison equivalence and the two compatibility 2-isomorphisms.
* `AlgebraicGeometry.nonempty_picardAmpleBaseChange_of_exists_equivalence`: the same, in
  propositional form.

## Implementation notes

`CategoryTheory.Bicategory.TwoCommSq.precomposeLegs` presents a square whose apex is `p`'s source
and whose legs are *prescribed* up to 2-isomorphism: the first leg of
`AlgebraicGeometry.PicardAmpleBaseChange` is the structure morphism of the Picard stack read over
the chart, and only a 2-isomorphism to the canonical projection is available.
`CategoryTheory.Bicategory.TwoCommSq.PreHom.ofPrecomposeLegs` makes `p` a pre-morphism of squares
from it to the canonical one, and `CategoryTheory.Bicategory.isTwoFibreProduct_of_isEquivalence_to`
turns the equivalence into the universal property, in the 2-category of categories fibred in
groupoids. That 2-category contains the 2-category of algebraic stacks as a full sub-2-category,
so `AlgebraicGeometry.Stack.AlgebraicStacks.isTwoFibreProduct_of_toCatFiberedInGroupoids` carries
it up.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 0D4X](https://stacks.math.columbia.edu/tag/0D4X)
* [Stacks Project, Tag 0D5C](https://stacks.math.columbia.edu/tag/0D5C)
* [Stacks Project, Tag 0DQ0](https://stacks.math.columbia.edu/tag/0DQ0)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u w

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **The canonical 2-fibre product square of the cospan of a scheme chart of `𝒞urves` and of
`PolarizedCurves ⟶ 𝒞urves`**, read between the categories fibred in groupoids underlying the
algebraic stacks: the square of **Stacks 0040** at hom universe `u`. Its apex is the base change
`(Sch/U) ×_{𝒞urves} PolarizedCurves`. -/
def picardAmpleCanonicalSquare
    (h0D5A : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)
    {U : BigFppfOver B integerBase hZ}
    (g : Stack.schemeStack.{u, w} B integerBase hZ U ⟶ curvesAlgebraicStack B hZ h0D5A) :
    Bicategory.TwoCommSq g.hom
      (polarizedCurvesToCurvesAlgebraicOfPolarized B hZ
        (polarizedCurvesToCurves_isAlgebraic_smooth_surjective.{w, u} B hZ).2.1.1 h0D5A).hom :=
  CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom
    (polarizedCurvesToCurvesAlgebraicOfPolarized B hZ
      (polarizedCurvesToCurves_isAlgebraic_smooth_surjective.{w, u} B hZ).2.1.1 h0D5A).hom

/-- The canonical square of `AlgebraicGeometry.picardAmpleCanonicalSquare` is a 2-fibre product,
being the canonical one (**Stacks 003Q**). -/
def isTwoFibreProduct_picardAmpleCanonicalSquare
    (h0D5A : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)
    {U : BigFppfOver B integerBase hZ}
    (g : Stack.schemeStack.{u, w} B integerBase hZ U ⟶ curvesAlgebraicStack B hZ h0D5A) :
    Bicategory.IsTwoFibreProduct (picardAmpleCanonicalSquare.{u, w} h0D5A g) :=
  CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom
    (polarizedCurvesToCurvesAlgebraicOfPolarized B hZ
      (polarizedCurvesToCurves_isAlgebraic_smooth_surjective.{w, u} B hZ).2.1.1 h0D5A).hom

variable {h0D5A : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val}
  {h0D04 : Is0D04ForCurveFamilies.{u, w} B hZ} {U : BigFppfOver B integerBase hZ}
  {g : Stack.schemeStack.{u, w} B integerBase hZ U ⟶ curvesAlgebraicStack B hZ h0D5A}

/-- **The moduli description of the base change from one equivalence of categories.** Let
`family` be a family of curves, let `substack` be the relatively ample open substack of its
Picard stack, let `chartMap` identify the stack of its base with the stack of the chart `U`, and
let `toPolarized` read the ample substack as a family of polarized curves. Suppose given a
comparison 1-morphism `p` from the ample substack to the apex
`(Sch/U) ×_{𝒞urves} PolarizedCurves` of the canonical 2-fibre product
(`AlgebraicGeometry.picardAmpleCanonicalSquare`) whose underlying functor is an equivalence of
categories, and suppose `p` is compatible with the two projections up to 2-isomorphism: `eu` for
the projection to the chart and `ev` for the one to `PolarizedCurves`. Then all of this is an
`AlgebraicGeometry.PicardAmpleBaseChange`. -/
def picardAmpleBaseChangeOfEquivalence
    (family : CurveFamily B hZ)
    (substack : Stack.OpenSubstack (Space.picardAlgebraicStackOfPicardSituation.{u, w}
      (Space.modulePushforwardCoherence B integerBase hZ) family.picardSituation
      (h0D04 family)))
    (substack_property : substack.property =
      Stack.smallModelObjectProperty B integerBase hZ (h0D04 family)
        (Space.picardAmple (Space.modulePushforwardCoherence B integerBase hZ)
          family.picardSituation))
    (chartMap : Stack.schemeStack.{u, w} B integerBase hZ family.base ⟶
      Stack.schemeStack.{u, w} B integerBase hZ U)
    (chartMap_isEquivalence :
      Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor chartMap.hom))
    (toPolarized : substack.toAlgebraicStack ⟶ polarizedCurvesAlgebraicStack B hZ
      (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)
      (isAlgebraicStack_polarizedCurvesUnconditional_of_h0D4X B hZ
        (polarizedCurvesToCurves_isAlgebraic_smooth_surjective.{w, u} B hZ).2.1.1))
    (p : substack.toAlgebraicStack.val ⟶ (picardAmpleCanonicalSquare.{u, w} h0D5A g).pt)
    (eu : (((substack.inclusion ≫ Space.picardToBaseAlgebraic.{u, w}
              (Space.modulePushforwardCoherence B integerBase hZ) family.picardSituation
              (h0D04 family)) ≫
            Space.baseAlgebraicStackToSchemeStack.{u, w} B integerBase hZ family.base) ≫
          chartMap).hom ≅
      p ≫ (picardAmpleCanonicalSquare.{u, w} h0D5A g).fst)
    (ev : toPolarized.hom ≅ p ≫ (picardAmpleCanonicalSquare.{u, w} h0D5A g).snd)
    (hp : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor p)) :
    PicardAmpleBaseChange (polarizedCurvesToCurves_isAlgebraic_smooth_surjective.{w, u} B hZ).2.1.1
      h0D5A h0D04 U g where
  family := family
  substack := substack
  substack_property := substack_property
  chartMap := chartMap
  chartMap_isEquivalence := chartMap_isEquivalence
  toChart := ((substack.inclusion ≫ Space.picardToBaseAlgebraic.{u, w}
          (Space.modulePushforwardCoherence B integerBase hZ) family.picardSituation
          (h0D04 family)) ≫
        Space.baseAlgebraicStackToSchemeStack.{u, w} B integerBase hZ family.base) ≫ chartMap
  toChart_eq := rfl
  toPolarized := toPolarized
  comm := Bicategory.InducedBicategory.isoMk
    ((picardAmpleCanonicalSquare.{u, w} h0D5A g).precomposeLegs p
      (((substack.inclusion ≫ Space.picardToBaseAlgebraic.{u, w}
              (Space.modulePushforwardCoherence B integerBase hZ) family.picardSituation
              (h0D04 family)) ≫
            Space.baseAlgebraicStackToSchemeStack.{u, w} B integerBase hZ family.base) ≫
          chartMap).hom
      toPolarized.hom eu ev).iso
  isTwoFibreProduct :=
    Stack.AlgebraicStacks.isTwoFibreProduct_of_toCatFiberedInGroupoids B integerBase hZ _
      (Bicategory.isTwoFibreProduct_of_isEquivalence_to
        (isTwoFibreProduct_picardAmpleCanonicalSquare.{u, w} h0D5A g)
        (Bicategory.TwoCommSq.PreHom.ofPrecomposeLegs
          (picardAmpleCanonicalSquare.{u, w} h0D5A g) p _ toPolarized.hom eu ev)
        hp)

/-- **The moduli description from one equivalence of categories, in propositional form.** If
there are a family of curves, a relatively ample open substack of its Picard stack, an
identification of the stack of its base with that of the chart `U`, a 1-morphism to
`PolarizedCurves` and a comparison equivalence `p` to the apex of
`AlgebraicGeometry.picardAmpleCanonicalSquare` compatible with the two projections up to
2-isomorphism, then `AlgebraicGeometry.PicardAmpleBaseChange` is inhabited. -/
theorem nonempty_picardAmpleBaseChange_of_exists_equivalence
    (h : ∃ (family : CurveFamily B hZ)
      (substack : Stack.OpenSubstack (Space.picardAlgebraicStackOfPicardSituation.{u, w}
        (Space.modulePushforwardCoherence B integerBase hZ) family.picardSituation
        (h0D04 family))),
      substack.property =
          Stack.smallModelObjectProperty B integerBase hZ (h0D04 family)
            (Space.picardAmple (Space.modulePushforwardCoherence B integerBase hZ)
              family.picardSituation) ∧
        ∃ chartMap : Stack.schemeStack.{u, w} B integerBase hZ family.base ⟶
          Stack.schemeStack.{u, w} B integerBase hZ U,
          Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor chartMap.hom) ∧
          ∃ (toPolarized : substack.toAlgebraicStack ⟶ polarizedCurvesAlgebraicStack B hZ
              (polarizedProjection_comp_schemeOverIntegers_isFiberedInGroupoids B)
              (isAlgebraicStack_polarizedCurvesUnconditional_of_h0D4X B hZ
                (polarizedCurvesToCurves_isAlgebraic_smooth_surjective.{w, u} B hZ).2.1.1))
            (p : substack.toAlgebraicStack.val ⟶
              (picardAmpleCanonicalSquare.{u, w} h0D5A g).pt),
            Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor p) ∧
            Nonempty ((((substack.inclusion ≫ Space.picardToBaseAlgebraic.{u, w}
                    (Space.modulePushforwardCoherence B integerBase hZ) family.picardSituation
                    (h0D04 family)) ≫
                  Space.baseAlgebraicStackToSchemeStack.{u, w} B integerBase hZ family.base) ≫
                chartMap).hom ≅
              p ≫ (picardAmpleCanonicalSquare.{u, w} h0D5A g).fst) ∧
            Nonempty (toPolarized.hom ≅
              p ≫ (picardAmpleCanonicalSquare.{u, w} h0D5A g).snd)) :
    Nonempty (PicardAmpleBaseChange
      (polarizedCurvesToCurves_isAlgebraic_smooth_surjective.{w, u} B hZ).2.1.1 h0D5A
      h0D04 U g) := by
  obtain ⟨family, substack, hprop, chartMap, hchart, toPolarized, p, hp, ⟨eu⟩, ⟨ev⟩⟩ := h
  exact ⟨picardAmpleBaseChangeOfEquivalence.{u, w} family substack hprop chartMap hchart
    toPolarized p eu ev hp⟩

end AlgebraicGeometry

end

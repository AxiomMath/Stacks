module

public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleSeparatedChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineGroupoidPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOverSchemeRepresentable

/-!
# The presentation attached to a finite flat chart from an object of the site

Let `𝒳` be an algebraic stack over `S` and let `f : 𝒮_W ⟶ 𝒳` be a 1-morphism from the algebraic
stack of an object `W` of the big fppf site which is surjective, flat, finite and of finite
presentation. The object `W` need not be affine. This file shows that the self-intersection
`R = 𝒮_W ×_𝒳 𝒮_W` is represented by an object `V` of the site, that the two projections are
finite locally free morphisms of schemes, and that the canonical 1-morphism `[W/R] ⟶ 𝒳` of
Stacks 04T4 is an equivalence (Stacks 04WY).

For `W` affine this is the content of the implication (1) ⟹ (2) of Stacks 0DUM; the proof is the
same, with the affineness of `R` replaced by its representability: a finite morphism of algebraic
spaces is affine, and an algebraic space affine over a scheme is a scheme.

It is applied in the proof of Stacks 0DUS to the base change `W = 𝒳' ×_𝒳 U` of a chart of a
well-nigh affine stack along an étale, separated, stabilizer-preserving 1-morphism `𝒳' ⟶ 𝒳`.

## Main results

* `AlgebraicGeometry.Stack.ChartBaseChange.chartStack_properties`: the base change of a
  surjective, flat, finite and finitely presented chart is again one.
* `AlgebraicGeometry.Stack.exists_flatChartPresentation`: the presentation described above.

## References

* [Stacks Project, Tag 0DUS](https://stacks.math.columbia.edu/tag/0DUS)
* [Stacks Project, Tag 0DUM](https://stacks.math.columbia.edu/tag/0DUM)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 04WY](https://stacks.math.columbia.edu/tag/04WY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ChartBaseChange

variable {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} (h : 𝒳' ⟶ 𝒳) {U : BigFppfOver B S hS}
  (x : schemeStack.{u, w} B S hS U ⟶ 𝒳) {W : BigFppfOver B S hS}
  (eK : StacksRepresentableCFG.EquivalenceOver (schemeStack.{u, w} B S hS W).val.val.p
    (chartBaseChangeSquare h x).pt.val.val.p)

/-- The base-changed chart `𝒮_W ⟶ 𝒳'`, as a 1-morphism of algebraic stacks: the equivalence
`𝒮_W ≃ 𝒳' ×_𝒳 𝒮_U` followed by the first projection. -/
noncomputable abbrev chartStack : schemeStack.{u, w} B S hS W ⟶ 𝒳' :=
  Bicategory.InducedBicategory.mkHom (comparison h x eK) ≫ (chartBaseChangeSquare h x).fst

/-- **The base-changed chart is surjective, flat, finite and of finite presentation** when the
chart `x` is. -/
theorem chartStack_properties (hsurj : IsSurjective B S hS x)
    (hflat : AlgebraicStacks.IsFlat B S hS x) (hfin : AlgebraicStacks.IsFinite B S hS x)
    (hfp : AlgebraicStacks.IsRelativelyFinitePresentation B S hS x) :
    IsSurjective B S hS (chartStack h x eK) ∧ AlgebraicStacks.IsFlat B S hS (chartStack h x eK) ∧
      AlgebraicStacks.IsFinite B S hS (chartStack h x eK) ∧
        AlgebraicStacks.IsRelativelyFinitePresentation B S hS (chartStack h x eK) :=
  chartBaseChange_properties h x (Bicategory.InducedBicategory.mkHom (comparison h x eK))
    eK.toEquivalence.isEquivalence_functor hsurj hflat hfin hfp

end ChartBaseChange

section FlatChart

variable (𝒳 : AlgebraicStacks.{u, w} B S hS) {W : BigFppfOver B S hS}

/-- **The presentation of an algebraic stack by a finite flat chart from an object of the site.**
Let `f : 𝒮_W ⟶ 𝒳` be surjective, flat, finite and of finite presentation, with `W` an arbitrary
object of the site. Then the self-intersection `𝒮_W ×_𝒳 𝒮_W` is represented by an object `V`
of the site, through an equivalence `eR`, the two projections are the Yoneda images of finite
locally free morphisms `s, t : V ⟶ W`, these carry a groupoid structure on their sections, and the
canonical 1-morphism from its quotient stack to `𝒳` is an equivalence over the site
(Stacks 04WY). -/
theorem exists_flatChartPresentation (f : schemeStack.{u, w} B S hS W ⟶ 𝒳)
    (eU : StacksRepresentableCFG.EquivalenceOver (schemeStack.{u, w} B S hS W).val.val.p
      (presheafOfCategories
        ((⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS).obj ⋙
          typeToCat)).p)
    (hsurj : IsSurjective B S hS f) (hflat : AlgebraicStacks.IsFlat B S hS f)
    (hfin : AlgebraicStacks.IsFinite B S hS f)
    (hfp : AlgebraicStacks.IsRelativelyFinitePresentation B S hS f) :
    ∃ (V : BigFppfOver B S hS)
      (eR : StacksRepresentableCFG.EquivalenceOver
        (SelfIntersection.relation B S hS (schemeStack.{u, w} B S hS W).val 𝒳.val
          f.hom.hom).val.p
        (presheafOfCategories
          ((⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS).obj ⋙
            typeToCat)).p)
      (s t : V ⟶ W)
      (c : Deformation.composableArrows (yoneda.obj W) (yoneda.obj V)
        (yoneda.map s) (yoneda.map t) ⟶ yoneda.obj V)
      (_hG : ∀ T, Nonempty (Deformation.PointwiseGroupoid ((yoneda.map s).app T)
        ((yoneda.map t).app T) fun p => c.app T p)),
      yoneda.map s = SelfIntersection.relationSourceMap eU eR ∧
      yoneda.map t = SelfIntersection.relationTargetMap eU eR ∧
      Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map s) ∧
      Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map t) ∧
      Nonempty (Functor.IsEquivalenceOver
        (Stack.quotientStack (SelfIntersection.selfIntersectionPresentation eU eR
          𝒳.property).groupoid).p
        𝒳.val.val.p
        (SelfIntersection.selfIntersectionPresentation eU eR
          𝒳.property).canonicalMap.toFunctor) := by
  classical
  obtain ⟨hrep, hfin⟩ := hfin
  obtain ⟨-, hfp⟩ := hfp
  let 𝒰 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
    schemeFibredCategory B S hS W
  let F : 𝒰 ⟶ 𝒳.val := f.hom
  let Uₛ : AlgebraicSpaces B S hS := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩
  obtain ⟨Robj, hRobj, ⟨eR₀⟩⟩ :=
    SelfIntersection.isRepresentableByAlgebraicSpace_relation_of_isAlgebraicStack
      B S hS 𝒰 𝒳.val F.hom 𝒳.property
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS W)
  let R₀ : AlgebraicSpaces B S hS := ⟨Robj, hRobj⟩
  let eR₀' : StacksRepresentableCFG.EquivalenceOver
      (SelfIntersection.relation B S hS 𝒰 𝒳.val F.hom).val.p
      (presheafOfCategories (R₀.obj ⋙ typeToCat)).p := eR₀
  -- the relative properties of the presentation
  have hfinP : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.finiteMorphismProperty B S hS) F hrep := hfin
  have hflatP : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (spaceProperty B S hS (fun _ _ h => Space.IsFlat B S hS h)) F hrep :=
    (hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_flat B S hS) (schemeStack.{u, w} B S hS W).property
      𝒳.property F hrep).1 hflat
  have hlfpP : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (g : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation B S hS g.hom) F hrep :=
    fun V y hy G hG he => (hfp V y hy G hG he).1
  have hsurjP : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) F hrep :=
    (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS f hrep).1 hsurj
  -- the self-intersection is represented by an object of the site, finite over `W`
  have ht₀ : Space.IsFinite B S hS (SelfIntersection.relationTarget eU eR₀').hom :=
    SelfIntersection.prop_relationTarget B S hS 𝒰 𝒳.val F Uₛ R₀ eU eR₀'
      (Space.finiteMorphismProperty B S hS) hrep hfinP
  obtain ⟨V, iV, -, -, -⟩ := Space.exists_representing_over_of_isAffineHom B S hS hRobj
    (SelfIntersection.relationTarget eU eR₀').hom (Space.IsFinite.isAffineHom ht₀)
  let Rₛ : AlgebraicSpaces B S hS := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
  let eR : StacksRepresentableCFG.EquivalenceOver
      (SelfIntersection.relation B S hS 𝒰 𝒳.val F.hom).val.p
      (presheafOfCategories (Rₛ.obj ⋙ typeToCat)).p :=
    eR₀'.trans (PresheafOfCategories.equivalenceOverOfIso iV)
  -- Stacks 04WY: the canonical 1-morphism out of `[W/R]` is an equivalence
  have E := SelfIntersection.nonempty_isEquivalenceOver_canonicalMap eU eR 𝒳.property
    (fun T y hy G hG he => ⟨hsurjP T y hy G hG he, hflatP T y hy G hG he,
      hlfpP T y hy G hG he⟩)
  -- the source and target of the groupoid
  have hsF := SelfIntersection.prop_relationSource B S hS 𝒰 𝒳.val F Uₛ Rₛ eU eR
      (Space.finiteMorphismProperty B S hS) hrep hfinP
  have htF := SelfIntersection.prop_relationTarget B S hS 𝒰 𝒳.val F Uₛ Rₛ eU eR
      (Space.finiteMorphismProperty B S hS) hrep hfinP
  obtain ⟨hsFl, htFl⟩ := SelfIntersection.isFlat_relationSource_and_relationTarget
    B S hS 𝒰 𝒳.val F Uₛ Rₛ eU eR hrep hflatP
  obtain ⟨hsL, htL⟩ :=
    SelfIntersection.isLocallyOfFinitePresentation_relationSource_and_relationTarget
      B S hS 𝒰 𝒳.val F Uₛ Rₛ eU eR hrep hlfpP
  obtain ⟨s, t, c', hG', hs, ht, -⟩ := exists_representedGroupoid_eq_ofComposable B S hS
    (SelfIntersection.relationSourceMap eU eR) (SelfIntersection.relationTargetMap eU eR)
    (SelfIntersection.compositionLaw eU eR (SelfIntersection.isFiberedInSetoids_source eU))
    (SelfIntersection.nonempty_pointwiseGroupoid eU eR
      (SelfIntersection.isFiberedInSetoids_source eU))
  refine ⟨V, eR, s, t, c', hG', hs, ht, ?_, ?_, E⟩
  · change Space.IsFinite B S hS (SelfIntersection.relationSourceMap eU eR) at hsF
    change Space.IsFlat B S hS (SelfIntersection.relationSourceMap eU eR) at hsFl
    change Space.IsLocallyOfFinitePresentation B S hS
      (SelfIntersection.relationSourceMap eU eR) at hsL
    rw [← hs] at hsF hsFl hsL
    exact isFiniteLocallyFree_of_yonedaMap B S hS s hsF hsFl hsL
  · change Space.IsFinite B S hS (SelfIntersection.relationTargetMap eU eR) at htF
    change Space.IsFlat B S hS (SelfIntersection.relationTargetMap eU eR) at htFl
    change Space.IsLocallyOfFinitePresentation B S hS
      (SelfIntersection.relationTargetMap eU eR) at htL
    rw [← ht] at htF htFl htL
    exact isFiniteLocallyFree_of_yonedaMap B S hS t htF htFl htL

end FlatChart

end AlgebraicGeometry.Stack

end

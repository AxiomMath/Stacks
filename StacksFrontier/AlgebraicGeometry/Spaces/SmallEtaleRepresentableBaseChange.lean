module

public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableEquivalence

/-!
# Chart base change of representable algebraic spaces is base change of schemes

Let `B` be a big fppf site containing a scheme `S` and let `g : T' ⟶ T` be a morphism of the big
fppf category over `S`.  The presheaves `yoneda.obj T'` and `yoneda.obj T` are algebraic spaces
over `S` and `g` represents a morphism `φ` between them; base change of étale scheme charts
along `φ`, `AlgebraicGeometry.Space.smallBaseChange`, is then a functor between the small étale
sites of the two representable algebraic spaces.

Those two sites are already identified with the small étale sites of the underlying *schemes*,
in the big étale site carried by the same category of schemes, by
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence`.  This file proves that the
identification is compatible with base change: the square

```
SmallEtale (yoneda.obj T) --- chart base change along φ ---> SmallEtale (yoneda.obj T')
          |                                                            |
 representedSmallEtaleEquivalence                   representedSmallEtaleEquivalence
          v                                                            v
     SmallEtale T  ------- base change along g ------->            SmallEtale T'
```

commutes up to a canonical natural isomorphism.  It does so because both composites send a
chart to a fibre product of the chart with `T'` over `T`: on the left the one supplied by the
chosen representability witness of `φ`, on the right the chosen fibre product of the bounded
category of schemes.

## Main definitions

* `AlgebraicGeometry.Space.representedSpaceMap` is the morphism of algebraic spaces over `S`
  represented by a morphism of the big fppf category over `S`, and
  `AlgebraicGeometry.Space.relativelyRepresentable_yoneda_map` says that it is relatively
  representable, so that chart base change applies to it.
* `AlgebraicGeometry.Space.representedSmallEtaleBaseChangeComponent` is the comparison at a
  single chart and `AlgebraicGeometry.Space.representedSmallEtaleBaseChangeIso` the natural
  isomorphism filling the square above.
* `AlgebraicGeometry.Space.representedChartHom` and
  `AlgebraicGeometry.Space.representedPullbackMap` are the two base changes of a morphism of
  charts, read on the underlying objects of the bounded category of schemes.

## Main results

* `AlgebraicGeometry.Space.isPullback_representedChart` is the representability square of `φ`
  read in the big fppf category over `S`, and
  `AlgebraicGeometry.Space.isPullback_representedChart_schemes` is its image in the bounded
  category of schemes.  Together they are the content of the comparison: the chosen
  representability witness of `yoneda.map g` computes a fibre product of the big fppf category,
  because `yoneda` is fully faithful and the slice projection preserves fibre products.

## Implementation notes

The direction in which the square is stated matters for the same reason as in
`AlgebraicGeometry.SmallEtale.toEtaleSiteBaseChangeIso`: stated with the chart base change
first, the components are morphisms *into* `CategoryTheory.Limits.pullback`, an honest chosen
fibre product of the bounded category of schemes to which
`CategoryTheory.Limits.pullback.hom_ext` applies directly.

Everything is computed on underlying morphisms of the bounded category of schemes.  The three
`rfl`-lemmas `AlgebraicGeometry.Space.representedSmallEtaleBaseChangeComponent_hom`,
`AlgebraicGeometry.Space.representedSmallEtaleBaseChange_lhs_map` and
`AlgebraicGeometry.Space.representedSmallEtaleBaseChange_rhs_map` reduce the two functors to
that level, and the naturality square is stated and proved there; no étale-ness condition
occurs in any of those computations, so no morphism property is ever matched against.  Stating
naturality separately, rather than rewriting inside the proof of the natural isomorphism, is
what keeps every rewritten goal type-correct at `implicit` transparency: the apex of a chosen
fibre product and the structure morphism of a base-changed chart are definitionally but not
syntactically equal, and a rewrite whose motive crosses that boundary fails.

The comparison depends on the chosen representability witness `hg`, because
`AlgebraicGeometry.Space.smallBaseChange` does: the object `hg.pullback` of
`CategoryTheory.Functor.relativelyRepresentable` is a choice, not the chosen fibre product of
the bounded category of schemes.  That is exactly what the comparison compares, and it is why
the witness is an explicit argument everywhere below.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 025Z](https://stacks.math.columbia.edu/tag/025Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] BigFppfSite.hasPullbacks_schemes

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The morphism of algebraic spaces over `S` represented by a morphism of the big fppf
category over `S`: an abbreviation of `AlgebraicGeometry.schemeSpaceMap`, typed between the
anonymous constructors in which the small étale sites of the two representable algebraic spaces
are written. -/
abbrev representedSpaceMap {T' T : BigFppfOver B S hS} (g : T' ⟶ T) :
    (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ :=
  schemeSpaceMap g

/-- A morphism of representable algebraic spaces over `S` is relatively representable: the big
fppf category over `S` has fibre products and `yoneda` preserves them. -/
theorem relativelyRepresentable_yoneda_map {T' T : BigFppfOver B S hS} (g : T' ⟶ T) :
    yoneda.relativelyRepresentable (yoneda.map g) :=
  have : HasPullbacks (BigFppfOver B S hS) := inferInstance
  Functor.relativelyRepresentable.map yoneda g

section RepresentedBaseChange

variable {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
  (hg : yoneda.relativelyRepresentable (yoneda.map g))

/-- A morphism of representable presheaves on the big fppf category over `S` is the Yoneda
image of its Yoneda preimage. -/
private theorem yoneda_map_yonedaEquiv {A U : BigFppfOver B S hS}
    (x : yoneda.obj A ⟶ (yoneda.obj U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :
    yoneda.map (yonedaEquiv x) = x := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_yoneda_map]

/-- The representability square of the represented morphism `φ`, read in the big fppf category
over `S`: the chosen representability witness of `yoneda.map g` exhibits a fibre product of a
chart with `T'` over `T` there, because `yoneda` is fully faithful. -/
theorem isPullback_representedChart (V : SmallEtale B S hS (yoneda.obj T)) :
    IsPullback (yonedaEquiv (hg.fst V.1.hom)) (hg.snd V.1.hom) g (yonedaEquiv V.1.hom) := by
  refine IsPullback.of_map_of_faithful yoneda ?_
  rw [yoneda_map_yonedaEquiv B S hS, yoneda_map_yonedaEquiv B S hS]
  exact hg.isPullback V.1.hom

/-- `AlgebraicGeometry.Space.isPullback_representedChart` read in the bounded category of
schemes, with the two projections exchanged so that the cospan is the one whose chosen fibre
product base change in the associated big étale site takes. -/
theorem isPullback_representedChart_schemes (V : SmallEtale B S hS (yoneda.obj T)) :
    IsPullback (hg.snd V.1.hom).left (yonedaEquiv (hg.fst V.1.hom)).left
      (yonedaEquiv V.1.hom).left g.left := by
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.forget B S hS) := inferInstance
  exact ((isPullback_representedChart B S hS g hg V).map (BigFppfOver.forget B S hS)).flip

/-- **The comparison of the two base changes at a single chart.** Both the chart base change
along the represented morphism and the base change of the underlying scheme chart are fibre
products of the same cospan in the bounded category of schemes, so they are canonically
isomorphic over `T'`. -/
noncomputable def representedSmallEtaleBaseChangeComponent
    (V : SmallEtale B S hS (yoneda.obj T)) :
    (smallBaseChange B S hS (representedSpaceMap B S hS g) hg ⋙
        (representedSmallEtaleEquivalence B S hS T').functor).obj V ≅
      ((representedSmallEtaleEquivalence B S hS T).functor ⋙
        _root_.AlgebraicGeometry.smallEtaleBaseChange (associatedBigEtaleSite B) g.left).obj V :=
  ObjectProperty.isoMk _ (Over.isoMk
    ((isPullback_representedChart_schemes B S hS g hg V).isoIsPullback _ _
      (IsPullback.of_hasPullback (yonedaEquiv V.1.hom).left g.left))
    ((isPullback_representedChart_schemes B S hS g hg V).isoIsPullback_hom_snd _ _ _))

/-- The comparison at a chart, read on underlying morphisms of the bounded category of
schemes. -/
theorem representedSmallEtaleBaseChangeComponent_hom
    (V : SmallEtale B S hS (yoneda.obj T)) :
    (representedSmallEtaleBaseChangeComponent B S hS g hg V).hom.hom.left =
      ((isPullback_representedChart_schemes B S hS g hg V).isoIsPullback _ _
        (IsPullback.of_hasPullback (yonedaEquiv V.1.hom).left g.left)).hom := rfl

/-- Chart base change of a morphism of charts, read in the big fppf category over `S`: it is
the morphism supplied by the universal property of the chosen representability witness. -/
noncomputable abbrev representedChartHom
    {V W : SmallEtale B S hS (yoneda.obj T)} (k : V ⟶ W) :
    hg.pullback V.1.hom ⟶ hg.pullback W.1.hom :=
  hg.lift (hg.fst V.1.hom) (hg.snd V.1.hom ≫ k.hom.left)
    (representablePullback_lift_cond B S hS (representedSpaceMap B S hS g) hg k)

/-- Chart base change along the represented morphism, followed by the identification of the
small étale site of a representable algebraic space, acts on underlying morphisms of the
bounded category of schemes by `AlgebraicGeometry.Space.representedChartHom`. -/
theorem representedSmallEtaleBaseChange_lhs_map
    {V W : SmallEtale B S hS (yoneda.obj T)} (k : V ⟶ W) :
    ((smallBaseChange B S hS (representedSpaceMap B S hS g) hg ⋙
        (representedSmallEtaleEquivalence B S hS T').functor).map k).hom.left =
      (representedChartHom B S hS g hg k).left := rfl

/-- A morphism of étale charts of a representable algebraic space is a morphism over `T` on
the underlying objects of the bounded category of schemes. -/
theorem representedChart_w {V W : SmallEtale B S hS (yoneda.obj T)} (k : V ⟶ W) :
    k.hom.left.left ≫ (yonedaEquiv W.1.hom).left = (yonedaEquiv V.1.hom).left := by
  have h : k.hom.left ≫ yonedaEquiv W.1.hom = yonedaEquiv V.1.hom := yoneda.map_injective <| by
    rw [Functor.map_comp, yoneda_map_yonedaEquiv B S hS, yoneda_map_yonedaEquiv B S hS]
    exact CostructuredArrow.w k.hom
  exact congrArg (fun z : V.1.left ⟶ T => z.left) h

/-- Base change along `g` in the associated big étale site, read on the chosen fibre products
of the bounded category of schemes: it is the canonical morphism of those fibre products. -/
noncomputable abbrev representedPullbackMap
    {V W : SmallEtale B S hS (yoneda.obj T)} (k : V ⟶ W) :
    pullback (yonedaEquiv V.1.hom).left g.left ⟶
      pullback (yonedaEquiv W.1.hom).left g.left :=
  pullback.lift (pullback.fst (yonedaEquiv V.1.hom).left g.left ≫ k.hom.left.left)
    (pullback.snd (yonedaEquiv V.1.hom).left g.left)
    ((Category.assoc _ _ _).trans
      ((congrArg (fun z => pullback.fst (yonedaEquiv V.1.hom).left g.left ≫ z)
        (representedChart_w B S hS k)).trans pullback.condition))

/-- The identification of the small étale site of a representable algebraic space, followed by
base change in the associated big étale site, acts on underlying morphisms of the bounded
category of schemes by `AlgebraicGeometry.Space.representedPullbackMap`. -/
theorem representedSmallEtaleBaseChange_rhs_map
    {V W : SmallEtale B S hS (yoneda.obj T)} (k : V ⟶ W) :
    (((representedSmallEtaleEquivalence B S hS T).functor ⋙
          _root_.AlgebraicGeometry.smallEtaleBaseChange
            (associatedBigEtaleSite B) g.left).map k).hom.left =
      representedPullbackMap B S hS g k := rfl

/-- Chart base change is compatible with the cartesian projections to the original charts. -/
theorem representedChartHom_comp_snd
    {V W : SmallEtale B S hS (yoneda.obj T)} (k : V ⟶ W) :
    (representedChartHom B S hS g hg k).left ≫ (hg.snd W.1.hom).left =
      (hg.snd V.1.hom).left ≫ k.hom.left.left :=
  congrArg (fun z : hg.pullback V.1.hom ⟶ W.1.left => z.left)
    (smallBaseChange_map_snd B S hS (representedSpaceMap B S hS g) hg k)

/-- Chart base change is compatible with the cartesian projections to `T'`. -/
theorem representedChartHom_comp_fst
    {V W : SmallEtale B S hS (yoneda.obj T)} (k : V ⟶ W) :
    (representedChartHom B S hS g hg k).left ≫ (yonedaEquiv (hg.fst W.1.hom)).left =
      (yonedaEquiv (hg.fst V.1.hom)).left := by
  have h : representedChartHom B S hS g hg k ≫ yonedaEquiv (hg.fst W.1.hom) =
      yonedaEquiv (hg.fst V.1.hom) := yoneda.map_injective <| by
    rw [Functor.map_comp, yoneda_map_yonedaEquiv B S hS, yoneda_map_yonedaEquiv B S hS]
    exact hg.lift_fst _ _ _
  exact congrArg (fun z : hg.pullback V.1.hom ⟶ T' => z.left) h

/-- The naturality square of the comparison, read on underlying morphisms of the bounded
category of schemes, where both sides are morphisms into a chosen fibre product. -/
theorem representedSmallEtaleBaseChange_naturality
    {V W : SmallEtale B S hS (yoneda.obj T)} (k : V ⟶ W) :
    (representedChartHom B S hS g hg k).left ≫
        ((isPullback_representedChart_schemes B S hS g hg W).isoIsPullback _ _
          (IsPullback.of_hasPullback (yonedaEquiv W.1.hom).left g.left)).hom =
      ((isPullback_representedChart_schemes B S hS g hg V).isoIsPullback _ _
          (IsPullback.of_hasPullback (yonedaEquiv V.1.hom).left g.left)).hom ≫
        representedPullbackMap B S hS g k := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, IsPullback.isoIsPullback_hom_fst, representedChartHom_comp_snd,
      Category.assoc, representedPullbackMap, pullback.lift_fst, ← Category.assoc,
      IsPullback.isoIsPullback_hom_fst]
  · rw [Category.assoc, IsPullback.isoIsPullback_hom_snd, representedChartHom_comp_fst,
      Category.assoc, representedPullbackMap, pullback.lift_snd,
      IsPullback.isoIsPullback_hom_snd]

/-- **Chart base change of a representable algebraic space is base change of schemes.** For a
morphism `g : T' ⟶ T` of the big fppf category over `S`, base change of étale scheme charts
along the represented morphism of algebraic spaces, followed by the identification of the small
étale site of `yoneda.obj T'` with the small étale site of the scheme `T'`, is that
identification for `T` followed by base change along `g` in the associated big étale site.

At a chart both composites are fibre products of the same cospan in the bounded category of
schemes — on the left the one chosen by the representability witness `hg`, on the right the
chosen fibre product — which is
`AlgebraicGeometry.Space.representedSmallEtaleBaseChangeComponent`, and naturality is checked
on the two projections of the chosen fibre product. -/
noncomputable def representedSmallEtaleBaseChangeIso :
    smallBaseChange B S hS (representedSpaceMap B S hS g) hg ⋙
        (representedSmallEtaleEquivalence B S hS T').functor ≅
      (representedSmallEtaleEquivalence B S hS T).functor ⋙
        _root_.AlgebraicGeometry.smallEtaleBaseChange (associatedBigEtaleSite B) g.left :=
  NatIso.ofComponents (representedSmallEtaleBaseChangeComponent B S hS g hg) fun k =>
    ObjectProperty.hom_ext _
      (Over.OverMorphism.ext (representedSmallEtaleBaseChange_naturality B S hS g hg k))

end RepresentedBaseChange

end AlgebraicGeometry.Space

end

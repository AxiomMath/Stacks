module

public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.Permanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartSlicingFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationBaseChangeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfSiteFunctor
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenImageSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackOfPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackUnion
public import StacksFrontier.AlgebraicGeometry.Stacks.PresentationStabilizerFlat
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategoryTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismCancellation
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningFlatDeformation
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# The smooth locus of a 1-morphism of algebraic stacks (Stacks 0DZR)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`. **Stacks 0DZR** asserts that there
is a largest open substack `𝒰 ⊆ 𝒳` such that the restriction of `f` to `𝒰` is smooth, and that
forming `𝒰` commutes with precomposition by smooth morphisms, with base change by morphisms flat
and locally of finite presentation, and — when `f` is locally of finite presentation — with base
change by flat morphisms. This file proves all of it.

## Main definitions

* `AlgebraicGeometry.Stack.IsSmoothLocus`: an open substack of `𝒳` is *the smooth locus* of `f`
  when `f` restricted to it is smooth and it contains every open substack with that property.
* `AlgebraicGeometry.Stack.openImage`: the open substack of `𝒳` whose points are the image of the
  points of a smooth 1-morphism into `𝒳`.

## Main results

* `AlgebraicGeometry.Stack.smoothLocus`: **Stacks 0DZR**, in full.
* `AlgebraicGeometry.Stack.exists_isSmoothLocus` and
  `AlgebraicGeometry.Stack.eq_of_isSmoothLocus`: the smooth locus exists and is unique.
* `AlgebraicGeometry.Stack.isSmoothLocus_comp_of_isSmooth`: clause (1).
* `AlgebraicGeometry.Stack.isSmoothLocus_baseChange_of_isFlat`: clauses (2) and (3).
* `AlgebraicGeometry.Stack.isSmooth_openImage_inclusion_comp`: smoothness descends to the open
  image of a smooth 1-morphism `c` along which `f` becomes smooth.
* `AlgebraicGeometry.Stack.range_pointsMap_subset_maximalSmoothOpen`: a smooth 1-morphism into an
  algebraic space along which a morphism of algebraic spaces becomes smooth lands in the smooth
  locus of that morphism (**Stacks 0DZI**).

## Implementation notes

The source's proof is followed. A smooth chart of `f` is a smooth surjection `V ⟶ 𝒴` from an
algebraic space, the 2-fibre product `Q = V ×_𝒴 𝒳`, a smooth surjection `U ⟶ Q` from an
algebraic space, and the induced morphism of algebraic spaces `h : U ⟶ V`
(`AlgebraicGeometry.Stack.exists_smoothChart`). The smooth locus of `f` is the open substack of
`𝒳` whose points are the image of the smooth locus `U'` of `h` (**Stacks 0DZI**): that image is
open because `U ⟶ 𝒳` is smooth, hence open on points (**Stacks 06R7**), and an open set of
points is the point set of an open substack by
`AlgebraicGeometry.Stack.openSubstackOfPoints` (**Stacks 06FJ**).

Three arguments do the work.

* *Descent to the open image* (`isSmooth_openImage_inclusion_comp`): if `c : 𝒜 ⟶ 𝒳` is smooth
  and `c ≫ f` is smooth, then `f` is smooth on the open image of `c`. A smooth chart of `𝒜`
  followed by `c` factors through the open image by a smooth surjection out of an algebraic
  space, along which smoothness cancels (**Stacks 0AHD** for stacks). This gives smoothness of
  `f` on the image of `U'` (where `U' ⟶ 𝒳 ⟶ 𝒴` is `U' ⟶ V ⟶ 𝒴`), clause (1) (with `c` the smooth
  locus of `g ≫ f` followed by `g`), and its smooth-base-change special case.
* *Maximality* (`mem_range_maximalSmoothOpenInclusion`): if `f` is smooth on an open substack
  `Z`, the inverse image of `Z` in the chart maps smoothly to the base change `V ×_𝒴 Z`, which is
  smooth over `V`; so `h` is smooth on that inverse image, which therefore lies in `U'`
  (`range_pointsMap_subset_maximalSmoothOpen`).
* *Flat base change* (`pointSet_subset_preimage_of_isSmoothLocus_baseChange`): for `g : 𝒴' ⟶ 𝒴`
  flat, a chart `V'' ⟶ V ×_𝒴 𝒴'` and the cartesian square of algebraic spaces
  `U'' = V'' ×_V U` give a chart of the base change `f'`: the 2-fibre products are identified by
  cancelling pastings (`isTwoFibreProduct_innerSq`, the converse direction of the pasting lemma
  of **Stacks 003Q**). A point of the smooth locus of `f'` lifts to the smooth locus of
  `U'' ⟶ V''`, which is the inverse image of `U'` by **Stacks 0DZI**, and maps into the smooth
  locus of `f`.

Containment of open substacks is containment of their object properties, and the commutation
clauses are stated as equalities of object properties: the smooth locus of the new 1-morphism
has exactly the objects carried into the smooth locus of `f`.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 06FJ](https://stacks.math.columbia.edu/tag/06FJ)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06R7](https://stacks.math.columbia.edu/tag/06R7)
* [Stacks Project, Tag 075U](https://stacks.math.columbia.edu/tag/075U)
* [Stacks Project, Tag 075V](https://stacks.math.columbia.edu/tag/075V)
* [Stacks Project, Tag 075W](https://stacks.math.columbia.edu/tag/075W)
* [Stacks Project, Tag 0AHD](https://stacks.math.columbia.edu/tag/0AHD)
* [Stacks Project, Tag 0DZI](https://stacks.math.columbia.edu/tag/0DZI)
* [Stacks Project, Tag 0DZR](https://stacks.math.columbia.edu/tag/0DZR)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An open substack `W` of `𝒳` is *the smooth locus* of a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic
stacks over `S` when the restriction of `f` to `W` is smooth and every open substack of `𝒳` with
that property is contained in `W`.

This is the conclusion of the first assertion of **Stacks 0DZR**: `W` is the `𝒰` of the source,
and the second clause is the force of the word *maximal* there. -/
def IsSmoothLocus {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (W : OpenSubstack 𝒳) :
    Prop :=
  AlgebraicStacks.IsSmooth B S hS
      (fullSubcategoryInclusion 𝒳 W.property W.isAlgebraic ≫ f) ∧
    ∀ V : OpenSubstack 𝒳,
      AlgebraicStacks.IsSmooth B S hS
          (fullSubcategoryInclusion 𝒳 V.property V.isAlgebraic ≫ f) →
        V.property ≤ W.property

/-- **Uniqueness of the smooth locus.** Two open substacks of `𝒳` on which `f` is smooth and
which are maximal with that property coincide: each is contained in the other, and an open
substack is determined by its object property. -/
theorem eq_of_isSmoothLocus {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴}
    {W W' : OpenSubstack 𝒳} (h : IsSmoothLocus B S hS f W) (h' : IsSmoothLocus B S hS f W') :
    W = W' :=
  OpenSubstack.ext (le_antisymm (h'.2 W h.1) (h.2 W' h'.1))

/-! ### Precomposition by a smooth 1-morphism -/

/-- **Smoothness of a 1-morphism of algebraic stacks over `S` depends only on its
2-isomorphism class.** Smoothness is the existential smooth-diagram test of **Stacks 06FM**,
whose diagram's 2-cell is reindexed by whiskering with the given 2-isomorphism. -/
theorem AlgebraicStacks.isSmooth_of_twoIso {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    {f g : 𝒳 ⟶ 𝒴} (e : f ≅ g) (hf : AlgebraicStacks.IsSmooth B S hS f) :
    AlgebraicStacks.IsSmooth B S hS g :=
  hasPropertyOnSomeSmoothDiagram_of_twoIso B S hS (fun _ _ h => Space.IsSmooth B S hS h)
    (Bicategory.InducedBicategory.isoHom e) hf

/-- **The inverse image of an open substack along a 1-morphism of algebraic stacks over `S`.**
For `g : 𝒳' ⟶ 𝒳` and an open substack `W` of `𝒳`, the objects of `𝒳'` carried by `g` into `W`
cut out an open substack of `𝒳'`, and smoothness of a 1-morphism out of `𝒳'` precomposed with
the projection of the 2-fibre product `𝒳' ×_𝒳 W` transfers to that open substack.

The open substack is the base change `𝒳' ×_𝒳 W ⟶ 𝒳'`, an open immersion by **Stacks 045C** and
**Stacks 0302**, read through its essential image by **Stacks 0506**; the transfer is along the
equivalence of **Stacks 0506** between the 2-fibre product and that essential image. -/
theorem exists_openSubstack_comap
    {𝒳' 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒳' ⟶ 𝒳) (W : OpenSubstack 𝒳) :
    ∃ W' : OpenSubstack 𝒳',
      (∀ x : 𝒳'.val.val.obj, W'.property x ↔ W.property (g.hom.hom.toFunctor.obj x)) ∧
      ∀ {𝒵 : AlgebraicStacks.{u, w} B S hS} (q : 𝒳' ⟶ 𝒵),
        AlgebraicStacks.IsSmooth B S hS
            ((twoFibreProductSquareAlgebraicStacks B S hS g
              (fullSubcategoryInclusion 𝒳 W.property W.isAlgebraic)).fst ≫ q) →
          AlgebraicStacks.IsSmooth B S hS
            (fullSubcategoryInclusion 𝒳' W'.property W'.isAlgebraic ≫ q) := by
  have := W.strictlyFull
  set j := fullSubcategoryInclusion 𝒳 W.property W.isAlgebraic
  set Qc := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom j.hom
  have hQc : Bicategory.IsTwoFibreProduct Qc :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      g.hom j.hom
  set Q := twoFibreProductSquareAlgebraicStacks B S hS g j
  have hQ : Bicategory.IsTwoFibreProduct Q :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g j
  have hrepr : IsRepresentableByAlgebraicSpaces B S hS Qc.fst.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS _ _ _ j.hom g.hom Qc hQc
      W.isOpenImmersion.1
  have hoi : Stack.IsOpenImmersion B S hS Qc.fst :=
    isOpenImmersion_baseChange.{u, u, u + 1} B S hS _ _ _ j.hom g.hom Qc hQc
      W.isOpenImmersion.2
  have himm : AlgebraicStacks.IsImmersion B S hS Q.fst :=
    ⟨hrepr, fun U y hy F hF he =>
      Space.isImmersion_of_isOpenImmersion B S hS (hoi U y hy F hF he)⟩
  have hPalg := AlgebraicStacks.isAlgebraicStack_essImage Q.fst himm
  refine ⟨⟨(CatFiberedInGroupoids.homFunctor Q.fst.hom).essImage, inferInstance, hPalg,
    AlgebraicStacks.isOpenImmersion_essImageInclusion Q.fst ⟨hrepr, hoi⟩ himm hPalg⟩,
    fun x => ?_, ?_⟩
  · constructor
    · rintro ⟨z, ⟨e⟩⟩
      exact W.property.prop_of_iso
        (z.iso.symm ≪≫ g.hom.hom.toFunctor.mapIso e) z.y.property
    · intro hxW
      exact ⟨{ base := 𝒳'.val.val.p.obj x
               x := x
               y := ⟨g.hom.hom.toFunctor.obj x, hxW⟩
               hx := rfl
               hy := g.hom.hom.w_obj x
               iso := Iso.refl _
               vertical := IsHomLift.id (g.hom.hom.w_obj x) }, ⟨Iso.refl _⟩⟩
  · obtain ⟨e, he, ⟨θ⟩⟩ := AlgebraicStacks.exists_isEquivalence_to_essImage Q.fst himm hPalg
    intro 𝒵 q hq
    exact hasPropertyOnSomeSmoothDiagram_of_isEquivalence B S hS
      (fun _ _ h => Space.IsSmooth B S hS h) _ _ e.hom he
      (Bicategory.InducedBicategory.isoHom
        (Bicategory.whiskerRightIso θ.symm q ≪≫
          Bicategory.associator e (fullSubcategoryInclusion 𝒳'
            (CatFiberedInGroupoids.homFunctor Q.fst.hom).essImage hPalg) q)) hq

/-- The projection to the source of a 2-fibre product is smooth when the other leg is. -/
private theorem isSmooth_snd_of_isTwoFibreProduct
    {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴} {g : 𝒴' ⟶ 𝒴}
    {P : Bicategory.TwoCommSq g f} (hP : Bicategory.IsTwoFibreProduct P)
    (hg : AlgebraicStacks.IsSmooth B S hS g) : AlgebraicStacks.IsSmooth B S hS P.snd :=
  AlgebraicStacks.isSmooth_baseChange B S hS g f P.swap (Bicategory.isTwoFibreProduct_swap hP) hg

/-- **The inverse image of an open substack along a smooth 1-morphism carries the composite
smoothly.** For `g : 𝒳' ⟶ 𝒳` smooth and `f : 𝒳 ⟶ 𝒴` smooth on an open substack `W` of `𝒳`, the
inverse image of `W` along `g` is an open substack of `𝒳'` on which `g ≫ f` is smooth.

The projection of `𝒳' ×_𝒳 W` to `W` is a base change of `g`, hence smooth by **Stacks 075W**, so
its composite with `f|_W` is smooth by **Stacks 075V**. -/
theorem exists_openSubstack_comap_isSmooth_comp
    {𝒳' 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (g : 𝒳' ⟶ 𝒳) (f : 𝒳 ⟶ 𝒴)
    (hg : AlgebraicStacks.IsSmooth B S hS g) (W : OpenSubstack 𝒳)
    (hW : AlgebraicStacks.IsSmooth B S hS
      (fullSubcategoryInclusion 𝒳 W.property W.isAlgebraic ≫ f)) :
    ∃ W' : OpenSubstack 𝒳',
      (∀ x : 𝒳'.val.val.obj, W'.property x ↔ W.property (g.hom.hom.toFunctor.obj x)) ∧
      AlgebraicStacks.IsSmooth B S hS
        (fullSubcategoryInclusion 𝒳' W'.property W'.isAlgebraic ≫ g ≫ f) := by
  set j := fullSubcategoryInclusion 𝒳 W.property W.isAlgebraic
  set Q := twoFibreProductSquareAlgebraicStacks B S hS g j
  have hQ : Bicategory.IsTwoFibreProduct Q :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g j
  obtain ⟨W', hprop, htransfer⟩ := exists_openSubstack_comap B S hS g W
  refine ⟨W', hprop, htransfer (g ≫ f) ?_⟩
  exact AlgebraicStacks.isSmooth_of_twoIso B S hS
    ((Bicategory.associator Q.fst g f).symm ≪≫
      Bicategory.whiskerRightIso Q.iso f ≪≫ Bicategory.associator Q.snd j f).symm
    (AlgebraicStacks.isSmooth_comp B S hS Q.snd (j ≫ f)
      (isSmooth_snd_of_isTwoFibreProduct B S hS hQ hg) hW)

/-- **Stacks 0DZR, clause (1), the inclusion `g^{-1}𝒰 ⊆ 𝒰'`.** Let `g : 𝒳' ⟶ 𝒳` be a smooth
1-morphism of algebraic stacks over `S`, let `f : 𝒳 ⟶ 𝒴`, let `W` be the smooth locus of `f` and
`W'` the smooth locus of `g ≫ f`. Then every object of `𝒳'` carried by `g` into `W` lies in `W'`.

The inverse image of `W` along `g` is an open substack on which `g ≫ f` is smooth. -/
theorem isSmoothLocus_comp_of_isSmooth_apply
    {𝒳' 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {g : 𝒳' ⟶ 𝒳} {f : 𝒳 ⟶ 𝒴}
    (hg : AlgebraicStacks.IsSmooth B S hS g) {W : OpenSubstack 𝒳} {W' : OpenSubstack 𝒳'}
    (hW : IsSmoothLocus B S hS f W) (hW' : IsSmoothLocus B S hS (g ≫ f) W')
    {x : 𝒳'.val.val.obj} (hx : W.property (g.hom.hom.toFunctor.obj x)) :
    W'.property x := by
  obtain ⟨V, hV, hVsm⟩ := exists_openSubstack_comap_isSmooth_comp B S hS g f hg W hW.1
  exact hW'.2 V hVsm x ((hV x).2 hx)

/-! ### Base change -/

/-- **Stacks 0DZR, clauses (2) and (3), the inclusion `g'^{-1}𝒰 ⊆ 𝒰'`.** Let `P` be a 2-fibre
product square over the cospan `(g, f)`, so that `P.fst` is the base change of `f : 𝒳 ⟶ 𝒴` along
`g : 𝒴' ⟶ 𝒴` and `P.snd` is the projection to `𝒳`. Let `W` be the smooth locus of `f` and `W'`
the smooth locus of `P.fst`. Then every object of the apex carried by `P.snd` into `W` lies in
`W'`.

This is the inclusion the source's clauses (2) and (3) share, and it holds for an **arbitrary**
base change: neither flatness of `g` nor local finite presentation of `f` or `g` is used. The
inverse image of `W` along `P.snd` is the 2-fibre product `𝒳' ×_𝒳 W`, which by pasting
(**Stacks 003Q**) is also `W ×_𝒴 𝒴'`, so its projection to `𝒴'` is a base change of the smooth
`f|_W` and is smooth by **Stacks 075W**; maximality of `W'` finishes. It is the stack-level form
of `AlgebraicGeometry.Space.preimage_maximalSmoothOpen_le`, which is the same inclusion one level
down and equally free of hypotheses. The reverse inclusion is
`AlgebraicGeometry.Stack.isSmoothLocus_baseChange_apply_of_isFlat`. -/
theorem isSmoothLocus_baseChange_apply
    {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴} {g : 𝒴' ⟶ 𝒴}
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    {W : OpenSubstack 𝒳} {W' : OpenSubstack P.pt}
    (hW : IsSmoothLocus B S hS f W) (hW' : IsSmoothLocus B S hS P.fst W')
    {x : P.pt.val.val.obj} (hx : W.property (P.snd.hom.hom.toFunctor.obj x)) :
    W'.property x := by
  set j := fullSubcategoryInclusion 𝒳 W.property W.isAlgebraic
  set R := twoFibreProductSquareAlgebraicStacks B S hS P.snd j
  have hR : Bicategory.IsTwoFibreProduct R :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS P.snd j
  obtain ⟨V, hprop, htransfer⟩ := exists_openSubstack_comap B S hS P.snd W
  refine hW'.2 V (htransfer P.fst ?_) x ((hprop x).2 hx)
  exact AlgebraicStacks.isSmooth_baseChange B S hS (j ≫ f) g (P.pasteSnd R)
    (Bicategory.isTwoFibreProduct_pasteSnd P hP R hR) hW.1

/-- **An open immersion of algebraic stacks is smooth.** -/
theorem AlgebraicStacks.isSmooth_of_isOpenImmersion {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (hf : AlgebraicStacks.IsOpenImmersion B S hS f) :
    AlgebraicStacks.IsSmooth B S hS f :=
  hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS
    (fun _ _ h => Space.IsSmooth B S hS h) 𝒴.property f.hom hf.1
    (fun U _ _ _ _ he => Space.isSmooth_of_isEtale B S hS (isAlgebraicSpace_yoneda B S hS U)
      (Space.isEtale_of_isOpenImmersion B S hS (hf.2 _ _ ‹_› _ _ he)))

/-- The factorization of a 1-morphism of algebraic stacks through an open substack containing the
image of every object. Composing it with the inclusion of the open substack returns the
1-morphism definitionally. -/
noncomputable def OpenSubstack.factor {𝒱 𝒳 : AlgebraicStacks.{u, w} B S hS} (W : OpenSubstack 𝒳)
    (g : 𝒱 ⟶ 𝒳) (hg : ∀ x, W.property (g.hom.hom.toFunctor.obj x)) :
    𝒱 ⟶ W.toAlgebraicStack :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    { toFunctor := W.property.lift (CatFiberedInGroupoids.homFunctor g.hom) hg
      w := g.hom.hom.w })

/-- The factorization through an open substack composed with its inclusion is the original
1-morphism. -/
theorem OpenSubstack.factor_comp_inclusion {𝒱 𝒳 : AlgebraicStacks.{u, w} B S hS}
    (W : OpenSubstack 𝒳) (g : 𝒱 ⟶ 𝒳) (hg : ∀ x, W.property (g.hom.hom.toFunctor.obj x)) :
    W.factor B S hS g hg ≫ W.inclusion = g := rfl

/-- **The points seen by an object of an open substack lie in it.** -/
theorem OpenSubstack.pointsWithin_pointSet {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (W : OpenSubstack 𝒳) {x : 𝒳.val.val.obj} (hx : W.property x) :
    pointsWithin 𝒳 (W.pointSet B S hS) x :=
  (pointsWithin_obj_iff 𝒳 W.inclusion.hom.hom (W.pointSet B S hS)
    (⟨x, hx⟩ : W.property.FullSubcategory)).2 fun r _ => ⟨pointClass B S hS _ _ r, rfl⟩


/-- **A 1-morphism into an open substack from an algebraic space is smooth as soon as its composite
with the inclusion is.** Smoothness of morphisms of algebraic spaces cancels against open
immersions (`AlgebraicGeometry.Space.isSmooth_of_comp_isEtale`), so the condition of Stacks 04XB
for smoothness cancels by `AlgebraicGeometry.Stack.prop_of_comp_of_spaceCancel`, and
**Stacks 06FM** reads it back as the smooth-diagram criterion of **Stacks 075U**. -/
theorem OpenSubstack.isSmooth_of_isSmooth_comp_inclusion {𝒱 𝒳 : AlgebraicStacks.{u, w} B S hS}
    (W : OpenSubstack 𝒳) (q : 𝒱 ⟶ W.toAlgebraicStack)
    (h𝒱 : IsRepresentableByAlgebraicSpace B S hS 𝒱.val)
    (hq : AlgebraicStacks.IsSmooth B S hS (q ≫ W.inclusion)) :
    AlgebraicStacks.IsSmooth B S hS q := by
  -- pin the universe of the fpqc locality of open immersions (Stacks 041X), which instance
  -- search would otherwise leave free
  have := Space.openImmersion_isLocalAtTarget_fpqc.{u, u} B S hS
  have hgrep : IsRepresentableByAlgebraicSpaces B S hS (q ≫ W.inclusion).hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒳.property h𝒱
      (q ≫ W.inclusion).hom
  have hqrep : IsRepresentableByAlgebraicSpaces B S hS q.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS
      W.toAlgebraicStack.property h𝒱 q.hom
  have hgrel : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.smoothMorphismProperty B S hS) (q ≫ W.inclusion).hom hgrep :=
    (hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS
      (fun _ _ h => Space.IsSmooth B S hS h)
      (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS)
      𝒱.property 𝒳.property (q ≫ W.inclusion).hom hgrep).1 hq
  have hqrel : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.smoothMorphismProperty B S hS) q.hom hqrep := by
    refine prop_of_comp_of_spaceCancel B S hS (Space.smoothMorphismProperty B S hS)
      (Space.openImmersionProperty B S hS) ?_ q.hom W.inclusion.hom
      W.isOpenImmersion.1 hgrep ?_ W.isOpenImmersion.2
    · intro X' Y' Z' a b hab hb
      exact Space.isSmooth_of_comp_isEtale B S hS a.hom b.hom
        (Space.isEtale_of_isOpenImmersion B S hS hb) hab
    · exact hgrel
  exact hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS
    (fun _ _ h => Space.IsSmooth B S hS h) W.toAlgebraicStack.property q.hom hqrep hqrel

/-- **The factorization through an open substack is surjective when the open substack has no
point outside the image.** The inclusion of an open substack is injective on points by
**Stacks 0500**. -/
theorem OpenSubstack.isSurjective_factor {𝒱 𝒳 : AlgebraicStacks.{u, w} B S hS}
    (W : OpenSubstack 𝒳) (g : 𝒱 ⟶ 𝒳) (hg : ∀ x, W.property (g.hom.hom.toFunctor.obj x))
    (hW : W.pointSet B S hS ⊆ Set.range (AlgebraicStacks.pointsMap B S hS g)) :
    IsSurjective B S hS (W.factor B S hS g hg) := by
  intro y
  obtain ⟨v, hv⟩ := hW ⟨y, rfl⟩
  refine ⟨v, pointsMap_injective_of_fullyFaithful B S hS W.inclusion ?_⟩
  have hgc : AlgebraicStacks.pointsMap B S hS g =
      AlgebraicStacks.pointsMap B S hS W.inclusion ∘
        AlgebraicStacks.pointsMap B S hS (W.factor B S hS g hg) := by
    rw [← AlgebraicStacks.pointsMap_comp B S hS (W.factor B S hS g hg) W.inclusion,
      W.factor_comp_inclusion B S hS g hg]
  rw [hgc] at hv
  exact hv

/-- The open substack of `𝒳` whose points are the image of the points of a smooth
1-morphism `c : 𝒜 ⟶ 𝒳`. -/
noncomputable abbrev openImage {𝒜 𝒳 : AlgebraicStacks.{u, w} B S hS} (c : 𝒜 ⟶ 𝒳)
    (hc : AlgebraicStacks.IsSmooth B S hS c) : OpenSubstack 𝒳 :=
  openSubstackOfPoints 𝒳 _ (isOpen_range_pointsMap_of_isSmooth B S hS c hc)

/-- The image of every object under a smooth 1-morphism lies in its open image. -/
theorem property_openImage_obj {𝒜 𝒳 : AlgebraicStacks.{u, w} B S hS} (c : 𝒜 ⟶ 𝒳)
    (hc : AlgebraicStacks.IsSmooth B S hS c) (x : 𝒜.val.val.obj) :
    (openImage B S hS c hc).property (c.hom.hom.toFunctor.obj x) := by
  rw [openSubstackOfPoints_property]
  exact (pointsWithin_obj_iff 𝒳 c.hom.hom _ x).2 fun r _ => ⟨pointClass B S hS _ _ r, rfl⟩

/-- A smooth surjective chart of an algebraic stack by an algebraic space. -/
private theorem exists_isSmooth_isSurjective_chart_aux (𝒲 : AlgebraicStacks.{u, w} B S hS) :
    ∃ (G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hG : IsAlgebraicSpace B S hS G)
      (γ : algebraicSpaceStack.{u, w} B S hS G hG ⟶ 𝒲),
      AlgebraicStacks.IsSmooth B S hS γ ∧ IsSurjective B S hS γ := by
  obtain ⟨G, hG, b, hbsm, hbsu⟩ :=
    exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation.{u, w} B S hS 𝒲.property
  refine ⟨G, hG, Bicategory.InducedBicategory.mkHom b, ?_, ?_⟩
  · exact hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS
      (fun _ _ h => Space.IsSmooth B S hS h) 𝒲.property b hbsm.1 hbsm.2
  · exact pointsMap_surjective_of_isSurjectiveOnObjects B S hS
      (Bicategory.InducedBicategory.mkHom b :
        algebraicSpaceStack.{u, w} B S hS G hG ⟶ 𝒲) hbsu

/-- **Smoothness descends to the open image of a smooth 1-morphism.** Let `c : 𝒜 ⟶ 𝒳` be a smooth
1-morphism of algebraic stacks over `S` and `f : 𝒳 ⟶ 𝒴` a 1-morphism such that `c ≫ f` is
smooth. Then `f` restricted to the open image of `c` is smooth.

A smooth chart `𝒱 ⟶ 𝒜` by an algebraic space, followed by `c`, factors through the open image by
a 1-morphism which is smooth (it is so after the inclusion) and surjective (the open image has no
point outside the image of `c`); its composite with `f` restricted to the open image is the
smooth composite `𝒱 ⟶ 𝒜 ⟶ 𝒳 ⟶ 𝒴`, so the cancellation of smoothness along a smooth surjection
out of an algebraic space applies. -/
theorem isSmooth_openImage_inclusion_comp {𝒜 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (c : 𝒜 ⟶ 𝒳) (f : 𝒳 ⟶ 𝒴) (hc : AlgebraicStacks.IsSmooth B S hS c)
    (hcf : AlgebraicStacks.IsSmooth B S hS (c ≫ f)) :
    AlgebraicStacks.IsSmooth B S hS ((openImage B S hS c hc).inclusion ≫ f) := by
  obtain ⟨V, hV, bb, hbb, hbbsu⟩ := exists_isSmooth_isSurjective_chart_aux B S hS 𝒜
  have h𝒱 : IsRepresentableByAlgebraicSpace B S hS
      (algebraicSpaceStack.{u, w} B S hS V hV).val :=
    isRepresentableByAlgebraicSpace_fibredCategory B S hS V hV
  set T := openImage B S hS c hc with hTdef
  have hd : ∀ x, T.property ((bb ≫ c).hom.hom.toFunctor.obj x) := fun x =>
    property_openImage_obj B S hS c hc _
  set w := T.factor B S hS (bb ≫ c) hd
  have hwsm : AlgebraicStacks.IsSmooth B S hS w :=
    T.isSmooth_of_isSmooth_comp_inclusion B S hS w h𝒱
      (AlgebraicStacks.isSmooth_comp B S hS bb c hbb hc)
  have hwsu : IsSurjective B S hS w := by
    refine T.isSurjective_factor B S hS (bb ≫ c) hd ?_
    rw [hTdef, pointSet_openSubstackOfPoints, AlgebraicStacks.pointsMap_comp,
      Set.range_comp, hbbsu.range_eq, Set.image_univ]
  have hwrep : IsRepresentableByAlgebraicSpaces B S hS w.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS
      T.toAlgebraicStack.property h𝒱 w.hom
  refine AlgebraicStacks.isSmooth_of_comp_surjective B S hS w (T.inclusion ≫ f) hwrep hwsm
    hwsu ?_
  refine AlgebraicStacks.isSmooth_of_twoIso B S hS ?_
    (AlgebraicStacks.isSmooth_comp B S hS bb (c ≫ f) hbb hcf)
  exact (Bicategory.associator bb c f).symm ≪≫ (Bicategory.associator w T.inclusion f)

/-- **The pasting lemma, converse direction (Stacks 003Q).** Let `Q` be a 2-fibre product of a
cospan of algebraic stacks and `T` a 2-commutative square over the cospan formed by the second
leg of `Q` and a 1-morphism `k`. If the rectangle `Q.paste T` is a 2-fibre product, so is `T`.

The canonical 2-fibre product `C` of the inner cospan receives a comparison from `T`; pasted
with `Q` it becomes a comparison between two 2-fibre products of the outer cospan, hence an
equivalence (**Stacks 003Z**), and a square receiving an equivalence into a 2-fibre product is a
2-fibre product. -/
noncomputable def isTwoFibreProduct_of_isTwoFibreProduct_paste
    {𝒳 𝒴 𝒵 𝒯 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒵} {g : 𝒴 ⟶ 𝒵} {k : 𝒯 ⟶ 𝒴}
    {Q : Bicategory.TwoCommSq f g} (hQ : Bicategory.IsTwoFibreProduct Q)
    (T : Bicategory.TwoCommSq Q.snd k) (hQT : Bicategory.IsTwoFibreProduct (Q.paste T)) :
    Bicategory.IsTwoFibreProduct T := by
  let C := twoFibreProductSquareAlgebraicStacks B S hS Q.snd k
  have hC : Bicategory.IsTwoFibreProduct C :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS Q.snd k
  let ρ : Bicategory.TwoCommSq.PreHom T C := Quotient.out (hC.from T)
  have hρ : ρ.hom.hom.hom.toFunctor.IsEquivalence :=
    isEquivalence_of_isTwoFibreProductAlgebraicStacks B S hS hQT
      (Bicategory.isTwoFibreProduct_paste hQ hC) (ρ.paste Q)
  exact Bicategory.isTwoFibreProduct_of_underlying
    (Bicategory.isTwoFibreProduct_of_isEquivalence_to
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        Q.snd.hom k.hom) ρ.underlying hρ)

/-- Two 2-isomorphic 1-morphisms of algebraic stacks induce the same map on points. -/
theorem AlgebraicStacks.pointsMap_eq_of_iso {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    {f g : 𝒳 ⟶ 𝒴} (e : f ≅ g) :
    AlgebraicStacks.pointsMap B S hS f = AlgebraicStacks.pointsMap B S hS g :=
  pointsMap_eq_of_basedNatTrans B S hS _ _ _ e.hom.hom.hom

/-- A 2-isomorphism between composites of 1-morphisms gives equal composites on points. -/
private theorem pointsMap_comp_eq_of_iso {𝒜 ℬ 𝒞 𝒟 : AlgebraicStacks.{u, w} B S hS}
    {a : 𝒜 ⟶ ℬ} {b : ℬ ⟶ 𝒟} {c : 𝒜 ⟶ 𝒞} {d : 𝒞 ⟶ 𝒟} (e : a ≫ b ≅ c ≫ d) :
    AlgebraicStacks.pointsMap B S hS b ∘ AlgebraicStacks.pointsMap B S hS a =
      AlgebraicStacks.pointsMap B S hS d ∘ AlgebraicStacks.pointsMap B S hS c :=
  (AlgebraicStacks.pointsMap_comp B S hS a b).symm.trans
    ((AlgebraicStacks.pointsMap_eq_of_iso B S hS e).trans
      (AlgebraicStacks.pointsMap_comp B S hS c d))

/-- **The 1-morphism attached to a morphism of presheaves acts on points as that morphism.** The
canonical identification of the points of a presheaf with the points of its category of elements
intertwines the map on points of a morphism of presheaves with that of the attached
1-morphism. -/
theorem spacePointMap_pointsMap_associatedMap {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (φ : F ⟶ G) (x : Space.points B S hS F) :
    spacePointMap B S hS G (fibredCategory B S hS G) (BasedFunctor.id _)
        (Space.pointsMap B S hS F φ x) =
      pointsMap B S hS _ (fibredCategory B S hS F).property (fibredCategory B S hS G).property
        (associatedMap B S hS φ).1.hom
        (spacePointMap B S hS F (fibredCategory B S hS F) (BasedFunctor.id _) x) := by
  induction x using Quot.inductionOn with
  | h p =>
    show spacePointMap B S hS G _ _ ((Space.FieldValuedPoint.map B S hS F φ p).class B S hS G) =
      pointsMap B S hS _ _ _ _ (spacePointMap B S hS F _ _ (p.class B S hS F))
    rw [spacePointMap_class, spacePointMap_class, pointsMap_class]
    have hobj : (associatedMap B S hS φ).1.hom.obj (spaceFieldValuedPoint B S hS F p).obj =
        (spaceFieldValuedPoint B S hS G (Space.FieldValuedPoint.map B S hS F φ p)).obj :=
      associatedMap_obj B S hS φ _
    exact (class_eq_class_iff_hasCommonExtension B S hS _ _ _ _).2
      ⟨_, ⟨𝟙 _⟩, ⟨eqToHom hobj.symm⟩⟩

/-- **A smooth surjective chart of an algebraic stack by an algebraic space.** -/
theorem exists_isSmooth_isSurjective_chart (𝒲 : AlgebraicStacks.{u, w} B S hS) :
    ∃ (G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hG : IsAlgebraicSpace B S hS G)
      (γ : algebraicSpaceStack.{u, w} B S hS G hG ⟶ 𝒲),
      AlgebraicStacks.IsSmooth B S hS γ ∧ IsSurjective B S hS γ :=
  exists_isSmooth_isSurjective_chart_aux B S hS 𝒲

/-- **A smooth 1-morphism into the algebraic stack of an algebraic space along which a morphism of
algebraic spaces becomes smooth lands in its smooth locus.** Let `h : U ⟶ V` be a morphism of
algebraic spaces over `S` and let `ψ : 𝒲 ⟶ U` be a smooth 1-morphism of algebraic stacks such
that `ψ ≫ h` is smooth. Then every point of `|U|` in the image of `ψ` lies in the smooth locus
of `h` (**Stacks 0DZI**).

A smooth surjective chart `G ⟶ 𝒲` composed with `ψ` is a smooth morphism of algebraic spaces
`φ : G ⟶ U` with `φ ≫ h` smooth. Its image is an open subspace of `U`, through which `φ`
factors by a smooth surjection; smoothness of `h` on that open subspace follows by cancellation
along that surjection (**Stacks 0AHD**), so the open subspace lies in the smooth locus. -/
theorem range_pointsMap_subset_maximalSmoothOpen {U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B S hS U) (hV : IsAlgebraicSpace B S hS V) (h : U ⟶ V)
    {𝒲 : AlgebraicStacks.{u, w} B S hS} (ψ : 𝒲 ⟶ algebraicSpaceStack.{u, w} B S hS U hU)
    (hψ : AlgebraicStacks.IsSmooth B S hS ψ)
    (hψh : AlgebraicStacks.IsSmooth B S hS (ψ ≫ algebraicSpaceStackMap.{u, w} B S hS hU hV h)) :
    Set.range (AlgebraicStacks.pointsMap B S hS ψ) ⊆
      Set.range (AlgebraicStacks.pointsMap B S hS (algebraicSpaceStackMap.{u, w} B S hS
        (Space.isOpenSubspace_maximalSmoothOpen B S hS hU hV h).1 hU
        (Space.maximalSmoothOpen B S hS h).ι)) := by
  set N := Space.maximalSmoothOpen B S hS h
  obtain ⟨G, hG, γ, hγsm, hγsu⟩ := exists_isSmooth_isSurjective_chart B S hS 𝒲
  set φ := representingMap B S hS (fibredCategory B S hS G) (fibredCategory B S hS U) G U
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) (γ ≫ ψ).hom
  obtain ⟨eφ⟩ := nonempty_twoIso_associatedMap_representingMap B S hS G U (γ ≫ ψ).hom
  let eφ' : algebraicSpaceStackMap.{u, w} B S hS hG hU φ ≅ γ ≫ ψ :=
    Bicategory.InducedBicategory.isoMk eφ
  have hφ : Space.IsSmooth B S hS φ :=
    (isSmooth_algebraicSpaceStackMap_iff.{u, w} B S hS hG hU φ).1
      (AlgebraicStacks.isSmooth_of_twoIso B S hS eφ'.symm
        (AlgebraicStacks.isSmooth_comp B S hS γ ψ hγsm hψ))
  have hφh : Space.IsSmooth B S hS (φ ≫ h) := by
    refine (isSmooth_algebraicSpaceStackMap_iff.{u, w} B S hS hG hV (φ ≫ h)).1 ?_
    have heq : algebraicSpaceStackMap.{u, w} B S hS hG hV (φ ≫ h) =
        algebraicSpaceStackMap.{u, w} B S hS hG hU φ ≫
          algebraicSpaceStackMap.{u, w} B S hS hU hV h :=
      congrArg Bicategory.InducedBicategory.mkHom (associatedMap_comp B S hS φ h)
    rw [heq]
    exact AlgebraicStacks.isSmooth_of_twoIso B S hS
      ((Bicategory.associator γ ψ _).symm ≪≫ Bicategory.whiskerRightIso eφ'.symm _)
      (AlgebraicStacks.isSmooth_comp B S hS γ _ hγsm hψh)
  let := Space.pointTopology B S hS U
  let := Space.pointTopology B S hS G
  have hopen : IsOpen (Set.range (Space.pointsMap B S hS G φ)) :=
    (Space.isOpenMap_pointsMap_of_isFlat_of_isLocallyOfFinitePresentation B S hS hG hU φ
      (Space.isFlat_of_isSmooth B S hS φ hφ)
      (Space.isLocallyOfFinitePresentation_of_isSmooth B S hS hφ)).isOpen_range
  set Im := Space.openSubspaceOfPoints B S hS U (Set.range (Space.pointsMap B S hS G φ))
  have hIm := Space.isOpenSubspace_openSubspaceOfPoints B S hS hU _ hopen
  have hImrange := Space.range_pointsMap_ι_openSubspaceOfPoints B S hS (F := U)
    (Set.range (Space.pointsMap B S hS G φ))
  obtain ⟨t, ht⟩ := (Space.factorsThrough_openSubspace_iff_points B S hS hU hG Im hIm φ).2
    (by rw [hImrange])
  have htsm : Space.IsSmooth B S hS t :=
    Space.isSmooth_of_comp_isEtale B S hS t Im.ι
      (Space.isEtale_of_isOpenImmersion B S hS hIm.2) (by rwa [ht])
  have htsu : Space.IsSurjective B S hS t := by
    intro y
    obtain ⟨g, hg⟩ : Space.pointsMap B S hS Im.toFunctor Im.ι y ∈
        Set.range (Space.pointsMap B S hS G φ) := by
      rw [← hImrange]
      exact ⟨y, rfl⟩
    refine ⟨g, ?_⟩
    have : Mono Im.ι := Space.mono_of_presheaf_isOpenImmersion hIm.2
    refine Space.pointsMap_injective_of_mono B S hS Im.ι ?_
    rw [← Space.pointsMap_comp_apply, ht, hg]
  have hImsm : Space.IsSmooth B S hS (Im.ι ≫ h) :=
    Space.isSmooth_of_comp_surjective_isSmooth B S hS hG hIm.1 hV t (φ ≫ h) (Im.ι ≫ h)
      (by rw [← Category.assoc, ht]) htsu htsm hφh
  have hle : Im ≤ N := Space.le_maximalSmoothOpen B S hS h hIm hImsm
  rintro _ ⟨w, rfl⟩
  obtain ⟨g', rfl⟩ := hγsu w
  obtain ⟨gs, rfl⟩ := (spacePointMap_id_bijective B S hS G).2 g'
  have hgs : Space.pointsMap B S hS G φ gs ∈
      Set.range (Space.pointsMap B S hS Im.toFunctor Im.ι) := by
    rw [hImrange]
    exact ⟨gs, rfl⟩
  obtain ⟨i, hi⟩ := hgs
  refine ⟨spacePointMap B S hS N.toFunctor (fibredCategory B S hS N.toFunctor)
    (BasedFunctor.id _) (Space.pointsMap B S hS Im.toFunctor (Subfunctor.homOfLe hle) i), ?_⟩
  show pointsMap B S hS _ _ _ (associatedMap B S hS N.ι).1.hom _ =
    AlgebraicStacks.pointsMap B S hS ψ (AlgebraicStacks.pointsMap B S hS γ _)
  rw [← spacePointMap_pointsMap_associatedMap, ← Space.pointsMap_comp_apply,
    Subfunctor.homOfLe_ι, hi, spacePointMap_pointsMap_associatedMap,
    ← Function.comp_apply (f := AlgebraicStacks.pointsMap B S hS ψ),
    ← AlgebraicStacks.pointsMap_comp, ← AlgebraicStacks.pointsMap_eq_of_iso B S hS eφ']

/-- **A 1-morphism of algebraic stacks whose underlying functor is an equivalence is smooth.** A
smooth chart of the source composed with it is a smooth chart of the target, over which the
identity of the chart's algebraic space witnesses the existential test of **Stacks 06FM**. -/
theorem AlgebraicStacks.isSmooth_of_isEquivalence {𝒦 𝒲 : AlgebraicStacks.{u, w} B S hS}
    (e : 𝒦 ⟶ 𝒲) (he : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor e.hom)) :
    AlgebraicStacks.IsSmooth B S hS e := by
  obtain ⟨G, hG, a, hasm, hasu⟩ :=
    exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation.{u, w} B S hS 𝒦.property
  obtain ⟨ι⟩ := nonempty_twoIso_associatedMap_id B S hS G
  exact ⟨G, G, hG, hG, a, a ≫ e.hom, 𝟙 G,
    ⟨Bicategory.whiskerRightIso ι _ ≪≫ Bicategory.leftUnitor _⟩, hasm, hasu,
    isRelativelySmooth_comp_of_isEquivalence B S hS a e.hom he hasm, Space.isSmooth_id B S hS hG⟩


/-- **Smoothness cancels against an equivalence.** If `φ ≫ e` is smooth and the functor underlying
`e` is an equivalence, then `φ` is smooth: `e` has a quasi-inverse over the site (**Stacks
003Z**), which is smooth, and `φ` is 2-isomorphic to `φ ≫ e` followed by it. -/
theorem AlgebraicStacks.isSmooth_of_comp_isEquivalence {𝒜 𝒦 𝒲 : AlgebraicStacks.{u, w} B S hS}
    (φ : 𝒜 ⟶ 𝒦) (e : 𝒦 ⟶ 𝒲)
    (he : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor e.hom))
    (hφe : AlgebraicStacks.IsSmooth B S hS (φ ≫ e)) : AlgebraicStacks.IsSmooth B S hS φ := by
  obtain ⟨F, hF, η, ε, hη, hε⟩ :=
    Functor.IsFiberedInGroupoids.isEquivalence_over 𝒦.val.val.p 𝒲.val.val.p
      𝒦.val.isFiberedInGroupoids 𝒲.val.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor e.hom) (CatFiberedInGroupoids.homFunctor_comp_p e.hom) he
  let j : 𝒲 ⟶ 𝒦 :=
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom ⟨F, hF⟩)
  have hj : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor j.hom) :=
    (CategoryTheory.Equivalence.mk (CatFiberedInGroupoids.homFunctor e.hom) F η.symm
      ε).isEquivalence_inverse
  have hej : e ≫ j ≅ 𝟙 𝒦 :=
    Bicategory.InducedBicategory.isoMk (Bicategory.InducedBicategory.isoMk
      (BasedNatIso.mkNatIso η hη))
  exact AlgebraicStacks.isSmooth_of_twoIso B S hS
    (Bicategory.associator φ e j ≪≫ Bicategory.whiskerLeftIso φ hej ≪≫ Bicategory.rightUnitor φ)
    (AlgebraicStacks.isSmooth_comp B S hS _ j hφe
      (AlgebraicStacks.isSmooth_of_isEquivalence B S hS j hj))

section Chart

variable {U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU : IsAlgebraicSpace B S hS U)
  (hV : IsAlgebraicSpace B S hS V) (h : U ⟶ V)

/-- The inclusion of the smooth locus of a morphism of algebraic spaces, as a 1-morphism of
algebraic stacks. -/
noncomputable abbrev maximalSmoothOpenInclusion :
    algebraicSpaceStack.{u, w} B S hS (Space.maximalSmoothOpen B S hS h).toFunctor
        (Space.isOpenSubspace_maximalSmoothOpen B S hS hU hV h).1 ⟶
      algebraicSpaceStack.{u, w} B S hS U hU :=
  algebraicSpaceStackMap.{u, w} B S hS (Space.isOpenSubspace_maximalSmoothOpen B S hS hU hV h).1
    hU (Space.maximalSmoothOpen B S hS h).ι

/-- The inclusion of the smooth locus of a morphism of algebraic spaces is smooth. -/
theorem isSmooth_maximalSmoothOpenInclusion :
    AlgebraicStacks.IsSmooth B S hS (maximalSmoothOpenInclusion.{u, w} B S hS hU hV h) :=
  isSmooth_algebraicSpaceStackMap_of_isOpenImmersion.{u, w} B S hS _ hU
    (Space.isOpenSubspace_maximalSmoothOpen B S hS hU hV h).2

/-- The morphism of algebraic spaces restricted to its smooth locus is smooth, read on algebraic
stacks. -/
theorem isSmooth_maximalSmoothOpenInclusion_comp :
    AlgebraicStacks.IsSmooth B S hS (maximalSmoothOpenInclusion.{u, w} B S hS hU hV h ≫
      algebraicSpaceStackMap.{u, w} B S hS hU hV h) := by
  have heq : algebraicSpaceStackMap.{u, w} B S hS
      (Space.isOpenSubspace_maximalSmoothOpen B S hS hU hV h).1 hV
        ((Space.maximalSmoothOpen B S hS h).ι ≫ h) =
      maximalSmoothOpenInclusion.{u, w} B S hS hU hV h ≫
        algebraicSpaceStackMap.{u, w} B S hS hU hV h :=
    congrArg Bicategory.InducedBicategory.mkHom (associatedMap_comp B S hS _ h)
  rw [← heq]
  exact (isSmooth_algebraicSpaceStackMap_iff.{u, w} B S hS _ hV _).2
    (Space.isSmooth_maximalSmoothOpen B S hS hU hV h)

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴}
  {bb : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒴} {Q : Bicategory.TwoCommSq bb f}
  (cc : algebraicSpaceStack.{u, w} B S hS U hU ⟶ Q.pt)
  (e : algebraicSpaceStackMap.{u, w} B S hS hU hV h ≅ cc ≫ Q.fst)

/-- The 1-morphism into `𝒳` that a chart of `f` restricts to on the smooth locus of its morphism
of algebraic spaces. -/
noncomputable abbrev chartSmoothPart : algebraicSpaceStack.{u, w} B S hS
    (Space.maximalSmoothOpen B S hS h).toFunctor
      (Space.isOpenSubspace_maximalSmoothOpen B S hS hU hV h).1 ⟶ 𝒳 :=
  maximalSmoothOpenInclusion.{u, w} B S hS hU hV h ≫ cc ≫ Q.snd

include e in
/-- **A chart restricted to the smooth locus of its morphism of algebraic spaces carries `f`
smoothly.** The composite with `f` is, up to the filler of `Q` and the given 2-isomorphism, the
restriction of the morphism of algebraic spaces to its smooth locus followed by the smooth
`bb`. -/
theorem isSmooth_chartSmoothPart_comp (hbb : AlgebraicStacks.IsSmooth B S hS bb) :
    AlgebraicStacks.IsSmooth B S hS (chartSmoothPart B S hS hU hV h cc ≫ f) := by
  refine AlgebraicStacks.isSmooth_of_twoIso B S hS ?_
    (AlgebraicStacks.isSmooth_comp B S hS _ bb
      (isSmooth_maximalSmoothOpenInclusion_comp.{u, w} B S hS hU hV h) hbb)
  exact Bicategory.associator _ _ bb ≪≫
    Bicategory.whiskerLeftIso _ (Bicategory.whiskerRightIso e bb ≪≫
      Bicategory.associator cc Q.fst bb ≪≫ Bicategory.whiskerLeftIso cc Q.iso ≪≫
      (Bicategory.associator cc Q.snd f).symm) ≪≫
    (Bicategory.associator _ (cc ≫ Q.snd) f).symm

end Chart

/-- The smooth part of a chart carries `f` smoothly when `bb` and `cc` are smooth. -/
private theorem isSmooth_chartSmoothPart {U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B S hS U) (hV : IsAlgebraicSpace B S hS V) (h : U ⟶ V)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴}
    {bb : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒴} {Q : Bicategory.TwoCommSq bb f}
    (hQ : Bicategory.IsTwoFibreProduct Q) (cc : algebraicSpaceStack.{u, w} B S hS U hU ⟶ Q.pt)
    (hbbsm : AlgebraicStacks.IsSmooth B S hS bb) (hccsm : AlgebraicStacks.IsSmooth B S hS cc) :
    AlgebraicStacks.IsSmooth B S hS (chartSmoothPart B S hS hU hV h cc) :=
  AlgebraicStacks.isSmooth_comp B S hS _ _
    (isSmooth_maximalSmoothOpenInclusion.{u, w} B S hS hU hV h)
    (AlgebraicStacks.isSmooth_comp B S hS cc _ hccsm
      (isSmooth_snd_of_isTwoFibreProduct B S hS hQ hbbsm))

/-- **Points of a chart over an open substack on which `f` is smooth lie in the smooth locus of
the chart's morphism of algebraic spaces.** Let `Q` be a 2-fibre product of `(bb, f)` with `bb`
smooth, let `cc` be a smooth 1-morphism from the algebraic stack of an algebraic space `U` to its
apex, and let `h : U ⟶ V` be a morphism of algebraic spaces whose 1-morphism, followed by an
equivalence `iV` onto the source of `bb`, is 2-isomorphic to `cc` followed by the projection. If
`Z` is an open substack of `𝒳` on which `f` is smooth and the image in `|𝒳|` of a point `u` of
the chart lies in `|Z|`, then `u` lies in the smooth locus of `h`.

The base change of `f|_Z` along `bb` is smooth (**Stacks 075W**), and the inverse image
`U ×_{Q} (Q ×_𝒳 Z)` of `Z` in the chart maps smoothly to it, so the morphism of algebraic spaces
is smooth there; `AlgebraicGeometry.Stack.range_pointsMap_subset_maximalSmoothOpen` concludes,
the point being lifted to the inverse image by **Stacks 04XH** twice. -/
theorem mem_range_maximalSmoothOpenInclusion {U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B S hS U) (hV : IsAlgebraicSpace B S hS V) (h : U ⟶ V)
    {𝒳 𝒴 𝒱 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴} {bb : 𝒱 ⟶ 𝒴}
    {Q : Bicategory.TwoCommSq bb f} (hQ : Bicategory.IsTwoFibreProduct Q)
    (cc : algebraicSpaceStack.{u, w} B S hS U hU ⟶ Q.pt)
    (iV : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒱)
    (hiV : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor iV.hom))
    (e : algebraicSpaceStackMap.{u, w} B S hS hU hV h ≫ iV ≅ cc ≫ Q.fst)
    (hcc : AlgebraicStacks.IsSmooth B S hS cc) (Z : OpenSubstack 𝒳)
    (hZ : AlgebraicStacks.IsSmooth B S hS (Z.inclusion ≫ f))
    (x : AlgebraicStacks.points B S hS (algebraicSpaceStack.{u, w} B S hS U hU))
    (hx : AlgebraicStacks.pointsMap B S hS (cc ≫ Q.snd) x ∈ Z.pointSet B S hS) :
    x ∈ Set.range (AlgebraicStacks.pointsMap B S hS
      (maximalSmoothOpenInclusion.{u, w} B S hS hU hV h)) := by
  set j := Z.inclusion
  set R := twoFibreProductSquareAlgebraicStacks B S hS Q.snd j
  have hR : Bicategory.IsTwoFibreProduct R :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS Q.snd j
  have hRsm : AlgebraicStacks.IsSmooth B S hS (R.fst ≫ Q.fst) :=
    AlgebraicStacks.isSmooth_baseChange B S hS (j ≫ f) bb (Q.pasteSnd R)
      (Bicategory.isTwoFibreProduct_pasteSnd Q hQ R hR) hZ
  have hRfst : AlgebraicStacks.IsSmooth B S hS R.fst :=
    AlgebraicStacks.isSmooth_baseChange B S hS j Q.snd R hR
      (AlgebraicStacks.isSmooth_of_isOpenImmersion B S hS j Z.isOpenImmersion)
  set E := twoFibreProductSquareAlgebraicStacks B S hS cc R.fst
  have hE : Bicategory.IsTwoFibreProduct E :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS cc R.fst
  have hEfst : AlgebraicStacks.IsSmooth B S hS E.fst :=
    AlgebraicStacks.isSmooth_baseChange B S hS R.fst cc E hE hRfst
  have hEh : AlgebraicStacks.IsSmooth B S hS
      (E.fst ≫ algebraicSpaceStackMap.{u, w} B S hS hU hV h) := by
    refine AlgebraicStacks.isSmooth_of_comp_isEquivalence B S hS _ iV hiV ?_
    exact AlgebraicStacks.isSmooth_of_twoIso B S hS
      ((Bicategory.associator E.snd R.fst Q.fst).symm ≪≫
        Bicategory.whiskerRightIso E.iso.symm Q.fst ≪≫ Bicategory.associator E.fst cc Q.fst ≪≫
        Bicategory.whiskerLeftIso E.fst e.symm ≪≫ (Bicategory.associator E.fst _ iV).symm)
      (AlgebraicStacks.isSmooth_comp B S hS E.snd _
        (isSmooth_snd_of_isTwoFibreProduct B S hS hE hcc) hRsm)
  obtain ⟨z, hz⟩ := hx
  obtain ⟨r, hr, -⟩ := AlgebraicStacks.exists_point_of_isTwoFibreProduct B S hS R hR
    (AlgebraicStacks.pointsMap B S hS cc x) z (by
      rw [hz, ← Function.comp_apply (f := AlgebraicStacks.pointsMap B S hS Q.snd),
        ← AlgebraicStacks.pointsMap_comp])
  obtain ⟨p, hp, -⟩ := AlgebraicStacks.exists_point_of_isTwoFibreProduct B S hS E hE x r hr.symm
  exact range_pointsMap_subset_maximalSmoothOpen B S hS hU hV h E.fst hEfst hEh ⟨p, hp⟩

/-- **A morphism of algebraic spaces through which a 1-morphism into an algebraic space
factors.** For `k : 𝒰 ⟶ 𝒱` between the algebraic stacks of two algebraic spaces, the morphism of
representing presheaves induces a 1-morphism 2-isomorphic to `k` (**Stacks 04SW**). -/
theorem exists_algebraicSpaceStackMap_iso {U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B S hS U) (hV : IsAlgebraicSpace B S hS V)
    (k : algebraicSpaceStack.{u, w} B S hS U hU ⟶ algebraicSpaceStack.{u, w} B S hS V hV) :
    ∃ h : U ⟶ V, Nonempty (algebraicSpaceStackMap.{u, w} B S hS hU hV h ≅ k) := by
  obtain ⟨e⟩ := nonempty_twoIso_associatedMap_representingMap B S hS U V k.hom
  exact ⟨_, ⟨Bicategory.InducedBicategory.isoMk e⟩⟩

/-- **A smooth chart of a 1-morphism of algebraic stacks.** For `f : 𝒳 ⟶ 𝒴` there are algebraic
spaces `U`, `V`, a smooth surjection `bb` from `V` onto `𝒴`, a 2-fibre product `Q` of `(bb, f)`, a
smooth surjection `cc` from `U` onto its apex, and a morphism `h : U ⟶ V` whose 1-morphism is the
composite of `cc` with the projection to `V`. -/
theorem exists_smoothChart {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    ∃ (V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hV : IsAlgebraicSpace B S hS V)
      (bb : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒴) (Q : Bicategory.TwoCommSq bb f)
      (_ : Bicategory.IsTwoFibreProduct Q)
      (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
      (cc : algebraicSpaceStack.{u, w} B S hS U hU ⟶ Q.pt) (h : U ⟶ V),
      AlgebraicStacks.IsSmooth B S hS bb ∧ IsSurjective B S hS bb ∧
        AlgebraicStacks.IsSmooth B S hS cc ∧ IsSurjective B S hS cc ∧
          Nonempty (algebraicSpaceStackMap.{u, w} B S hS hU hV h ≅ cc ≫ Q.fst) := by
  obtain ⟨V, hV, bb, hbbsm, hbbsu⟩ := exists_isSmooth_isSurjective_chart B S hS 𝒴
  obtain ⟨U, hU, cc, hccsm, hccsu⟩ := exists_isSmooth_isSurjective_chart B S hS
    (twoFibreProductSquareAlgebraicStacks B S hS bb f).pt
  obtain ⟨h, ⟨e⟩⟩ := exists_algebraicSpaceStackMap_iso B S hS hU hV
    (cc ≫ (twoFibreProductSquareAlgebraicStacks B S hS bb f).fst)
  exact ⟨V, hV, bb, _, isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS bb f,
    U, hU, cc, h, hbbsm, hbbsu, hccsm, hccsu, ⟨e⟩⟩

/-- **The open image of the smooth part of a chart is the smooth locus.** Let `Q` be a 2-fibre
product of `(bb, f)` with `bb` smooth and surjective, `cc` a smooth surjection onto its apex
from an algebraic space `U`, and `h : U ⟶ V` a morphism 2-isomorphic to `cc` followed by the
projection to `V`. Then the open image in `𝒳` of the smooth locus of `h` is the smooth locus of
`f`. -/
theorem isSmoothLocus_openImage_chartSmoothPart {U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B S hS U) (hV : IsAlgebraicSpace B S hS V) (h : U ⟶ V)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴}
    {bb : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒴} {Q : Bicategory.TwoCommSq bb f}
    (hQ : Bicategory.IsTwoFibreProduct Q)
    (cc : algebraicSpaceStack.{u, w} B S hS U hU ⟶ Q.pt)
    (e : algebraicSpaceStackMap.{u, w} B S hS hU hV h ≅ cc ≫ Q.fst)
    (hbbsm : AlgebraicStacks.IsSmooth B S hS bb) (hbbsu : IsSurjective B S hS bb)
    (hccsm : AlgebraicStacks.IsSmooth B S hS cc) (hccsu : IsSurjective B S hS cc)
    (hc : AlgebraicStacks.IsSmooth B S hS (chartSmoothPart B S hS hU hV h cc)) :
    IsSmoothLocus B S hS f (openImage B S hS _ hc) := by
  have hQsndsu : IsSurjective B S hS Q.snd := isSurjective_of_isTwoFibreProduct B S hS Q hQ hbbsu
  refine ⟨isSmooth_openImage_inclusion_comp B S hS _ f hc
      (isSmooth_chartSmoothPart_comp B S hS hU hV h cc e hbbsm), fun Z hZ x hx => ?_⟩
  have hZW : Z.pointSet B S hS ⊆
      Set.range (AlgebraicStacks.pointsMap B S hS (chartSmoothPart B S hS hU hV h cc)) := by
    intro ξ hξ
    obtain ⟨y, rfl⟩ := (isSurjective_comp B S hS cc Q.snd hccsu hQsndsu) ξ
    obtain ⟨y', rfl⟩ := mem_range_maximalSmoothOpenInclusion B S hS hU hV h hQ cc (𝟙 _)
      (inferInstanceAs (𝟭 _).IsEquivalence) (Bicategory.rightUnitor _ ≪≫ e) hccsm Z hZ y hξ
    refine ⟨y', ?_⟩
    simp only [chartSmoothPart, AlgebraicStacks.pointsMap_comp, Function.comp_apply]
  have hZx := Z.pointsWithin_pointSet B S hS hx
  rw [openSubstackOfPoints_property]
  exact fun q φ => hZW (hZx q φ)

/-- **Stacks 0DZR, existence.** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` has a
smooth locus: an open substack of `𝒳` on which `f` is smooth and which contains every open
substack with that property. -/
theorem exists_isSmoothLocus {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    ∃ W : OpenSubstack 𝒳, IsSmoothLocus B S hS f W := by
  obtain ⟨V, hV, bb, Q, hQ, U, hU, cc, h, hbbsm, hbbsu, hccsm, hccsu, ⟨e⟩⟩ :=
    exists_smoothChart B S hS f
  exact ⟨_, isSmoothLocus_openImage_chartSmoothPart B S hS hU hV h hQ cc e hbbsm hbbsu hccsm
    hccsu (isSmooth_chartSmoothPart B S hS hU hV h hQ cc hbbsm hccsm)⟩

/-- **Smooth loci are invariant under 2-isomorphism.** -/
theorem IsSmoothLocus.of_iso {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {f g : 𝒳 ⟶ 𝒴} (θ : f ≅ g)
    {W : OpenSubstack 𝒳} (hW : IsSmoothLocus B S hS f W) : IsSmoothLocus B S hS g W :=
  ⟨AlgebraicStacks.isSmooth_of_twoIso B S hS (Bicategory.whiskerLeftIso _ θ) hW.1,
    fun V hV => hW.2 V (AlgebraicStacks.isSmooth_of_twoIso B S hS
      (Bicategory.whiskerLeftIso _ θ.symm) hV)⟩

/-- If `f` is smooth on `W` and an open substack `W'` of `𝒳'` has `W'.inclusion ≫ g ≫ f` smooth
for a smooth `g`, then `g` carries every object of `W'` into `W`. -/
private theorem property_of_isSmoothLocus_of_isSmooth
    {𝒳' 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {g : 𝒳' ⟶ 𝒳} {f : 𝒳 ⟶ 𝒴}
    {W : OpenSubstack 𝒳} {W' : OpenSubstack 𝒳'} (hW : IsSmoothLocus B S hS f W)
    (hg : AlgebraicStacks.IsSmooth B S hS g)
    (hW' : AlgebraicStacks.IsSmooth B S hS (W'.inclusion ≫ g ≫ f))
    {x : 𝒳'.val.val.obj} (hx : W'.property x) : W.property (g.hom.hom.toFunctor.obj x) := by
  have hc : AlgebraicStacks.IsSmooth B S hS (W'.inclusion ≫ g) :=
    AlgebraicStacks.isSmooth_comp B S hS _ g
      (AlgebraicStacks.isSmooth_of_isOpenImmersion B S hS _ W'.isOpenImmersion) hg
  have hcf : AlgebraicStacks.IsSmooth B S hS ((W'.inclusion ≫ g) ≫ f) :=
    AlgebraicStacks.isSmooth_of_twoIso B S hS (Bicategory.associator _ g f).symm hW'
  exact hW.2 _ (isSmooth_openImage_inclusion_comp B S hS _ f hc hcf) _
    (property_openImage_obj B S hS _ hc (⟨x, hx⟩ : W'.property.FullSubcategory))

/-- **Stacks 0DZR, clause (1), the inclusion `𝒰' ⊆ g^{-1}𝒰`.** With `g : 𝒳' ⟶ 𝒳` smooth, `W` the
smooth locus of `f : 𝒳 ⟶ 𝒴` and `W'` the smooth locus of `g ≫ f`, every object of `W'` is carried
by `g` into `W`: the open image of `W'` in `𝒳` carries `f` smoothly by descent along the smooth
`W' ⟶ 𝒳` (`AlgebraicGeometry.Stack.isSmooth_openImage_inclusion_comp`), so it is contained in
`W`. -/
theorem isSmoothLocus_comp_of_isSmooth_apply'
    {𝒳' 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {g : 𝒳' ⟶ 𝒳} {f : 𝒳 ⟶ 𝒴}
    (hg : AlgebraicStacks.IsSmooth B S hS g) {W : OpenSubstack 𝒳} {W' : OpenSubstack 𝒳'}
    (hW : IsSmoothLocus B S hS f W) (hW' : IsSmoothLocus B S hS (g ≫ f) W')
    {x : 𝒳'.val.val.obj} (hx : W'.property x) :
    W.property (g.hom.hom.toFunctor.obj x) := by
  exact property_of_isSmoothLocus_of_isSmooth B S hS hW hg hW'.1 hx

/-- **Stacks 0DZR, smooth base change, the inclusion `𝒰' ⊆ g'^{-1}𝒰`.** Let `P` be a 2-fibre
product of `(g, f)` with `g` smooth, `W` the smooth locus of `f` and `W'` that of the projection
`P.fst`. Every object of `W'` is carried into `W` by `P.snd`: that projection is smooth and its
composite with `f` restricted to `W'` is `P.fst` restricted to `W'` followed by `g`, so the open
image of `W'` carries `f` smoothly. -/
theorem isSmoothLocus_baseChange_apply_of_isSmooth
    {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴} {g : 𝒴' ⟶ 𝒴}
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (hg : AlgebraicStacks.IsSmooth B S hS g)
    {W : OpenSubstack 𝒳} {W' : OpenSubstack P.pt}
    (hW : IsSmoothLocus B S hS f W) (hW' : IsSmoothLocus B S hS P.fst W')
    {x : P.pt.val.val.obj} (hx : W'.property x) :
    W.property (P.snd.hom.hom.toFunctor.obj x) := by
  exact property_of_isSmoothLocus_of_isSmooth B S hS hW
    (isSmooth_snd_of_isTwoFibreProduct B S hS hP hg)
    (AlgebraicStacks.isSmooth_of_twoIso B S hS
      (Bicategory.associator _ P.fst g ≪≫ Bicategory.whiskerLeftIso _ P.iso)
      (AlgebraicStacks.isSmooth_comp B S hS _ g hW'.1 hg)) hx

/-- **The inner square cut out of a 2-fibre product over a composite cospan is a 2-fibre product
(Stacks 003Q).** Let `Sq` be a 2-fibre product of `(f, g)` and `Z` one of `(f, k ≫ g)`. The square
over `(Sq.snd, k)` that the universal property of `Sq` cuts out of `Z` is a 2-fibre product: its
pasting with `Sq` compares to `Z` by the identity, and the pasting lemma reverses. -/
noncomputable def isTwoFibreProduct_innerSq
    {𝒳 𝒴 𝒵 𝒯 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒵} {g : 𝒴 ⟶ 𝒵} {k : 𝒯 ⟶ 𝒴}
    {Sq : Bicategory.TwoCommSq f g} (hSq : Bicategory.IsTwoFibreProduct Sq)
    {Z : Bicategory.TwoCommSq f (k ≫ g)} (hZ : Bicategory.IsTwoFibreProduct Z) :
    Bicategory.IsTwoFibreProduct (Bicategory.innerSq hSq Z) :=
  isTwoFibreProduct_of_isTwoFibreProduct_paste B S hS hSq _
    (Bicategory.isTwoFibreProduct_of_section hZ (Bicategory.toPasteInner hSq Z) (𝟙 _)
      (Bicategory.leftUnitor _))

/-- The 2-commutative square of algebraic stacks attached to a pullback square of algebraic
spaces. -/
noncomputable def algebraicSpaceStackSquare {F G H T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hH : IsAlgebraicSpace B S hS H) (hT : IsAlgebraicSpace B S hS T)
    {p : T ⟶ F} {q : T ⟶ G} {a : F ⟶ H} {b : G ⟶ H} (hcomm : p ≫ a = q ≫ b) :
    Bicategory.TwoCommSq (algebraicSpaceStackMap.{u, w} B S hS hF hH a)
      (algebraicSpaceStackMap.{u, w} B S hS hG hH b) where
  pt := algebraicSpaceStack.{u, w} B S hS T hT
  fst := algebraicSpaceStackMap.{u, w} B S hS hT hF p
  snd := algebraicSpaceStackMap.{u, w} B S hS hT hG q
  iso := Bicategory.InducedBicategory.isoMk (fibredCategorySquare hcomm).iso

/-- **A pullback square of algebraic spaces is a 2-fibre product of algebraic stacks.** -/
noncomputable def isTwoFibreProduct_algebraicSpaceStackSquare
    {F G H T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hH : IsAlgebraicSpace B S hS H) (hT : IsAlgebraicSpace B S hS T)
    {p : T ⟶ F} {q : T ⟶ G} {a : F ⟶ H} {b : G ⟶ H} (h : IsPullback p q a b) :
    Bicategory.IsTwoFibreProduct
      (algebraicSpaceStackSquare.{u, w} B S hS hF hG hH hT h.w) :=
  Bicategory.isTwoFibreProduct_of_underlying (isTwoFibreProduct_fibredCategorySquare h)

/-- **The image of a smooth 1-morphism along which `f` becomes smooth lies in the smooth locus.**
If `c : 𝒜 ⟶ 𝒳` is smooth and `c ≫ f` is smooth, the points of `|𝒳|` in the image of `c` lie in
the smooth locus of `f`: the open image of `c` carries `f` smoothly. -/
theorem range_pointsMap_subset_pointSet_of_isSmoothLocus {𝒜 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    {f : 𝒳 ⟶ 𝒴} {W : OpenSubstack 𝒳} (hW : IsSmoothLocus B S hS f W) (c : 𝒜 ⟶ 𝒳)
    (hc : AlgebraicStacks.IsSmooth B S hS c) (hcf : AlgebraicStacks.IsSmooth B S hS (c ≫ f)) :
    Set.range (AlgebraicStacks.pointsMap B S hS c) ⊆ W.pointSet B S hS := by
  rw [← pointSet_openSubstackOfPoints 𝒳 _ (isOpen_range_pointsMap_of_isSmooth B S hS c hc)]
  exact OpenSubstack.pointSet_mono B S hS
    (hW.2 _ (isSmooth_openImage_inclusion_comp B S hS c f hc hcf))

/-- A smooth 1-morphism into the apex of a base change of a locally finitely presented
1-morphism, followed by the projection, is locally of finite presentation. -/
private theorem isLocallyOfFinitePresentation_comp_fst_of_isSmooth
    {𝒜 𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴} {g : 𝒴' ⟶ 𝒴}
    {P : Bicategory.TwoCommSq g f} (hP : Bicategory.IsTwoFibreProduct P) {a : 𝒜 ⟶ P.pt}
    (ha : AlgebraicStacks.IsSmooth B S hS a)
    (hf : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f) :
    AlgebraicStacks.IsLocallyOfFinitePresentation B S hS (a ≫ P.fst) :=
  AlgebraicStacks.isLocallyOfFinitePresentation_comp B S hS a P.fst
    (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS a ha)
    (AlgebraicStacks.isLocallyOfFinitePresentation_baseChange B S hS f g P hP hf)

/-- **Stacks 0DZR, clauses (2) and (3), the inclusion `𝒰' ⊆ g'^{-1}𝒰` on points.** Let `P` be a
2-fibre product of `(g, f)` with `g` flat, and suppose that `f` or `g` is locally of finite
presentation. Then the projection `P.snd` carries every point of the smooth locus of `P.fst` into
the smooth locus of `f`.

The proof is the source's: a chart of `f` (`V ⟶ 𝒴` and `U ⟶ V ×_𝒴 𝒳`) and a chart `V'' ⟶ V ×_𝒴 𝒴'`
give the cartesian square of algebraic spaces `U'' = V'' ×_V U`, whose top morphism `h''` is a
base change of the chart morphism `h` along the flat `t : V'' ⟶ V`. The 2-fibre products are
identified by cancelling pastings, so that `U''` is a smooth chart of `V'' ×_{𝒴'} 𝒳'`: a point of
the smooth locus of `P.fst` lifts to `U''` into the smooth locus of `h''`, which by
**Stacks 0DZI** is the inverse image of that of `h`, and that maps into the smooth locus of `f`. -/
@[ega "IV 17.7.2" "(ii)"]
theorem pointSet_subset_preimage_of_isSmoothLocus_baseChange
    {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴} {g : 𝒴' ⟶ 𝒴}
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (hflat : AlgebraicStacks.IsFlat B S hS g)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f ∨
      AlgebraicStacks.IsLocallyOfFinitePresentation B S hS g)
    {W : OpenSubstack 𝒳} {W' : OpenSubstack P.pt}
    (hW : IsSmoothLocus B S hS f W) (hW' : IsSmoothLocus B S hS P.fst W') :
    W'.pointSet B S hS ⊆ AlgebraicStacks.pointsMap B S hS P.snd ⁻¹' W.pointSet B S hS := by
  -- a chart of `f`
  obtain ⟨V, hV, bb, Q, hQ, U, hU, cc, h, hbbsm, hbbsu, hccsm, hccsu, ⟨e⟩⟩ :=
    exists_smoothChart B S hS f
  -- a chart of `𝒴'` over `V`
  set E := twoFibreProductSquareAlgebraicStacks B S hS bb g
  have hE : Bicategory.IsTwoFibreProduct E :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS bb g
  obtain ⟨V'', hV'', cE, hcEsm, hcEsu⟩ := exists_isSmooth_isSurjective_chart B S hS E.pt
  set b'' := cE ≫ E.snd
  have hb''su : IsSurjective B S hS b'' :=
    isSurjective_comp B S hS cE E.snd hcEsu (isSurjective_of_isTwoFibreProduct B S hS E hE hbbsu)
  obtain ⟨t, ⟨et⟩⟩ := exists_algebraicSpaceStackMap_iso B S hS hV'' hV (cE ≫ E.fst)
  let θ : b'' ≫ g ≅ algebraicSpaceStackMap.{u, w} B S hS hV'' hV t ≫ bb :=
    Bicategory.associator cE E.snd g ≪≫ Bicategory.whiskerLeftIso cE E.iso.symm ≪≫
      (Bicategory.associator cE E.fst bb).symm ≪≫ Bicategory.whiskerRightIso et.symm bb
  -- the chart of `P.fst`
  set Q'' := twoFibreProductSquareAlgebraicStacks B S hS b'' P.fst
  have hQ'' : Bicategory.IsTwoFibreProduct Q'' :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS b'' P.fst
  -- `Q''.pt` is a 2-fibre product over `V''` and `Q.pt`
  have hZ₁ := Bicategory.isTwoFibreProduct_reindexSnd θ (Bicategory.isTwoFibreProduct_paste
    (Bicategory.isTwoFibreProduct_swap hP) (Bicategory.isTwoFibreProduct_swap hQ''))
  have hT₁ := isTwoFibreProduct_innerSq B S hS (Bicategory.isTwoFibreProduct_swap hQ) hZ₁
  set T₁ := Bicategory.innerSq (Bicategory.isTwoFibreProduct_swap hQ)
    ((P.swap.paste Q''.swap).reindexSnd θ)
  -- the pullback of algebraic spaces
  have sq := IsPullback.of_hasPullback h t
  have hU'' : IsAlgebraicSpace B S hS (Limits.pullback h t) :=
    isAlgebraicSpace_of_isPullback hU hV'' hV.isSheaf hV.diagonal_representable sq
  have hFsq := isTwoFibreProduct_algebraicSpaceStackSquare.{u, w} B S hS hU hV'' hV hU'' sq
  have hZ₂ := Bicategory.isTwoFibreProduct_reindexSnd e (Bicategory.isTwoFibreProduct_swap hFsq)
  have hT₂ := isTwoFibreProduct_innerSq B S hS (Bicategory.isTwoFibreProduct_swap hT₁) hZ₂
  set T₂ := Bicategory.innerSq (Bicategory.isTwoFibreProduct_swap hT₁)
    ((algebraicSpaceStackSquare.{u, w} B S hS hU hV'' hV hU'' sq.w).swap.reindexSnd e)
  have hcc''sm : AlgebraicStacks.IsSmooth B S hS T₂.fst :=
    AlgebraicStacks.isSmooth_baseChange B S hS cc T₁.fst T₂ hT₂ hccsm
  have hcc''su : IsSurjective B S hS T₂.fst :=
    isSurjective_of_isTwoFibreProduct B S hS T₂.swap (Bicategory.isTwoFibreProduct_swap hT₂) hccsu
  intro x' hx'
  have hQ''su : IsSurjective B S hS Q''.snd :=
    isSurjective_of_isTwoFibreProduct B S hS Q'' hQ'' hb''su
  obtain ⟨u'', rfl⟩ := isSurjective_comp B S hS T₂.fst Q''.snd hcc''su hQ''su x'
  set h'' := Limits.pullback.snd h t
  set pr := Limits.pullback.fst h t
  let e'' : algebraicSpaceStackMap.{u, w} B S hS hU'' hV'' h'' ≫ 𝟙 _ ≅ T₂.fst ≫ Q''.fst :=
    Bicategory.rightUnitor _ ≪≫
      (Bicategory.canLower (Bicategory.isTwoFibreProduct_swap hT₁)
        ((algebraicSpaceStackSquare.{u, w} B S hS hU hV'' hV hU'' sq.w).swap.reindexSnd e)).isoFst
  obtain ⟨m'', rfl⟩ := mem_range_maximalSmoothOpenInclusion B S hS hU'' hV'' h'' hQ'' T₂.fst (𝟙 _)
    (inferInstanceAs (𝟭 _).IsEquivalence) e'' hcc''sm W' hW'.1 u'' hx'
  -- Stacks 0DZI for the cartesian square of algebraic spaces
  have sqA : IsPullback (ObjectProperty.homMk pr : (⟨_, hU''⟩ : AlgebraicSpaces B S hS) ⟶ ⟨U, hU⟩)
      (ObjectProperty.homMk h'' : (⟨_, hU''⟩ : AlgebraicSpaces B S hS) ⟶ ⟨V'', hV''⟩)
      (ObjectProperty.homMk h : (⟨U, hU⟩ : AlgebraicSpaces B S hS) ⟶ ⟨V, hV⟩)
      (ObjectProperty.homMk t : (⟨V'', hV''⟩ : AlgebraicSpaces B S hS) ⟶ ⟨V, hV⟩) :=
    IsPullback.of_map_of_faithful (F := ObjectProperty.ι _) sq
  have hflatIso : ∀ {𝒜 𝒞 : AlgebraicStacks.{u, w} B S hS} {a b : 𝒜 ⟶ 𝒞}, (a ≅ b) →
      AlgebraicStacks.IsFlat B S hS a → AlgebraicStacks.IsFlat B S hS b := fun ε ha =>
    (AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS _).2
      (hasPropertyOnSomeSmoothDiagram_of_twoIso B S hS (fun _ _ k => Space.IsFlat B S hS k)
        (Bicategory.InducedBicategory.isoHom ε)
        ((AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS _).1 ha))
  have hlfpIso : ∀ {𝒜 𝒞 : AlgebraicStacks.{u, w} B S hS} {a b : 𝒜 ⟶ 𝒞}, (a ≅ b) →
      AlgebraicStacks.IsLocallyOfFinitePresentation B S hS a →
        AlgebraicStacks.IsLocallyOfFinitePresentation B S hS b := fun {𝒜 𝒞} {a b} ε ha =>
    (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS) 𝒜.property
      𝒞.property b.hom).2
      (hasPropertyOnSomeSmoothDiagram_of_twoIso B S hS _
        (Bicategory.InducedBicategory.isoHom ε)
        ((hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _
          (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS) 𝒜.property
          𝒞.property a.hom).1 ha))
  have htflat : Space.IsFlat B S hS t :=
    (isFlat_algebraicSpaceStackMap_iff.{u, w} B S hS hV'' hV t).1
      (hflatIso et.symm
        (AlgebraicStacks.isFlat_comp B S hS cE E.fst
          (AlgebraicStacks.isFlat_of_isSmooth B S hS cE hcEsm)
          (AlgebraicStacks.isFlat_baseChange B S hS g bb E hE hflat)))
  have hM : Space.maximalSmoothOpen B S hS h'' ≤
      (Space.maximalSmoothOpen B S hS h).preimage pr := by
    rcases hlfp with hf | hg
    · refine (Space.maximalSmoothOpen_eq_preimage_of_isLocallyOfFinitePresentation_isFlat B S hS
        sqA ?_ htflat).le
      exact (isLocallyOfFinitePresentation_algebraicSpaceStackMap_iff.{u, w} B S hS hU hV h).1
        (hlfpIso e.symm
          (isLocallyOfFinitePresentation_comp_fst_of_isSmooth B S hS hQ hccsm hf))
    · refine (Space.maximalSmoothOpen_eq_preimage_of_isFlat_isLocallyOfFinitePresentation B S hS
        sqA htflat ?_).le
      exact (isLocallyOfFinitePresentation_algebraicSpaceStackMap_iff.{u, w} B S hS hV'' hV t).1
        (hlfpIso et.symm
          (isLocallyOfFinitePresentation_comp_fst_of_isSmooth B S hS hE hcEsm hg))
  -- the smooth part of the chart of `f`
  refine range_pointsMap_subset_pointSet_of_isSmoothLocus B S hS hW _
    (isSmooth_chartSmoothPart B S hS hU hV h hQ cc hbbsm hccsm)
    (isSmooth_chartSmoothPart_comp B S hS hU hV h cc e hbbsm) ?_
  -- the 1-morphism of the inclusion of `N''` into `N`
  set N := Space.maximalSmoothOpen B S hS h
  set N'' := Space.maximalSmoothOpen B S hS h''
  have hNalg := (Space.isOpenSubspace_maximalSmoothOpen B S hS hU hV h).1
  have hN''alg := (Space.isOpenSubspace_maximalSmoothOpen B S hS hU'' hV'' h'').1
  have hkey : maximalSmoothOpenInclusion.{u, w} B S hS hU'' hV'' h'' ≫
        algebraicSpaceStackMap.{u, w} B S hS hU'' hU pr =
      algebraicSpaceStackMap.{u, w} B S hS hN''alg hNalg
          (Subfunctor.homOfLe hM ≫ N.fromPreimage pr) ≫
        maximalSmoothOpenInclusion.{u, w} B S hS hU hV h := by
    have h₁ : N''.ι ≫ pr = (Subfunctor.homOfLe hM ≫ N.fromPreimage pr) ≫ N.ι := by
      rw [Category.assoc, Subfunctor.fromPreimage_ι, ← Category.assoc, Subfunctor.homOfLe_ι]
    have h₂ := congrArg (fun k => (associatedMap B S hS k).1) h₁
    simp only [associatedMap_comp] at h₂
    exact congrArg Bicategory.InducedBicategory.mkHom h₂
  -- the two routes from the chart of `P.fst` to `𝒳`
  set c₁ := Bicategory.canLower (Bicategory.isTwoFibreProduct_swap hQ)
    ((P.swap.paste Q''.swap).reindexSnd θ)
  set c₂ := Bicategory.canLower (Bicategory.isTwoFibreProduct_swap hT₁)
    ((algebraicSpaceStackSquare.{u, w} B S hS hU hV'' hV hU'' sq.w).swap.reindexSnd e)
  refine ⟨AlgebraicStacks.pointsMap B S hS (algebraicSpaceStackMap.{u, w} B S hS hN''alg hNalg
    (Subfunctor.homOfLe hM ≫ N.fromPreimage pr)) m'', ?_⟩
  set x₀ := AlgebraicStacks.pointsMap B S hS
    (maximalSmoothOpenInclusion.{u, w} B S hS hU'' hV'' h'') m''
  have r₁ := pointsMap_comp_eq_of_iso B S hS c₁.isoFst
  have r₂ := pointsMap_comp_eq_of_iso B S hS T₂.iso
  have r₃ := pointsMap_comp_eq_of_iso B S hS (eqToIso hkey)
  have r₄ := AlgebraicStacks.pointsMap_comp B S hS
    (maximalSmoothOpenInclusion.{u, w} B S hS hU hV h) (cc ≫ Q.snd)
  have r₅ := AlgebraicStacks.pointsMap_comp B S hS cc Q.snd
  calc AlgebraicStacks.pointsMap B S hS (chartSmoothPart B S hS hU hV h cc) _
      = AlgebraicStacks.pointsMap B S hS Q.snd (AlgebraicStacks.pointsMap B S hS cc
          (AlgebraicStacks.pointsMap B S hS (maximalSmoothOpenInclusion.{u, w} B S hS hU hV h)
            (AlgebraicStacks.pointsMap B S hS (algebraicSpaceStackMap.{u, w} B S hS hN''alg
              hNalg (Subfunctor.homOfLe hM ≫ N.fromPreimage pr)) m''))) := by
        rw [chartSmoothPart, r₄, Function.comp_apply, r₅, Function.comp_apply]
    _ = AlgebraicStacks.pointsMap B S hS Q.snd (AlgebraicStacks.pointsMap B S hS cc
          (AlgebraicStacks.pointsMap B S hS (algebraicSpaceStackMap.{u, w} B S hS hU'' hU pr)
            x₀)) := congrArg _ (congrArg _ (congrFun r₃ m'').symm)
    _ = AlgebraicStacks.pointsMap B S hS Q.snd (AlgebraicStacks.pointsMap B S hS T₁.fst
          (AlgebraicStacks.pointsMap B S hS T₂.fst x₀)) := congrArg _ (congrFun r₂ x₀).symm
    _ = AlgebraicStacks.pointsMap B S hS P.snd (AlgebraicStacks.pointsMap B S hS Q''.snd
          (AlgebraicStacks.pointsMap B S hS T₂.fst x₀)) :=
        (congrFun r₁ (AlgebraicStacks.pointsMap B S hS T₂.fst x₀)).symm
    _ = _ := congrArg _ (congrFun (AlgebraicStacks.pointsMap_comp B S hS T₂.fst Q''.snd) x₀).symm

/-- **The smooth locus is cut out by its points.** The objects of the smooth locus of `f` are
exactly those every point seen by which lies in its point set. -/
theorem IsSmoothLocus.property_eq {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴}
    {W : OpenSubstack 𝒳} (hW : IsSmoothLocus B S hS f W) :
    W.property = pointsWithin 𝒳 (W.pointSet B S hS) := by
  obtain ⟨V, hV, bb, Q, hQ, U, hU, cc, h, hbbsm, hbbsu, hccsm, hccsu, ⟨e⟩⟩ :=
    exists_smoothChart B S hS f
  obtain rfl := eq_of_isSmoothLocus B S hS hW
    (isSmoothLocus_openImage_chartSmoothPart B S hS hU hV h hQ cc e hbbsm hbbsu hccsm hccsu
      (isSmooth_chartSmoothPart B S hS hU hV h hQ cc hbbsm hccsm))
  rw [pointSet_openSubstackOfPoints, openSubstackOfPoints_property]

/-- **Stacks 0DZR, clauses (2) and (3), the inclusion `𝒰' ⊆ g'^{-1}𝒰`.** -/
theorem isSmoothLocus_baseChange_apply_of_isFlat
    {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴} {g : 𝒴' ⟶ 𝒴}
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (hflat : AlgebraicStacks.IsFlat B S hS g)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f ∨
      AlgebraicStacks.IsLocallyOfFinitePresentation B S hS g)
    {W : OpenSubstack 𝒳} {W' : OpenSubstack P.pt}
    (hW : IsSmoothLocus B S hS f W) (hW' : IsSmoothLocus B S hS P.fst W')
    {x : P.pt.val.val.obj} (hx : W'.property x) :
    W.property (P.snd.hom.hom.toFunctor.obj x) := by
  rw [hW.property_eq B S hS]
  refine (pointsWithin_obj_iff 𝒳 P.snd.hom.hom _ x).2 fun r ψ => ?_
  exact pointSet_subset_preimage_of_isSmoothLocus_baseChange B S hS P hP hflat hlfp hW hW'
    (W'.pointsWithin_pointSet B S hS hx r ψ)


/-! ### The three clauses -/

/-- **Stacks 0DZR, clause (1).** Formation of the smooth locus commutes with precomposition by a
smooth 1-morphism: for `g : 𝒳' ⟶ 𝒳` smooth, the smooth locus of `g ≫ f` is the inverse image
along `g` of the smooth locus of `f`. -/
theorem isSmoothLocus_comp_of_isSmooth
    {𝒳' 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {g : 𝒳' ⟶ 𝒳} {f : 𝒳 ⟶ 𝒴}
    (hg : AlgebraicStacks.IsSmooth B S hS g) {W : OpenSubstack 𝒳} {W' : OpenSubstack 𝒳'}
    (hW : IsSmoothLocus B S hS f W) (hW' : IsSmoothLocus B S hS (g ≫ f) W') :
    W'.property = fun x => W.property (g.hom.hom.toFunctor.obj x) := by
  funext x
  exact propext ⟨fun hx => isSmoothLocus_comp_of_isSmooth_apply' B S hS hg hW hW' hx,
    fun hx => isSmoothLocus_comp_of_isSmooth_apply B S hS hg hW hW' hx⟩

/-- **Stacks 0DZR, clauses (2) and (3) together.** Let `P` be a 2-fibre product of `(g, f)` with
`g` flat, and suppose that `g` or `f` is locally of finite presentation. Then the smooth locus of
the base change `P.fst` is the inverse image along `P.snd` of the smooth locus of `f`. -/
theorem isSmoothLocus_baseChange_of_isFlat
    {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴} {g : 𝒴' ⟶ 𝒴}
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (hflat : AlgebraicStacks.IsFlat B S hS g)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f ∨
      AlgebraicStacks.IsLocallyOfFinitePresentation B S hS g)
    {W : OpenSubstack 𝒳} {W' : OpenSubstack P.pt}
    (hW : IsSmoothLocus B S hS f W) (hW' : IsSmoothLocus B S hS P.fst W') :
    W'.property = fun x => W.property (P.snd.hom.hom.toFunctor.obj x) := by
  funext x
  exact propext ⟨fun hx => isSmoothLocus_baseChange_apply_of_isFlat B S hS P hP hflat hlfp hW hW'
      hx,
    fun hx => isSmoothLocus_baseChange_apply B S hS P hP hW hW' hx⟩

/-- **Stacks 0DZR.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`. There is a
maximal open substack `𝒰 ⊆ 𝒳` such that `f|_𝒰 : 𝒰 ⟶ 𝒴` is smooth — an open substack on which `f`
is smooth containing every other one, unique by maximality. Moreover, formation of this open
substack commutes with

1. precomposing by smooth morphisms: for `g : 𝒳' ⟶ 𝒳` smooth, the open substack of `g ≫ f` is
   the inverse image along `g` of that of `f`;
2. base change by morphisms which are flat and locally of finite presentation: for any 2-fibre
   product `P` of `f` along such a `g : 𝒴' ⟶ 𝒴`, the open substack of the base change `P.fst` is
   the inverse image along the projection `P.snd` of that of `f`;
3. base change by flat morphisms, provided `f` is locally of finite presentation.

The open substack is constructed from a smooth chart of `f`: the image of the smooth locus of the
chart's morphism of algebraic spaces (**Stacks 0DZI**), read as an open substack by
**Stacks 06FJ** (`AlgebraicGeometry.Stack.openSubstackOfPoints`). Clause (1) is descent along the
smooth `𝒰' ⟶ 𝒳`, and clauses (2) and (3) reduce to **Stacks 0DZI** on a cartesian square of
charts. -/
@[stacks 0DZR "the maximal open substack on which f is smooth exists and is unique, and its \
formation commutes with precomposition by smooth morphisms, with base change by flat morphisms \
locally of finite presentation, and with flat base change when f is locally of finite \
presentation"]
theorem smoothLocus {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    (∃! W : OpenSubstack 𝒳, IsSmoothLocus B S hS f W) ∧
    (∀ (𝒳' : AlgebraicStacks.{u, w} B S hS) (g : 𝒳' ⟶ 𝒳),
      AlgebraicStacks.IsSmooth B S hS g →
      ∀ (W : OpenSubstack 𝒳) (W' : OpenSubstack 𝒳'),
        IsSmoothLocus B S hS f W → IsSmoothLocus B S hS (g ≫ f) W' →
          W'.property = fun x => W.property (g.hom.hom.toFunctor.obj x)) ∧
    (∀ (𝒴' : AlgebraicStacks.{u, w} B S hS) (g : 𝒴' ⟶ 𝒴) (P : Bicategory.TwoCommSq g f),
      Bicategory.IsTwoFibreProduct P →
      AlgebraicStacks.IsFlat B S hS g → AlgebraicStacks.IsLocallyOfFinitePresentation B S hS g →
      ∀ (W : OpenSubstack 𝒳) (W' : OpenSubstack P.pt),
        IsSmoothLocus B S hS f W → IsSmoothLocus B S hS P.fst W' →
          W'.property = fun x => W.property (P.snd.hom.hom.toFunctor.obj x)) ∧
    (AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f →
      ∀ (𝒴' : AlgebraicStacks.{u, w} B S hS) (g : 𝒴' ⟶ 𝒴) (P : Bicategory.TwoCommSq g f),
        Bicategory.IsTwoFibreProduct P → AlgebraicStacks.IsFlat B S hS g →
        ∀ (W : OpenSubstack 𝒳) (W' : OpenSubstack P.pt),
          IsSmoothLocus B S hS f W → IsSmoothLocus B S hS P.fst W' →
            W'.property = fun x => W.property (P.snd.hom.hom.toFunctor.obj x)) := by
  refine ⟨?_, fun _ _ hg _ _ hW hW' => isSmoothLocus_comp_of_isSmooth B S hS hg hW hW',
    fun _ _ P hP hflat hlfp _ _ hW hW' =>
      isSmoothLocus_baseChange_of_isFlat B S hS P hP hflat (Or.inr hlfp) hW hW',
    fun hf _ _ P hP hflat _ _ hW hW' =>
      isSmoothLocus_baseChange_of_isFlat B S hS P hP hflat (Or.inl hf) hW hW'⟩
  obtain ⟨W, hW⟩ := exists_isSmoothLocus B S hS f
  exact ⟨W, hW, fun W' hW' => eq_of_isSmoothLocus B S hS hW' hW⟩

end AlgebraicGeometry.Stack

end

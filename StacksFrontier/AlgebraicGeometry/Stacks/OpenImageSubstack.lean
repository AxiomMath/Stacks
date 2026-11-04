module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartShrinkingQuasiFiniteEtale
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatOpenPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsInjective
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyCancel
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable
import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionFppfLocalAtTarget

/-!
# The open substack covered by an open part of a smooth chart (Stacks 05UP)

Let `𝒳` be an algebraic stack over a scheme `S` contained in a big fppf site `B`, let `U` be an
algebraic space with a surjective smooth 1-morphism `U ⟶ 𝒳`, and let `V ↪ U` be an open
immersion. **Stacks 05UP** says that there are an algebraic stack `𝒴`, an open immersion
`𝒴 ⟶ 𝒳` and a surjective smooth 1-morphism `V ⟶ 𝒴`.

The `𝒴` produced here is *constructed*, not merely asserted: it is the open substack of `𝒳`
(**Stacks 04YM**) whose set of points is the image of `|V|` in `|𝒳|`, so the open immersion
`𝒴 ⟶ 𝒳` is the inclusion of that substack and the 1-morphism `V ⟶ 𝒴` is the factorization of
`V ⟶ 𝒳` through it. The three pieces are asserted together, in one existential statement which
also records the 2-commutativity of the resulting square.

## Main definitions

* `AlgebraicGeometry.Stack.openImageSubstack`: the open substack of `𝒳` whose points are the
  image of the points of the source of a smooth 1-morphism.
* `AlgebraicGeometry.Stack.openImageFactorization`: the factorization of that 1-morphism through
  `AlgebraicGeometry.Stack.openImageSubstack`.

## Main results

* `AlgebraicGeometry.Space.isSmooth_of_comp_isEtale`: a morphism of algebraic spaces whose
  composite with an étale morphism is smooth is smooth.
* `AlgebraicGeometry.Stack.isSmooth_algebraicSpaceStackMap_iff`: a morphism of algebraic spaces
  over `S` is smooth exactly when the 1-morphism of algebraic stacks it induces is.
* `AlgebraicGeometry.Stack.isSmooth_openImageFactorization` and
  `AlgebraicGeometry.Stack.isSurjective_openImageFactorization`: the factorization is smooth and
  surjective.
* `AlgebraicGeometry.Stack.exists_openSubstack_isOpenImmersion_smooth_surjective`:
  **Stacks 05UP**.

## Inputs

Three general facts enter the proof, each a theorem of this library.

* **Stacks 06FJ**, that `𝒴 ↦ |𝒴|` is an inclusion-preserving bijection from the open substacks
  of an algebraic stack onto the opens of its space of points. Its surjective half,
  `AlgebraicGeometry.Stack.OpenSubstack.ofIsOpen` with
  `AlgebraicGeometry.Stack.OpenSubstack.pointSet_ofIsOpen`, produces `𝒴`.
* An open immersion of algebraic stacks surjective on points is essentially surjective on
  objects, `AlgebraicGeometry.Stack.AlgebraicStacks.essSurj_of_isOpenImmersion_of_isSurjective`.
  This is what puts the image of every object of `V` inside `𝒴`.
* **Stacks 041X**, that being an open immersion of algebraic spaces is local on the base, in the
  fppf form `AlgebraicGeometry.Space.openImmersion_isLocalAtTarget_fppf`. It is used when the
  inclusion of `𝒴` is base changed along `V ⟶ 𝒳`. Its module is imported non-publicly, for the
  reason recorded in `StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack`.

The rest of the proof is in this file: that `V` is an algebraic space, that `V ⟶ 𝒳` is smooth,
that its image on points is open, the construction of `𝒴` and of the factorization, and that the
factorization is smooth and surjective.

## Implementation notes

The image of the points of `V` is open because a smooth 1-morphism is flat (**Stacks 04TA** at
`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_of_isSmooth`) and locally of finite presentation
(**Stacks 0DNP**), and such a 1-morphism is open on points by **Stacks 06R7**.

Smoothness of the factorization is the source's own argument in the form
`AlgebraicGeometry.Stack.prop_of_comp_of_spaceCancel`, the cancellation of a condition of
Stacks 04XB: the composite `V ⟶ 𝒴 ⟶ 𝒳` is smooth and the inclusion `𝒴 ⟶ 𝒳` is an open
immersion, so the factorization is smooth as soon as smoothness of morphisms of algebraic spaces
cancels against open immersions, which is `AlgebraicGeometry.Space.isSmooth_of_comp_isEtale`
together with **Stacks 0CIP** for algebraic spaces
(`AlgebraicGeometry.Space.isEtale_of_isOpenImmersion`). That cancellation is immediate from the
étale-chart definition of smoothness: a pair of étale charts of `V ⟶ 𝒴` becomes a pair of étale
charts of `V ⟶ 𝒳` on composing the chart of `𝒴` with the inclusion, with the same morphism of
schemes on top. The relative condition is turned back into the smooth-diagram criterion of
Stacks 075U by **Stacks 06FM**
(`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty`), whose
representability hypothesis holds because the source is an algebraic space
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_isAlgebraicStack`).

The factorization composed with the inclusion is the original 1-morphism *on the nose*: the
functor of the factorization is `CategoryTheory.ObjectProperty.lift` of the original functor, and
composing that with the full-subcategory inclusion returns it definitionally. That is why the
2-commutativity of the square is an identity and why no 2-cell algebra occurs anywhere below.

Surjectivity of the factorization uses that the inclusion of an open substack is injective on
points (**Stacks 0500**,
`AlgebraicGeometry.Stack.pointsMap_injective_of_fullyFaithful`, at the full faithfulness of a
full-subcategory inclusion), so the equality of the two images in `|𝒳|` may be cancelled.

## References

* [Stacks Project, Tag 0429](https://stacks.math.columbia.edu/tag/0429)
* [Stacks Project, Tag 041X](https://stacks.math.columbia.edu/tag/041X)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 0500](https://stacks.math.columbia.edu/tag/0500)
* [Stacks Project, Tag 0506](https://stacks.math.columbia.edu/tag/0506)
* [Stacks Project, Tag 0507](https://stacks.math.columbia.edu/tag/0507)
* [Stacks Project, Tag 05UP](https://stacks.math.columbia.edu/tag/05UP)
* [Stacks Project, Tag 06FJ](https://stacks.math.columbia.edu/tag/06FJ)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06R7](https://stacks.math.columbia.edu/tag/06R7)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u w

namespace Space

/-- **Smoothness of morphisms of algebraic spaces cancels against étale morphisms.** If the
composite of `p` with an étale morphism `i` is smooth then `p` is smooth.

A pair of étale charts of `p` becomes a pair of étale charts of `p ≫ i` on composing the chart
of the target with `i`, which is étale by the definition of Stacks 03FR, and the morphism of
schemes tested on top is the same. -/
theorem isSmooth_of_comp_isEtale (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : F ⟶ G) (i : G ⟶ H)
    (hi : IsEtale B S hS i) (hpi : IsSmooth B S hS (p ≫ i)) :
    IsSmooth B S hS p := fun U V a b k ha hb hsq =>
  hpi U V a (b ≫ i) k ha (hi V b hb) (by rw [← Category.assoc, hsq, Category.assoc])

end Space

namespace Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Smoothness of the 1-morphism attached to a morphism of algebraic spaces -/

/-- **A morphism of algebraic spaces over `S` is smooth exactly when the 1-morphism of algebraic
stacks it induces is smooth.** The smooth-diagram test of **Stacks 075U** is read on the
representable source and target by **Stacks 06FM**, through the identity comparisons of
**Stacks 04SW**; what Stacks 06FM asks of the property is that it be smooth local on source and
target, which for smoothness is the smooth case of **Stacks 06FC**.

This is the mirror at smoothness of
`AlgebraicGeometry.Stack.isLocallyOfFiniteType_algebraicSpaceStackMap_iff`. -/
theorem isSmooth_algebraicSpaceStackMap_iff
    {T G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B S hS T) (hG : IsAlgebraicSpace B S hS G) (g : T ⟶ G) :
    AlgebraicStacks.IsSmooth B S hS (algebraicSpaceStackMap.{u, w} B S hS hT hG g) ↔
      Space.IsSmooth B S hS g := by
  refine Iff.trans (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS _
    (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS)
    (isAlgebraicStack_fibredCategory.{u, w} B S hS T hT)
    (isAlgebraicStack_fibredCategory.{u, w} B S hS G hG) T G hT hG
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) _) ?_
  rw [representingMap_associatedMap B S hS T G g]

/-- **The 1-morphism of algebraic stacks attached to an open immersion of algebraic spaces is
smooth.** An open immersion of algebraic spaces is étale (**Stacks 0CIP** for spaces) and an
étale morphism of algebraic spaces is smooth (**Stacks 04XX**). -/
theorem isSmooth_algebraicSpaceStackMap_of_isOpenImmersion
    {U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hV : IsAlgebraicSpace B S hS V) (hU : IsAlgebraicSpace B S hS U)
    {i : V ⟶ U} (hi : Space.IsOpenImmersion B S hS i) :
    AlgebraicStacks.IsSmooth B S hS (algebraicSpaceStackMap.{u, w} B S hS hV hU i) :=
  (isSmooth_algebraicSpaceStackMap_iff.{u, w} B S hS hV hU i).2
    (Space.isSmooth_of_isEtale B S hS hU (Space.isEtale_of_isOpenImmersion B S hS hi))

/-! ### The open substack covered by a smooth 1-morphism -/

/-- **The image on points of a smooth 1-morphism of algebraic stacks is open.** A smooth
1-morphism is flat (**Stacks 04TA**) and locally of finite presentation (**Stacks 0DNP**), and
such a 1-morphism is open on the spaces of points of Stacks 04XL by **Stacks 06R7**. -/
theorem isOpen_range_pointsMap_of_isSmooth
    {𝒱 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒱 ⟶ 𝒳)
    (hg : AlgebraicStacks.IsSmooth B S hS g) :
    @IsOpen _ (pointTopology B S hS 𝒳.val)
      (Set.range (AlgebraicStacks.pointsMap B S hS g)) := by
  let _ := pointTopology B S hS 𝒱.val
  let _ := pointTopology B S hS 𝒳.val
  exact (AlgebraicStacks.isOpenMap_pointsMap B S hS g
    (AlgebraicStacks.isFlat_of_isSmooth B S hS g hg)
    (AlgebraicStacks.isLocallyOfFinitePresentation_of_isSmooth B S hS g hg)).isOpen_range

/-- **The open substack of `𝒳` covered by a smooth 1-morphism `g : 𝒱 ⟶ 𝒳`**: the one whose set
of points is the image of `|𝒱|`, which is open: the open substack attached to that open set of
points by **Stacks 06FJ** (`AlgebraicGeometry.Stack.OpenSubstack.ofIsOpen`). -/
noncomputable def openImageSubstack {𝒱 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒱 ⟶ 𝒳)
    (hg : AlgebraicStacks.IsSmooth B S hS g) : OpenSubstack 𝒳 :=
  OpenSubstack.ofIsOpen B S hS _ (isOpen_range_pointsMap_of_isSmooth B S hS g hg)

/-- The points of `AlgebraicGeometry.Stack.openImageSubstack` are the image of the points of the
source. -/
theorem openImageSubstack_pointSet {𝒱 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒱 ⟶ 𝒳)
    (hg : AlgebraicStacks.IsSmooth B S hS g) :
    (openImageSubstack B S hS g hg).pointSet B S hS =
      Set.range (AlgebraicStacks.pointsMap B S hS g) :=
  OpenSubstack.pointSet_ofIsOpen _ (isOpen_range_pointsMap_of_isSmooth B S hS g hg)

/-! ### The factorization through the open substack -/

/-- The base change along `g` of the inclusion of the open substack covered by `g`. -/
noncomputable abbrev openImageBaseChange {𝒱 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒱 ⟶ 𝒳)
    (hg : AlgebraicStacks.IsSmooth B S hS g) :
    Bicategory.TwoCommSq g (openImageSubstack B S hS g hg).inclusion :=
  twoFibreProductSquareAlgebraicStacks B S hS g
    (openImageSubstack B S hS g hg).inclusion

/-- The base change of the inclusion of the open substack covered by `g` is an open immersion:
**Stacks 0302** for representability and **Stacks 045C** for the condition of Stacks 04XB. -/
theorem isOpenImmersion_openImageBaseChange
    {𝒱 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒱 ⟶ 𝒳)
    (hg : AlgebraicStacks.IsSmooth B S hS g) :
    AlgebraicStacks.IsOpenImmersion B S hS
      (openImageBaseChange B S hS g hg).fst := by
  -- Stacks 041X, in its fppf form, for the composition and base-change rules used below.
  have := Space.openImmersion_isLocalAtTarget_fppf.{u, u} B S hS
  have hu : Bicategory.IsTwoFibreProduct
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom
        (openImageSubstack B S hS g hg).inclusion.hom) :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom
      (openImageSubstack B S hS g hg).inclusion.hom
  refine ⟨isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS
    (openImageSubstack B S hS g hg).toAlgebraicStack.val 𝒳.val 𝒱.val
    (openImageSubstack B S hS g hg).inclusion.hom g.hom _ hu
    (openImageSubstack B S hS g hg).isOpenImmersion.1, ?_⟩
  exact hasRelativeProperty_baseChange.{u, u, u + 1} B S hS
    (Space.openImmersionProperty B S hS)
    (openImageSubstack B S hS g hg).toAlgebraicStack.val 𝒳.val 𝒱.val
    (openImageSubstack B S hS g hg).inclusion.hom g.hom _ hu
    (openImageSubstack B S hS g hg).isOpenImmersion.1
    (openImageSubstack B S hS g hg).isOpenImmersion.2

/-- The base change of the inclusion of the open substack covered by `g` is surjective: its
points are exactly the image of `|𝒱|`, so **Stacks 04XH** lifts every point of `𝒱`. -/
theorem isSurjective_openImageBaseChange {𝒱 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒱 ⟶ 𝒳)
    (hg : AlgebraicStacks.IsSmooth B S hS g) :
    IsSurjective B S hS (openImageBaseChange B S hS g hg).fst := by
  intro v
  have hpt : AlgebraicStacks.pointsMap B S hS g v ∈
      (openImageSubstack B S hS g hg).pointSet B S hS := by
    rw [openImageSubstack_pointSet B S hS g hg]
    exact ⟨v, rfl⟩
  obtain ⟨y, hy⟩ := hpt
  obtain ⟨p, hp, -⟩ := AlgebraicStacks.exists_point_of_isTwoFibreProduct B S hS
    (openImageBaseChange B S hS g hg)
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g
      (openImageSubstack B S hS g hg).inclusion) v y hy.symm
  exact ⟨p, hp⟩

/-- Every object in the image of `g` lies in the open substack covered by `g`: the base change
of the inclusion along `g` is an open immersion, surjective on points, hence essentially
surjective, and the filler of the base-change square identifies the image of each object of `𝒱`
with an object of the substack. -/
theorem property_openImageSubstack_obj
    {𝒱 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒱 ⟶ 𝒳)
    (hg : AlgebraicStacks.IsSmooth B S hS g) (x : 𝒱.val.val.obj) :
    (openImageSubstack B S hS g hg).property
      ((CatFiberedInGroupoids.homFunctor g.hom).obj x) := by
  have hess := AlgebraicStacks.essSurj_of_isOpenImmersion_of_isSurjective B S hS
    (openImageBaseChange B S hS g hg).fst
    (isOpenImmersion_openImageBaseChange B S hS g hg)
    (isSurjective_openImageBaseChange B S hS g hg)
  obtain ⟨z, ⟨e⟩⟩ := hess.mem_essImage x
  refine (openImageSubstack B S hS g hg).strictlyFull.of_iso ?_
    (((openImageBaseChange B S hS g hg).snd.hom.hom.toFunctor.obj z).property)
  exact ((CatFiberedInGroupoids.underlyingIso
      (AlgebraicStacks.toCatFiberedInGroupoids B S hS
        (openImageBaseChange B S hS g hg)).iso).app z).symm ≪≫
    (CatFiberedInGroupoids.homFunctor g.hom).mapIso e

/-- **The factorization of a smooth 1-morphism through the open substack it covers.** Its
functor is `CategoryTheory.ObjectProperty.lift` of the functor of `g`, so composing it with the
inclusion of the substack returns `g` definitionally. -/
noncomputable def openImageFactorization
    {𝒱 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒱 ⟶ 𝒳)
    (hg : AlgebraicStacks.IsSmooth B S hS g) :
    𝒱 ⟶ (openImageSubstack B S hS g hg).toAlgebraicStack :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    { toFunctor := (openImageSubstack B S hS g hg).property.lift
        (CatFiberedInGroupoids.homFunctor g.hom)
        (property_openImageSubstack_obj B S hS g hg)
      w := g.hom.hom.w })

/-- The factorization composed with the inclusion of the substack is the original
1-morphism. -/
theorem openImageFactorization_comp_inclusion
    {𝒱 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒱 ⟶ 𝒳)
    (hg : AlgebraicStacks.IsSmooth B S hS g) :
    openImageFactorization B S hS g hg ≫
      (openImageSubstack B S hS g hg).inclusion = g := rfl

/-- **The factorization is surjective.** Its composite with the inclusion is `g`, whose image on
points is the point set of the substack, and the inclusion is injective on points by
**Stacks 0500**. -/
theorem isSurjective_openImageFactorization
    {𝒱 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒱 ⟶ 𝒳)
    (hg : AlgebraicStacks.IsSmooth B S hS g) :
    IsSurjective B S hS (openImageFactorization B S hS g hg) := by
  intro y
  have hmem : AlgebraicStacks.pointsMap B S hS
      (openImageSubstack B S hS g hg).inclusion y ∈
      Set.range (AlgebraicStacks.pointsMap B S hS g) := by
    rw [← openImageSubstack_pointSet B S hS g hg]
    exact ⟨y, rfl⟩
  obtain ⟨v, hv⟩ := hmem
  refine ⟨v, pointsMap_injective_of_fullyFaithful B S hS
    (openImageSubstack B S hS g hg).inclusion ?_⟩
  have hgc : AlgebraicStacks.pointsMap B S hS g =
      AlgebraicStacks.pointsMap B S hS
          (openImageSubstack B S hS g hg).inclusion ∘
        AlgebraicStacks.pointsMap B S hS
          (openImageFactorization B S hS g hg) := by
    rw [← AlgebraicStacks.pointsMap_comp B S hS
      (openImageFactorization B S hS g hg)
      (openImageSubstack B S hS g hg).inclusion,
      openImageFactorization_comp_inclusion B S hS g hg]
  rw [hgc] at hv
  exact hv

/-- **The factorization is smooth.** The composite with the inclusion is `g`, which is smooth,
and the inclusion is an open immersion; smoothness of morphisms of algebraic spaces cancels
against open immersions by `AlgebraicGeometry.Space.isSmooth_of_comp_isEtale`, so the condition
of Stacks 04XB for smoothness cancels by
`AlgebraicGeometry.Stack.prop_of_comp_of_spaceCancel`, and **Stacks 06FM** turns it back into
the smooth-diagram criterion of **Stacks 075U**. -/
theorem isSmooth_openImageFactorization
    {𝒱 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒱 ⟶ 𝒳)
    (hg : AlgebraicStacks.IsSmooth B S hS g)
    (h𝒱 : IsRepresentableByAlgebraicSpace B S hS 𝒱.val) :
    AlgebraicStacks.IsSmooth B S hS (openImageFactorization B S hS g hg) := by
  have hrep : ∀ {𝒵 : AlgebraicStacks.{u, w} B S hS} (k : 𝒱 ⟶ 𝒵),
      IsRepresentableByAlgebraicSpaces B S hS k.hom.hom := fun {𝒵} k =>
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒵.property h𝒱 k.hom
  have hgrep := hrep g
  have hqrep := hrep (openImageFactorization B S hS g hg)
  have hgrel : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.smoothMorphismProperty B S hS) g.hom hgrep :=
    (hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS
      (fun _ _ h => Space.IsSmooth B S hS h)
      (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS)
      𝒱.property 𝒳.property g.hom hgrep).1 hg
  have hqrel : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.smoothMorphismProperty B S hS)
      (openImageFactorization B S hS g hg).hom hqrep := by
    refine prop_of_comp_of_spaceCancel B S hS (Space.smoothMorphismProperty B S hS)
      (Space.openImmersionProperty B S hS) ?_
      (openImageFactorization B S hS g hg).hom
      (openImageSubstack B S hS g hg).inclusion.hom
      (openImageSubstack B S hS g hg).isOpenImmersion.1 hgrep ?_
      (openImageSubstack B S hS g hg).isOpenImmersion.2
    · intro X' Y' Z' a b hab hb
      exact Space.isSmooth_of_comp_isEtale B S hS a.hom b.hom
        (Space.isEtale_of_isOpenImmersion B S hS hb) hab
    · exact hgrel
  exact hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u} B S hS
    (fun _ _ h => Space.IsSmooth B S hS h)
    (openImageSubstack B S hS g hg).toAlgebraicStack.property
    (openImageFactorization B S hS g hg).hom hqrep hqrel

/-! ### Stacks 05UP -/

/-- **Stacks 05UP.** Let `𝒳` be an algebraic stack over `S`, let `U` be an algebraic space over
`S` with a surjective smooth 1-morphism `f : U ⟶ 𝒳`, and let `i : V ⟶ U` be an open immersion of
presheaves on the big fppf site of `S`. Then `V` is an algebraic space over `S` and there are an
algebraic stack `𝒴` over `S`, an open immersion `j : 𝒴 ⟶ 𝒳` and a surjective smooth 1-morphism
`q : V ⟶ 𝒴` making the square `(i, f, q, j)` 2-commute.

The algebraic stack `𝒴` is the open substack of `𝒳` whose points are the image of `|V|`, and `q`
is the factorization of `V ⟶ 𝒳` through it, so the three pieces are produced from one
construction rather than chosen from an existential; the 2-commutativity is an identity. -/
@[stacks 05UP "the algebraic stack, the open immersion into the given stack and the smooth \
surjection from the open subspace, all three together with the 2-commutativity of the resulting \
square. The stack is constructed as the open substack of Stacks 04YM whose point set is the image \
of the points of the open subspace, by Stacks 06FJ"]
theorem exists_openSubstack_isOpenImmersion_smooth_surjective
    {U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B S hS U) {i : V ⟶ U}
    (hi : Space.IsOpenImmersion B S hS i)
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
    (hfsm : AlgebraicStacks.IsSmooth B S hS f)
    (_hfsurj : IsSurjective B S hS f) :
    ∃ (hV : IsAlgebraicSpace B S hS V) (𝒴 : AlgebraicStacks.{u, w} B S hS)
      (j : 𝒴 ⟶ 𝒳) (q : algebraicSpaceStack.{u, w} B S hS V hV ⟶ 𝒴),
      AlgebraicStacks.IsOpenImmersion B S hS j ∧
        AlgebraicStacks.IsSmooth B S hS q ∧
          IsSurjective B S hS q ∧
            Nonempty (algebraicSpaceStackMap.{u, w} B S hS hV hU i ≫ f ≅ q ≫ j) := by
  have hV : IsAlgebraicSpace B S hS V :=
    AlgebraicGeometry.isAlgebraicSpace_of_relativelyRepresentable B S hS i hi.1 hU
  set 𝒱 := algebraicSpaceStack.{u, w} B S hS V hV with h𝒱def
  set g : 𝒱 ⟶ 𝒳 := algebraicSpaceStackMap.{u, w} B S hS hV hU i ≫ f with hgdef
  have hg : AlgebraicStacks.IsSmooth B S hS g :=
    AlgebraicStacks.isSmooth_comp B S hS _ f
      (isSmooth_algebraicSpaceStackMap_of_isOpenImmersion.{u, w} B S hS hV hU hi) hfsm
  have h𝒱 : IsRepresentableByAlgebraicSpace B S hS 𝒱.val :=
    isRepresentableByAlgebraicSpace_fibredCategory B S hS V hV
  refine ⟨hV, (openImageSubstack B S hS g hg).toAlgebraicStack,
    (openImageSubstack B S hS g hg).inclusion,
    openImageFactorization B S hS g hg,
    (openImageSubstack B S hS g hg).isOpenImmersion,
    isSmooth_openImageFactorization B S hS g hg h𝒱,
    isSurjective_openImageFactorization B S hS g hg,
    ⟨Iso.refl _⟩⟩

end Stack

end AlgebraicGeometry

end

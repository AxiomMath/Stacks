module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeLocalCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionFppfLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.Zariski
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRelocalize
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySchemeMap
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityComp
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentedTwoFibreProductPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemePointBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemePointProductPasting
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CancelSndTwoFibreProduct

/-!
# Descent of a relative property to a 1-morphism out of a coproduct, with no chart

Let `𝒴` be a category fibred in groupoids over the big fppf site of `S`, let `W` be an object of
the site which is, in schemes, the coproduct of a family `Z i` of objects of the site, and let
`g : (Sch/W)_{fppf} ⟶ 𝒴` be a 1-morphism representable by algebraic spaces. This file proves that
a relative property of **Stacks 03YK** which is local on the source for the étale topology holds
for `g` as soon as it holds for the restriction of `g` to each summand.

Nothing is assumed about `𝒴` beyond being fibred in groupoids: in particular `𝒴` is *not*
assumed algebraic, so no smooth surjective chart of it is available. This is what
`AlgebraicGeometry.Stack.relativeProperty_of_isColimit_of_forall_relativeProperty` — the same
descent run on a chart — cannot provide, and it is the form the descent has to take when the
property being descended is one of the inputs to a criterion for algebraicity of `𝒴` itself.

## Main results

* `AlgebraicGeometry.Stack.relativeProperty_of_isColimit_of_forall`: the descent.

## Implementation notes

The relative property of **Stacks 03YK** is a condition on the base change of `g` along every
scheme-valued point of `𝒴`, so the proof fixes such a point `y : U → 𝒴` and a presheaf `T` on the
big fppf site of `U` representing that base change, and must show that the structural morphism of
the lower-shriek extension `Λ_U T` of **Stacks 03I5** has `P`. That is where the chart of the
algebraic version is replaced: the point `y` itself plays the role the chart played there.

Crossing from the site over `U` to the site over `S` is
`AlgebraicGeometry.Stack.relocalizeFibreEquivalence` together with
`AlgebraicGeometry.Stack.representingMap_relocalizeFibre`: the point is a 1-morphism
`ŷ : (Sch/U)_{fppf} ⟶ 𝒴` out of a category fibred in groupoids represented by `h_U`
(`AlgebraicGeometry.Stack.schemeSliceMap`), the extension `Λ_U T` represents the apex `𝒬` of the
canonical 2-fibre product square of `(ŷ, g)`, and the structural morphism of `Λ_U T` *is* the
morphism of representing presheaves induced by the projection `𝒬 ⟶ (Sch/U)_{fppf}`. The whole
argument then runs on morphisms of algebraic spaces over `S`.

There the summand inclusions are base changed: the apex of the 2-fibre product square of
`(𝒬 ⟶ (Sch/W)_{fppf}, (Sch/Z i)_{fppf} ⟶ (Sch/W)_{fppf})` is represented by an algebraic space
`R i` (**Stacks 0300**, the summand inclusion being representable by algebraic spaces because
both its source and its target are, **Stacks 02ZZ**), the induced morphism `R i ⟶ Λ_U T` is an
open immersion because it is a base change of the open immersion `h_{Z i} ⟶ h_W` of algebraic
spaces (**Stacks 0501** in the form `AlgebraicGeometry.Stack.hasRelativeProperty_baseChange`,
**Stacks 045C**), and the family of them is jointly surjective on points because the summand
inclusions are and because the square of representing presheaves is cartesian (**Stacks 04SD**,
**Stacks 03H4**). A jointly surjective family of open immersions is an étale covering,
**Stacks 0DF1**.

Each `R i` also represents the base change along `ŷ` of the restriction of `g` to the summand:
that is **Stacks 02XD** in the 2-category of categories fibred in groupoids,
`CategoryTheory.CatFiberedInGroupoids.isTwoFibreProduct_cancelSndSquare`, and the composite
`R i ⟶ Λ_U T ⟶ h_U` is on the nose the morphism of representing presheaves induced by the
projection of that square, by the functoriality of **Stacks 04SW**. So the hypothesis on the
restriction, base changed by **Stacks 045C** and read through **Stacks 04XB**, gives `P` of
`R i ⟶ h_U`, and source locality concludes.

## References

* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
* [Stacks Project, Tag 02ZZ](https://stacks.math.columbia.edu/tag/02ZZ)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04SD](https://stacks.math.columbia.edu/tag/04SD)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 0501](https://stacks.math.columbia.edu/tag/0501)
* [Stacks Project, Tag 0DF1](https://stacks.math.columbia.edu/tag/0DF1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The base change of a summand inclusion along a scheme-valued point -/

section Summand

variable {𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  (W : BigFppfOver B S hS) (g : schemeFibredCategory B S hS W ⟶ 𝒴)
  (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
  (hy : y ⋙ 𝒴.val.p = Over.map U.hom)
  (Z : BigFppfOver B S hS) (j : Z ⟶ W)

/-- The square which exhibits the apex of the 2-fibre product of the summand inclusion with the
projection `𝒬 ⟶ (Sch/W)_{fppf}` as a base change along the point `ŷ` of the restriction of `g`
to the summand: **Stacks 02XD** in the 2-category of categories fibred in groupoids. -/
private noncomputable def summandSquare :
    Bicategory.TwoCommSq (schemeSliceMap B S hS U y hy)
      (schemeFibredCategoryMap B S hS j ≫ g) :=
  CatFiberedInGroupoids.cancelSndSquare.{u, u, u + 1, u + 1}
    (schemeSliceMap B S hS U y hy) g (schemeFibredCategoryMap B S hS j)
    (schemeFibredCategoryMap B S hS j ≫ g) (Iso.refl _)

/-- `AlgebraicGeometry.Stack.summandSquare` is a 2-fibre product square. -/
private noncomputable def isTwoFibreProduct_summandSquare :
    Bicategory.IsTwoFibreProduct (summandSquare B S hS W g U y hy Z j) :=
  CatFiberedInGroupoids.isTwoFibreProduct_cancelSndSquare.{u, u, u + 1, u + 1}
    (schemeSliceMap B S hS U y hy) g (schemeFibredCategoryMap B S hS j)
    (schemeFibredCategoryMap B S hS j ≫ g) (Iso.refl _)

/-- The morphism of representing algebraic spaces induced by the projection of the base change of
`g` along the point onto the big fppf site of `U`. -/
private noncomputable abbrev pointProjection
    (Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eQ : StacksRepresentableCFG.EquivalenceOver
      (twoFibreSquare (schemeSliceMap B S hS U y hy) g).pt.val.p
      (presheafOfCategories (Q ⋙ typeToCat)).p) :
    Q ⟶ yoneda.obj U :=
  representingMap B S hS (twoFibreSquare (schemeSliceMap B S hS U y hy) g).pt
    (schemeSlice B S hS U) Q (yoneda.obj U) eQ (schemeSliceEquivalenceOver B S hS U)
    (twoFibreSquare (schemeSliceMap B S hS U y hy) g).fst

/-- The morphism of representing algebraic spaces induced by the projection of the base change of
`g` along the point onto the big fppf site of `W`. -/
private noncomputable abbrev coproductProjection
    (Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eQ : StacksRepresentableCFG.EquivalenceOver
      (twoFibreSquare (schemeSliceMap B S hS U y hy) g).pt.val.p
      (presheafOfCategories (Q ⋙ typeToCat)).p) :
    Q ⟶ yoneda.obj W :=
  representingMap B S hS (twoFibreSquare (schemeSliceMap B S hS U y hy) g).pt
    (schemeFibredCategory B S hS W) Q (yoneda.obj W) eQ
    (PresheafOfCategories.sliceElementsEquivalenceOver W)
    (twoFibreSquare (schemeSliceMap B S hS U y hy) g).snd

/-- The morphism of representing algebraic spaces induced by the base change of the summand
inclusion along the projection `𝒬 ⟶ (Sch/W)_{fppf}`. -/
private noncomputable abbrev summandMap
    (Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eQ : StacksRepresentableCFG.EquivalenceOver
      (twoFibreSquare (schemeSliceMap B S hS U y hy) g).pt.val.p
      (presheafOfCategories (Q ⋙ typeToCat)).p)
    (R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eR : StacksRepresentableCFG.EquivalenceOver
      (twoFibreSquare (twoFibreSquare (schemeSliceMap B S hS U y hy) g).snd
        (schemeFibredCategoryMap B S hS j)).pt.val.p
      (presheafOfCategories (R ⋙ typeToCat)).p) :
    R ⟶ Q :=
  representingMap B S hS
    (twoFibreSquare (twoFibreSquare (schemeSliceMap B S hS U y hy) g).snd
      (schemeFibredCategoryMap B S hS j)).pt
    (twoFibreSquare (schemeSliceMap B S hS U y hy) g).pt R Q eR eQ
    (twoFibreSquare (twoFibreSquare (schemeSliceMap B S hS U y hy) g).snd
      (schemeFibredCategoryMap B S hS j)).fst

/-- The morphism of representing algebraic spaces induced by the first projection of a 2-fibre
product square has `P` as soon as the base changed 1-morphism has the relative property at `P`. -/
private theorem prop_representingMap_fst_of_baseChange
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴) (R : Bicategory.TwoCommSq g f)
    (hR : Bicategory.IsTwoFibreProduct R) (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hPf : HasRelativeProperty B S hS P f hf)
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (eF : StacksRepresentableCFG.EquivalenceOver
      R.pt.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒵.val.p (presheafOfCategories (G ⋙ typeToCat)).p) :
    P (ObjectProperty.homMk (representingMap B S hS R.pt 𝒵 F G eF eG R.fst) :
      (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩) :=
  (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS P R.fst _ F G hF hG eF eG).mp
    (hasRelativeProperty_baseChange.{u, u, u + 1} B S hS P 𝒳 𝒴 𝒵 f g R hR hf hPf)

/-- The morphism of representing algebraic spaces induced by the base change of the summand
inclusion is an open immersion: the summand inclusion induces the open immersion
`h_Z ⟶ h_W` of algebraic spaces, which has the relative property of **Stacks 03YK** at open
immersions, and that property is inherited by a base change (**Stacks 045C**). -/
private theorem isOpenImmersion_summandMap
    (Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eQ : StacksRepresentableCFG.EquivalenceOver
      (twoFibreSquare (schemeSliceMap B S hS U y hy) g).pt.val.p
      (presheafOfCategories (Q ⋙ typeToCat)).p)
    (R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eR : StacksRepresentableCFG.EquivalenceOver
      (twoFibreSquare (twoFibreSquare (schemeSliceMap B S hS U y hy) g).snd
        (schemeFibredCategoryMap B S hS j)).pt.val.p
      (presheafOfCategories (R ⋙ typeToCat)).p)
    (hj : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j))
    (hQ : IsAlgebraicSpace B S hS Q) (hR : IsAlgebraicSpace B S hS R) :
    Space.IsOpenImmersion B S hS (summandMap B S hS W g U y hy Z j Q eQ R eR) := by
  have : (Space.openImmersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.openImmersion_isLocalAtTarget_fppf.{u, u} B S hS
  exact prop_representingMap_fst_of_baseChange B S hS (Space.openImmersionProperty B S hS)
    (schemeFibredCategoryMap B S hS j)
    (twoFibreSquare (schemeSliceMap B S hS U y hy) g).snd
    (twoFibreSquare (twoFibreSquare (schemeSliceMap B S hS U y hy) g).snd
      (schemeFibredCategoryMap B S hS j))
    (isTwoFibreSquare (twoFibreSquare (schemeSliceMap B S hS U y hy) g).snd
      (schemeFibredCategoryMap B S hS j))
    (isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS j)
    (hasRelativeProperty_schemeFibredCategoryMap.{u, u} B S hS
      (Space.openImmersionProperty B S hS) j
      (Space.isOpenImmersion_yoneda_map B S hS j hj)) R Q hR hQ eR eQ

/-- The square of representing algebraic spaces attached to the base change of the summand
inclusion is cartesian: **Stacks 04SD** for the canonical 2-fibre product square, with the
morphism induced by the summand inclusion recognised as its Yoneda image. -/
private theorem isPullback_summandMap
    (Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eQ : StacksRepresentableCFG.EquivalenceOver
      (twoFibreSquare (schemeSliceMap B S hS U y hy) g).pt.val.p
      (presheafOfCategories (Q ⋙ typeToCat)).p)
    (R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eR : StacksRepresentableCFG.EquivalenceOver
      (twoFibreSquare (twoFibreSquare (schemeSliceMap B S hS U y hy) g).snd
        (schemeFibredCategoryMap B S hS j)).pt.val.p
      (presheafOfCategories (R ⋙ typeToCat)).p) :
    IsPullback (summandMap B S hS W g U y hy Z j Q eQ R eR)
      (representingMap B S hS
        (twoFibreSquare (twoFibreSquare (schemeSliceMap B S hS U y hy) g).snd
          (schemeFibredCategoryMap B S hS j)).pt
        (schemeFibredCategory B S hS Z) R (yoneda.obj Z) eR
        (PresheafOfCategories.sliceElementsEquivalenceOver Z)
        (twoFibreSquare (twoFibreSquare (schemeSliceMap B S hS U y hy) g).snd
          (schemeFibredCategoryMap B S hS j)).snd)
      (coproductProjection B S hS W g U y hy Q eQ) (yoneda.map j) := by
  let : (twoFibreProductStructureFunctor B S hS
      (twoFibreSquare (schemeSliceMap B S hS U y hy) g).pt
      (schemeFibredCategory B S hS Z) (schemeFibredCategory B S hS W)
      (twoFibreSquare (schemeSliceMap B S hS U y hy) g).snd
      (schemeFibredCategoryMap B S hS j)).IsFibered :=
    (twoFibreSquare (twoFibreSquare (schemeSliceMap B S hS U y hy) g).snd
      (schemeFibredCategoryMap B S hS j)).pt.isFiberedInGroupoids.isFibered
  have h := isPullback_representingMap_twoFibreProductSquare B S hS
    (twoFibreSquare (schemeSliceMap B S hS U y hy) g).pt
    (schemeFibredCategory B S hS Z) (schemeFibredCategory B S hS W)
    Q (yoneda.obj Z) (yoneda.obj W) eQ
    (PresheafOfCategories.sliceElementsEquivalenceOver Z)
    (PresheafOfCategories.sliceElementsEquivalenceOver W)
    (twoFibreSquare (schemeSliceMap B S hS U y hy) g).snd
    (schemeFibredCategoryMap B S hS j) R eR
  rwa [representingMap_schemeFibredCategoryMap B S hS j] at h

/-- **The relative property at one summand, read on the representing algebraic spaces.** The
composite `R ⟶ 𝒬 ⟶ h_U` has `P` as soon as the restriction of `g` to the summand has the
relative property of **Stacks 03YK** at `P`: the composite is the morphism of representing
presheaves induced by the projection of `AlgebraicGeometry.Stack.summandSquare`, which is a base
change of that restriction. -/
private theorem prop_summandMap_comp_pointProjection
    (Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eQ : StacksRepresentableCFG.EquivalenceOver
      (twoFibreSquare (schemeSliceMap B S hS U y hy) g).pt.val.p
      (presheafOfCategories (Q ⋙ typeToCat)).p)
    (R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eR : StacksRepresentableCFG.EquivalenceOver
      (twoFibreSquare (twoFibreSquare (schemeSliceMap B S hS U y hy) g).snd
        (schemeFibredCategoryMap B S hS j)).pt.val.p
      (presheafOfCategories (R ⋙ typeToCat)).p)
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    (hg : IsRepresentableByAlgebraicSpaces B S hS g.hom)
    (hR : IsAlgebraicSpace B S hS R)
    (hrest : RelativeProperty.{u, u, u + 1} B S hS P
      (schemeFibredCategoryMap B S hS j ≫ g)) :
    P (ObjectProperty.homMk (summandMap B S hS W g U y hy Z j Q eQ R eR ≫
        pointProjection B S hS W g U y hy Q eQ) :
      (⟨R, hR⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) := by
  have hrep : IsRepresentableByAlgebraicSpaces B S hS
      (schemeFibredCategoryMap B S hS j ≫ g).hom :=
    isRepresentableByAlgebraicSpaces_comp B S hS (schemeFibredCategoryMap B S hS j) g
      (isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS j) hg
  have hcomp : representingMap B S hS (summandSquare B S hS W g U y hy Z j).pt
        (schemeSlice B S hS U) R (yoneda.obj U) eR (schemeSliceEquivalenceOver B S hS U)
        (summandSquare B S hS W g U y hy Z j).fst =
      summandMap B S hS W g U y hy Z j Q eQ R eR ≫
        pointProjection B S hS W g U y hy Q eQ :=
    representingMap_comp B S hS R Q (yoneda.obj U) eR eQ
      (schemeSliceEquivalenceOver B S hS U)
      (twoFibreSquare (twoFibreSquare (schemeSliceMap B S hS U y hy) g).snd
        (schemeFibredCategoryMap B S hS j)).fst
      (twoFibreSquare (schemeSliceMap B S hS U y hy) g).fst
  rw [← hcomp]
  exact prop_representingMap_fst_of_baseChange B S hS P (schemeFibredCategoryMap B S hS j ≫ g)
    (schemeSliceMap B S hS U y hy) (summandSquare B S hS W g U y hy Z j)
    (isTwoFibreProduct_summandSquare B S hS W g U y hy Z j) hrep hrest R
    (yoneda.obj U) hR (isAlgebraicSpace_yoneda B S hS U) eR (schemeSliceEquivalenceOver B S hS U)

end Summand

/-! ### The descent -/

section Descent

variable {𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} {I : Type u}
  (Z : I → BigFppfOver B S hS) (W : BigFppfOver B S hS) (jj : ∀ i, Z i ⟶ W)
  (g : schemeFibredCategory B S hS W ⟶ 𝒴)

/-- **The relative property on one base change of `g` along a scheme-valued point.** With the
apex of that base change represented by `Q`, the projection `Q ⟶ h_U` has `P` as soon as every
restriction of `g` to a summand has the relative property of **Stacks 03YK** at `P`. -/
private theorem prop_pointProjection_of_forall
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    [P.IsLocalAtSource (Space.Topology.etale.precoverage.{u, u} B S hS)]
    (hW : IsColimit (Cofan.mk ((BigFppfOver.toScheme B S hS).obj W)
      (fun i => (BigFppfOver.toScheme B S hS).map (jj i))))
    (hg : IsRepresentableByAlgebraicSpaces B S hS g.hom)
    (hf : ∀ i, RelativeProperty.{u, u, u + 1} B S hS P
      (schemeFibredCategoryMap B S hS (jj i) ≫ g))
    (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hQ : IsAlgebraicSpace B S hS Q)
    (eQ : StacksRepresentableCFG.EquivalenceOver
      (twoFibreSquare (schemeSliceMap B S hS U y hy) g).pt.val.p
      (presheafOfCategories (Q ⋙ typeToCat)).p) :
    P (ObjectProperty.homMk (pointProjection B S hS W g U y hy Q eQ) :
      (⟨Q, hQ⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) := by
  classical
  have hjOI : ∀ i, AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (jj i)) :=
    fun i => isOpenImmersion_of_isColimit_cofanMk hW i
  have hRrep : ∀ i, IsRepresentableByAlgebraicSpace B S hS
      (summandSquare B S hS W g U y hy (Z i) (jj i)).pt := fun i =>
    isRepresentableByAlgebraicSpace_twoFibreProductSquare_pt B S hS
      (schemeFibredCategoryMap B S hS (jj i))
      (twoFibreSquare (schemeSliceMap B S hS U y hy) g).snd
      (isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS (jj i))
      ⟨Q, hQ, ⟨eQ⟩⟩
  choose R hR heR using hRrep
  -- each base change of a summand inclusion is an open immersion of algebraic spaces
  have hOI : ∀ i, Space.IsOpenImmersion B S hS
      (summandMap B S hS W g U y hy (Z i) (jj i) Q eQ (R i) (heR i).some) := fun i =>
    isOpenImmersion_summandMap B S hS W g U y hy (Z i) (jj i) Q eQ (R i) (heR i).some
      (hjOI i) hQ (hR i)
  -- and the family of them is jointly surjective on points
  have hSurj : ∀ x : Space.points B S hS Q, ∃ i, ∃ r : Space.points B S hS (R i),
      Space.pointsMap B S hS (R i)
        (summandMap B S hS W g U y hy (Z i) (jj i) Q eQ (R i) (heR i).some) r = x := by
    intro x
    obtain ⟨i, t, ht⟩ := exists_mem_range_of_isColimit_cofanMk hW
      (Space.pointsToScheme B S hS W (Space.pointsMap B S hS Q
        (coproductProjection B S hS W g U y hy Q eQ) x))
    refine ⟨i, ?_⟩
    have hζ : Space.pointsMap B S hS Q (coproductProjection B S hS W g U y hy Q eQ) x =
        Space.pointsMap B S hS (yoneda.obj (Z i)) (yoneda.map (jj i))
          ((Space.pointsEquivScheme B S hS (Z i)).symm t) := by
      refine (Space.injective_pointsToScheme B S hS W ?_).symm
      rw [Space.pointsToScheme_pointsMap_yoneda]
      exact (congrArg ((BigFppfOver.toScheme B S hS).map (jj i))
        ((Space.pointsEquivScheme B S hS (Z i)).apply_symm_apply t)).trans ht
    obtain ⟨r, hr, -⟩ := Space.exists_point_of_isPullback_presheaf B S hS
      (isPullback_summandMap B S hS W g U y hy (Z i) (jj i) Q eQ (R i) (heR i).some) x _ hζ
    exact ⟨r, hr⟩
  -- so it is an étale covering of the source
  have hcov : Presieve.ofArrows (fun i => (⟨R i, hR i⟩ : AlgebraicSpaces B S hS))
      (fun i => (ObjectProperty.homMk
        (summandMap B S hS W g U y hy (Z i) (jj i) Q eQ (R i) (heR i).some) :
          (⟨R i, hR i⟩ : AlgebraicSpaces B S hS) ⟶ (⟨Q, hQ⟩ : AlgebraicSpaces B S hS))) ∈
      (Space.Topology.etale.precoverage.{u, u} B S hS) (⟨Q, hQ⟩ : AlgebraicSpaces B S hS) :=
    ⟨I, _, _, rfl, hQ, hR, Space.isEtaleCovering_of_isZariskiCovering B S hS hQ hR ⟨hOI, hSurj⟩⟩
  refine MorphismProperty.IsLocalAtSource.of_forall_comp (P := P) hcov ?_
  rintro V k ⟨i⟩
  exact prop_summandMap_comp_pointProjection B S hS W g U y hy (Z i) (jj i) Q eQ (R i)
    (heR i).some P hg (hR i) (hf i)

/-- **A 1-morphism out of a coproduct of objects of the site has a source-local relative property
as soon as its restriction to every summand has it, with no chart of the target.** Let `P` be a
property of morphisms of algebraic spaces over `S` which is stable under base change, local on
the target for the fppf topology and local on the source for the étale topology; let `W` be an
object of the big fppf site over `S` which is, in schemes, the coproduct of a family `Z i` of
objects of the site; and let `g : (Sch/W)_{fppf} ⟶ 𝒴` be a 1-morphism into a category fibred in
groupoids over the big fppf site of `S`, representable by algebraic spaces. If the restriction of
`g` along every summand inclusion has the relative property `P` of **Stacks 03YK**, then so does
`g`.

Nothing is assumed about `𝒴` beyond being fibred in groupoids. The argument is described in the
implementation notes of this file: the condition is tested at a scheme-valued point of `𝒴`, the
base change along that point is read on representing algebraic spaces, and the base changes of
the summand inclusions form a covering of its source by open subspaces each of which is a base
change of a summand. -/
theorem relativeProperty_of_isColimit_of_forall
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    [P.IsLocalAtSource (Space.Topology.etale.precoverage.{u, u} B S hS)]
    (hW : IsColimit (Cofan.mk ((BigFppfOver.toScheme B S hS).obj W)
      (fun i => (BigFppfOver.toScheme B S hS).map (jj i))))
    (hg : IsRepresentableByAlgebraicSpaces B S hS g.hom)
    (hf : ∀ i, RelativeProperty.{u, u, u + 1} B S hS P
      (schemeFibredCategoryMap B S hS (jj i) ≫ g)) :
    RelativeProperty.{u, u, u + 1} B S hS P g := by
  intro U y hy T hT he
  obtain ⟨e⟩ := he
  refine (prop_algebraicSpaceMap_iff B S hS P U T hT).mpr ?_
  rw [← representingMap_relocalizeFibre B S hS U g y T e hy]
  exact prop_pointProjection_of_forall B S hS Z W jj g P hW hg hf U y hy
    ((OverShriek.relocalizePresheafFunctor U.hom).obj T)
    (isAlgebraicSpace_viewOver B U.left.1 S U.left.2 hS U.hom T hT)
    (relocalizeFibreEquivalence B S hS U g y T e)

end Descent

end AlgebraicGeometry.Stack

end

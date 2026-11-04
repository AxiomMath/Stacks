module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothRelationPullbackStepC
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalRingDimensionSquareIndependence
public import StacksFrontier.AlgebraicGeometry.Stacks.RefinedChartSelfIntersectionPullback

/-!
# The local ring dimension invariant along a refinement of smooth charts

Let `f : U ⟶ 𝒳` be a smooth chart of a locally Noetherian algebraic stack, let `sq` present its
self-intersection `R = U ×_𝒳 U` by an algebraic space, and let `h : U' ⟶ U` be a *smooth*
refinement of the chart. The self-intersection of the refined chart `h ≫ f` is the pasted
rectangle `AlgebraicGeometry.Stack.refinedSelfIntersectionSquare`, presented by an algebraic
space `W`. This file compares the invariant `2 dim(𝒪_{U', ū'}) - dim(𝒪_{W, r})` measured on the
refined chart with the invariant `2 dim(𝒪_{U, ū}) - dim(𝒪_{R, ρ})` measured on the original one,
at the image `ρ` of `r` in `R` under the two legs of the refined relation.

## Main definitions

* `AlgebraicGeometry.Stack.selfIntersectionTargetMap`: the target map `t : R ⟶ U` of a presented
  self-intersection.
* `AlgebraicGeometry.Stack.relationRefinementFst`: the leg `W ⟶ P` of the refined relation onto
  the intermediate stage `P = U' ×_{h, U, t} R`.
* `AlgebraicGeometry.Stack.relationRefinementSnd`: the leg `P ⟶ R` of the intermediate stage onto
  the relation.
* `AlgebraicGeometry.Stack.relationRefinementMidFst` and
  `AlgebraicGeometry.Stack.relationRefinementRight`: the two `U'`-coordinates, of the
  intermediate stage and of the refined relation. The second is the source map of the refined
  relation.

## Main results

* `AlgebraicGeometry.Stack.selfIntersectionDiagonalMap_comp_selfIntersectionTargetMap`: the
  diagonal is a section of the target map.
* `AlgebraicGeometry.Stack.relationRefinementRight_comp_yoneda_map`: the source map of the
  refined relation followed by `h` is the projection onto the relation followed by the source map
  of the relation.
* `AlgebraicGeometry.Stack.relationRefinementFst_comp_relationRefinementMidFst`: the two legs
  onto the first `U'`-coordinate compose to the target map of the refined self-intersection.
* `AlgebraicGeometry.Stack.ringKrullDim_etaleLocalRing_refinement_stepC`: the dimension identity
  for a refinement of charts, in subtraction-free form.
* `AlgebraicGeometry.Stack.hasChartLocalRingDimension_refinement_iff`: the invariant measured on
  the refined chart at `r` is the invariant measured on the original chart at the image `ρ` of `r`
  in the relation.
* `AlgebraicGeometry.Stack.geometricPointMap_relationRefinement_coord_eq_of_diagonal`: at a point
  of the diagonal the two `U'`-coordinates of the refined relation agree.

## Implementation notes

The comparison assumes that the chart point is closed in its chart fibres, one condition for each
leg (`AlgebraicGeometry.Space.HasClosedChartFibreSquare`), and that the two `U'`-coordinates of
`r` agree; the second condition holds at every point of the diagonal.

Everything is stated at the canonical comparison equivalences of the two charts,
`CategoryTheory.PresheafOfCategories.sliceElementsEquivalenceOver`. The presentations of the two
relations are arbitrary.

## References

* [Stacks Project, Tag 00ON](https://stacks.math.columbia.edu/tag/00ON)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 0DS8](https://stacks.math.columbia.edu/tag/0DS8)
* [Stacks Project, Tag 0DS9](https://stacks.math.columbia.edu/tag/0DS9)
* [Stacks Project, Tag 0DSA](https://stacks.math.columbia.edu/tag/0DSA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The target map of a presented self-intersection -/

section TargetMap

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} (U : BigFppfOver B S hS)
  (f : schemeStack.{u, w} B S hS U ⟶ 𝒳) (sq : Bicategory.TwoCommSq f f)
  (R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eU : StacksRepresentableCFG.EquivalenceOver
    (schemeStack.{u, w} B S hS U).val.val.p
    (presheafOfCategories (yoneda.obj U ⋙ typeToCat)).p)
  (eR : StacksRepresentableCFG.EquivalenceOver
    sq.pt.val.val.p (presheafOfCategories (R ⋙ typeToCat)).p)

/-- The **target morphism** `t : R ⟶ U` of a presented self-intersection `R = U ×_𝒳 U`: the
morphism of representing presheaves induced by the *first* leg `pr₀` of the 2-fibre product
square. -/
noncomputable abbrev selfIntersectionTargetMap : R ⟶ yoneda.obj U :=
  representingMap B S hS sq.pt.val (schemeStack.{u, w} B S hS U).val R (yoneda.obj U) eR eU
    sq.fst.hom

/-- **The diagonal `e : U ⟶ R` of a presented self-intersection is a section of the target
morphism `t : R ⟶ U`.** -/
theorem selfIntersectionDiagonalMap_comp_selfIntersectionTargetMap
    (δ : Bicategory.TwoCommSq.PreHom (selfIntersectionDiagonalSquare B S hS U f) sq) :
    selfIntersectionDiagonalMap B S hS U f sq R eU eR δ ≫
        selfIntersectionTargetMap B S hS U f sq R eU eR = 𝟙 (yoneda.obj U) :=
  calc selfIntersectionDiagonalMap B S hS U f sq R eU eR δ ≫
        selfIntersectionTargetMap B S hS U f sq R eU eR
      = representingMap B S hS (schemeStack.{u, w} B S hS U).val
          (schemeStack.{u, w} B S hS U).val (yoneda.obj U) (yoneda.obj U) eU eU
          (δ.hom.hom ≫ sq.fst.hom) :=
        (representingMap_comp B S hS (yoneda.obj U) R (yoneda.obj U) eU eR eU
          δ.hom.hom sq.fst.hom).symm
    _ = representingMap B S hS (schemeStack.{u, w} B S hS U).val
          (schemeStack.{u, w} B S hS U).val (yoneda.obj U) (yoneda.obj U) eU eU
          (𝟙 (schemeStack.{u, w} B S hS U).val) :=
        representingMap_congr_twoIso B S hS (yoneda.obj U) (yoneda.obj U) eU eU
          (Bicategory.InducedBicategory.isoHom
            (f := δ.hom ≫ sq.fst) (g := 𝟙 (schemeStack.{u, w} B S hS U)) δ.isoFst.symm)
    _ = 𝟙 (yoneda.obj U) :=
        representingMap_id B S hS (schemeStack.{u, w} B S hS U).val (yoneda.obj U) eU

end TargetMap

/-- The Krull dimension of the étale local ring at a geometric point of a locally Noetherian
algebraic space is a natural number. -/
private theorem exists_natCast_eq_ringKrullDim_etaleLocalRing
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hN : Space.HasEtaleLocalProperty B S hS F (fun X : Scheme.{u} => IsLocallyNoetherian X))
    (x : Space.GeometricPoint B S hS F) :
    ∃ n : ℕ, ringKrullDim (Space.etaleLocalRing B S hS F x) = (n : WithBot ℕ∞) := by
  let : IsLocalRing (Space.etaleLocalRing B S hS F x) :=
    Space.isLocalRing_etaleLocalRing B S hS F hF x
  let : IsNoetherianRing (Space.etaleLocalRing B S hS F x) :=
    Space.isNoetherianRing_etaleLocalRing_of_isLocallyNoetherian B S hS F hF hN x
  exact Stacks.RegularLocalRing.KernelRegularity.exists_natCast_eq_ringKrullDim
    (Space.etaleLocalRing B S hS F x)

/-- A locally Noetherian target makes the source of a smooth map of algebraic spaces locally
Noetherian. -/
private theorem hasEtaleLocalProperty_isLocallyNoetherian_of_isSmooth
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (g : F ⟶ G) (hg : Space.IsSmooth B S hS g)
    (hN : Space.HasEtaleLocalProperty B S hS G (fun X : Scheme.{u} => IsLocallyNoetherian X)) :
    Space.HasEtaleLocalProperty B S hS F (fun X : Scheme.{u} => IsLocallyNoetherian X) :=
  Space.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hF hG g
    (Space.isLocallyOfFiniteType_of_isSmooth B S hS hg) hN

/-! ### The structural maps of the self-intersection of a refined chart -/

/-- The **first leg of the refined relation**, `pr₁ : W ⟶ P`, onto the intermediate stage
`P = U' ×_{h, U, t} R`: the morphism of representing presheaves induced by the first leg of the
square `T` of the second base change. It is a base change of `h`. -/
noncomputable abbrev relationRefinementFst
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {U U' : BigFppfOver B S hS}
    {f : schemeStack.{u, w} B S hS U ⟶ 𝒳} {h : U' ⟶ U}
    (sq : Bicategory.TwoCommSq f f)
    (Q : Bicategory.TwoCommSq (schemeStackMap.{u, w} B S hS h) sq.fst)
    (T : Bicategory.TwoCommSq (sq.pasteFst Q).snd (schemeStackMap.{u, w} B S hS h))
    (P W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eP : StacksRepresentableCFG.EquivalenceOver
      Q.pt.val.val.p (presheafOfCategories (P ⋙ typeToCat)).p)
    (eW : StacksRepresentableCFG.EquivalenceOver
      T.pt.val.val.p (presheafOfCategories (W ⋙ typeToCat)).p) :
    W ⟶ P :=
  representingMap B S hS T.pt.val Q.pt.val W P eW eP T.fst.hom

/-- The **second leg of the refined relation**, `pr₂ : P ⟶ R`, from the intermediate stage onto
the relation: the morphism of representing presheaves induced by the second leg of the square `Q`
of the first base change. It is a base change of `h` along the target map. -/
noncomputable abbrev relationRefinementSnd
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {U U' : BigFppfOver B S hS}
    {f : schemeStack.{u, w} B S hS U ⟶ 𝒳} {h : U' ⟶ U}
    (sq : Bicategory.TwoCommSq f f)
    (Q : Bicategory.TwoCommSq (schemeStackMap.{u, w} B S hS h) sq.fst)
    (R P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eR : StacksRepresentableCFG.EquivalenceOver
      sq.pt.val.val.p (presheafOfCategories (R ⋙ typeToCat)).p)
    (eP : StacksRepresentableCFG.EquivalenceOver
      Q.pt.val.val.p (presheafOfCategories (P ⋙ typeToCat)).p) :
    P ⟶ R :=
  representingMap B S hS Q.pt.val sq.pt.val P R eP eR Q.snd.hom

/-- The **first `U'`-coordinate**, `P ⟶ h_{U'}`: the other leg of the first base change. -/
noncomputable abbrev relationRefinementMidFst
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {U U' : BigFppfOver B S hS}
    {f : schemeStack.{u, w} B S hS U ⟶ 𝒳} {h : U' ⟶ U}
    (sq : Bicategory.TwoCommSq f f)
    (Q : Bicategory.TwoCommSq (schemeStackMap.{u, w} B S hS h) sq.fst)
    (P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eP : StacksRepresentableCFG.EquivalenceOver
      Q.pt.val.val.p (presheafOfCategories (P ⋙ typeToCat)).p) :
    P ⟶ yoneda.obj U' :=
  representingMap B S hS Q.pt.val (schemeStack.{u, w} B S hS U').val P (yoneda.obj U') eP
    (PresheafOfCategories.sliceElementsEquivalenceOver U') Q.fst.hom

/-- The **second `U'`-coordinate**, `W ⟶ h_{U'}`: the other leg of the second base change. This
is the *source map of the refined relation*, that is
`AlgebraicGeometry.Stack.selfIntersectionSourceMap` of the pasted rectangle
`AlgebraicGeometry.Stack.refinedSelfIntersectionSquare`, whose second leg is `T.snd`. -/
noncomputable abbrev relationRefinementRight
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {U U' : BigFppfOver B S hS}
    {f : schemeStack.{u, w} B S hS U ⟶ 𝒳} {h : U' ⟶ U}
    (sq : Bicategory.TwoCommSq f f)
    (Q : Bicategory.TwoCommSq (schemeStackMap.{u, w} B S hS h) sq.fst)
    (T : Bicategory.TwoCommSq (sq.pasteFst Q).snd (schemeStackMap.{u, w} B S hS h))
    (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eW : StacksRepresentableCFG.EquivalenceOver
      T.pt.val.val.p (presheafOfCategories (W ⋙ typeToCat)).p) :
    W ⟶ yoneda.obj U' :=
  representingMap B S hS T.pt.val (schemeStack.{u, w} B S hS U').val W (yoneda.obj U') eW
    (PresheafOfCategories.sliceElementsEquivalenceOver U') T.snd.hom

/-! ### The dimension comparison for a refinement of charts -/

section Refinement

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} {U U' : BigFppfOver B S hS}
  {f : schemeStack.{u, w} B S hS U ⟶ 𝒳} {h : U' ⟶ U}
  (sq : Bicategory.TwoCommSq f f)
  (Q : Bicategory.TwoCommSq (schemeStackMap.{u, w} B S hS h) sq.fst)
  (T : Bicategory.TwoCommSq (sq.pasteFst Q).snd (schemeStackMap.{u, w} B S hS h))
  (R P W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eR : StacksRepresentableCFG.EquivalenceOver
    sq.pt.val.val.p (presheafOfCategories (R ⋙ typeToCat)).p)
  (eP : StacksRepresentableCFG.EquivalenceOver
    Q.pt.val.val.p (presheafOfCategories (P ⋙ typeToCat)).p)
  (eW : StacksRepresentableCFG.EquivalenceOver
    T.pt.val.val.p (presheafOfCategories (W ⋙ typeToCat)).p)

/-- The presenting algebraic space of the self-intersection of a smooth chart of a locally
Noetherian stack has the étale local property of being locally Noetherian. -/
private theorem hasEtaleLocalProperty_isLocallyNoetherian_selfIntersection
    (eR : StacksRepresentableCFG.EquivalenceOver
      sq.pt.val.val.p (presheafOfCategories (R ⋙ typeToCat)).p)
    (hf : AlgebraicStacks.IsSmooth B S hS f) (hsq : Bicategory.IsTwoFibreProduct sq)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳) (hR : IsAlgebraicSpace B S hS R) :
    Space.HasEtaleLocalProperty B S hS R (fun X : Scheme.{u} => IsLocallyNoetherian X) :=
  hasEtaleLocalProperty_isLocallyNoetherian_of_isSmooth B S hS hR
    (isAlgebraicSpace_yoneda B S hS U) _
    (isSmooth_selfIntersectionSourceMap B S hS U f sq R
      (PresheafOfCategories.sliceElementsEquivalenceOver U) eR hf hsq hR)
    (hasEtaleLocalProperty_isLocallyNoetherian_chart B S hS U f hf h𝒳)

/-- **The source map of the refined relation, followed by `h`, is the projection onto the
relation followed by the source map of the relation.**

```
W --- pr₁ ≫ pr₂ ---> R
|                    |
right                s
↓                    ↓
h_{U'} --- h ------> h_U
```
-/
theorem relationRefinementRight_comp_yoneda_map :
    relationRefinementRight B S hS sq Q T W eW ≫ yoneda.map h =
      relationRefinementFst B S hS sq Q T P W eP eW ≫
        (relationRefinementSnd B S hS sq Q R P eR eP ≫
          selfIntersectionSourceMap B S hS U f sq R
            (PresheafOfCategories.sliceElementsEquivalenceOver U) eR) := by
  have hiso := representingMap_congr_twoIso B S hS W (yoneda.obj U) eW
    (PresheafOfCategories.sliceElementsEquivalenceOver U)
    (Bicategory.InducedBicategory.isoHom (f := T.fst ≫ (sq.pasteFst Q).snd)
      (g := T.snd ≫ schemeStackMap.{u, w} B S hS h) T.iso)
  have ecomp1 := representingMap_comp (𝒜 := T.pt.val) (ℬ := Q.pt.val)
    (𝒞 := (schemeStack.{u, w} B S hS U).val) B S hS W P (yoneda.obj U) eW eP
    (PresheafOfCategories.sliceElementsEquivalenceOver U) T.fst.hom (sq.pasteFst Q).snd.hom
  have ecomp2 := representingMap_comp (𝒜 := T.pt.val)
    (ℬ := (schemeStack.{u, w} B S hS U').val) (𝒞 := (schemeStack.{u, w} B S hS U).val)
    B S hS W (yoneda.obj U') (yoneda.obj U) eW
    (PresheafOfCategories.sliceElementsEquivalenceOver U')
    (PresheafOfCategories.sliceElementsEquivalenceOver U) T.snd.hom
    (schemeStackMap.{u, w} B S hS h).hom
  have step1 := congrArg (fun k => relationRefinementRight B S hS sq Q T W eW ≫ k)
    (representingMap_schemeStackMap.{u, w} B S hS h)
  have step2 := congrArg (fun k => relationRefinementFst B S hS sq Q T P W eP eW ≫ k)
    (representingMap_pasteFst_snd B S hS sq Q R P eR eP)
  exact step1.symm.trans (ecomp2.symm.trans (hiso.symm.trans (ecomp1.trans step2)))

/-- **The two legs of the refined relation compose to the target map of the refined
self-intersection.** -/
theorem relationRefinementFst_comp_relationRefinementMidFst :
    relationRefinementFst B S hS sq Q T P W eP eW ≫ relationRefinementMidFst B S hS sq Q P eP =
      selfIntersectionTargetMap B S hS U' (schemeStackMap.{u, w} B S hS h ≫ f)
        (refinedSelfIntersectionSquare B S hS sq Q T) W
        (PresheafOfCategories.sliceElementsEquivalenceOver U') eW := by
  exact (representingMap_comp (𝒜 := T.pt.val) (ℬ := Q.pt.val)
    (𝒞 := (schemeStack.{u, w} B S hS U').val) B S hS W P (yoneda.obj U') eW eP
    (PresheafOfCategories.sliceElementsEquivalenceOver U') T.fst.hom Q.fst.hom).symm

/-- **At a point of the diagonal the two `U'`-coordinates of the refined relation agree**, both
being the point of the chart it comes from. -/
theorem geometricPointMap_relationRefinement_coord_eq_of_diagonal
    (δ' : Bicategory.TwoCommSq.PreHom
      (selfIntersectionDiagonalSquare B S hS U' (schemeStackMap.{u, w} B S hS h ≫ f))
      (refinedSelfIntersectionSquare B S hS sq Q T))
    (ν : Space.GeometricPoint B S hS (yoneda.obj U')) :
    Space.geometricPointMap (relationRefinementMidFst B S hS sq Q P eP)
        (Space.geometricPointMap (relationRefinementFst B S hS sq Q T P W eP eW)
          (Space.geometricPointMap (selfIntersectionDiagonalMap B S hS U'
            (schemeStackMap.{u, w} B S hS h ≫ f) (refinedSelfIntersectionSquare B S hS sq Q T)
            W (PresheafOfCategories.sliceElementsEquivalenceOver U') eW δ') ν)) =
      Space.geometricPointMap (relationRefinementRight B S hS sq Q T W eW)
        (Space.geometricPointMap (selfIntersectionDiagonalMap B S hS U'
          (schemeStackMap.{u, w} B S hS h ≫ f) (refinedSelfIntersectionSquare B S hS sq Q T)
          W (PresheafOfCategories.sliceElementsEquivalenceOver U') eW δ') ν) := by
  have htgt : selfIntersectionDiagonalMap B S hS U' (schemeStackMap.{u, w} B S hS h ≫ f)
        (refinedSelfIntersectionSquare B S hS sq Q T) W
        (PresheafOfCategories.sliceElementsEquivalenceOver U') eW δ' ≫
      (relationRefinementFst B S hS sq Q T P W eP eW ≫
        relationRefinementMidFst B S hS sq Q P eP) = 𝟙 (yoneda.obj U') :=
    (congrArg (fun k => selfIntersectionDiagonalMap B S hS U'
        (schemeStackMap.{u, w} B S hS h ≫ f) (refinedSelfIntersectionSquare B S hS sq Q T) W
        (PresheafOfCategories.sliceElementsEquivalenceOver U') eW δ' ≫ k)
      (relationRefinementFst_comp_relationRefinementMidFst B S hS sq Q T P W eP eW)).trans
      (selfIntersectionDiagonalMap_comp_selfIntersectionTargetMap B S hS U'
        (schemeStackMap.{u, w} B S hS h ≫ f) (refinedSelfIntersectionSquare B S hS sq Q T) W
        (PresheafOfCategories.sliceElementsEquivalenceOver U') eW δ')
  have hsrc : selfIntersectionDiagonalMap B S hS U' (schemeStackMap.{u, w} B S hS h ≫ f)
        (refinedSelfIntersectionSquare B S hS sq Q T) W
        (PresheafOfCategories.sliceElementsEquivalenceOver U') eW δ' ≫
      relationRefinementRight B S hS sq Q T W eW = 𝟙 (yoneda.obj U') :=
    selfIntersectionDiagonalMap_comp_selfIntersectionSourceMap B S hS U'
      (schemeStackMap.{u, w} B S hS h ≫ f) (refinedSelfIntersectionSquare B S hS sq Q T) W
      (PresheafOfCategories.sliceElementsEquivalenceOver U') eW δ'
  exact (congrArg (fun k => Space.geometricPointMap k ν) htgt).trans
    (congrArg (fun k => Space.geometricPointMap k ν) hsrc).symm

/-- **The dimension identity for a refinement of smooth charts**, in the subtraction-free
form

`dim(𝒪_{U', ū'}) + dim(𝒪_{U', ū'}) + dim(𝒪_{R, ρ})
    = dim(𝒪_{U, h(ū')}) + dim(𝒪_{U, h(ū')}) + dim(𝒪_{W, r})`,

which is `2 dim(𝒪_{U', ū'}) - dim(𝒪_{W, r}) = 2 dim(𝒪_{U, h(ū')}) - dim(𝒪_{R, ρ})` with the two
differences cleared, `ringKrullDim` being valued in `WithBot ℕ∞`. Here `ū'` is the second
`U'`-coordinate of the point `r` of the refined relation and `ρ` is its image in the relation.

The hypothesis `hcoord` identifies the two `U'`-coordinates of `r`, and `hcl₁`, `hcl₂` are the
closedness of the chart point in its chart fibres, one for each leg. -/
theorem ringKrullDim_etaleLocalRing_refinement_stepC
    (hf : AlgebraicStacks.IsSmooth B S hS f) (hsq : Bicategory.IsTwoFibreProduct sq)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (hhsm : Space.IsSmooth B S hS (yoneda.map h))
    (hQ : Bicategory.IsTwoFibreProduct Q) (hT : Bicategory.IsTwoFibreProduct T)
    (hR : IsAlgebraicSpace B S hS R) (hP : IsAlgebraicSpace B S hS P)
    (hW : IsAlgebraicSpace B S hS W)
    (r : Space.GeometricPoint B S hS W)
    (hcoord : Space.geometricPointMap (relationRefinementMidFst B S hS sq Q P eP)
        (Space.geometricPointMap (relationRefinementFst B S hS sq Q T P W eP eW) r) =
      Space.geometricPointMap (relationRefinementRight B S hS sq Q T W eW) r)
    (hcl₁ : Space.HasClosedChartFibreSquare B S hS (yoneda.map h)
      (relationRefinementFst B S hS sq Q T P W eP eW)
      (relationRefinementRight B S hS sq Q T W eW) r)
    (hcl₂ : Space.HasClosedChartFibreSquare B S hS (yoneda.map h)
      (relationRefinementSnd B S hS sq Q R P eR eP)
      (relationRefinementMidFst B S hS sq Q P eP)
      (Space.geometricPointMap (relationRefinementFst B S hS sq Q T P W eP eW) r)) :
    ringKrullDim (Space.etaleLocalRing B S hS (yoneda.obj U')
          (Space.geometricPointMap (relationRefinementRight B S hS sq Q T W eW) r)) +
        ringKrullDim (Space.etaleLocalRing B S hS (yoneda.obj U')
          (Space.geometricPointMap (relationRefinementRight B S hS sq Q T W eW) r)) +
      ringKrullDim (Space.etaleLocalRing B S hS R
        (Space.geometricPointMap (relationRefinementSnd B S hS sq Q R P eR eP)
          (Space.geometricPointMap (relationRefinementFst B S hS sq Q T P W eP eW) r))) =
    ringKrullDim (Space.etaleLocalRing B S hS (yoneda.obj U)
            (Space.geometricPointMap (yoneda.map h)
              (Space.geometricPointMap (relationRefinementRight B S hS sq Q T W eW) r))) +
          ringKrullDim (Space.etaleLocalRing B S hS (yoneda.obj U)
            (Space.geometricPointMap (yoneda.map h)
              (Space.geometricPointMap (relationRefinementRight B S hS sq Q T W eW) r))) +
        ringKrullDim (Space.etaleLocalRing B S hS W r) := by
  have hUy : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hUy' : IsAlgebraicSpace B S hS (yoneda.obj U') := isAlgebraicSpace_yoneda B S hS U'
  have hNU : Space.HasEtaleLocalProperty B S hS (yoneda.obj U)
      (fun X : Scheme.{u} => IsLocallyNoetherian X) :=
    hasEtaleLocalProperty_isLocallyNoetherian_chart B S hS U f hf h𝒳
  have hNR := hasEtaleLocalProperty_isLocallyNoetherian_selfIntersection B S hS sq R eR hf hsq
    h𝒳 hR
  exact Space.ringKrullDim_etaleLocalRing_stepC_isPullback_of_isClosed B S hS hUy hUy' hR hP hW
    (yoneda.map h)
    (selfIntersectionSourceMap B S hS U f sq R
      (PresheafOfCategories.sliceElementsEquivalenceOver U) eR)
    (selfIntersectionTargetMap B S hS U f sq R
      (PresheafOfCategories.sliceElementsEquivalenceOver U) eR)
    (relationRefinementSnd B S hS sq Q R P eR eP)
    (relationRefinementMidFst B S hS sq Q P eP)
    (relationRefinementFst B S hS sq Q T P W eP eW)
    (relationRefinementRight B S hS sq Q T W eW)
    (isPullback_representingMap_refinementTargetBaseChange.{u, w} B S hS sq hQ R P hR eR eP).flip
    (isPullback_representingMap_refinementSourceBaseChange.{u, w} B S hS sq Q hT R P W hP
      eR eP eW)
    hhsm hNU hNR r _ rfl hcoord hcl₁ hcl₂

/-- **The local ring dimension invariant is unchanged by a smooth refinement of the chart.** At a
geometric point `r` of the self-intersection of the refined chart `h ≫ f` whose two
`U'`-coordinates agree, the invariant `2 dim(𝒪_{U', ū'}) - dim(𝒪_{W, r})` measured by the refined
chart equals the invariant `2 dim(𝒪_{U, ū}) - dim(𝒪_{R, ρ})` measured by the original chart at
the image `ρ` of `r` in the relation, whose image under the source map of the relation is
`h(ū')`. The hypotheses `hcoord`, `hcl₁` and `hcl₂` are those of
`AlgebraicGeometry.Stack.ringKrullDim_etaleLocalRing_refinement_stepC`. -/
theorem hasChartLocalRingDimension_refinement_iff
    (hf : AlgebraicStacks.IsSmooth B S hS f) (hsq : Bicategory.IsTwoFibreProduct sq)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (hhsm : Space.IsSmooth B S hS (yoneda.map h))
    (hQ : Bicategory.IsTwoFibreProduct Q) (hT : Bicategory.IsTwoFibreProduct T)
    (hR : IsAlgebraicSpace B S hS R) (hP : IsAlgebraicSpace B S hS P)
    (hW : IsAlgebraicSpace B S hS W)
    (r : Space.GeometricPoint B S hS W)
    (hcoord : Space.geometricPointMap (relationRefinementMidFst B S hS sq Q P eP)
        (Space.geometricPointMap (relationRefinementFst B S hS sq Q T P W eP eW) r) =
      Space.geometricPointMap (relationRefinementRight B S hS sq Q T W eW) r)
    (hcl₁ : Space.HasClosedChartFibreSquare B S hS (yoneda.map h)
      (relationRefinementFst B S hS sq Q T P W eP eW)
      (relationRefinementRight B S hS sq Q T W eW) r)
    (hcl₂ : Space.HasClosedChartFibreSquare B S hS (yoneda.map h)
      (relationRefinementSnd B S hS sq Q R P eR eP)
      (relationRefinementMidFst B S hS sq Q P eP)
      (Space.geometricPointMap (relationRefinementFst B S hS sq Q T P W eP eW) r))
    (d : ℤ) :
    HasChartLocalRingDimension B S hS U' (schemeStackMap.{u, w} B S hS h ≫ f)
        (refinedSelfIntersectionSquare B S hS sq Q T) W
        (PresheafOfCategories.sliceElementsEquivalenceOver U') eW r d ↔
      HasChartLocalRingDimension B S hS U f sq R
        (PresheafOfCategories.sliceElementsEquivalenceOver U) eR
        (Space.geometricPointMap (relationRefinementSnd B S hS sq Q R P eR eP)
          (Space.geometricPointMap (relationRefinementFst B S hS sq Q T P W eP eW) r)) d := by
  have hUy : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hUy' : IsAlgebraicSpace B S hS (yoneda.obj U') := isAlgebraicSpace_yoneda B S hS U'
  have key := ringKrullDim_etaleLocalRing_refinement_stepC.{u, w} B S hS sq Q T R P W eR eP eW
    hf hsq h𝒳 hhsm hQ hT hR hP hW r hcoord hcl₁ hcl₂
  have hchart : Space.geometricPointMap
        (selfIntersectionSourceMap B S hS U f sq R
          (PresheafOfCategories.sliceElementsEquivalenceOver U) eR)
        (Space.geometricPointMap (relationRefinementSnd B S hS sq Q R P eR eP)
          (Space.geometricPointMap (relationRefinementFst B S hS sq Q T P W eP eW) r)) =
      Space.geometricPointMap (yoneda.map h)
        (Space.geometricPointMap (relationRefinementRight B S hS sq Q T W eW) r) :=
    (congrArg (fun k => Space.geometricPointMap k r)
      (relationRefinementRight_comp_yoneda_map.{u, w} B S hS sq Q T R P W eR eP eW)).symm
  have hNU : Space.HasEtaleLocalProperty B S hS (yoneda.obj U)
      (fun X : Scheme.{u} => IsLocallyNoetherian X) :=
    hasEtaleLocalProperty_isLocallyNoetherian_chart B S hS U f hf h𝒳
  have hNR := hasEtaleLocalProperty_isLocallyNoetherian_selfIntersection B S hS sq R eR hf hsq
    h𝒳 hR
  have hNU' := hasEtaleLocalProperty_isLocallyNoetherian_of_isSmooth B S hS hUy' hUy _ hhsm hNU
  have hq : Space.IsSmooth B S hS (relationRefinementSnd B S hS sq Q R P eR eP) :=
    Space.isSmooth_fst_of_isPullback B S hS hR hUy' hUy hP
      (isPullback_representingMap_refinementTargetBaseChange.{u, w} B S hS sq hQ R P hR
        eR eP).flip hhsm
  have hNP := hasEtaleLocalProperty_isLocallyNoetherian_of_isSmooth B S hS hP hR _ hq hNR
  have hp : Space.IsSmooth B S hS (relationRefinementFst B S hS sq Q T P W eP eW) :=
    Space.isSmooth_fst_of_isPullback B S hS hP hUy' hUy hW
      (isPullback_representingMap_refinementSourceBaseChange.{u, w} B S hS sq Q hT R P W hP
        eR eP eW) hhsm
  have hNW := hasEtaleLocalProperty_isLocallyNoetherian_of_isSmooth B S hS hW hP _ hp hNP
  obtain ⟨a', ha'⟩ := exists_natCast_eq_ringKrullDim_etaleLocalRing B S hS hUy' hNU'
    (Space.geometricPointMap (relationRefinementRight B S hS sq Q T W eW) r)
  obtain ⟨b', hb'⟩ := exists_natCast_eq_ringKrullDim_etaleLocalRing B S hS hW hNW r
  obtain ⟨a, ha⟩ := exists_natCast_eq_ringKrullDim_etaleLocalRing B S hS hUy hNU
    (Space.geometricPointMap (yoneda.map h)
      (Space.geometricPointMap (relationRefinementRight B S hS sq Q T W eW) r))
  obtain ⟨b, hb⟩ := exists_natCast_eq_ringKrullDim_etaleLocalRing B S hS hR hNR
    (Space.geometricPointMap (relationRefinementSnd B S hS sq Q R P eR eP)
      (Space.geometricPointMap (relationRefinementFst B S hS sq Q T P W eP eW) r))
  have ha₂ : ringKrullDim (chartEtaleLocalRing B S hS U f sq R
        (PresheafOfCategories.sliceElementsEquivalenceOver U) eR
        (Space.geometricPointMap (relationRefinementSnd B S hS sq Q R P eR eP)
          (Space.geometricPointMap (relationRefinementFst B S hS sq Q T P W eP eW) r)))
      = (a : WithBot ℕ∞) :=
    (congrArg (fun x => ringKrullDim (Space.etaleLocalRing B S hS (yoneda.obj U) x)) hchart).trans
      ha
  have hinv : 2 * (a' : ℤ) - (b' : ℤ) = 2 * (a : ℤ) - (b : ℤ) :=
    two_mul_sub_eq_two_mul_sub_of_add_add_eq ha hb ha' hb' key
  constructor
  · rintro ⟨m, n, hm, hn, hd⟩
    refine ⟨a, b, ha₂, hb, ?_⟩
    have hma : m = a' := by exact_mod_cast hm.symm.trans ha'
    have hnb : n = b' := by exact_mod_cast hn.symm.trans hb'
    rw [← hd, hma, hnb, hinv]
  · rintro ⟨m, n, hm, hn, hd⟩
    refine ⟨a', b', ha', hb', ?_⟩
    have hma : m = a := by exact_mod_cast hm.symm.trans ha₂
    have hnb : n = b := by exact_mod_cast hn.symm.trans hb
    rw [← hd, hma, hnb, ← hinv]

end Refinement

end AlgebraicGeometry.Stack

end

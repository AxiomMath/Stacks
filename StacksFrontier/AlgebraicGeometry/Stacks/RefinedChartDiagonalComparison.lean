module

public import StacksFrontier.AlgebraicGeometry.Stacks.RefinedChartLocalRingDimension
public import StacksFrontier.CategoryTheory.TwoFibreProduct.PasteOuterFunctorial
public import StacksFrontier.CategoryTheory.TwoFibreProduct.PastingFunctorial

/-!
# The diagonal of a refined self-intersection lies over the diagonal (Stacks 0DS9)

Let `f : U ⟶ 𝒳` be a chart of an algebraic stack with relation `R`, and let `h : U' ⟶ U` be a
refinement of it, with refined relation `W`. The diagonal `h_{U'} ⟶ W` of the refined
self-intersection, followed by the projection `W ⟶ R`, is `h` followed by the diagonal
`h_U ⟶ R`. Consequently, at the diagonal point above `ν'`, the invariant of Stacks 0DSA measured
on the refined chart is the invariant measured on the original chart at the diagonal point above
`h(ν')`.

## Main definitions

* `AlgebraicGeometry.Stack.refinedDiagonalBasePreHom`: the comparison of the reassociated
  tautological square of the refined chart with the tautological square of the original chart,
  by `schemeStackMap h`.

## Main results

* `AlgebraicGeometry.Stack.selfIntersectionDiagonalMap_comp_relationRefinementProj`: the diagonal
  of the refined self-intersection, followed by the projection onto the relation, is `h` followed
  by the diagonal of the relation.
* `AlgebraicGeometry.Stack.geometricPointMap_relationRefinementSnd_diagonal`: the same at a
  geometric point.
* `AlgebraicGeometry.Stack.hasChartLocalRingDimension_refinement_diagonal_iff`: the invariant
  measured on the refined chart at the diagonal point above `ν'` is the invariant measured on the
  original chart at the diagonal point above `h(ν')`.
* `AlgebraicGeometry.Stack.hasRelationLocalRingDimension_refinement_diagonal_iff`: the same for
  `AlgebraicGeometry.Stack.HasRelationLocalRingDimension`.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 0DS9](https://stacks.math.columbia.edu/tag/0DS9)
* [Stacks Project, Tag 0DSA](https://stacks.math.columbia.edu/tag/0DSA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Diagonal

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

/-- The pre-morphism, with underlying 1-morphism `schemeStackMap h` and the unitors as
comparison 2-cells, from the reassociated tautological square
`CategoryTheory.Bicategory.pasteOuterSq (schemeStackMap h) (TwoCommSq.lower Z)` of the refined
chart `h ≫ f` to the tautological square of `f`. -/
def refinedDiagonalBasePreHom :
    Bicategory.TwoCommSq.PreHom
      (Bicategory.pasteOuterSq (schemeStackMap.{u, w} B S hS h)
        (Bicategory.TwoCommSq.lower
          (selfIntersectionDiagonalSquare B S hS U' (schemeStackMap.{u, w} B S hS h ≫ f))))
      (selfIntersectionDiagonalSquare B S hS U f) where
  hom := schemeStackMap.{u, w} B S hS h
  isoFst := (Bicategory.leftUnitor (schemeStackMap.{u, w} B S hS h)).trans
    (Bicategory.rightUnitor (schemeStackMap.{u, w} B S hS h)).symm
  isoSnd := (Bicategory.leftUnitor (schemeStackMap.{u, w} B S hS h)).trans
    (Bicategory.rightUnitor (schemeStackMap.{u, w} B S hS h)).symm
  compat := by
    dsimp [Bicategory.pasteOuterSq, selfIntersectionDiagonalSquare,
      Bicategory.TwoCommSq.lower, Bicategory.TwoCommSq.postcomposeSnd]
    simp only [Bicategory.whiskerLeftIso_hom, Bicategory.InducedBicategory.bicategory_Hom,
      Iso.refl_hom, Bicategory.id_whiskerLeft, Category.id_comp, Iso.hom_inv_id]
    bicategory

/-- The diagonal `e' : h_{U'} ⟶ W` of the refined self-intersection, followed by the
projection `W ⟶ P ⟶ R` onto the relation, is `h` followed by the diagonal `e : h_U ⟶ R` of the
relation. -/
theorem selfIntersectionDiagonalMap_comp_relationRefinementProj
    (hsq : Bicategory.IsTwoFibreProduct sq)
    (δ : Bicategory.TwoCommSq.PreHom (selfIntersectionDiagonalSquare B S hS U f) sq)
    (δ' : Bicategory.TwoCommSq.PreHom
      (selfIntersectionDiagonalSquare B S hS U' (schemeStackMap.{u, w} B S hS h ≫ f))
      (refinedSelfIntersectionSquare B S hS sq Q T)) :
    selfIntersectionDiagonalMap B S hS U' (schemeStackMap.{u, w} B S hS h ≫ f)
          (refinedSelfIntersectionSquare B S hS sq Q T) W
          (PresheafOfCategories.sliceElementsEquivalenceOver U') eW δ' ≫
        (relationRefinementFst B S hS sq Q T P W eP eW ≫
          relationRefinementSnd B S hS sq Q R P eR eP) =
      yoneda.map h ≫ selfIntersectionDiagonalMap B S hS U f sq R
        (PresheafOfCategories.sliceElementsEquivalenceOver U) eR δ := by
  obtain ⟨θ, -, -⟩ := Bicategory.twoFibreProductPreHom_rel hsq
    ((Bicategory.TwoCommSq.PreHom.pasteOuter
      (Bicategory.lowerPreHom
        (selfIntersectionDiagonalSquare B S hS U' (schemeStackMap.{u, w} B S hS h ≫ f))
        δ')).comp (Bicategory.pasteFstOuterPreHom sq Q))
    ((refinedDiagonalBasePreHom B S hS).comp δ)
  have θ' : (δ'.hom ≫ T.fst) ≫ Q.snd ≅
      schemeStackMap.{u, w} B S hS h ≫ δ.hom := θ
  have hiso := representingMap_congr_twoIso B S hS (yoneda.obj U') R
    (PresheafOfCategories.sliceElementsEquivalenceOver U') eR
    (Bicategory.InducedBicategory.isoHom
      (f := (δ'.hom ≫ T.fst) ≫ Q.snd)
      (g := schemeStackMap.{u, w} B S hS h ≫ δ.hom) θ')
  have splitL1 := representingMap_comp (𝒜 := (schemeStack.{u, w} B S hS U').val)
    (ℬ := Q.pt.val) (𝒞 := sq.pt.val) B S hS (yoneda.obj U') P R
    (PresheafOfCategories.sliceElementsEquivalenceOver U') eP eR
    (δ'.hom.hom ≫ T.fst.hom) Q.snd.hom
  have splitL2 := representingMap_comp (𝒜 := (schemeStack.{u, w} B S hS U').val)
    (ℬ := T.pt.val) (𝒞 := Q.pt.val) B S hS (yoneda.obj U') W P
    (PresheafOfCategories.sliceElementsEquivalenceOver U') eW eP δ'.hom.hom T.fst.hom
  have splitR := representingMap_comp (𝒜 := (schemeStack.{u, w} B S hS U').val)
    (ℬ := (schemeStack.{u, w} B S hS U).val) (𝒞 := sq.pt.val) B S hS
    (yoneda.obj U') (yoneda.obj U) R
    (PresheafOfCategories.sliceElementsEquivalenceOver U')
    (PresheafOfCategories.sliceElementsEquivalenceOver U) eR
    (schemeStackMap.{u, w} B S hS h).hom δ.hom.hom
  have eL := splitL1.trans
    (congrArg (fun k : yoneda.obj U' ⟶ P =>
      k ≫ relationRefinementSnd B S hS sq Q R P eR eP) splitL2)
  have eR₀ := splitR.trans
    (congrArg (fun k : yoneda.obj U' ⟶ yoneda.obj U =>
      k ≫ selfIntersectionDiagonalMap B S hS U f sq R
        (PresheafOfCategories.sliceElementsEquivalenceOver U) eR δ)
      (representingMap_schemeStackMap.{u, w} B S hS h))
  exact (Category.assoc _ _ _).symm.trans
    (eL.symm.trans (hiso.trans eR₀))

/-- The image in the relation of the diagonal point above a geometric point `ν̄'` of `U'` of
the refined relation is the diagonal point above `h(ν̄')`. -/
theorem geometricPointMap_relationRefinementSnd_diagonal
    (hsq : Bicategory.IsTwoFibreProduct sq)
    (δ : Bicategory.TwoCommSq.PreHom (selfIntersectionDiagonalSquare B S hS U f) sq)
    (δ' : Bicategory.TwoCommSq.PreHom
      (selfIntersectionDiagonalSquare B S hS U' (schemeStackMap.{u, w} B S hS h ≫ f))
      (refinedSelfIntersectionSquare B S hS sq Q T))
    (ν : Space.GeometricPoint B S hS (yoneda.obj U')) :
    Space.geometricPointMap (relationRefinementSnd B S hS sq Q R P eR eP)
        (Space.geometricPointMap (relationRefinementFst B S hS sq Q T P W eP eW)
          (Space.geometricPointMap (selfIntersectionDiagonalMap B S hS U'
            (schemeStackMap.{u, w} B S hS h ≫ f) (refinedSelfIntersectionSquare B S hS sq Q T)
            W (PresheafOfCategories.sliceElementsEquivalenceOver U') eW δ') ν)) =
      Space.geometricPointMap (selfIntersectionDiagonalMap B S hS U f sq R
          (PresheafOfCategories.sliceElementsEquivalenceOver U) eR δ)
        (Space.geometricPointMap (yoneda.map h) ν) :=
  congrArg (fun k => Space.geometricPointMap k ν)
    (selfIntersectionDiagonalMap_comp_relationRefinementProj.{u, w} B S hS sq Q T R P W
      eR eP eW hsq δ δ')

/-- For a smooth chart `f : U ⟶ 𝒳` of a locally Noetherian algebraic stack, a smooth refinement
`h : U' ⟶ U` of it, and a geometric point `ν̄'` of `U'` whose chart points are closed in their
chart fibres, the invariant of Stacks 0DSA

`2 dim(𝒪_{U', ν̄'}) - dim(𝒪_{W, e'(ν̄')})`

measured on the refined chart `h ≫ f` equals the invariant

`2 dim(𝒪_{U, h(ν̄')}) - dim(𝒪_{R, e(h(ν̄'))})`

measured on the original chart at the image point. -/
theorem hasChartLocalRingDimension_refinement_diagonal_iff
    (hf : AlgebraicStacks.IsSmooth B S hS f) (hsq : Bicategory.IsTwoFibreProduct sq)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (hhsm : Space.IsSmooth B S hS (yoneda.map h))
    (hQ : Bicategory.IsTwoFibreProduct Q) (hT : Bicategory.IsTwoFibreProduct T)
    (hR : IsAlgebraicSpace B S hS R) (hP : IsAlgebraicSpace B S hS P)
    (hW : IsAlgebraicSpace B S hS W)
    (δ : Bicategory.TwoCommSq.PreHom (selfIntersectionDiagonalSquare B S hS U f) sq)
    (δ' : Bicategory.TwoCommSq.PreHom
      (selfIntersectionDiagonalSquare B S hS U' (schemeStackMap.{u, w} B S hS h ≫ f))
      (refinedSelfIntersectionSquare B S hS sq Q T))
    (ν : Space.GeometricPoint B S hS (yoneda.obj U'))
    (hcl₁ : Space.HasClosedChartFibreSquare B S hS (yoneda.map h)
      (relationRefinementFst B S hS sq Q T P W eP eW)
      (relationRefinementRight B S hS sq Q T W eW)
      (Space.geometricPointMap (selfIntersectionDiagonalMap B S hS U'
        (schemeStackMap.{u, w} B S hS h ≫ f) (refinedSelfIntersectionSquare B S hS sq Q T) W
        (PresheafOfCategories.sliceElementsEquivalenceOver U') eW δ') ν))
    (hcl₂ : Space.HasClosedChartFibreSquare B S hS (yoneda.map h)
      (relationRefinementSnd B S hS sq Q R P eR eP)
      (relationRefinementMidFst B S hS sq Q P eP)
      (Space.geometricPointMap (relationRefinementFst B S hS sq Q T P W eP eW)
        (Space.geometricPointMap (selfIntersectionDiagonalMap B S hS U'
          (schemeStackMap.{u, w} B S hS h ≫ f) (refinedSelfIntersectionSquare B S hS sq Q T) W
          (PresheafOfCategories.sliceElementsEquivalenceOver U') eW δ') ν)))
    (d : ℤ) :
    HasChartLocalRingDimension B S hS U' (schemeStackMap.{u, w} B S hS h ≫ f)
        (refinedSelfIntersectionSquare B S hS sq Q T) W
        (PresheafOfCategories.sliceElementsEquivalenceOver U') eW
        (Space.geometricPointMap (selfIntersectionDiagonalMap B S hS U'
          (schemeStackMap.{u, w} B S hS h ≫ f) (refinedSelfIntersectionSquare B S hS sq Q T) W
          (PresheafOfCategories.sliceElementsEquivalenceOver U') eW δ') ν) d ↔
      HasChartLocalRingDimension B S hS U f sq R
        (PresheafOfCategories.sliceElementsEquivalenceOver U) eR
        (Space.geometricPointMap (selfIntersectionDiagonalMap B S hS U f sq R
            (PresheafOfCategories.sliceElementsEquivalenceOver U) eR δ)
          (Space.geometricPointMap (yoneda.map h) ν)) d := by
  rw [← geometricPointMap_relationRefinementSnd_diagonal.{u, w} B S hS sq Q T R P W
    eR eP eW hsq δ δ' ν]
  exact hasChartLocalRingDimension_refinement_iff.{u, w} B S hS sq Q T R P W eR eP eW
    hf hsq h𝒳 hhsm hQ hT hR hP hW _
    (geometricPointMap_relationRefinement_coord_eq_of_diagonal.{u, w} B S hS sq Q T P W eP eW
      δ' ν)
    hcl₁ hcl₂ d

/-- `AlgebraicGeometry.Stack.hasChartLocalRingDimension_refinement_diagonal_iff` for
`AlgebraicGeometry.Stack.HasRelationLocalRingDimension`, at the points of the two relations
below the diagonal points above `ν̄'` and `h(ν̄')`. -/
theorem hasRelationLocalRingDimension_refinement_diagonal_iff
    (hf : AlgebraicStacks.IsSmooth B S hS f) (hsq : Bicategory.IsTwoFibreProduct sq)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (hhsm : Space.IsSmooth B S hS (yoneda.map h))
    (hQ : Bicategory.IsTwoFibreProduct Q) (hT : Bicategory.IsTwoFibreProduct T)
    (hR : IsAlgebraicSpace B S hS R) (hP : IsAlgebraicSpace B S hS P)
    (hW : IsAlgebraicSpace B S hS W)
    (δ : Bicategory.TwoCommSq.PreHom (selfIntersectionDiagonalSquare B S hS U f) sq)
    (δ' : Bicategory.TwoCommSq.PreHom
      (selfIntersectionDiagonalSquare B S hS U' (schemeStackMap.{u, w} B S hS h ≫ f))
      (refinedSelfIntersectionSquare B S hS sq Q T))
    (ν : Space.GeometricPoint B S hS (yoneda.obj U'))
    (hcl₁ : Space.HasClosedChartFibreSquare B S hS (yoneda.map h)
      (relationRefinementFst B S hS sq Q T P W eP eW)
      (relationRefinementRight B S hS sq Q T W eW)
      (Space.geometricPointMap (selfIntersectionDiagonalMap B S hS U'
        (schemeStackMap.{u, w} B S hS h ≫ f) (refinedSelfIntersectionSquare B S hS sq Q T) W
        (PresheafOfCategories.sliceElementsEquivalenceOver U') eW δ') ν))
    (hcl₂ : Space.HasClosedChartFibreSquare B S hS (yoneda.map h)
      (relationRefinementSnd B S hS sq Q R P eR eP)
      (relationRefinementMidFst B S hS sq Q P eP)
      (Space.geometricPointMap (relationRefinementFst B S hS sq Q T P W eP eW)
        (Space.geometricPointMap (selfIntersectionDiagonalMap B S hS U'
          (schemeStackMap.{u, w} B S hS h ≫ f) (refinedSelfIntersectionSquare B S hS sq Q T) W
          (PresheafOfCategories.sliceElementsEquivalenceOver U') eW δ') ν)))
    (d : ℤ) :
    HasRelationLocalRingDimension B S hS U' (schemeStackMap.{u, w} B S hS h ≫ f)
        (refinedSelfIntersectionSquare B S hS sq Q T) W
        (PresheafOfCategories.sliceElementsEquivalenceOver U') eW
        (Space.pointsMap B S hS (yoneda.obj U')
          (selfIntersectionDiagonalMap B S hS U' (schemeStackMap.{u, w} B S hS h ≫ f)
            (refinedSelfIntersectionSquare B S hS sq Q T) W
            (PresheafOfCategories.sliceElementsEquivalenceOver U') eW δ') ν.image) d ↔
      HasRelationLocalRingDimension B S hS U f sq R
        (PresheafOfCategories.sliceElementsEquivalenceOver U) eR
        (Space.pointsMap B S hS (yoneda.obj U)
          (selfIntersectionDiagonalMap B S hS U f sq R
            (PresheafOfCategories.sliceElementsEquivalenceOver U) eR δ)
          (Space.pointsMap B S hS (yoneda.obj U') (yoneda.map h) ν.image)) d :=
  (hasChartLocalRingDimension_iff_hasRelationLocalRingDimension B S hS U'
      (schemeStackMap.{u, w} B S hS h ≫ f) (refinedSelfIntersectionSquare B S hS sq Q T) W
      (PresheafOfCategories.sliceElementsEquivalenceOver U') eW hW
      (Space.geometricPointMap (selfIntersectionDiagonalMap B S hS U'
        (schemeStackMap.{u, w} B S hS h ≫ f) (refinedSelfIntersectionSquare B S hS sq Q T) W
        (PresheafOfCategories.sliceElementsEquivalenceOver U') eW δ') ν) d).symm.trans
    ((hasChartLocalRingDimension_refinement_diagonal_iff.{u, w} B S hS sq Q T R P W eR eP eW
        hf hsq h𝒳 hhsm hQ hT hR hP hW δ δ' ν hcl₁ hcl₂ d).trans
      (hasChartLocalRingDimension_iff_hasRelationLocalRingDimension B S hS U f sq R
        (PresheafOfCategories.sliceElementsEquivalenceOver U) eR hR
        (Space.geometricPointMap (selfIntersectionDiagonalMap B S hS U f sq R
            (PresheafOfCategories.sliceElementsEquivalenceOver U) eR δ)
          (Space.geometricPointMap (yoneda.map h) ν)) d))

end Diagonal

end AlgebraicGeometry.Stack

end

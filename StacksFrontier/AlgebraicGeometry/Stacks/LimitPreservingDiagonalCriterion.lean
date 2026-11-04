module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingCanonicalDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingDiagonalColimitCoherence
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatCategoricalPullbackConverse
public import StacksFrontier.CategoryTheory.TwoFibreProduct.SquareComparisonTransfer

/-!
# Stacks 0CMW: the diagonal is limit preserving exactly when the comparison is fully faithful

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf category of
a scheme `S`. **Stacks 0CMW** says that the relative diagonal
`Δ : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳` is limit preserving (Stacks 0CMR) if and only if, at every directed
limit `U = lim Uᵢ` of affine schemes over `S`, the canonical functor

`colim 𝒳_{Uᵢ} ⟶ 𝒳_U ×_{𝒴_U} colim 𝒴_{Uᵢ}`

is fully faithful; in particular a limit preserving `f` has a limit preserving diagonal.

Both conditions are properties of the single square
`AlgebraicGeometry.Stack.canonicalSquare` -- of `Δ` for the first, of `f` for the second -- by
`AlgebraicGeometry.Stack.isLimitPreserving_iff_isTwoFibreProduct_canonicalSquare` and
`AlgebraicGeometry.Stack.isFullyFaithfulOnAffineLimits_iff_isEquivalence_squareDiagonalComparison`.
What remains, and is done here, is the identification of the two squares the comparisons come out
of:

* `Δ`'s square of Stacks 0CMR, whose lower corners are `colim (𝒳 ×_𝒴 𝒳)_{Uᵢ}` and
  `(𝒳 ×_𝒴 𝒳)_U`;
* the square of relative diagonals of `f`'s square, whose lower corners are
  `colim 𝒳_{Uᵢ} ×_{colim 𝒴_{Uᵢ}} colim 𝒳_{Uᵢ}` and `𝒳_U ×_{𝒴_U} 𝒳_U`.

They have the same apex and the same upper leg, and their cospans are compared by the equivalence
`K` of Stacks 0CMW (filtered colimits of categories commute with 2-fibre products) and the
equivalence `M` of Stacks 02XI (the fibre of a 2-fibre product is the 2-fibre product of the
fibres), compatibly with the three legs and -- by
`AlgebraicGeometry.Stack.diagonalFillerCoherence` -- with the two fillers. Hence
`CategoryTheory.Limits.CategoricalPullback.isEquivalence_squareComparison_iff_of_transfer`
applies: the two comparisons are equivalences together.

The last step is Stacks 003Q in the form
`CategoryTheory.Cat.nonempty_isTwoFibreProduct_of_isEquivalence_toCategoricalPullbackFunctor` and
its converse, which turn "`Δ`'s square is 2-cartesian" into "its comparison is an equivalence".

## Main results

* `AlgebraicGeometry.Stack.isEquivalence_squareComparison_canonicalSquare_diagonal_iff`: the
  comparison of `Δ`'s square and the comparison of the square of relative diagonals of `f`'s
  square are equivalences together.
* `AlgebraicGeometry.Stack.isLimitPreserving_twoFibreProductDiagonal_iff`: **Stacks 0CMW**, the
  equivalence of the two conditions.
* `AlgebraicGeometry.Stack.isLimitPreserving_twoFibreProductDiagonal`: **Stacks 0CMW**, the
  "in particular" clause -- a limit preserving 1-morphism has a limit preserving diagonal.

## References

* [Stacks Project, Tag 0CMW](https://stacks.math.columbia.edu/tag/0CMW)
* [Stacks Project, Tag 0CMR](https://stacks.math.columbia.edu/tag/0CMR)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 02XI](https://stacks.math.columbia.edu/tag/02XI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u v w

attribute [local implicit_reducible] AsSmall AsSmall.up AsSmall.down
  Bicategory.InducedBicategory Functor.Fiber Functor.Fiber.fiberInclusion
  Functor.SplitFiber.restrict Deformation.Artin.fiberCocone
  Deformation.Artin.fiberDiagram Functor.splitPresheaf Cat.asSmallFunctor
  Deformation.Artin.colimitComparison Deformation.Artin.evaluateSplitFiber
  BigFppfOver.twoFibreProduct BasedCategory.ofFunctor Functor.fiberMap

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 𝒴 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w} (BigFppfOver B S hS))
  (f : 𝒳 ⟶ 𝒴) {I : Type v} [Category.{w} I]

/-- **The two comparisons of Stacks 0CMW are equivalences together.** The square of Stacks 0CMR
for the relative diagonal `Δ : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳` and the square of relative diagonals of the
square of `f` have the same apex and upper leg, and their cospans are compared by the equivalence
`K` of Stacks 0CMW and the equivalence `M` of Stacks 02XI, compatibly with the legs and the
fillers; so
`CategoryTheory.Limits.CategoricalPullback.isEquivalence_squareComparison_iff_of_transfer`
applies.

Filteredness of the index category is used only for `K`: it is there that filtered colimits of
categories are required to commute with 2-fibre products. -/
lemma isEquivalence_squareComparison_canonicalSquare_diagonal_iff
    (E : I ⥤ BigFppfOver B S hS) (d : Cone E) [IsFiltered Iᵒᵖ] :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
    letI := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
    (CategoricalPullback.squareComparison
          (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙ AsSmall.up)
          (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS
            (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f) E)).toFunctor
          (AsSmall.down ⋙
            Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p
              (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f)) d.pt ⋙
            AsSmall.up)
          (Deformation.Artin.colimitComparison
            (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p E d ⋙
            AsSmall.up)
          (canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS
            (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f) E d)).IsEquivalence ↔
      (CategoricalPullback.squareComparison
          (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙ AsSmall.up)
          (CategoricalPullback.diagonal
            (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v}
              B S hS f E)).toFunctor)
          (CategoricalPullback.diagonal
            (AsSmall.down ⋙
              Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt ⋙
              AsSmall.up))
          (CategoricalPullback.mapDiagonal
            (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙ AsSmall.up)
            (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v}
              B S hS f E)).toFunctor
            (AsSmall.down ⋙
              Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt ⋙
              AsSmall.up)
            (Deformation.Artin.colimitComparison 𝒴.val.p E d ⋙ AsSmall.up)
            (canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS f E d))
          (CategoricalPullback.diagonalSquareFiller
            (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙ AsSmall.up)
            (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v}
              B S hS f E)).toFunctor
            (AsSmall.down ⋙
              Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt ⋙
              AsSmall.up)
            (Deformation.Artin.colimitComparison 𝒴.val.p E d ⋙ AsSmall.up)
            (canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v}
              B S hS f E d))).IsEquivalence := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
  let := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
  let := hasColimitsOfSize_sSet_fiberDiagram.{u, v, w}
  have hM : (diagonalFiberPullback B S hS 𝒳 𝒴 f d.pt).IsEquivalence :=
    TwoFibreProductOver.isEquivalence_asSmallFiberPullback.{max (u + 1) v w} 𝒳.val.p 𝒳.val.p
      𝒴.val.p (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor f)
      (CatFiberedInGroupoids.homFunctor_comp_p f) (CatFiberedInGroupoids.homFunctor_comp_p f)
      d.pt
  exact @CategoricalPullback.isEquivalence_squareComparison_iff_of_transfer
    _ _ _ _ _ _ _ _ _ _ _ _
    (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙ AsSmall.up)
    (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS
      (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f) E)).toFunctor
    (AsSmall.down ⋙
      Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p
        (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f)) d.pt ⋙
      AsSmall.up)
    (Deformation.Artin.colimitComparison
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p E d ⋙ AsSmall.up)
    (canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS
      (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f) E d)
    (CategoricalPullback.diagonal
      (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E)).toFunctor)
    (CategoricalPullback.diagonal
      (AsSmall.down ⋙
        Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt ⋙
        AsSmall.up))
    (CategoricalPullback.mapDiagonal
      (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙ AsSmall.up)
      (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E)).toFunctor
      (AsSmall.down ⋙
        Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt ⋙
        AsSmall.up)
      (Deformation.Artin.colimitComparison 𝒴.val.p E d ⋙ AsSmall.up)
      (canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS f E d))
    (CategoricalPullback.diagonalSquareFiller
      (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙ AsSmall.up)
      (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E)).toFunctor
      (AsSmall.down ⋙
        Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt ⋙
        AsSmall.up)
      (Deformation.Artin.colimitComparison 𝒴.val.p E d ⋙ AsSmall.up)
      (canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS f E d))
    (colimitSplitFiberTwoFibreProductComparison B S hS 𝒳 𝒴 𝒳 f f E)
    (diagonalFiberPullback B S hS 𝒳 𝒴 f d.pt)
    (eqToIso (BigFppfOver.colimMap_twoFibreProductDiagonal_comp_comparison.{u, v, w}
      B S hS 𝒳 𝒴 f E))
    (diagonalFiberLegIso B S hS 𝒳 𝒴 f d.pt)
    (diagonalLegIso B S hS 𝒳 𝒴 f E d)
    (isEquivalence_colimitSplitFiberTwoFibreProductComparison B S hS 𝒳 𝒴 𝒳 f f E)
    hM.full hM.faithful (diagonalFillerCoherence B S hS 𝒳 𝒴 f E d)

/-- **The fullness half of Stacks 0CMW at one cone.** If the comparison out of the square of
Stacks 0CMR for the relative diagonal `Δ : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳` is essentially surjective, then
the canonical functor `colim 𝒳_{Uᵢ} ⟶ 𝒳_U ×_{𝒴_U} colim 𝒴_{Uᵢ}` is full.

This is the one-directional, essential-surjectivity-only form of
`AlgebraicGeometry.Stack.isEquivalence_squareComparison_canonicalSquare_diagonal_iff`, over the
same identification of the two squares and hence the same transfer data; the transport is
`CategoryTheory.Limits.CategoricalPullback.essSurj_squareComparison_iff_of_transfer` instead of
its 2-cartesian sibling, and essential surjectivity of the comparison of the square of relative
diagonals already forces fullness
(`CategoryTheory.Cat.full_toCategoricalPullbackFunctor_of_essSurj_squareDiagonalComparison`).

It is what makes the converse of Stacks 0CMV available: full faithfulness of the comparison is
condition (2) of Stacks 0CMW, and this supplies its fullness half from descent of objects along
`Δ` rather than from limit preservation of `Δ`, which is the property being proved. -/
lemma full_toCategoricalPullbackFunctor_canonicalSquare_of_essSurj_diagonal
    (E : I ⥤ BigFppfOver B S hS) (d : Cone E) [IsFiltered Iᵒᵖ]
    (h : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
        (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
      letI := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
      (Cat.toCategoricalPullbackFunctor
        (canonicalSquare.{u, v, w, max (u + 1) v w, max u v} B S hS
          (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f) E d)).EssSurj) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
    (Cat.toCategoricalPullbackFunctor
      (canonicalSquare.{u, v, w, max (u + 1) v w, max u v} B S hS f E d)).Full := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
  let := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
  let := hasColimitsOfSize_sSet_fiberDiagram.{u, v, w}
  have : IsCofiltered I := (isFiltered_op_iff_isCofiltered I).1 inferInstance
  have : IsGroupoid (𝒳.val.p.Fiber d.pt) := 𝒳.2.fiber_isGroupoid _
  have := isGroupoid_colimit_fiberDiagram B S hS 𝒴 E
  have hM : (diagonalFiberPullback B S hS 𝒳 𝒴 f d.pt).IsEquivalence :=
    TwoFibreProductOver.isEquivalence_asSmallFiberPullback.{max (u + 1) v w} 𝒳.val.p 𝒳.val.p
      𝒴.val.p (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor f)
      (CatFiberedInGroupoids.homFunctor_comp_p f) (CatFiberedInGroupoids.homFunctor_comp_p f)
      d.pt
  refine Cat.full_toCategoricalPullbackFunctor_of_essSurj_squareDiagonalComparison _ ?_
  exact (@CategoricalPullback.essSurj_squareComparison_iff_of_transfer
    _ _ _ _ _ _ _ _ _ _ _ _
    (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙ AsSmall.up)
    (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS
      (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f) E)).toFunctor
    (AsSmall.down ⋙
      Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p
        (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f)) d.pt ⋙
      AsSmall.up)
    (Deformation.Artin.colimitComparison
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p E d ⋙ AsSmall.up)
    (canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS
      (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f) E d)
    (CategoricalPullback.diagonal
      (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E)).toFunctor)
    (CategoricalPullback.diagonal
      (AsSmall.down ⋙
        Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt ⋙
        AsSmall.up))
    (CategoricalPullback.mapDiagonal
      (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙ AsSmall.up)
      (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E)).toFunctor
      (AsSmall.down ⋙
        Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt ⋙
        AsSmall.up)
      (Deformation.Artin.colimitComparison 𝒴.val.p E d ⋙ AsSmall.up)
      (canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS f E d))
    (CategoricalPullback.diagonalSquareFiller
      (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙ AsSmall.up)
      (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E)).toFunctor
      (AsSmall.down ⋙
        Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt ⋙
        AsSmall.up)
      (Deformation.Artin.colimitComparison 𝒴.val.p E d ⋙ AsSmall.up)
      (canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS f E d))
    (colimitSplitFiberTwoFibreProductComparison B S hS 𝒳 𝒴 𝒳 f f E)
    (diagonalFiberPullback B S hS 𝒳 𝒴 f d.pt)
    (eqToIso (BigFppfOver.colimMap_twoFibreProductDiagonal_comp_comparison.{u, v, w}
      B S hS 𝒳 𝒴 f E))
    (diagonalFiberLegIso B S hS 𝒳 𝒴 f d.pt)
    (diagonalLegIso B S hS 𝒳 𝒴 f E d)
    (isEquivalence_colimitSplitFiberTwoFibreProductComparison B S hS 𝒳 𝒴 𝒳 f f E)
    hM.full hM.faithful (diagonalFillerCoherence B S hS 𝒳 𝒴 f E d)).mp h

/-- **Stacks 0CMW.** The relative diagonal `Δ : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳` of a 1-morphism of
categories fibred in groupoids over the big fppf category of `S` is limit preserving if and only
if, at every directed limit `U = lim Uᵢ` of affine schemes over `S`, the canonical functor
`colim 𝒳_{Uᵢ} ⟶ 𝒳_U ×_{𝒴_U} colim 𝒴_{Uᵢ}` is fully faithful.

Both sides are properties of `AlgebraicGeometry.Stack.canonicalSquare` -- of `Δ` on the left, of
`f` on the right -- and the two squares are equivalent, so the source's criterion
`CategoryTheory.Limits.CategoricalPullback.fullyFaithful_squareComparison_iff` transfers between
them. -/
@[stacks 0CMW]
theorem isLimitPreserving_twoFibreProductDiagonal_iff :
    IsLimitPreserving.{u, v, w, max (u + 1) v w, max u v} B S hS
        (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f) ↔
      IsFullyFaithfulOnAffineLimits.{u, v, w, max (u + 1) v w, max u v} B S hS f := by
  rw [isLimitPreserving_iff_isTwoFibreProduct_canonicalSquare,
    isFullyFaithfulOnAffineLimits_iff_isEquivalence_squareDiagonalComparison]
  refine ⟨fun h J _ _ D c hc => ?_, fun h J _ _ D c hc => ?_⟩
  · have : IsFiltered Jᵒᵖ := (isFiltered_op_iff_isCofiltered J).2 inferInstance
    exact (isEquivalence_squareComparison_canonicalSquare_diagonal_iff B S hS 𝒳 𝒴 f
      (D ⋙ BigAffineFppf.inclusion B S hS)
      ((BigAffineFppf.inclusion B S hS).mapCone c)).mp
      (Cat.isEquivalence_toCategoricalPullbackFunctor (h J D c hc).some)
  · have : IsFiltered Jᵒᵖ := (isFiltered_op_iff_isCofiltered J).2 inferInstance
    exact Cat.nonempty_isTwoFibreProduct_of_isEquivalence_toCategoricalPullbackFunctor _
      ((isEquivalence_squareComparison_canonicalSquare_diagonal_iff B S hS 𝒳 𝒴 f
        (D ⋙ BigAffineFppf.inclusion B S hS)
        ((BigAffineFppf.inclusion B S hS).mapCone c)).mpr (h J D c hc))

/-- **Stacks 0CMW, the "in particular" clause.** A limit preserving 1-morphism of categories
fibred in groupoids has a limit preserving relative diagonal: it satisfies the full faithfulness
condition by
`AlgebraicGeometry.Stack.isFullyFaithfulOnAffineLimits_of_isLimitPreserving`, and that condition
is limit preservation of the diagonal. -/
@[stacks 0CMW]
theorem isLimitPreserving_twoFibreProductDiagonal
    (hf : IsLimitPreserving.{u, v, w, max (u + 1) v w, max u v} B S hS f) :
    IsLimitPreserving.{u, v, w, max (u + 1) v w, max u v} B S hS
      (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f) :=
  (isLimitPreserving_twoFibreProductDiagonal_iff B S hS 𝒳 𝒴 f).mpr
    (isFullyFaithfulOnAffineLimits_of_isLimitPreserving B S hS f hf)

end AlgebraicGeometry.Stack

end

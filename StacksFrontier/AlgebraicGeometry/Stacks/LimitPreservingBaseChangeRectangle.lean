module

public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingBaseChangeColimitLeg
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingBaseChangeFiber
public import StacksFrontier.CategoryTheory.TwoFibreProduct.SquareComparisonPaste

/-!
# The two rectangles of Stacks 0CMT

Stacks 0CMT asserts that the base change `p' : 𝒳 ×_𝒴 𝒵 ⟶ 𝒵` of a limit preserving `p` is limit
preserving, which by `StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingCanonicalCell` is the
2-cartesian property of `AlgebraicGeometry.Stack.canonicalSquare` for `p'`. This file compares
that square with the square of `p` by two pastings, both instances of
`CategoryTheory.Limits.CategoricalPullback.isEquivalence_squareComparison_paste_iff`.

The first pastes the square of Stacks 02XI at the cone point,
`AlgebraicGeometry.Stack.isEquivalence_squareComparison_baseChangeFiber`, onto the right of the
square of Stacks 0CMR for `p'`; the resulting rectangle `R` has apex `colim (𝒳 ×_𝒴 𝒵)_{Uᵢ}`, upper
leg the colimit comparison followed by the fibre of the first projection, and cospan the fibres of
`p` and `q` at the cone point. The pasted square is 2-cartesian, so `R` and the square of `p'` are
2-cartesian together.

The second pastes the square of `p` onto the right of the square of the colimits,
`AlgebraicGeometry.BigFppfOver.isEquivalence_squareComparison_colimitTwoFibreProduct`. The
resulting rectangle `R′` has the same apex, left leg and right leg as `R`, and its two horizontal
legs factor the other way round -- through the colimits rather than through the fibres at the cone
point. Both of its squares are 2-cartesian, the left one because filtered colimits of categories
commute with 2-fibre products and the right one by hypothesis, so `R′` is 2-cartesian outright.

What is left, and is not done here, is that `R` and `R′` are 2-cartesian together: their
horizontal legs differ by the 2-cells `AlgebraicGeometry.Stack.canonicalTwoCellUp` of the two
projections, and the single remaining coherence between the two fillers is
`AlgebraicGeometry.Stack.baseChangeFillerCoherence`.

## Main results

* `AlgebraicGeometry.Stack.isEquivalence_squareComparison_baseChangeRectangle_iff`: the first
  pasting -- `R` is 2-cartesian exactly when the square of `p'` is.
* `AlgebraicGeometry.Stack.isEquivalence_squareComparison_baseChangeColimitRectangle`: the second
  pasting -- `R′` is 2-cartesian as soon as the square of `p` is.

## Implementation notes

The nine pieces of data of each pasting are written out only once, in the statement; in the proofs
they are left to unification, the conclusion of
`CategoryTheory.Limits.CategoricalPullback.isEquivalence_squareComparison_paste_iff` determining
all of them from the rectangle alone.

## References

* [Stacks Project, Tag 0CMT](https://stacks.math.columbia.edu/tag/0CMT)
* [Stacks Project, Tag 0CMR](https://stacks.math.columbia.edu/tag/0CMR)
* [Stacks Project, Tag 02XI](https://stacks.math.columbia.edu/tag/02XI)
* [Stacks Project, Tag 003R](https://stacks.math.columbia.edu/tag/003R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w}
    (BigFppfOver B S hS))
  (p : 𝒳 ⟶ 𝒴) (q : 𝒵 ⟶ 𝒴) {I : Type v} [Category.{w} I]

/-- **The first pasting of Stacks 0CMT.** Pasting the square of Stacks 02XI at the cone point onto
the right of the square of Stacks 0CMR for the base change `p'` replaces `(𝒳 ×_𝒴 𝒵)_U` by `𝒳_U` in
the cospan. The pasted square is 2-cartesian -- it is Stacks 02XI,
`AlgebraicGeometry.Stack.isEquivalence_squareComparison_baseChangeFiber` -- so the rectangle and
the square of `p'` are 2-cartesian together. -/
lemma isEquivalence_squareComparison_baseChangeRectangle_iff (E : I ⥤ BigFppfOver B S hS)
    (d : Cone E) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
    letI := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
    (CategoricalPullback.squareComparison
          ((Deformation.Artin.colimitComparison
              (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p E d ⋙
            AsSmall.up) ⋙
            (AsSmall.down ⋙
              Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p
                (BigFppfOver.twoFibreProductFst.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q)) d.pt ⋙
              AsSmall.up))
          (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS
            (BigFppfOver.twoFibreProductSnd.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q) E)).toFunctor
          (AsSmall.down ⋙
            Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p p) d.pt ⋙
            AsSmall.up)
          ((Deformation.Artin.colimitComparison 𝒵.val.p E d ⋙ AsSmall.up) ⋙
            (AsSmall.down ⋙
              Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p q) d.pt ⋙
              AsSmall.up))
          (CategoricalPullback.pasteFiller
            (Deformation.Artin.colimitComparison
              (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p E d ⋙ AsSmall.up)
            (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS
              (BigFppfOver.twoFibreProductSnd.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q) E)).toFunctor
            (AsSmall.down ⋙
              Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p
                (BigFppfOver.twoFibreProductSnd.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q)) d.pt ⋙
              AsSmall.up)
            (Deformation.Artin.colimitComparison 𝒵.val.p E d ⋙ AsSmall.up)
            (canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS
              (BigFppfOver.twoFibreProductSnd.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q) E d)
            (AsSmall.down ⋙
              Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p
                (BigFppfOver.twoFibreProductFst.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q)) d.pt ⋙
              AsSmall.up)
            (AsSmall.down ⋙
              Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p p) d.pt ⋙
              AsSmall.up)
            (AsSmall.down ⋙
              Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p q) d.pt ⋙
              AsSmall.up)
            (baseChangeFiberFiller.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q d.pt))).IsEquivalence ↔
      (CategoricalPullback.squareComparison
        (Deformation.Artin.colimitComparison
          (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p E d ⋙ AsSmall.up)
        (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS
          (BigFppfOver.twoFibreProductSnd.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q) E)).toFunctor
        (AsSmall.down ⋙
          Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p
            (BigFppfOver.twoFibreProductSnd.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q)) d.pt ⋙
          AsSmall.up)
        (Deformation.Artin.colimitComparison 𝒵.val.p E d ⋙ AsSmall.up)
        (canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS
          (BigFppfOver.twoFibreProductSnd.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q) E d)).IsEquivalence :=
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
  let : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
  let := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
  let := isEquivalence_squareComparison_baseChangeFiber.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q d.pt
  CategoricalPullback.isEquivalence_squareComparison_paste_iff _ _ _ _ _ _ _ _ _

/-- **The second pasting of Stacks 0CMT.** Pasting the square of Stacks 0CMR for `p` onto the right
of the square of the colimits gives a rectangle with the same apex, left leg and right leg as the
first pasting's. Its left-hand square is 2-cartesian because filtered colimits of categories
commute with 2-fibre products
(`AlgebraicGeometry.BigFppfOver.isEquivalence_squareComparison_colimitTwoFibreProduct`) and its
right-hand square is 2-cartesian by hypothesis, so the rectangle is 2-cartesian. -/
lemma isEquivalence_squareComparison_baseChangeColimitRectangle (E : I ⥤ BigFppfOver B S hS)
    (d : Cone E) [IsFiltered Iᵒᵖ]
    (hp : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
      letI := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
      (CategoricalPullback.squareComparison
        (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙ AsSmall.up)
        (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS p E)).toFunctor
        (AsSmall.down ⋙
          Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p p) d.pt ⋙
          AsSmall.up)
        (Deformation.Artin.colimitComparison 𝒴.val.p E d ⋙ AsSmall.up)
        (canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v}
          B S hS p E d)).IsEquivalence) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
    letI := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
    (CategoricalPullback.squareComparison
      ((colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS
          (BigFppfOver.twoFibreProductFst.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q) E)).toFunctor ⋙
        (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙ AsSmall.up))
      (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS
        (BigFppfOver.twoFibreProductSnd.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q) E)).toFunctor
      (AsSmall.down ⋙
        Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p p) d.pt ⋙
        AsSmall.up)
      ((colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v}
          B S hS q E)).toFunctor ⋙
        (Deformation.Artin.colimitComparison 𝒴.val.p E d ⋙ AsSmall.up))
      (CategoricalPullback.pasteFiller
        (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS
          (BigFppfOver.twoFibreProductFst.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q) E)).toFunctor
        (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS
          (BigFppfOver.twoFibreProductSnd.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q) E)).toFunctor
        (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS p E)).toFunctor
        (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS q E)).toFunctor
        (CategoricalPullback.projFillerOfEq _ _ _ _
          (colimitSplitFiberTwoFibreProductComparison B S hS 𝒳 𝒴 𝒵 p q E)
          (BigFppfOver.colimMap_twoFibreProductFst_comp_comparison.{u, v, w}
            B S hS 𝒳 𝒴 𝒵 p q E)
          (BigFppfOver.colimMap_twoFibreProductSnd_comp_comparison.{u, v, w}
            B S hS 𝒳 𝒴 𝒵 p q E))
        (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙ AsSmall.up)
        (AsSmall.down ⋙
          Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p p) d.pt ⋙
          AsSmall.up)
        (Deformation.Artin.colimitComparison 𝒴.val.p E d ⋙ AsSmall.up)
        (canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v}
          B S hS p E d))).IsEquivalence :=
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let : 𝒵.val.p.IsFibered := 𝒵.2.isFibered
  let : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).val.p.IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒵 p q).2.isFibered
  let := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
  let := hp
  (CategoricalPullback.isEquivalence_squareComparison_paste_iff _ _ _ _ _ _ _ _ _).mpr
    (BigFppfOver.isEquivalence_squareComparison_colimitTwoFibreProduct.{u, v, w}
      B S hS 𝒳 𝒴 𝒵 p q E)

end AlgebraicGeometry.Stack

end

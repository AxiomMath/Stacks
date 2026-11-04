module

public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingDiagonalColimitEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingDiagonalColimitLegFiber
public import StacksFrontier.CategoryTheory.Limits.FilteredColimitCatNatIsoWhisker
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFibresDiagonal

/-!
# The comparison of the lower legs of the two squares of Stacks 0CMW

The two squares that Stacks 0CMW compares -- the canonical square of Stacks 0CMR for the diagonal
`Δ : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳` and the square of relative diagonals of the canonical square of `f` --
have the comparison `K` of Stacks 0CMW between their lower left corners and the comparison `M` of
Stacks 02XI between their lower right ones. This file compares their lower legs: it builds the
isomorphism

`K ⋙ b₂ ≅ b₁ ⋙ M`

that `CategoryTheory.Limits.CategoricalPullback.isEquivalence_squareComparison_iff_of_transfer`
takes for its input `ib`.

It is built one stage of the colimit at a time, by `CategoryTheory.Cat.natIsoOfStages`, and at a
stage both legs factor through the split fibre of `𝒳 ×_{f, 𝒴, f} 𝒳` at the cone point:

* the left leg by
  `AlgebraicGeometry.Stack.splitFiberCospanUp_comp_twoFibreProductStage_comp_mapDiagonal`,
  followed by the strict naturality in the base of
  `AlgebraicGeometry.Stack.splitFiberTwoFibreProductComparisonApp`;
* the right leg by `Deformation.Artin.ι_comp_colimitComparison_comp_up`.

The two factorizations are compared by the single isomorphism
`AlgebraicGeometry.Stack.splitFiberTwoFibreProductComparisonApp_evaluationIso`, whiskered into the
universe lift of the cospan of fibres at the cone point. Since that isomorphism does not depend on
the stage, the compatibility with the transition functors of the diagram reduces to the strict
functoriality of restriction, which is `CategoryTheory.Cat.stageIsoOfWhisker_compat`.

## Implementation notes

The two factorizations are proved by composing `CategoryTheory.congrArg`s along a chain of
functors. Associativity of `CategoryTheory.Functor.comp` is definitional, but letting the
unifier discover it on terms this size does not terminate: each `congrArg` produces a composite
bracketed the way its own statement is, and a failed structural match on two functors of this
depth is more expensive than the proof. The chain is therefore right-normalized with
`CategoryTheory.Functor.assoc` before the steps are composed, so that every composition is a
syntactic match.

## Main definitions

* `AlgebraicGeometry.Stack.diagonalFiberCompare` and
  `AlgebraicGeometry.Stack.diagonalFiberPullback`: the comparison of Stacks 02XI for the 2-fibre
  product of Stacks 0CMW, before and after the universe lift, read in the spelling the squares of
  Stacks 0CMR use. This is the comparison `M` of the lower right corners.
* `AlgebraicGeometry.Stack.diagonalFiberLegIso`: the comparison `ip` of the lower right legs.
* `AlgebraicGeometry.Stack.diagonalLegIso`: the comparison `ib` of the lower legs.

## Main results

* `AlgebraicGeometry.Stack.ι_comp_colimitSplitFiberTwoFibreProductComparison_comp_mapDiagonal`:
  the factorization of the left leg at a stage.
* `AlgebraicGeometry.Stack.ι_comp_colimitComparison_comp_asSmallFiberPullback`: the factorization
  of the right leg at a stage.
* `AlgebraicGeometry.Stack.diagonalLegIso_inv_app_ι`: the inverse of `ib` at an object of a
  stage, which is the form the coherence hypothesis of the transfer lemma needs.
* `AlgebraicGeometry.Stack.diagonalFiberPullback_map_canonicalTwoCellUp_hom_app_fst`,
  `…_snd`, `AlgebraicGeometry.Stack.diagonalLegFiberIso_inv_app_fst`, `…_snd`,
  `AlgebraicGeometry.Stack.diagonalFiberCompare_map_splitEvaluationIso_hom_app_fst`, `…_snd`,
  `AlgebraicGeometry.Stack.diagonalLegRestrict_obj_fiberDiagramMap_obj` and `…_hom`: the two
  components of each factor of the coherence hypothesis of the transfer lemma, in the cospan of
  fibres at the cone point. On the image of the diagonal the base-change comparison of the
  diagonal and the comparison of Stacks 02XI are inverse chosen-pullback comparisons of one and
  the same object, which is what makes that hypothesis hold.

## References

* [Stacks Project, Tag 0CMW](https://stacks.math.columbia.edu/tag/0CMW)
* [Stacks Project, Tag 0CMR](https://stacks.math.columbia.edu/tag/0CMR)
* [Stacks Project, Tag 02XI](https://stacks.math.columbia.edu/tag/02XI)
* [Stacks Project, Tag 004A](https://stacks.math.columbia.edu/tag/004A)
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

/-- **The componentwise comparison of a split fibre of a 2-fibre product at a stage, unpacked.**
The component of the diagram-level comparison at a stage is the universe lift of the
componentwise comparison followed by the universe lift of the cospan. -/
lemma splitFiberTwoFibreProductComparison_app_toFunctor (E : I ⥤ BigFppfOver B S hS) (j : Iᵒᵖ) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
    ((splitFiberTwoFibreProductComparison B S hS 𝒳 𝒴 𝒳 f f E).app j).toFunctor =
      AsSmall.down ⋙ splitFiberTwoFibreProductComparisonApp B S hS 𝒳 𝒴 𝒳 f f (E.obj j.unop) ⋙
        splitFiberCospanUp B S hS 𝒳 𝒴 f E j := rfl

/-- **The comparison of Stacks 02XI for the 2-fibre product of Stacks 0CMW, at a fibre.** This is
`CategoryTheory.TwoFibreProductOver.toFiberPullback`, with its source read as the fibre of
`𝒳 ×_{f, 𝒴, f} 𝒳` and its target as the 2-fibre product of the cospan
`CategoryTheory.Functor.fiberFunctorOfCompEq` of `f`.

Both readings are definitional, and naming them is what makes the identities of this file
usable: `CategoryTheory.TwoFibreProductOver.toFiberPullback` is stated over
`CategoryTheory.TwoFibreProductOver.structureFunctor` and
`CategoryTheory.Functor.fiberMap`, while the squares of Stacks 0CMR are stated over
`AlgebraicGeometry.BigFppfOver.twoFibreProduct` and
`CategoryTheory.Functor.fiberFunctorOfCompEq`. The two spellings are different terms, so a
composite built from both is type-correct only at default transparency, and `simp` and `rw`
decline to touch any subterm of such a composite. -/
noncomputable def diagonalFiberCompare (V : BigFppfOver B S hS) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.Fiber V ⥤
      CategoricalPullback
        (Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) V)
        (Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) V) :=
  letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
  TwoFibreProductOver.toFiberPullback 𝒳.val.p 𝒳.val.p 𝒴.val.p
    (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor f)
    (CatFiberedInGroupoids.homFunctor_comp_p f) (CatFiberedInGroupoids.homFunctor_comp_p f) V

/-- **The comparison `M` of the lower right corners of the two squares of Stacks 0CMW.** It is
`CategoryTheory.TwoFibreProductOver.asSmallFiberPullback`, read in the spelling the squares of
Stacks 0CMR use: `AlgebraicGeometry.Stack.diagonalFiberCompare` followed by the universe lift of
the cospan of fibres. -/
noncomputable def diagonalFiberPullback (V : BigFppfOver B S hS) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
    AsSmall.{max (u + 1) v w}
        ((BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.Fiber V) ⥤
      CategoricalPullback
        (AsSmall.down.{max u v, max (u + 1) v w, max (u + 1) v w} ⋙
          Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) V ⋙
          AsSmall.up.{max u v, max (u + 1) v w, max (u + 1) v w})
        (AsSmall.down.{max u v, max (u + 1) v w, max (u + 1) v w} ⋙
          Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) V ⋙
          AsSmall.up.{max u v, max (u + 1) v w, max (u + 1) v w}) :=
  letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
  AsSmall.down ⋙ diagonalFiberCompare B S hS 𝒳 𝒴 f V ⋙ fiberCospanUp B S hS 𝒳 𝒴 f V

/-- `AlgebraicGeometry.Stack.diagonalFiberPullback` is the comparison of Stacks 02XI after the
universe lift. -/
lemma diagonalFiberPullback_eq (V : BigFppfOver B S hS) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
    diagonalFiberPullback B S hS 𝒳 𝒴 f V =
      TwoFibreProductOver.asSmallFiberPullback.{max (u + 1) v w} 𝒳.val.p 𝒳.val.p 𝒴.val.p
        (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor f)
        (CatFiberedInGroupoids.homFunctor_comp_p f)
        (CatFiberedInGroupoids.homFunctor_comp_p f) V := rfl

/-- **The fibre of the diagonal is the diagonal of the fibre, in the spelling of Stacks 0CMR.**
This is `CategoryTheory.TwoFibreProductOver.fiberFunctor_diagonal_comp_asSmallFiberPullback`
restated with `CategoryTheory.Functor.fiberFunctorOfCompEq` for the cospan and
`AlgebraicGeometry.Stack.diagonalFiberPullback` for the comparison. The restating is what the
coherence check of the transfer lemma needs: the source lemma states the cospan with
`CategoryTheory.Functor.fiberMap`, and a composite that mixes the two spellings has a
`CategoryTheory.Limits.CategoricalPullback.Hom.fst` which is ill-typed at `implicit`
transparency, so no rewriting tactic will touch it. -/
lemma fiberFunctor_diagonal_comp_diagonalFiberPullback (V : BigFppfOver B S hS) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
    (AsSmall.down.{max u v, max (u + 1) v w, max (u + 1) v w} ⋙
          Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p
            (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f)) V ⋙
          AsSmall.up.{max u v, max (u + 1) v w, max (u + 1) v w}) ⋙
        diagonalFiberPullback B S hS 𝒳 𝒴 f V =
      CategoricalPullback.diagonal
        (AsSmall.down.{max u v, max (u + 1) v w, max (u + 1) v w} ⋙
          Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) V ⋙
          AsSmall.up.{max u v, max (u + 1) v w, max (u + 1) v w}) :=
  TwoFibreProductOver.fiberFunctor_diagonal_comp_asSmallFiberPullback.{max (u + 1) v w}
    (CatFiberedInGroupoids.homFunctor_comp_p f) V

/-- **The comparison `ip` of the lower right legs of the two squares of Stacks 0CMW.** It is the
transport along `AlgebraicGeometry.Stack.fiberFunctor_diagonal_comp_diagonalFiberPullback`. -/
noncomputable def diagonalFiberLegIso (V : BigFppfOver B S hS) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
    (AsSmall.down.{max u v, max (u + 1) v w, max (u + 1) v w} ⋙
          Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p
            (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f)) V ⋙
          AsSmall.up.{max u v, max (u + 1) v w, max (u + 1) v w}) ⋙
        diagonalFiberPullback B S hS 𝒳 𝒴 f V ≅
      CategoricalPullback.diagonal
        (AsSmall.down.{max u v, max (u + 1) v w, max (u + 1) v w} ⋙
          Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) V ⋙
          AsSmall.up.{max u v, max (u + 1) v w, max (u + 1) v w}) :=
  eqToIso (fiberFunctor_diagonal_comp_diagonalFiberPullback B S hS 𝒳 𝒴 f V)

/-- **The universe lift cancels into the comparison of Stacks 02XI.** Precomposing
`CategoryTheory.TwoFibreProductOver.asSmallFiberPullback` with the universe lift undoes the
`CategoryTheory.AsSmall.down` built into it, leaving Stacks 02XI followed by the universe lift of
the cospan of fibres. -/
lemma asSmall_up_comp_asSmallFiberPullback (V : BigFppfOver B S hS) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
    AsSmall.up ⋙ diagonalFiberPullback B S hS 𝒳 𝒴 f V =
      diagonalFiberCompare B S hS 𝒳 𝒴 f V ⋙ fiberCospanUp B S hS 𝒳 𝒴 f V := rfl

/-- **Strict restriction of a stage of the diagram of split fibres to the cone point.** This is
the functor through which both lower legs of Stacks 0CMW's diagonal square factor at a stage; it
is named so that the two factorizations and their compatibility are stated over one and the same
term. -/
noncomputable abbrev diagonalLegRestrict (E : I ⥤ BigFppfOver B S hS) (d : Cone E) (j : Iᵒᵖ) :
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
    ↑((Deformation.Artin.fiberDiagram
          (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p E).obj j) ⥤
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.SplitFiber d.pt :=
  letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
  AsSmall.down ⋙ Functor.SplitFiber.restrict
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p (d.π.app j.unop)

/-- **The comparison of the two factorizations of the lower legs, in the cospan of fibres at the
cone point.** It is
`AlgebraicGeometry.Stack.splitFiberTwoFibreProductComparisonApp_evaluationIso` whiskered into the
universe lift of that cospan, and it does not depend on the stage -- which is why the stagewise
comparisons of the lower legs are automatically compatible with the transition functors. -/
noncomputable def diagonalLegFiberIso (V : BigFppfOver B S hS) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
    (splitFiberTwoFibreProductComparisonApp B S hS 𝒳 𝒴 𝒳 f f V ⋙
          splitFiberCospanEval B S hS 𝒳 𝒴 f V) ⋙ fiberCospanUp B S hS 𝒳 𝒴 f V ≅
      (Deformation.Artin.evaluateSplitFiber
            (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p V ⋙
          diagonalFiberCompare B S hS 𝒳 𝒴 f V) ⋙
        fiberCospanUp B S hS 𝒳 𝒴 f V :=
  letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
  Functor.isoWhiskerRight
    (splitFiberTwoFibreProductComparisonApp_evaluationIso B S hS 𝒳 𝒴 𝒳 f f V)
    (fiberCospanUp B S hS 𝒳 𝒴 f V)

/-- **The left leg of Stacks 0CMW's diagonal square, restricted to a stage.** The comparison `K`
of the lower left corners followed by the change of cospan `b₂` factors, at a stage, through the
split fibre of `𝒳 ×_{f, 𝒴, f} 𝒳` at the cone point: strict restriction to the cone point, then
the componentwise reading of that split fibre, then evaluation and the universe lift. -/
lemma ι_comp_colimitSplitFiberTwoFibreProductComparison_comp_mapDiagonal
    (E : I ⥤ BigFppfOver B S hS) (d : Cone E) (j : Iᵒᵖ) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
    letI := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
    (colimit.ι (Deformation.Artin.fiberDiagram
          (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p E) j).toFunctor ⋙
        (colimitSplitFiberTwoFibreProductComparison B S hS 𝒳 𝒴 𝒳 f f E ⋙
          CategoricalPullback.mapDiagonal
            (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙ AsSmall.up)
            (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E)).toFunctor
            (AsSmall.down ⋙
              Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt ⋙
              AsSmall.up)
            (Deformation.Artin.colimitComparison 𝒴.val.p E d ⋙ AsSmall.up)
            (canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS f E d)) =
      diagonalLegRestrict B S hS 𝒳 𝒴 f E d j ⋙
        ((splitFiberTwoFibreProductComparisonApp B S hS 𝒳 𝒴 𝒳 f f d.pt ⋙
            splitFiberCospanEval B S hS 𝒳 𝒴 f d.pt) ⋙
          fiberCospanUp B S hS 𝒳 𝒴 f d.pt) := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
  let := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
  have h₁ := congrArg
    (fun H => H ⋙ CategoricalPullback.mapDiagonal
      (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙ AsSmall.up)
      (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E)).toFunctor
      (AsSmall.down ⋙
        Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt ⋙
        AsSmall.up)
      (Deformation.Artin.colimitComparison 𝒴.val.p E d ⋙ AsSmall.up)
      (canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS f E d))
    (ι_comp_colimitSplitFiberTwoFibreProductComparison B S hS 𝒳 𝒴 𝒳 f f E j)
  rw [splitFiberTwoFibreProductComparison_app_toFunctor B S hS 𝒳 𝒴 f E j] at h₁
  have h₂ := congrArg
    (fun H => AsSmall.down ⋙
      splitFiberTwoFibreProductComparisonApp B S hS 𝒳 𝒴 𝒳 f f (E.obj j.unop) ⋙ H)
    (splitFiberCospanUp_comp_twoFibreProductStage_comp_mapDiagonal B S hS 𝒳 𝒴 f E d j)
  have h₃ := congrArg
    (fun H => AsSmall.down ⋙ H ⋙
      splitFiberCospanEval B S hS 𝒳 𝒴 f d.pt ⋙ fiberCospanUp B S hS 𝒳 𝒴 f d.pt)
    (splitFiberTwoFibreProductComparisonApp_naturality B S hS 𝒳 𝒴 𝒳 f f
      (d.π.app j.unop)).symm
  simp only [Functor.assoc] at h₁ h₂ h₃ ⊢
  exact h₁.trans (h₂.trans h₃)

/-- **The right leg of Stacks 0CMW's diagonal square, restricted to a stage.** The colimit
comparison of Stacks 07XL for `𝒳 ×_{f, 𝒴, f} 𝒳` followed by the comparison `M` of Stacks 02XI
factors, at a stage, through the same split fibre at the cone point: strict restriction, then
evaluation, then Stacks 02XI and the universe lift. -/
lemma ι_comp_colimitComparison_comp_asSmallFiberPullback
    (E : I ⥤ BigFppfOver B S hS) (d : Cone E) (j : Iᵒᵖ) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
    (colimit.ι (Deformation.Artin.fiberDiagram
          (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p E) j).toFunctor ⋙
        ((Deformation.Artin.colimitComparison
            (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p E d ⋙
            AsSmall.up.{max u v, max (u + 1) v w, max (u + 1) v w}) ⋙
          diagonalFiberPullback B S hS 𝒳 𝒴 f d.pt) =
      diagonalLegRestrict B S hS 𝒳 𝒴 f E d j ⋙
        ((Deformation.Artin.evaluateSplitFiber
              (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p d.pt ⋙
            diagonalFiberCompare B S hS 𝒳 𝒴 f d.pt) ⋙
          fiberCospanUp B S hS 𝒳 𝒴 f d.pt) := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
  have h₁ := congrArg
    (fun H => H ⋙ diagonalFiberPullback B S hS 𝒳 𝒴 f d.pt)
    (Deformation.Artin.ι_comp_colimitComparison_comp_up
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p E d j)
  exact h₁.trans (congrArg
    (fun H => AsSmall.down ⋙ Functor.SplitFiber.restrict
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p (d.π.app j.unop) ⋙
      Deformation.Artin.evaluateSplitFiber
        (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p d.pt ⋙ H)
    (asSmall_up_comp_asSmallFiberPullback B S hS 𝒳 𝒴 f d.pt))

/-- **Strict restriction to the cone point is compatible with the transition functors of the
diagram of split fibres.** This is the one hypothesis
`CategoryTheory.Cat.stageIsoOfWhisker_compat` needs; it is the strict functoriality of
restriction (`CategoryTheory.Functor.SplitFiber.restrict_comp`) together with the cone
identity. -/
lemma fiberDiagram_map_comp_restrict (E : I ⥤ BigFppfOver B S hS) (d : Cone E) {i j : Iᵒᵖ}
    (r : i ⟶ j) :
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
    ((Deformation.Artin.fiberDiagram
            (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p E).map r).toFunctor ⋙
        diagonalLegRestrict B S hS 𝒳 𝒴 f E d j =
      diagonalLegRestrict B S hS 𝒳 𝒴 f E d i :=
  let : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
  congrArg (fun H => AsSmall.down ⋙ H)
    ((Functor.SplitFiber.restrict_comp
        (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p
        (E.map r.unop) (d.π.app j.unop)).trans
      (congrArg
        (Functor.SplitFiber.restrict
          (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p)
        (d.w r.unop)))

/-- **The comparison `ib` of the lower legs of the two squares of Stacks 0CMW.** At every stage
of the colimit both legs factor through the split fibre of `𝒳 ×_{f, 𝒴, f} 𝒳` at the cone point,
and there they are compared by
`AlgebraicGeometry.Stack.splitFiberTwoFibreProductComparisonApp_evaluationIso`; the stagewise
isomorphisms assemble by `CategoryTheory.Cat.natIsoOfStages`. No filteredness is needed. -/
noncomputable def diagonalLegIso (E : I ⥤ BigFppfOver B S hS) (d : Cone E) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
    letI := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
    (colimitSplitFiberTwoFibreProductComparison B S hS 𝒳 𝒴 𝒳 f f E ⋙
        CategoricalPullback.mapDiagonal
          (Deformation.Artin.colimitComparison 𝒳.val.p E d ⋙ AsSmall.up)
          (colimMap (fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E)).toFunctor
          (AsSmall.down ⋙
            Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) d.pt ⋙
            AsSmall.up)
          (Deformation.Artin.colimitComparison 𝒴.val.p E d ⋙ AsSmall.up)
          (canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS f E d)) ≅
      ((Deformation.Artin.colimitComparison
            (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p E d ⋙
          AsSmall.up.{max u v, max (u + 1) v w, max (u + 1) v w}) ⋙
        diagonalFiberPullback B S hS 𝒳 𝒴 f d.pt) :=
  letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
  letI := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
  letI := hasColimitsOfSize_sSet_fiberDiagram.{u, v, w}
  Cat.natIsoOfStages.{u + 1, v, w}
    (Deformation.Artin.fiberDiagram
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p E)
    (fun j => Cat.stageIsoOfWhisker
      (Deformation.Artin.fiberDiagram
        (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p E)
      (diagonalLegFiberIso B S hS 𝒳 𝒴 f d.pt)
      (diagonalLegRestrict B S hS 𝒳 𝒴 f E d)
      (ι_comp_colimitSplitFiberTwoFibreProductComparison_comp_mapDiagonal B S hS 𝒳 𝒴 f E d)
      (ι_comp_colimitComparison_comp_asSmallFiberPullback B S hS 𝒳 𝒴 f E d) j)
    (fun {_ _} r a => Cat.stageIsoOfWhisker_compat
      (Deformation.Artin.fiberDiagram
        (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p E)
      (diagonalLegFiberIso B S hS 𝒳 𝒴 f d.pt)
      (diagonalLegRestrict B S hS 𝒳 𝒴 f E d)
      (ι_comp_colimitSplitFiberTwoFibreProductComparison_comp_mapDiagonal B S hS 𝒳 𝒴 f E d)
      (ι_comp_colimitComparison_comp_asSmallFiberPullback B S hS 𝒳 𝒴 f E d)
      (fun {_ _} s => fiberDiagram_map_comp_restrict B S hS 𝒳 𝒴 f E d s) r a)

/-- **The comparison `ib` of the lower legs, read at an object of a stage.** It is the component
of `AlgebraicGeometry.Stack.diagonalLegFiberIso` at the restriction of that object to the cone
point, conjugated by the two factorizations of the legs. This is the form in which the coherence
hypothesis of
`CategoryTheory.Limits.CategoricalPullback.isEquivalence_squareComparison_iff_of_transfer` is
checked. -/
lemma diagonalLegIso_inv_app_ι (E : I ⥤ BigFppfOver B S hS) (d : Cone E) (j : Iᵒᵖ)
    (a : letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
        (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
      ↑((Deformation.Artin.fiberDiagram
        (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p E).obj j)) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
    letI := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
    (diagonalLegIso B S hS 𝒳 𝒴 f E d).inv.app
        ((colimit.ι (Deformation.Artin.fiberDiagram
          (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p E) j).toFunctor.obj a) =
      eqToHom (Functor.congr_obj
          (ι_comp_colimitComparison_comp_asSmallFiberPullback B S hS 𝒳 𝒴 f E d j) a) ≫
        (diagonalLegFiberIso B S hS 𝒳 𝒴 f d.pt).inv.app
          ((diagonalLegRestrict B S hS 𝒳 𝒴 f E d j).obj a) ≫
        eqToHom (Functor.congr_obj
          (ι_comp_colimitSplitFiberTwoFibreProductComparison_comp_mapDiagonal
            B S hS 𝒳 𝒴 f E d j).symm a) := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
  let := hasColimitsOfSize_cat_fiberDiagram.{u, v, w}
  let := hasColimitsOfSize_sSet_fiberDiagram.{u, v, w}
  rw [diagonalLegIso, Cat.natIsoOfStages_inv_app, Cat.stageIsoOfWhisker_inv_app]
  exact fun {_ _} r b => Cat.stageIsoOfWhisker_compat _ _ _ _ _
    (fun {_ _} t => fiberDiagram_map_comp_restrict B S hS 𝒳 𝒴 f E d t) r b

/-- **The first component of `M` applied to the 2-cell `η` of the diagonal's square.** The
universe lift passes outside, leaving the comparison of Stacks 02XI applied to the unlifted
2-cell. -/
lemma diagonalFiberPullback_map_canonicalTwoCellUp_hom_app_fst
    (E : I ⥤ BigFppfOver B S hS) (d : Cone E)
    (x : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      ↑(colimit (Deformation.Artin.fiberDiagram 𝒳.val.p E))) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
    ((diagonalFiberPullback B S hS 𝒳 𝒴 f d.pt).map
        ((canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS
          (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f) E d).hom.app x)).fst =
      AsSmall.up.map (((diagonalFiberCompare B S hS 𝒳 𝒴 f d.pt).map
        ((canonicalTwoCell B S hS
          (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f) E d).hom.app
          x)).fst) := rfl

/-- The second component of
`AlgebraicGeometry.Stack.diagonalFiberPullback_map_canonicalTwoCellUp_hom_app_fst`. -/
lemma diagonalFiberPullback_map_canonicalTwoCellUp_hom_app_snd
    (E : I ⥤ BigFppfOver B S hS) (d : Cone E)
    (x : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      ↑(colimit (Deformation.Artin.fiberDiagram 𝒳.val.p E))) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
    ((diagonalFiberPullback B S hS 𝒳 𝒴 f d.pt).map
        ((canonicalTwoCellUp.{u, v, w, max (u + 1) v w, max u v} B S hS
          (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f) E d).hom.app x)).snd =
      AsSmall.up.map (((diagonalFiberCompare B S hS 𝒳 𝒴 f d.pt).map
        ((canonicalTwoCell B S hS
          (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f) E d).hom.app
          x)).snd) := rfl

/-- **The first component of the inverse of
`AlgebraicGeometry.Stack.diagonalLegFiberIso`.** It is the universe lift of the comparison of the
chosen pullbacks of the 2-fibre product with those of its first factor. -/
lemma diagonalLegFiberIso_inv_app_fst (V : BigFppfOver B S hS)
    (o : letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
        (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.SplitFiber V) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
    letI : (TwoFibreProductOver.structureFunctor 𝒳.val.p 𝒳.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor f)).IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
    ((diagonalLegFiberIso B S hS 𝒳 𝒴 f V).inv.app o).fst =
      AsSmall.up.map
        (TwoFibreProductOver.pullbackFiberFstIsoOfFiberedInGroupoids 𝒳.val.p 𝒳.val.p 𝒴.val.p
          (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor f)
          (CatFiberedInGroupoids.homFunctor_comp_p f)
          (CatFiberedInGroupoids.homFunctor_comp_p f) o.obj o.hom
          𝒳.isFiberedInGroupoids).hom := rfl

/-- The second component of
`AlgebraicGeometry.Stack.diagonalLegFiberIso_inv_app_fst`, with the second factor. -/
lemma diagonalLegFiberIso_inv_app_snd (V : BigFppfOver B S hS)
    (o : letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
        (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.SplitFiber V) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
    letI : (TwoFibreProductOver.structureFunctor 𝒳.val.p 𝒳.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor f)).IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
    ((diagonalLegFiberIso B S hS 𝒳 𝒴 f V).inv.app o).snd =
      AsSmall.up.map
        (TwoFibreProductOver.pullbackFiberSndIsoOfFiberedInGroupoids 𝒳.val.p 𝒳.val.p 𝒴.val.p
          (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor f)
          (CatFiberedInGroupoids.homFunctor_comp_p f)
          (CatFiberedInGroupoids.homFunctor_comp_p f) o.obj o.hom
          𝒳.isFiberedInGroupoids).hom := rfl

/-- **The first component of the base-change comparison of the diagonal, read through Stacks
02XI, is the inverse chosen-pullback comparison.** This is
`CategoryTheory.TwoFibreProductOver.toFiberPullback_map_mapPullbackFiberIso_inv_fst` in the
spelling the squares of Stacks 0CMR use, the 2-cell of
`AlgebraicGeometry.Stack.splitEvaluationIso` of the diagonal being the inverse base-change
comparison. -/
lemma diagonalFiberCompare_map_splitEvaluationIso_hom_app_fst (V : BigFppfOver B S hS)
    (o : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      𝒳.val.p.SplitFiber V) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
    letI : (TwoFibreProductOver.structureFunctor 𝒳.val.p 𝒳.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor f)).IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
    ((diagonalFiberCompare B S hS 𝒳 𝒴 f V).map
        ((splitEvaluationIso B S hS
          (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f) V).hom.app
          o)).fst =
      (TwoFibreProductOver.pullbackFiberFstIsoOfFiberedInGroupoids 𝒳.val.p 𝒳.val.p 𝒴.val.p
        (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor f)
        (CatFiberedInGroupoids.homFunctor_comp_p f)
        (CatFiberedInGroupoids.homFunctor_comp_p f)
        ((Functor.fiberFunctorOfCompEq
          (isFibredOneMorphism B S hS
            (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f)).comp_eq o.base).obj
              o.obj) o.hom
        𝒳.isFiberedInGroupoids).inv :=
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
  let : (TwoFibreProductOver.structureFunctor 𝒳.val.p 𝒳.val.p 𝒴.val.p
    (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor f)).IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
  TwoFibreProductOver.toFiberPullback_map_mapPullbackFiberIso_inv_fst 𝒳.val.p
    𝒴.val.p (CatFiberedInGroupoids.homFunctor f)
    (isFibredOneMorphism B S hS (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f))
      𝒳.isFiberedInGroupoids o.obj o.hom

/-- The second component of
`AlgebraicGeometry.Stack.diagonalFiberCompare_map_splitEvaluationIso_hom_app_fst`. -/
lemma diagonalFiberCompare_map_splitEvaluationIso_hom_app_snd (V : BigFppfOver B S hS)
    (o : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      𝒳.val.p.SplitFiber V) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
    letI : (TwoFibreProductOver.structureFunctor 𝒳.val.p 𝒳.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor f)).IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
    ((diagonalFiberCompare B S hS 𝒳 𝒴 f V).map
        ((splitEvaluationIso B S hS
          (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f) V).hom.app
          o)).snd =
      (TwoFibreProductOver.pullbackFiberSndIsoOfFiberedInGroupoids 𝒳.val.p 𝒳.val.p 𝒴.val.p
        (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor f)
        (CatFiberedInGroupoids.homFunctor_comp_p f)
        (CatFiberedInGroupoids.homFunctor_comp_p f)
        ((Functor.fiberFunctorOfCompEq
          (isFibredOneMorphism B S hS
            (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f)).comp_eq o.base).obj
              o.obj) o.hom
        𝒳.isFiberedInGroupoids).inv :=
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
  let : (TwoFibreProductOver.structureFunctor 𝒳.val.p 𝒳.val.p 𝒴.val.p
    (CatFiberedInGroupoids.homFunctor f) (CatFiberedInGroupoids.homFunctor f)).IsFibered :=
    (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
  TwoFibreProductOver.toFiberPullback_map_mapPullbackFiberIso_inv_snd 𝒳.val.p
    𝒴.val.p (CatFiberedInGroupoids.homFunctor f)
    (isFibredOneMorphism B S hS (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f))
      𝒳.isFiberedInGroupoids o.obj o.hom

/-- **The object of the split fibre at the cone point that a stage object of the diagonal's
diagram restricts to**: the image of the object under the fibre of the diagonal. -/
lemma diagonalLegRestrict_obj_fiberDiagramMap_obj
    (E : I ⥤ BigFppfOver B S hS) (d : Cone E) (j : Iᵒᵖ)
    (y₀ : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      𝒳.val.p.SplitFiber (E.obj j.unop)) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
    ((diagonalLegRestrict B S hS 𝒳 𝒴 f E d j).obj
        (((fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS
          (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f) E).app j).toFunctor.obj
          (AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj y₀))).obj =
      (Functor.fiberFunctorOfCompEq
        (isFibredOneMorphism B S hS
          (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f)).comp_eq y₀.base).obj
            y₀.obj := rfl

/-- The morphism of
`AlgebraicGeometry.Stack.diagonalLegRestrict_obj_fiberDiagramMap_obj`: the cone projection
followed by the morphism of the stage object. -/
lemma diagonalLegRestrict_obj_fiberDiagramMap_hom
    (E : I ⥤ BigFppfOver B S hS) (d : Cone E) (j : Iᵒᵖ)
    (y₀ : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      𝒳.val.p.SplitFiber (E.obj j.unop)) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    letI : (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).val.p.IsFibered :=
      (BigFppfOver.twoFibreProduct.{u, v, w} B S hS 𝒳 𝒴 𝒳 f f).2.isFibered
    ((diagonalLegRestrict B S hS 𝒳 𝒴 f E d j).obj
        (((fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS
          (BigFppfOver.twoFibreProductDiagonal.{u, v, w} B S hS 𝒳 𝒴 f) E).app j).toFunctor.obj
          (AsSmall.up.{max u v, max (u + 1) v w, max v w}.obj y₀))).hom =
      d.π.app j.unop ≫ y₀.hom := rfl

end AlgebraicGeometry.Stack

end

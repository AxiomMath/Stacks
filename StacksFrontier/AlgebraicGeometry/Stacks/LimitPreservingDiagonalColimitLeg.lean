module

public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingBaseChangeEvaluation
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingCanonicalCellStage

/-!
# The cospan changes through which the lower leg of Stacks 0CMW's diagonal square factors

The two squares that Stacks 0CMW compares have, for their lower right corners, the universe lift
of the fibre of `𝒳 ×_{f, 𝒴, f} 𝒳` at the cone point on one side and the 2-fibre product
`AsSmall 𝒳_U ×_{AsSmall 𝒴_U} AsSmall 𝒳_U` on the other. At a stage of the colimit, both lower
legs are composites of changes of cospan (`CategoryTheory.Limits.CategoricalPullback.map`,
Stacks 02XA) applied to the three functors that make up the colimit comparison of Stacks 004A.
This file defines these changes of cospan.

## Main definitions

* `AlgebraicGeometry.Stack.splitFiberCospanUp`: the universe lift of the cospan of split fibres
  at a stage.
* `AlgebraicGeometry.Stack.splitFiberCospanRestrict`: strict restriction of split fibres along a
  cone projection.
* `AlgebraicGeometry.Stack.splitFiberCospanEval`: evaluation of split fibres in the fibre, filled
  by `AlgebraicGeometry.Stack.splitEvaluationIso`.
* `AlgebraicGeometry.Stack.fiberCospanUp`: the universe lift of the cospan of fibres at a point.

## References

* [Stacks Project, Tag 0CMW](https://stacks.math.columbia.edu/tag/0CMW)
* [Stacks Project, Tag 0CMR](https://stacks.math.columbia.edu/tag/0CMR)
* [Stacks Project, Tag 02XA](https://stacks.math.columbia.edu/tag/02XA)
* [Stacks Project, Tag 004A](https://stacks.math.columbia.edu/tag/004A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u v w

attribute [local implicit_reducible] Bicategory.InducedBicategory Functor.Fiber
  Functor.Fiber.fiberInclusion Functor.SplitFiber.restrict Deformation.Artin.fiberCocone
  Deformation.Artin.fiberDiagram Functor.splitPresheaf Cat.asSmallFunctor

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 𝒴 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w} (BigFppfOver B S hS))
  (f : 𝒳 ⟶ 𝒴) {I : Type v} [Category.{w} I]

/-- **The universe lift of the cospan of split fibres at a stage, read on 2-fibre products.** -/
noncomputable abbrev splitFiberCospanUp (E : I ⥤ BigFppfOver B S hS) (j : Iᵒᵖ) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    CategoricalPullback (splitFiberMap B S hS f (E.obj j.unop))
        (splitFiberMap B S hS f (E.obj j.unop)) ⥤
      CategoricalPullback
        ((fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E).app j).toFunctor
        ((fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E).app j).toFunctor :=
  letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  CategoricalPullback.map (splitFiberMap B S hS f (E.obj j.unop))
    (splitFiberMap B S hS f (E.obj j.unop)) AsSmall.up AsSmall.up AsSmall.up
    ((fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E).app j).toFunctor
    ((fiberDiagramMap.{u, v, w, max (u + 1) v w, max u v} B S hS f E).app j).toFunctor
    (eqToIso (asSmall_up_comp_fiberDiagramMap_app B S hS f E j))
    (eqToIso (asSmall_up_comp_fiberDiagramMap_app B S hS f E j).symm)

/-- **Strict restriction along the cone projection `d.π.app j.unop`, read on 2-fibre products of
split fibres.** -/
noncomputable abbrev splitFiberCospanRestrict (E : I ⥤ BigFppfOver B S hS) (d : Cone E)
    (j : Iᵒᵖ) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    CategoricalPullback (splitFiberMap B S hS f (E.obj j.unop))
        (splitFiberMap B S hS f (E.obj j.unop)) ⥤
      CategoricalPullback (splitFiberMap B S hS f d.pt) (splitFiberMap B S hS f d.pt) :=
  letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  CategoricalPullback.map (splitFiberMap B S hS f (E.obj j.unop))
    (splitFiberMap B S hS f (E.obj j.unop))
    (Functor.SplitFiber.restrict 𝒳.val.p (d.π.app j.unop))
    (Functor.SplitFiber.restrict 𝒳.val.p (d.π.app j.unop))
    (Functor.SplitFiber.restrict 𝒴.val.p (d.π.app j.unop))
    (splitFiberMap B S hS f d.pt) (splitFiberMap B S hS f d.pt)
    (eqToIso (splitFiberMap_naturality B S hS f (d.π.app j.unop)))
    (eqToIso (splitFiberMap_naturality B S hS f (d.π.app j.unop)).symm)

/-- **Evaluation of split fibres at `V`, read on 2-fibre products.** This is the change of
cospan from `splitFiberMap B S hS f V` against itself to the fibre functor of `f` at `V` against
itself, filled by `AlgebraicGeometry.Stack.splitEvaluationIso`. -/
noncomputable abbrev splitFiberCospanEval (V : BigFppfOver B S hS) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    CategoricalPullback (splitFiberMap B S hS f V) (splitFiberMap B S hS f V) ⥤
      CategoricalPullback
        (Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) V)
        (Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) V) :=
  letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  CategoricalPullback.map (splitFiberMap B S hS f V) (splitFiberMap B S hS f V)
    (Deformation.Artin.evaluateSplitFiber 𝒳.val.p V)
    (Deformation.Artin.evaluateSplitFiber 𝒳.val.p V)
    (Deformation.Artin.evaluateSplitFiber 𝒴.val.p V)
    (Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) V)
    (Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) V)
    (splitEvaluationIso B S hS f V) (splitEvaluationIso B S hS f V).symm

/-- **The universe lift of the cospan of fibres at `V`, read on 2-fibre products.** -/
noncomputable abbrev fiberCospanUp (V : BigFppfOver B S hS) :
    CategoricalPullback
        (Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) V)
        (Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) V) ⥤
      CategoricalPullback
        (AsSmall.down.{max u v, max (u + 1) v w, max (u + 1) v w} ⋙
          Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) V ⋙
          AsSmall.up.{max u v, max (u + 1) v w, max (u + 1) v w})
        (AsSmall.down.{max u v, max (u + 1) v w, max (u + 1) v w} ⋙
          Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) V ⋙
          AsSmall.up.{max u v, max (u + 1) v w, max (u + 1) v w}) :=
  CategoricalPullback.map
    (Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) V)
    (Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) V)
    AsSmall.up AsSmall.up AsSmall.up
    (AsSmall.down ⋙ Functor.fiberFunctorOfCompEq
      (CatFiberedInGroupoids.homFunctor_comp_p f) V ⋙ AsSmall.up)
    (AsSmall.down ⋙ Functor.fiberFunctorOfCompEq
      (CatFiberedInGroupoids.homFunctor_comp_p f) V ⋙ AsSmall.up)
    (eqToIso rfl) (eqToIso rfl)

end AlgebraicGeometry.Stack

end

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingCanonicalCell
public import StacksFrontier.CategoryTheory.Limits.FilteredColimitCatStagewiseEquivalence

/-!
# Faithfulness of the colimit comparison of a faithful 1-morphism

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf category of
a scheme `S` whose underlying functor is faithful — as it is when `f` is representable by
algebraic spaces, by Stacks 04Y5. This file proves that the comparison functor

`colim 𝒳_{Uᵢ} ⟶ 𝒳_U ×_{𝒴_U} colim 𝒴_{Uᵢ}`

out of the canonical square of Stacks 0CMR is faithful. It is the step of the proof of
Stacks 0CMV that the source records as "since `p` is faithful on fibre categories we see that the
functor is faithful".

## Main results

* `AlgebraicGeometry.Stack.faithful_toCategoricalPullbackFunctor_canonicalSquare`: the comparison
  out of `AlgebraicGeometry.Stack.canonicalSquare` is faithful.

## Implementation notes

Faithfulness is read off the second projection alone: the comparison composed with the projection
to `colim 𝒴_{Uᵢ}` is `colimMap` of the stagewise maps of split fibres, so it suffices that that
functor be faithful, and a functor whose composite with another is faithful is faithful.

`CategoryTheory.Cat.faithful_colimMap` reduces faithfulness of the colimit map to faithfulness at
every stage, and at a stage `AlgebraicGeometry.Stack.splitFiberMap` acts on a morphism of split
fibres by conjugating the induced map of fibres with the base-change comparisons of the fibred
1-morphism. Conjugation by isomorphisms is cancellable and the passage between a morphism of split
fibres and the underlying morphism of fibres is injective, so faithfulness at a stage is
faithfulness of `CategoryTheory.Functor.fiberFunctorOfCompEq`, which in turn is faithfulness of
the underlying functor because that functor's action on a fibre morphism *is* its action on the
underlying morphism of `𝒳`.

## References

* [Stacks Project, Tag 0CMV](https://stacks.math.columbia.edu/tag/0CMV)
* [Stacks Project, Tag 0CMR](https://stacks.math.columbia.edu/tag/0CMR)
* [Stacks Project, Tag 02ZY](https://stacks.math.columbia.edu/tag/02ZY)
* [Stacks Project, Tag 04Y5](https://stacks.math.columbia.edu/tag/04Y5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u v w uX vX

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion
  Functor.SplitFiber.restrict

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : CatFiberedInGroupoids.{u, vX, u + 1, uX} (BigFppfOver B S hS)}

/-- **A 1-morphism with faithful underlying functor is faithful on fibres.** The functor induced
on the fibre over `V` acts on a morphism of the fibre by applying the underlying functor to the
underlying morphism, so it is injective on morphisms as soon as that functor is. -/
theorem faithful_fiberFunctorOfCompEq_of_faithful (f : 𝒳 ⟶ 𝒴)
    (hf : (CatFiberedInGroupoids.homFunctor f).Faithful) (V : BigFppfOver B S hS) :
    (Functor.fiberFunctorOfCompEq
      (CatFiberedInGroupoids.homFunctor_comp_p f) V).Faithful where
  map_injective {a b} φ φ' h := by
    refine Functor.Fiber.hom_ext (hf.map_injective ?_)
    simpa only [Functor.fiberInclusion_map_fiberFunctorOfCompEq_map] using
      congrArg Functor.Fiber.fiberInclusion.map h

/-- **A 1-morphism with faithful underlying functor is faithful on split fibres.** -/
theorem faithful_splitFiberMap_of_faithful (f : 𝒳 ⟶ 𝒴)
    (hf : (CatFiberedInGroupoids.homFunctor f).Faithful) (V : BigFppfOver B S hS) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    (splitFiberMap B S hS f V).Faithful := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let := faithful_fiberFunctorOfCompEq_of_faithful B S hS f hf V
  refine ⟨fun {o o'} α β h => Functor.SplitFiber.toFiberHom_injective ?_⟩
  have h' := congrArg Functor.SplitFiber.toFiberHom h
  dsimp only [splitFiberMap] at h'
  simp only [Functor.SplitFiber.toFiberHom_ofFiberHom] at h'
  exact Functor.Faithful.map_injective
    ((cancel_mono _).mp ((cancel_epi _).mp h'))

variable {I : Type v} [Category.{w} I]

/-- **The stagewise map of the canonical square is faithful**, for a 1-morphism whose underlying
functor is faithful. -/
theorem faithful_fiberDiagramMap_app_of_faithful (f : 𝒳 ⟶ 𝒴)
    (hf : (CatFiberedInGroupoids.homFunctor f).Faithful) (E : I ⥤ BigFppfOver B S hS)
    (j : Iᵒᵖ) :
    ((fiberDiagramMap B S hS f E).app j).toFunctor.Faithful := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let := faithful_splitFiberMap_of_faithful B S hS f hf (E.obj j.unop)
  change (AsSmall.down ⋙ splitFiberMap B S hS f (E.obj j.unop) ⋙ AsSmall.up).Faithful
  infer_instance

/-- **Faithfulness of the comparison out of the canonical square of Stacks 0CMR**, for a
1-morphism whose underlying functor is faithful. This is the step of Stacks 0CMV that the source
records as "since `p` is faithful on fibre categories we see that the functor is faithful". -/
theorem faithful_toCategoricalPullbackFunctor_canonicalSquare [IsCofiltered I] (f : 𝒳 ⟶ 𝒴)
    (hf : (CatFiberedInGroupoids.homFunctor f).Faithful) (E : I ⥤ BigFppfOver B S hS)
    (d : Cone E) :
    (Cat.toCategoricalPullbackFunctor
      (canonicalSquare.{u, v, w, uX, vX} B S hS f E d)).Faithful := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let : (colimMap (fiberDiagramMap B S hS f E)).toFunctor.Faithful :=
    Cat.faithful_colimMap.{max vX (u + 1) uX u, v, w} (fiberDiagramMap B S hS f E)
      (faithful_fiberDiagramMap_app_of_faithful B S hS f hf E)
  refine ⟨fun {P Q} α β h => ?_⟩
  exact Functor.Faithful.map_injective
    (F := (colimMap (fiberDiagramMap B S hS f E)).toFunctor)
    (congrArg Limits.CategoricalPullback.Hom.snd h)

end AlgebraicGeometry.Stack

end

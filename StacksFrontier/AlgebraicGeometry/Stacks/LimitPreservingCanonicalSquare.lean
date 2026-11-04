module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingMorphism

/-!
# The canonical square of Stacks 0CMR attached to a 1-morphism

`AlgebraicGeometry.Stack.IsLimitPreserving` and
`AlgebraicGeometry.Stack.IsFullyFaithfulOnAffineLimits` quantify over the data `(T, H, η)` of the
square of Stacks 0CMR and pin it down: `T` is componentwise
`AlgebraicGeometry.Stack.splitFiberMap`, `H` is the colimit of `T`, and `η` is on every colimit
generator the base-change comparison of the fibred 1-morphism. Proving either property of a
*given* 1-morphism therefore requires exhibiting that data, and this file constructs it.

The diagram of fibres is `Deformation.Artin.fiberDiagram p E = E.op ⋙ Functor.splitPresheaf p ⋙
Cat.asSmallFunctor`, so `T` is obtained by whiskering a morphism of split presheaves, and the
only thing to prove is that `AlgebraicGeometry.Stack.splitFiberMap` commutes with the strict
restriction functors of Stacks 004A.

## Main definitions

* `AlgebraicGeometry.Stack.splitPresheafMap`: the morphism of split presheaves of Stacks 004A
  induced by a 1-morphism of categories fibred in groupoids.
* `AlgebraicGeometry.Stack.fiberDiagramMap`: the natural transformation of diagrams of fibres,
  the `T` of the square of Stacks 0CMR.
* `AlgebraicGeometry.Stack.splitEvaluationIso`: the 2-cell of the square of Stacks 0CMR at a
  single stage, the base-change comparison of the fibred 1-morphism read on split fibres.

## Main results

* `AlgebraicGeometry.Stack.splitFiberMap_naturality`: `splitFiberMap` commutes with strict
  restriction.
* `AlgebraicGeometry.Stack.fiberDiagramMap_app`: the first pinning condition of Stacks 0CMR,
  which holds definitionally.

What is *not* here is the 2-cell `η` of the square itself: assembling it out of
`AlgebraicGeometry.Stack.splitEvaluationIso` needs the compatibility of
`colimMap (fiberDiagramMap …)` with the two restriction cocones, and `H = colimMap T` is then
forced. That is done in
`StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingCanonicalCell`, which assembles all three
pieces of pinned data and reduces both `AlgebraicGeometry.Stack.IsLimitPreserving` and
`AlgebraicGeometry.Stack.IsFullyFaithfulOnAffineLimits` to a property of the resulting square
alone.

## Implementation notes

The naturality of `splitFiberMap` is an equality of functors between strict split fibres, and the
two functors agree on objects on the nose, so it is proved with
`CategoryTheory.Functor.hext`. On morphisms both sides are determined by their composite with the
cartesian projection of the restricted object, which is
`CategoryTheory.Functor.SplitFiber.restrictHom_uniq`; the identity that comes out is the
compatibility of the base-change comparison
`CategoryTheory.Functor.IsFibredOneMorphism.mapPullbackFiberIso` with composition of the two
morphisms of the slice, which is
`CategoryTheory.Functor.IsFibredOneMorphism.pullbackFiberMap_mapPullbackFiberIso_hom`.

## References

* [Stacks Project, Tag 0CMR](https://stacks.math.columbia.edu/tag/0CMR)
* [Stacks Project, Tag 004A](https://stacks.math.columbia.edu/tag/004A)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u v w uX vX

attribute [local implicit_reducible] Bicategory.InducedBicategory Functor.Fiber
  Functor.Fiber.fiberInclusion Functor.SplitFiber.restrict

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : CatFiberedInGroupoids.{u, vX, u + 1, uX} (BigFppfOver B S hS)}

/-- **`AlgebraicGeometry.Stack.splitFiberMap` commutes with strict restriction.** Restricting an
object of the split fibre of `𝒳` over `W` to `V` and then pushing it to `𝒴` is the same as
pushing it to `𝒴` and then restricting. -/
lemma splitFiberMap_naturality (f : 𝒳 ⟶ 𝒴)
    {V W : BigFppfOver B S hS} (g : V ⟶ W) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    Functor.SplitFiber.restrict 𝒳.val.p g ⋙ splitFiberMap B S hS f V =
      splitFiberMap B S hS f W ⋙ Functor.SplitFiber.restrict 𝒴.val.p g := by
  let : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  let hF := isFibredOneMorphism B S hS f
  apply CategoryTheory.Functor.hext
  · intro a
    rfl
  intro a b α
  apply heq_of_eq
  apply Functor.SplitFiber.toFiberHom_injective
  dsimp only [Functor.comp_map, splitFiberMap, Functor.SplitFiber.restrict]
  simp only [Functor.SplitFiber.toFiberHom_ofFiberHom]
  apply Functor.SplitFiber.restrictHom_uniq
    (o := (splitFiberMap B S hS f W).obj a)
    (o' := (splitFiberMap B S hS f W).obj b) g
  dsimp only [splitFiberMap, Functor.SplitFiber.proj]
  have hn := hF.pullbackFiberMap_mapPullbackFiberIso_hom a.obj
    (g₁ := Over.mk (g ≫ a.hom)) (g₂ := Over.mk a.hom) (Over.homMk g rfl)
  simp only [Over.mk_hom] at hn
  simp only [Functor.map_comp, Functor.fiberInclusion_map_fiberFunctorOfCompEq_map]
  rw [Category.assoc, Category.assoc,
    Functor.IsFibredOneMorphism.mapPullbackFiberIso_inv_fac, ← Functor.map_comp,
    Functor.SplitFiber.restrictHom_fac, Functor.map_comp, Functor.map_comp]
  dsimp only [Functor.pullbackFiberProj]
  rw [← Category.assoc, ← hn, Category.assoc, Category.assoc]
  dsimp only [Functor.SplitFiber.proj]
  simp only [Category.assoc, Functor.IsFibredOneMorphism.mapPullbackFiberIso_inv_fac]

/-- The morphism of split presheaves of Stacks 004A induced by a 1-morphism of categories fibred
in groupoids: at `V` it is `AlgebraicGeometry.Stack.splitFiberMap`. -/
noncomputable def splitPresheafMap (f : 𝒳 ⟶ 𝒴) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    Functor.splitPresheaf 𝒳.val.p ⟶ Functor.splitPresheaf 𝒴.val.p :=
  letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  { app := fun V => (splitFiberMap B S hS f V.unop).toCatHom
    naturality := fun _ _ g => Cat.Hom.ext (splitFiberMap_naturality B S hS f g.unop) }

/-- The component of `AlgebraicGeometry.Stack.splitPresheafMap` at `V` is
`AlgebraicGeometry.Stack.splitFiberMap` at `V`. -/
@[simp]
lemma splitPresheafMap_app (f : 𝒳 ⟶ 𝒴) (V : (BigFppfOver B S hS)ᵒᵖ) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    (splitPresheafMap B S hS f).app V = (splitFiberMap B S hS f V.unop).toCatHom := rfl

variable {I : Type v} [Category.{w} I]

/-- **The `T` of the square of Stacks 0CMR.** The natural transformation of diagrams of fibres
induced by a 1-morphism of categories fibred in groupoids, obtained by whiskering
`AlgebraicGeometry.Stack.splitPresheafMap`. -/
noncomputable def fiberDiagramMap (f : 𝒳 ⟶ 𝒴) (E : I ⥤ BigFppfOver B S hS) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    Deformation.Artin.fiberDiagram 𝒳.val.p E ⟶ Deformation.Artin.fiberDiagram 𝒴.val.p E :=
  letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  Functor.whiskerRight (Functor.whiskerLeft E.op (splitPresheafMap B S hS f))
    Cat.asSmallFunctor.{max v w}

/-- **The first pinning condition of Stacks 0CMR.** The component of
`AlgebraicGeometry.Stack.fiberDiagramMap` at a stage is the universe lift of
`AlgebraicGeometry.Stack.splitFiberMap` at that stage. -/
lemma fiberDiagramMap_app (f : 𝒳 ⟶ 𝒴) (E : I ⥤ BigFppfOver B S hS) (i : I) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    (fiberDiagramMap B S hS f E).app (op i) =
      (AsSmall.down ⋙ splitFiberMap B S hS f (E.obj i) ⋙ AsSmall.up).toCatHom := rfl

/-- **The two universe lifts cancel.** Precomposing a stage of
`AlgebraicGeometry.Stack.fiberDiagramMap` with `CategoryTheory.AsSmall.up` undoes the
`CategoryTheory.AsSmall.down` built into it, leaving `AlgebraicGeometry.Stack.splitFiberMap`
followed by the lift. Stated as an equality of functors so that the 2-cells of a comparison out
of a stagewise 2-fibre product can be transports rather than reflexivity isomorphisms, which are
type-correct only at default transparency. -/
lemma asSmall_up_comp_fiberDiagramMap_app (f : 𝒳 ⟶ 𝒴) (E : I ⥤ BigFppfOver B S hS) (j : Iᵒᵖ) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    AsSmall.up ⋙ ((fiberDiagramMap B S hS f E).app j).toFunctor =
      splitFiberMap B S hS f (E.obj j.unop) ⋙ AsSmall.up := rfl

/-- **The transition functor of the diagram of split fibres is the universe lift of strict
restriction.** Stated as an equality of functors so that transporting along it is available to
`CategoryTheory.Functor.congr_hom`: the two sides have types that agree only definitionally, and a
tactic working at `implicit` transparency cannot cross that gap on its own. -/
lemma fiberDiagram_map_toFunctor (E : I ⥤ BigFppfOver B S hS) {j k : Iᵒᵖ} (s : j ⟶ k) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    ((Deformation.Artin.fiberDiagram 𝒳.val.p E).map s).toFunctor =
      AsSmall.down ⋙ Functor.SplitFiber.restrict 𝒳.val.p (E.map s.unop) ⋙ AsSmall.up := rfl

/-- **The 2-cell of the square of Stacks 0CMR at a stage.** Evaluating a split fibre of `𝒳` and
then pushing it to `𝒴` is, up to the base-change comparison of the fibred 1-morphism, the same as
pushing the split fibre to `𝒴` and then evaluating. -/
noncomputable def splitEvaluationIso (f : 𝒳 ⟶ 𝒴) (V : BigFppfOver B S hS) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    Deformation.Artin.evaluateSplitFiber 𝒳.val.p V ⋙
        Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p f) V ≅
      splitFiberMap B S hS f V ⋙ Deformation.Artin.evaluateSplitFiber 𝒴.val.p V := by
  letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
  refine NatIso.ofComponents
    (fun x => ((isFibredOneMorphism B S hS f).mapPullbackFiberIso x.obj x.hom).symm) ?_
  intro x y α
  dsimp [Deformation.Artin.evaluateSplitFiber, splitFiberMap]
  simp [Functor.SplitFiber.toFiberHom]

/-- **The 2-cell of `AlgebraicGeometry.Stack.splitEvaluationIso` at an object of the split
fibre** is the inverse of the base-change comparison of the fibred 1-morphism there. -/
lemma splitEvaluationIso_hom_app (f : 𝒳 ⟶ 𝒴) (V : BigFppfOver B S hS)
    (o : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      𝒳.val.p.SplitFiber V) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    (splitEvaluationIso B S hS f V).hom.app o =
      ((isFibredOneMorphism B S hS f).mapPullbackFiberIso o.obj o.hom).inv := rfl

/-- `AlgebraicGeometry.Stack.splitEvaluationIso_hom_app` on the inverse side. -/
lemma splitEvaluationIso_inv_app (f : 𝒳 ⟶ 𝒴) (V : BigFppfOver B S hS)
    (o : letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
      𝒳.val.p.SplitFiber V) :
    letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
    letI : 𝒴.val.p.IsFibered := 𝒴.2.isFibered
    (splitEvaluationIso B S hS f V).inv.app o =
      ((isFibredOneMorphism B S hS f).mapPullbackFiberIso o.obj o.hom).hom := rfl

end AlgebraicGeometry.Stack

end

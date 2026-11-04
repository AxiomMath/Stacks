module

public import Mathlib.CategoryTheory.Category.Cat.Colimit
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.FiberedCategory.ChoiceOfPullbacks
public import StacksFrontier.CategoryTheory.FiberedCategory.SplitFiberEvaluation
public import StacksFrontier.CategoryTheory.FiberedCategory.Strictification
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoCategory

/-!
# Limit preserving categories fibred in groupoids

A category fibred in groupoids over the big fppf site of `S` is *limit preserving* when,
for every directed inverse system of affine schemes over `S` with limit `T`, the canonical
functor `colim 𝒳_{Tᵢ} ⥤ 𝒳_T` is an equivalence of categories.

The fibres are taken in the split replacement of the fibred category, whose fibres are
equivalent to the original ones and whose restriction functors compose on the nose, and the
colimit is the categorical colimit in `Cat` of the resulting diagram, after `AsSmall` raises
object and morphism universes to a common universe containing the index category.

## Main definitions

* `Deformation.Artin.evaluateSplitFiber`: evaluation of a split fibre in the original
  fibre; an equivalence of categories.
* `Deformation.Artin.fiberDiagram`: the strict contravariant diagram of fibres.
* `Deformation.Artin.colimitComparison`: the canonical functor from the colimit of the
  stage fibres to the fibre over the cone point.
* `Deformation.Artin.IsLimitPreserving`: the requirement that this functor be an
  equivalence for every affine cofiltered limit over the base scheme.

## Main results

* `Deformation.Artin.colimitComparisonStageIso`: the comparison on each stage is pullback
  along the corresponding cone projection.

## References

* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
* [Stacks Project, Tag 004A](https://stacks.math.columbia.edu/tag/004A)
* [Stacks Project, Tag 02XY](https://stacks.math.columbia.edu/tag/02XY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace Deformation.Artin

universe u v w uC vC uX vX

section Comparison

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion
  Functor.chosenPullbacks

variable {C : Type uC} [Category.{vC} C] {X : Type uX} [Category.{vX} X]
  (p : X ⥤ C) [p.IsFibered]

/-- Evaluation of the split fibre in the original fibre; it is an equivalence of categories
(`CategoryTheory.Functor.SplitFiber.fiberEquiv`). -/
public noncomputable def evaluateSplitFiber (V : C) : p.SplitFiber V ⥤ p.Fiber V :=
  Functor.SplitFiber.evaluation p V

/-- The comparison between iterated pullback and restriction in the split model commutes with
the projection to the first pullback. -/
@[reassoc]
public lemma pullbackComparison_proj {V W : C} (g : W ⟶ V) (x : p.SplitFiber V) :
    Functor.Fiber.fiberInclusion.map
        (Functor.pullbackFiberCompIso x.obj x.hom g).hom ≫
        Functor.pullbackFiberProj x.obj x.hom g =
      Functor.IsPreFibered.pullbackMap x.toFiber.2 g :=
  Functor.SplitFiber.pullbackFiberCompIso_hom_pullbackFiberProj p g x

/-- Evaluation intertwines strict restriction in the split model with the pullback functor. -/
public noncomputable def evaluatePullbackIso {V W : C} (g : W ⟶ V) :
    evaluateSplitFiber p V ⋙ (Functor.chosenPullbacks p).pullbackFunctor g ≅
      Functor.SplitFiber.restrict p g ⋙ evaluateSplitFiber p W :=
  Functor.SplitFiber.evaluationPullbackIso p g

variable {I : Type v} [Category.{w} I] (D : I ⥤ C)

/-- The contravariant diagram of fibres, with the strict restriction functors of the split
model and a universe lift. -/
public noncomputable def fiberDiagram : Iᵒᵖ ⥤
    Cat.{max v w vX uC uX vC, max v w vX uC uX vC} :=
  D.op ⋙ Functor.splitPresheaf p ⋙ Cat.asSmallFunctor.{max v w}

/-- The diagram of fibres has a colimit in `Cat`. -/
public instance : HasColimit (fiberDiagram p D) := by
  let : HasColimitsOfSize.{w, v}
      Cat.{max v w vX uC uX vC, max v w vX uC uX vC} :=
    hasColimitsOfSizeShrink.{w, v, max v w vX uC uX vC, max v w vX uC uX vC} _
  infer_instance

/-- The cone projections induce restriction from each stage to the cone point. -/
public noncomputable def fiberCocone (c : Cone D) : Cocone (fiberDiagram p D) where
  pt := ((Functor.splitPresheaf p) ⋙ Cat.asSmallFunctor.{max v w}).obj (op c.pt)
  ι :=
    { app i := ((Functor.splitPresheaf p) ⋙ Cat.asSmallFunctor.{max v w}).map
        (c.π.app i.unop).op
      naturality := by
        intro i j f
        change ((Functor.splitPresheaf p) ⋙ Cat.asSmallFunctor.{max v w}).map
            (D.map f.unop).op ≫
          ((Functor.splitPresheaf p) ⋙ Cat.asSmallFunctor.{max v w}).map
            (c.π.app j.unop).op =
          ((Functor.splitPresheaf p) ⋙ Cat.asSmallFunctor.{max v w}).map
            (c.π.app i.unop).op ≫ 𝟙 _
        rw [← Functor.map_comp, ← op_comp, c.w f.unop, Category.comp_id] }

/-- The canonical comparison from the colimit of the stage fibres to the fibre at the cone
point: the descent of the restriction cocone, followed by evaluation of the split fibre. -/
public noncomputable def colimitComparison (c : Cone D) :
    (colimit (fiberDiagram p D) : Cat) ⥤ p.Fiber c.pt :=
  (colimit.desc (fiberDiagram p D) (fiberCocone p D c)).toFunctor ⋙
    AsSmall.down ⋙ evaluateSplitFiber p c.pt

/-- The comparison restricted to a stage is restriction to the cone point in the split model,
followed by evaluation in the original fibre. -/
public lemma colimitComparison_ι (c : Cone D) (i : I) :
    (colimit.ι (fiberDiagram p D) (op i)).toFunctor ⋙ colimitComparison p D c =
      AsSmall.down ⋙ Functor.SplitFiber.restrict p (c.π.app i) ⋙
        evaluateSplitFiber p c.pt := by
  rw [colimitComparison, ← Functor.assoc, ← Cat.Hom.comp_toFunctor, colimit.ι_desc]
  rfl

/-- On every stage the canonical colimit comparison is naturally isomorphic to evaluation
followed by pullback along the corresponding cone projection. -/
public noncomputable def colimitComparisonStageIso (c : Cone D) (i : I) :
    (colimit.ι (fiberDiagram p D) (op i)).toFunctor ⋙ colimitComparison p D c ≅
      AsSmall.down ⋙ evaluateSplitFiber p (D.obj i) ⋙
        (Functor.chosenPullbacks p).pullbackFunctor (c.π.app i) :=
  eqToIso (colimitComparison_ι p D c i) ≪≫
    Functor.isoWhiskerLeft AsSmall.down (evaluatePullbackIso p (c.π.app i)).symm

end Comparison

/-- A category fibred in groupoids is limit preserving if for every directed inverse
limit of affine schemes the canonical comparison `colim 𝒳_{Tᵢ} ⥤ 𝒳_T` is an equivalence
of categories. -/
@[stacks 07XL]
public abbrev IsLimitPreserving
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : CatFiberedInGroupoids.{u, vX, u + 1, uX}
      (BigFppfOver B S hS)) : Prop :=
  letI : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  ∀ (I : Type v) [Category.{w} I] [IsCofiltered I]
    (D : I ⥤ BigAffineFppf B S hS) (c : Cone D),
    IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c) →
      (colimitComparison 𝒳.val.p
        (D ⋙ BigAffineFppf.inclusion B S hS)
        ((BigAffineFppf.inclusion B S hS).mapCone c)).IsEquivalence

end Deformation.Artin

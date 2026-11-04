module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Artin.FormalObject.ApproximationEssSurj
public import StacksFrontier.Deformation.Artin.FormalObject.Predeformation
public import StacksFrontier.Deformation.Artin.FormalObject.SmoothLift

/-!
# Formal objects of a category fibred in groupoids

Formal objects of a category fibred in groupoids over the big fppf site of a scheme `S` form a
category, a `1`-morphism of categories fibred in groupoids induces a functor between the
categories of formal objects, restriction of objects over complete local rings to the
infinitesimal thickenings of the closed point gives a functor to formal objects, and for an
algebraic stack every formal object is effective.

## Main definitions

* `Deformation.Artin.FormalObject.mapFunctor`: the functor on formal objects induced by a
  `1`-morphism.

## Implementation notes

The objects of the functor are `Deformation.Artin.FormalObject.map`. The remaining notions of the
section are registered below on the declarations formalizing them: formal objects and their
morphisms (Tag 07X4), the passage to predeformation categories (Tag 0CXH), the lifting along a
formally smooth `1`-morphism (Tag 07X5), the restriction functor (Tag 07X6), effectiveness
(Tag 07X7), and the equivalence for algebraic stacks (Tag 07X8).

## References

* [Stacks Project, Tag 07X3](https://stacks.math.columbia.edu/tag/07X3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace Deformation.Artin

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)) (p : 𝒳 ⟶ 𝒴)

/-- The functor between categories of formal objects induced by a `1`-morphism of categories
fibred in groupoids: every level and every level map is pushed forward. -/
@[stacks 07X3 "a 1-morphism induces a functor between categories of formal objects"]
def FormalObject.mapFunctor : FormalObject B S hS 𝒳.val.p ⥤ FormalObject B S hS 𝒴.val.p where
  obj := FormalObject.map B S hS 𝒳 𝒴 p
  map f :=
    { app := fun n ↦ (CatFiberedInGroupoids.homFunctor p).map (f.app n)
      naturality := fun n ↦ ((CatFiberedInGroupoids.homFunctor p).map_comp _ _).symm.trans
        ((congrArg (CatFiberedInGroupoids.homFunctor p).map (f.naturality n)).trans
          ((CatFiberedInGroupoids.homFunctor p).map_comp _ _)) }
  map_id _ := FormalObject.Hom.ext fun _ ↦ (CatFiberedInGroupoids.homFunctor p).map_id _
  map_comp _ _ := FormalObject.Hom.ext fun _ ↦ (CatFiberedInGroupoids.homFunctor p).map_comp _ _

end Deformation.Artin

add_to_stacks 07X3 "formal objects" Deformation.Artin.FormalObject
add_to_stacks 07X3 "morphisms of formal objects" Deformation.Artin.FormalObject.Hom
add_to_stacks 07X3 "the formal object of a predeformation category"
  Deformation.Artin.FormalObject.exists_predeformationFormalObject
add_to_stacks 07X3 "lifting formal objects along a formally smooth 1-morphism"
  Deformation.Artin.exists_formalObject_lift
add_to_stacks 07X3 "the functor to formal objects" Deformation.Artin.approximationFunctorData
add_to_stacks 07X3 "effective formal objects" Deformation.Artin.FormalObject.IsEffective
add_to_stacks 07X3 "for an algebraic stack every formal object is effective"
  Deformation.Artin.isEquivalence_approximationFunctor_algebraicStacks

module

public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoCategory
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.FiberIso
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.PullbackFiberHom

/-!
# Formally smooth on objects (Stacks 06D0)

A 1-morphism `p : 𝒳 ⟶ 𝒴` of categories fibred in groupoids over the big fppf site of a
scheme `S` is *formally smooth on objects* when, for every first-order thickening `i : U ⟶ U'`
of affine objects of the site, every object of `𝒳` over `U` together with an identification
of its image with the restriction of an object of `𝒴` over `U'` lifts to an object of `𝒳`
over `U'`, compatibly.

## Main definitions

* `AlgebraicGeometry.Stack.IsFormallySmoothOnObjects`: the first-order lifting condition,
  including the compatibility equation.
* `AlgebraicGeometry.Stack.IsFormallySmoothOnObjectsOn`: the same condition for those
  thickenings whose larger object lies in a prescribed class.

## Main results

* `AlgebraicGeometry.Stack.IsFormallySmoothOnObjects.isFormallySmoothOnObjectsOn`: formal
  smoothness on objects gives the lifting condition for every class of larger test objects.
* `AlgebraicGeometry.Stack.isFormallySmoothOnObjectsOn_true_iff`: against the class of all
  objects the lifting condition is formal smoothness on objects.

## References

* [Stacks Project, Tag 06D0](https://stacks.math.columbia.edu/tag/06D0)
* [Stacks Project, Tag 0DNW](https://stacks.math.columbia.edu/tag/0DNW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Stacks.Thickenings

namespace AlgebraicGeometry.Stack

universe u v w

/-- The first-order lifting condition for a 1-morphism of categories fibred in groupoids, with
the comparison square required to commute: the restriction along a first-order thickening of
affine objects is the chosen pullback `CategoryTheory.Functor.pullbackFiber`. -/
@[stacks 06D0,
  stacks 0DNW "formal smoothness of a morphism of algebraic stacks is formal smoothness on"]
def IsFormallySmoothOnObjects
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (BigFppfOver B S hS)) (p : 𝒳 ⟶ 𝒴) : Prop :=
  letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  letI : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  let F := CatFiberedInGroupoids.homFunctor p
  let hF := CatFiberedInGroupoids.homFunctor_comp_p p
  let pU := fun U => Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p F hF U
  let compare := fun (U U' : BigFppfOver B S hS)
      (i : U ⟶ U') (x' : 𝒳.val.p.Fiber U') =>
    Functor.fiberIsoOfCartesian (p := 𝒴.val.p) i
      (Functor.IsPreFibered.pullbackMap ((pU U').obj x').2 i)
      (F.map (Functor.IsPreFibered.pullbackMap x'.2 i))
      (by infer_instance)
      (@Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian _ _ _ _ _ _ _ _ _ _ _
        (CatFiberedInGroupoids.isStronglyCartesian_map p i
          (Functor.IsPreFibered.pullbackMap x'.2 i)))
  ∀ (U U' : BigFppfOver B S hS) (i : U ⟶ U'),
    IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
    IsAffine ((BigFppfOver.toScheme B S hS).obj U') →
    Stacks.Thickenings.IsFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map i) →
    ∀ (x : 𝒳.val.p.Fiber U) (y' : 𝒴.val.p.Fiber U')
      (γ : (pU U).obj x ≅ Functor.pullbackFiber 𝒴.val.p y' i),
      ∃ (x' : 𝒳.val.p.Fiber U')
        (β : Functor.pullbackFiber 𝒳.val.p x' i ≅ x)
        (γ' : (pU U').obj x' ≅ y'),
        ((compare U U' i x').hom ≫
          (pU U).map β.hom) ≫ γ.hom =
          Functor.pullbackFiberHom (p := 𝒴.val.p) γ'.hom i

/-- The first-order lifting condition of `AlgebraicGeometry.Stack.IsFormallySmoothOnObjects`,
for those first-order thickenings `i : U ⟶ U'` of affine objects whose larger object `U'`
satisfies `P`. -/
def IsFormallySmoothOnObjectsOn
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : BigFppfOver B S hS → Prop)
    (𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w}
      (BigFppfOver B S hS)) (p : 𝒳 ⟶ 𝒴) : Prop :=
  letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  letI : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  let F := CatFiberedInGroupoids.homFunctor p
  let hF := CatFiberedInGroupoids.homFunctor_comp_p p
  let pU := fun U => Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p F hF U
  let compare := fun (U U' : BigFppfOver B S hS)
      (i : U ⟶ U') (x' : 𝒳.val.p.Fiber U') =>
    Functor.fiberIsoOfCartesian (p := 𝒴.val.p) i
      (Functor.IsPreFibered.pullbackMap ((pU U').obj x').2 i)
      (F.map (Functor.IsPreFibered.pullbackMap x'.2 i))
      (by infer_instance)
      (@Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian _ _ _ _ _ _ _ _ _ _ _
        (CatFiberedInGroupoids.isStronglyCartesian_map p i
          (Functor.IsPreFibered.pullbackMap x'.2 i)))
  ∀ (U U' : BigFppfOver B S hS) (i : U ⟶ U'),
    IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
    IsAffine ((BigFppfOver.toScheme B S hS).obj U') → P U' →
    Stacks.Thickenings.IsFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map i) →
    ∀ (x : 𝒳.val.p.Fiber U) (y' : 𝒴.val.p.Fiber U')
      (γ : (pU U).obj x ≅ Functor.pullbackFiber 𝒴.val.p y' i),
      ∃ (x' : 𝒳.val.p.Fiber U')
        (β : Functor.pullbackFiber 𝒳.val.p x' i ≅ x)
        (γ' : (pU U').obj x' ≅ y'),
        ((compare U U' i x').hom ≫
          (pU U).map β.hom) ≫ γ.hom =
          Functor.pullbackFiberHom (p := 𝒴.val.p) γ'.hom i

/-- Formal smoothness on objects gives the lifting condition for every class of larger test
objects. -/
theorem IsFormallySmoothOnObjects.isFormallySmoothOnObjectsOn
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} {p : 𝒳 ⟶ 𝒴}
    (hp : IsFormallySmoothOnObjects B S hS 𝒳 𝒴 p) (P : BigFppfOver B S hS → Prop) :
    IsFormallySmoothOnObjectsOn B S hS P 𝒳 𝒴 p :=
  fun U U' i hU hU' _ hi x y' γ => hp U U' i hU hU' hi x y' γ

/-- Against the class of all objects the lifting condition is formal smoothness on objects. -/
theorem isFormallySmoothOnObjectsOn_true_iff
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (p : 𝒳 ⟶ 𝒴) :
    IsFormallySmoothOnObjectsOn B S hS (fun _ => True) 𝒳 𝒴 p ↔
      IsFormallySmoothOnObjects B S hS 𝒳 𝒴 p :=
  ⟨fun h U U' i hU hU' hi x y' γ => h U U' i hU hU' trivial hi x y' γ,
    fun h => h.isFormallySmoothOnObjectsOn _⟩

end AlgebraicGeometry.Stack

end

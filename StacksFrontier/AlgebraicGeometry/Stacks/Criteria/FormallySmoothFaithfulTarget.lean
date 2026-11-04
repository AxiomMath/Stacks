module

public import StacksFrontier.AlgebraicGeometry.Stacks.FormallySmoothOnObjects
public import StacksFrontier.CategoryTheory.FiberedCategory.Inertia

/-!
# Formal smoothness on objects over a target with faithful structure functor

Let `g : 𝒜 ⟶ ℬ` be a 1-morphism of categories fibred in groupoids over the big fppf site of a
scheme `S`, and assume the structure functor of `ℬ` is faithful, as it is for a category fibred
in sets such as the test schemes `𝒮_Y` over an algebraic space `Y`. Then the fibres of `ℬ` have
at most one morphism between any two objects, so the compatibility equation of Stacks 06D0 holds
automatically, and formal smoothness on objects reduces to the existence of lifts: for a
first-order thickening `i : U ⟶ U'` of affine objects, an object `x` of `𝒜` over `U` and a
morphism `ψ : g(x) ⟶ y'` of `ℬ` over `i`, there are an object `x'` of `𝒜` over `U'` with a
morphism `x ⟶ x'` over `i` and a morphism `g(x') ⟶ y'` over the identity of `U'`.

## Main results

* `AlgebraicGeometry.Stack.isFormallySmoothOnObjects_of_faithful_of_exists_lift`: the
  reduction.

## References

* [Stacks Project, Tag 06D0](https://stacks.math.columbia.edu/tag/06D0)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒜 ℬ : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} {g : 𝒜 ⟶ ℬ}

/-- **Formal smoothness on objects over a target with faithful structure functor.** If the
structure functor of `ℬ` is faithful, then `g : 𝒜 ⟶ ℬ` is formally smooth on objects (Stacks
06D0) as soon as, for every first-order thickening `i : U ⟶ U'` of affine objects of the site,
every object `x` of `𝒜` over `U` and every morphism `ψ : g(x) ⟶ y'` of `ℬ` over `i`, there are
an object `x'` of `𝒜` over `U'`, a morphism `x ⟶ x'` over `i` and a morphism `g(x') ⟶ y'` over
the identity of `U'`. -/
theorem isFormallySmoothOnObjects_of_faithful_of_exists_lift [ℬ.val.p.Faithful]
    (h : ∀ {U U' : BigFppfOver B S hS} (i : U ⟶ U'),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj U') →
      Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map i) →
      ∀ {x : 𝒜.val.obj} (_ : 𝒜.val.p.obj x = U) {y' : ℬ.val.obj} (_ : ℬ.val.p.obj y' = U')
        (ψ : (CatFiberedInGroupoids.homFunctor g).obj x ⟶ y') [ℬ.val.p.IsHomLift i ψ],
        ∃ (x' : 𝒜.val.obj) (_ : 𝒜.val.p.obj x' = U') (β : x ⟶ x') (_ : 𝒜.val.p.IsHomLift i β)
          (γ' : (CatFiberedInGroupoids.homFunctor g).obj x' ⟶ y'),
          ℬ.val.p.IsHomLift (𝟙 U') γ') :
    IsFormallySmoothOnObjects B S hS 𝒜 ℬ g := by
  have : 𝒜.val.p.IsFibered := 𝒜.isFiberedInGroupoids.isFibered
  have : ℬ.val.p.IsFibered := ℬ.isFiberedInGroupoids.isFibered
  intro U U' i hU hU' hi x y' γ
  let F := CatFiberedInGroupoids.homFunctor g
  let ψ : F.obj x.1 ⟶ y'.1 :=
    Functor.Fiber.fiberInclusion.map γ.hom ≫ Functor.IsPreFibered.pullbackMap y'.2 i
  have hγ : ℬ.val.p.IsHomLift (𝟙 U) (Functor.Fiber.fiberInclusion.map γ.hom) := γ.hom.2
  have hψ : ℬ.val.p.IsHomLift i ψ :=
    @IsHomLift.comp_lift_id_left' _ _ _ _ ℬ.val.p _ _ _ U _ hγ _ _ i _
      (Functor.IsPreFibered.pullbackMap.IsCartesian y'.2 i).toIsHomLift
  obtain ⟨x', hx', β, hβ, γ', hγ'⟩ := h i hU hU' hi x.2 y'.2 ψ
  have := 𝒜.isFiberedInGroupoids.isStronglyCartesian_homLift i β
  have hβc : 𝒜.val.p.IsCartesian i β := inferInstance
  let x'F : 𝒜.val.p.Fiber U' := ⟨x', hx'⟩
  have hγ'iso : IsIso (Functor.Fiber.homMk ℬ.val.p U' γ') :=
    (ℬ.isFiberedInGroupoids.fiber_isGroupoid U').all_isIso _
  refine ⟨x'F,
    Functor.fiberIsoOfCartesian (p := 𝒜.val.p) (z := Functor.pullbackFiber 𝒜.val.p x'F i)
      (z' := x) i (Functor.IsPreFibered.pullbackMap x'F.2 i) β
      (Functor.IsPreFibered.pullbackMap.IsCartesian x'F.2 i) hβc,
    @asIso _ _ _ _ (Functor.Fiber.homMk ℬ.val.p U' γ') hγ'iso, ?_⟩
  ext
  apply ℬ.val.p.map_injective
  rw [IsHomLift.fac' ℬ.val.p (𝟙 U) (Functor.Fiber.fiberInclusion.map _),
    IsHomLift.fac' ℬ.val.p (𝟙 U) (Functor.Fiber.fiberInclusion.map _)]

end AlgebraicGeometry.Stack

end

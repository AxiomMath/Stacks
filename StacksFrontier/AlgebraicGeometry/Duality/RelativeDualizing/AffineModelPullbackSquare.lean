module

public import
  StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexSyntomicDescent

/-!
# The affine comparison square of a pullback, for an arbitrary morphism

Let `f : X ⟶ Y` be a morphism of schemes — no flatness is assumed — let `U` be an affine open of
`Y` and `V` an affine open of `X` with `f(V) ⊆ U`. Pulling back to `V` the module of sheaves
associated to a `Γ(Y, U)`-module, read on `U`, gives the module of sheaves associated to its
extension of scalars along `f.appLE U V`, read on `V`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.affineModelPullbackIso_unconditional`: the comparison square
  on modules, the same construction as
  `AlgebraicGeometry.Scheme.Modules.affineModelPullbackIso` without its flatness assumption.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry

namespace Scheme.Modules

attribute [local instance] AlgebraicGeometry.preservesFiniteLimits_modulesPullback_of_flat
  AlgebraicGeometry.preservesFiniteColimits_modulesPullback
  AlgebraicGeometry.pullback_additive

/-- **The affine comparison square at two nested affine opens.** Let `f : X ⟶ Y` be a morphism of
schemes, let `U` be an affine open of `Y` and `V` an affine open of `X` with `f(V) ⊆ U`. Pulling
back to `V` the module of sheaves associated to a `Γ(Y, U)`-module, read on `U`, gives the module
of sheaves associated to its extension of scalars along `f.appLE U V`, read on `V`.

This is [Stacks, Tag 01I9] conjugated by the two canonical isomorphisms `U ≅ Spec Γ(Y, U)` and
`V ≅ Spec Γ(X, V)`, which identify `f|_V : V ⟶ U` with `Spec (f.appLE U V)`. -/
def affineModelPullbackIso_unconditional {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U : Y.Opens} (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V)
    (hVU : V ≤ f ⁻¹ᵁ U) :
    (tilde.functor Γ(Y, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom) ⋙
        Scheme.Modules.pullback (f.resLE U V hVU) ≅
      ModuleCat.extendScalars (f.appLE U V hVU).hom ⋙
        (tilde.functor Γ(X, V) ⋙ Scheme.Modules.restrictFunctor hV.isoSpec.hom) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (pullbackRestrictionSquareIso (Spec.map (f.appLE U V hVU)) (f.resLE U V hVU)
        hV.isoSpec.hom hU.isoSpec.hom (hU.isoSpec_hom_specMap_appLE f hV hVU)).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (pullbackTildeIso Γ(Y, U) Γ(X, V) (f.appLE U V hVU)) _ ≪≫
    Functor.associator _ _ _

end Scheme.Modules

end AlgebraicGeometry

end

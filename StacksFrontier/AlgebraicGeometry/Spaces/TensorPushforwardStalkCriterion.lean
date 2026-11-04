module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleTensorPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleStalkConservative
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# The canonical map `𝓕 ⊗_𝒜 f_*𝓖 ⟶ f_*(f^*𝓕 ⊗_ℬ 𝓖)` is invertible when its geometric stalks are

Let `S` be a scheme, `i : Z ⟶ X` a morphism of algebraic spaces over `S`, `𝒜` a sheaf of rings
on `X_étale`, `ℬ` one on `Z_étale` and `φ : 𝒜 ⟶ i_{small,*}ℬ` a homomorphism of sheaves of
rings, so that `f = (i, φ)` is a morphism of ringed topoi and
`AlgebraicGeometry.Space.tensorPushforwardMap` is the canonical map

`𝓕 ⊗_𝒜 f_*𝓖 ⟶ f_*(f^*𝓕 ⊗_ℬ 𝓖)`

of Stacks 04G0, which is equally the canonical map of Stacks 0DK4 for the same datum. This file
records the first step of the *source's* proof of invertibility, which is stalkwise in both
tags: the map is invertible as soon as each of its stalks at a geometric point of `X` is.

## Main results

* `AlgebraicGeometry.Space.isIso_tensorPushforwardMap_of_isIso_geometricModuleStalk`: the
  canonical map is an isomorphism if its stalk at every geometric point of `X` is.

## Implementation notes

`AlgebraicGeometry.Space.isIso_tensorPushforwardMap` reduces invertibility instead to the
counit and the unit of the adjunction of Stacks 03D7, which is how Stacks 04G0 is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionModuleTensorPushforward.lean`. That route
is specific to a closed immersion: the counit is invertible exactly when the direct image of
modules is fully faithful, and for a finite morphism — the hypothesis of Stacks 0DK4 — it is
not. The criterion here
is the entry point of the other route, the one both tags take in the source.

For Stacks 0DK4 the stalkwise route is completed, at points of the small étale sites rather
than through `AlgebraicGeometry.Space.geometricModuleStalkFunctor`, by
`AlgebraicGeometry.Space.isIso_tensorPushforwardMap_of_isFinite`: the stalk of a direct image along
a finite morphism is Stacks 0DK3
(`AlgebraicGeometry.Space.bijective_pushforwardFiberMap_of_isFinite`), and the assembly of the
stalks of the canonical map is
`Stacks.SheafOfModules.isIso_pushforwardTensorMap_of_isConservativeFamilyOfPoints`.

The criterion is stated for an arbitrary `i`, since
`AlgebraicGeometry.Space.isIso_of_isIso_geometricModuleStalk` needs no hypothesis on it: the
hypothesis of either tag enters only in computing the stalks.

## References

* [Stacks Project, Tag 04G0](https://stacks.math.columbia.edu/tag/04G0)
* [Stacks Project, Tag 0DK4](https://stacks.math.columbia.edu/tag/0DK4)
* [Stacks Project, Tag 0DK3](https://stacks.math.columbia.edu/tag/0DK3)
* [Stacks Project, Tag 04K5](https://stacks.math.columbia.edu/tag/04K5)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {Z X : AlgebraicSpaces B S hS}

/-- **The stalkwise criterion for the invertibility clause of Stacks 04G0 and Stacks 0DK4.**
The canonical map `𝓕 ⊗_𝒜 f_*𝓖 ⟶ f_*(f^*𝓕 ⊗_ℬ 𝓖)` is an isomorphism as soon as its stalk at
every geometric point of `X` is an isomorphism of modules over the stalk of `𝒜`.

This is `AlgebraicGeometry.Space.isIso_of_isIso_geometricModuleStalk` at the canonical map; no
hypothesis on `i` is needed for it, those of the two tags being needed only to compute the
stalks. -/
theorem isIso_tensorPushforwardMap_of_isIso_geometricModuleStalk (i : Z ⟶ X)
    {𝒜 : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}}
    {ℬ : Sheaf (SmallEtale.topology B S hS Z.1) CommRingCat.{u}}
    (φ : 𝒜 ⟶ (pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
      (smallToposMorphismTypeU B S hS i)).obj ℬ)
    (𝓕 : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedToposOfRings B S hS X 𝒜).O))
    (𝓖 : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedToposOfRings B S hS Z ℬ).O))
    (hstalk : ∀ x : GeometricPoint B S hS X.1,
      IsIso ((geometricModuleStalkFunctor B S hS X.1 X.2
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedToposOfRings B S hS X 𝒜).O)
          x).map (tensorPushforwardMap B S hS i φ 𝓕 𝓖))) :
    IsIso (tensorPushforwardMap B S hS i φ 𝓕 𝓖) :=
  isIso_of_isIso_geometricModuleStalk B S hS X.1 X.2
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedToposOfRings B S hS X 𝒜).O)
    (tensorPushforwardMap B S hS i φ 𝓕 𝓖) hstalk

end AlgebraicGeometry.Space

end

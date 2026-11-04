module

public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.FunctorialityOfCohomology

/-!
# The pullback map on cohomology

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `𝒢` be an `𝒪_Y`-module.
The unit `𝒢 ⟶ f_* f^* 𝒢` of the pullback–pushforward adjunction is an `f`-map from `𝒢` to
`f^* 𝒢`, so the functoriality of cohomology along an `f`-map gives the canonical map

```
H^i(Y, 𝒢) ⟶ H^i(X, f^* 𝒢).
```

This file takes that specialization and records that it is natural in `𝒢`.
`Stacks.Cohomology.moduleCohomologyMap` is stated for an arbitrary `f`-map `𝒢 ⟶ f_* ℱ`; the
adjoint form is what a client with a module on the source rather than an `f`-map has, and it is
the shape in which base-change maps of cohomology are assembled.

## Main definitions

* `Stacks.Cohomology.moduleCohomologyPullbackMap`: the map `H^i(Y, 𝒢) ⟶ H^i(X, f^* 𝒢)`.

## Main results

* `Stacks.Cohomology.moduleCohomologyPullbackMap_naturality`: it is natural in `𝒢`.

## Implementation notes

Naturality is the two functoriality lemmas of
`StacksFrontier/Topology/Sheaves/Cohomology/HigherDirectImage/FunctorialityOfCohomology.lean`
together with the naturality of the unit of the adjunction: both composites are the map on
cohomology attached to the `f`-map `𝒢' ⟶ 𝒢 ⟶ f_* f^* 𝒢 = 𝒢' ⟶ f_* f^* 𝒢' ⟶ f_* f^* 𝒢`.

## References

* [Stacks Project, Tag 01FA](https://stacks.math.columbia.edu/tag/01FA)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The pullback map on cohomology**, `H^i(Y, 𝒢) ⟶ H^i(X, f^* 𝒢)`: the map attached by
[Stacks, Tag 01FA] to the unit `𝒢 ⟶ f_* f^* 𝒢` of the pullback–pushforward adjunction. The
target carries its `Γ(Y, 𝒪_Y)`-module structure by restriction of scalars along `f`. -/
noncomputable def moduleCohomologyPullbackMap (i : ℤ)
    (G : SheafOfModules.{u} (structureSheafRing Y)) :
    (spaceModuleCohomology Y i).obj G ⟶
      (moduleCohomologyAlong f i).obj ((modulePullback f).obj G) :=
  moduleCohomologyMap f i ((modulePullbackPushforwardAdjunction f).unit.app G)

/-- **The pullback map on cohomology is natural in the module.** -/
theorem moduleCohomologyPullbackMap_naturality (i : ℤ)
    {G G' : SheafOfModules.{u} (structureSheafRing Y)} (g : G' ⟶ G) :
    (spaceModuleCohomology Y i).map g ≫ moduleCohomologyPullbackMap f i G =
      moduleCohomologyPullbackMap f i G' ≫
        (moduleCohomologyAlong f i).map ((modulePullback f).map g) := by
  rw [moduleCohomologyPullbackMap, moduleCohomologyPullbackMap,
    moduleCohomologyMap_comp_left f i g ((modulePullbackPushforwardAdjunction f).unit.app G),
    moduleCohomologyMap_comp_right f i
      ((modulePullbackPushforwardAdjunction f).unit.app G') ((modulePullback f).map g)]
  refine congrArg (moduleCohomologyMap f i) ?_
  exact (modulePullbackPushforwardAdjunction f).unit.naturality g

end Stacks.Cohomology

end

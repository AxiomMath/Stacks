module

public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.CohomologyIdentityFunctoriality
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.CohomologyPullback

/-!
# The pullback map on cohomology followed by a coefficient map is one map of [Stacks, Tag 01FA]

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces, let `𝒢` be an `𝒪_Y`-module and let
`k : f^* 𝒢 ⟶ ℱ` be a morphism of `𝒪_X`-modules — a *coefficient map*. Every base-change map of
cohomology in this development is assembled as

```
H^i(Y, 𝒢) ⟶ H^i(X, f^* 𝒢) ⟶ H^i(X, ℱ),
```

the pullback map of `Stacks.Cohomology.moduleCohomologyPullbackMap` followed by `H^i(X, k)`. This
file records that the composite is a *single* map of [Stacks, Tag 01FA] — the one attached to the
`f`-map `𝒢 ⟶ f_* ℱ` adjoint to `k` — and specializes that to `f = 𝟙 X`.

## Main results

* `Stacks.Cohomology.moduleCohomologyPullbackMap_comp` — the two factors are the Tag 01FA map of
  the adjoint `f`-map `𝒢 ⟶ f_* f^* 𝒢 ⟶ f_* ℱ`.
* `Stacks.Cohomology.moduleCohomologyPullbackMap_comp_id` — **at `f = 𝟙 X` the composite is
  `H^i(X, η_𝒢 ≫ k)`**, for `η` the unit of the pullback–pushforward adjunction.

## Implementation notes

The first statement is `Stacks.Cohomology.moduleCohomologyMap_comp_right` at the unit of the
adjunction, since `moduleCohomologyPullbackMap` is by definition the Tag 01FA map of that unit. The
second is the first followed by `Stacks.Cohomology.moduleCohomologyMap_id`.

Both are stated with the modules in the `Stacks.Cohomology.Modules` spelling, which is the one
`moduleCohomologyMap` and `moduleCohomologyMap_id` use; `moduleCohomologyPullbackMap` is stated in
the `SheafOfModules.{u} (structureSheafRing _)` spelling, and the two agree only definitionally.
The identity law is therefore applied in **term mode** and not by `rw`: the `f`-map in the goal is
`η ≫ f_*(k)` with `f_* = 𝟭`, whose codomain is `(f_* ℱ)` rather than `ℱ`, so `rw` reports the goal
as "not type-correct under the `implicit` transparency level" and declines. In term mode the
elaborator may use the full definitional unfolding, and `(𝟙_X)_* = 𝟭` holds on the nose.

Note that `η_𝒢 : 𝒢 ⟶ (𝟙_X)^* 𝒢` is **not** the identity: `(𝟙_X)^*` is an abstract left adjoint
and is not equal to `𝟭`. So this is as far as the Tag 01FA layer degenerates on its own; what a
consumer must still supply is the computation of `η_𝒢 ≫ k` at its own coefficient map.

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

/-- **The pullback map on cohomology followed by a coefficient map is one map of
[Stacks, Tag 01FA].** For `k : f^* 𝒢 ⟶ ℱ`, the composite
`H^i(Y, 𝒢) ⟶ H^i(X, f^* 𝒢) ⟶ H^i(X, ℱ)` is the Tag 01FA map attached to the `f`-map
`𝒢 ⟶ f_* f^* 𝒢 ⟶ f_* ℱ` adjoint to `k`. -/
theorem moduleCohomologyPullbackMap_comp (i : ℤ) (G : Modules Y) {F : Modules X}
    (k : (modulePullback f).obj G ⟶ F) :
    moduleCohomologyPullbackMap f i G ≫ (moduleCohomologyAlong f i).map k =
      moduleCohomologyMap f i ((modulePullbackPushforwardAdjunction f).unit.app G ≫
        (modulePushforward f).map k) :=
  moduleCohomologyMap_comp_right f i _ k

/-- **At an identity morphism the pullback map on cohomology followed by a coefficient map is
`H^i` of the coefficient map composed with the unit of the adjunction.** Both factors of the
arrow of [Stacks, Tag 01F9] degenerate there, by `Stacks.Cohomology.moduleCohomologyMap_id`, so
nothing of the Tag 01FA layer survives — but the unit `𝒢 ⟶ (𝟙_X)^* 𝒢` does, since `(𝟙_X)^*` is
an abstract left adjoint and is not the identity functor. -/
theorem moduleCohomologyPullbackMap_comp_id (i : ℤ) (G : Modules X) {F : Modules X}
    (k : (modulePullback (𝟙 X)).obj G ⟶ F) :
    moduleCohomologyPullbackMap (𝟙 X) i G ≫ (moduleCohomologyAlong (𝟙 X) i).map k =
      (spaceModuleCohomology X i).map
        ((modulePullbackPushforwardAdjunction (𝟙 X)).unit.app G ≫ k) :=
  (moduleCohomologyPullbackMap_comp (𝟙 X) i G k).trans
    (moduleCohomologyMap_id X i
      ((modulePullbackPushforwardAdjunction (𝟙 X)).unit.app G ≫ k))

end Stacks.Cohomology

end

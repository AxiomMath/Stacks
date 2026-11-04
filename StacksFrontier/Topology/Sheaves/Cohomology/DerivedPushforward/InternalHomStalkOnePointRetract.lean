module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomStalkOnePointTarget
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackDevissage

/-!
# The stalk of a derived internal hom at a retract of the structure sheaf

For a ringed space `X`, a point `x` and `K ∈ D(𝒪_X)` admitting `i : K ⟶ 𝒪_X[0]` and
`r : 𝒪_X[0] ⟶ K` with `i ≫ r = 𝟙`, the canonical map

`R𝓗om_{𝒪_X}(K, M)_x ⟶ RHom_{𝒪_{X,x}}(K_x, M_x)`

is an isomorphism for every `M`.

## Main results

* `Stacks.Cohomology.DerivedInternalHomStalk.isIso_stalkSheafHomMapOnePoint_of_retract_singleUnit`:
  the statement above.

## References

* [Stacks Project, Tag 0GM8](https://stacks.math.columbia.edu/tag/0GM8)
* [Stacks Project, Tag 0GM7](https://stacks.math.columbia.edu/tag/0GM7)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Cohomology.DerivedInternalHomStalk

open Stacks.Cohomology.DerivedInternalHomPullback
open Stacks.Cohomology.DerivedProjectionFormula (singleUnit)

attribute [local instance 10000] HasDerivedCategory.standard

variable (X : RingedSpace.{u, u}) (x : X.carrier)

attribute [local instance] stalkCommRing

attribute [local implicit_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

/-- **The stalk map at a retract of `𝒪_X[0]`.**  For an arbitrary ringed space `X`, an
arbitrary point `x` of `X`, an arbitrary `M ∈ D(𝒪_X)` and any `K` admitting `i : K ⟶ 𝒪_X[0]` and
`r : 𝒪_X[0] ⟶ K` with `i ≫ r = 𝟙`, the displayed map

`R𝓗om_{𝒪_X}(K, M)_x ⟶ RHom_{𝒪_{X,x}}(K_x, M_x)`

is an isomorphism, the right-hand side being the derived internal hom of the one-point space
`Y = {x}` read through the stalk identification. -/
theorem isIso_stalkSheafHomMapOnePoint_of_retract_singleUnit
    (M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X))
    {K : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X)}
    (i : K ⟶ singleUnit X) (r : singleUnit X ⟶ K) (hir : i ≫ r = 𝟙 K) :
    IsIso (stalkSheafHomMapOnePoint X x K M) :=
  (isIso_stalkSheafHomMapOnePoint_iff X x K M).2
    (isIso_derivedPullbackSheafHomMap_of_retract_singleUnit (pointHom X x) M i r hir)

end Stacks.Cohomology.DerivedInternalHomStalk

end

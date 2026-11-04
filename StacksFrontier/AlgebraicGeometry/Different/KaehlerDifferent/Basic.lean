module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FittingIdeals
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.Over
public import StacksFrontier.Topology.Sheaves.Modules.Differentials

/-!
# The Kähler different

For a morphism of schemes which is locally of finite type, the sheaf of relative differentials
is a quasi-coherent module of finite type, so its Fitting ideal sheaves are defined. The *Kähler
different* of the morphism is the zeroth of them.

## Main definitions

* `Stacks.Discriminant.kaehlerDifferent` is the Kähler different of a morphism of schemes which
  is locally of finite type.

## Implementation notes

The sheaf of relative differentials is the module representing derivations along the structure
map `f⁻¹𝒪_X ⟶ 𝒪_Y` of the morphism, namely
`AlgebraicGeometry.SheafOfModules.moduleOfDifferentials` applied to
`AlgebraicGeometry.inverseImageStructureMap`. Fitting ideal sheaves are represented by
`AlgebraicGeometry.Scheme.IdealSheafData`. The definition is an abbreviation, so that the
existing Fitting-ideal API applies to it directly.

## References

* [Stacks Project, Tag 0BVW](https://stacks.math.columbia.edu/tag/0BVW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Discriminant

/-- **Stacks Project, Tag 0BVW.** The Kähler different of a morphism of schemes which is
locally of finite type: the zeroth Fitting ideal sheaf of its sheaf of relative
differentials. -/
@[stacks 0BVW]
noncomputable abbrev kaehlerDifferent {Y X : Scheme.{u}} (f : Y ⟶ X)
    [LocallyOfFiniteType f] : Y.IdealSheafData :=
  fittingIdeal (SheafOfModules.moduleOfDifferentials (inverseImageStructureMap f)) 0

end Stacks.Discriminant

end

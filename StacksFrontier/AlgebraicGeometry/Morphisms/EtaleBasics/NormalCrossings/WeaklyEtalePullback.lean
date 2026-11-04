module

public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.ClosedFibre

/-!
# Weakly étale pullback of a strict normal crossings divisor

The scheme-theoretic inverse image of a strict normal crossings divisor along a weakly étale
morphism with locally Noetherian source is again a strict normal crossings divisor.

## Main results

* `Stacks.Divisors.isStrictNormalCrossingsDivisor_comap_of_weaklyEtale`: pullback along a weakly
  étale morphism preserves strict normal crossings divisors.
* `Stacks.Divisors.isStrictNormalCrossingsDivisor_comap_comp_of_weaklyEtale`: the same for a
  morphism factoring weakly étale-ly through a chart on which the divisor is already strict
  normal crossings.

## Implementation notes

A weakly étale morphism is flat and the closed fibres of its stalk maps are fields, hence
regular local rings, so this is the flat criterion
`Stacks.Divisors.isStrictNormalCrossingsDivisor_comap_of_flat` combined with
`AlgebraicGeometry.isRegularLocalRing_closedFibre_of_weaklyEtale`. Unlike for a smooth morphism,
local Noetherianness of the source does not follow from the morphism and is assumed.

## References

* [Stacks Project, Tag 0CBP](https://stacks.math.columbia.edu/tag/0CBP)
* [Stacks Project, Tag 094Q](https://stacks.math.columbia.edu/tag/094Q)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Divisors

/-- The pullback of a strict normal crossings divisor along a weakly étale morphism with locally
Noetherian source is a strict normal crossings divisor. -/
theorem isStrictNormalCrossingsDivisor_comap_of_weaklyEtale {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : Y ⟶ X)
    [AlgebraicGeometry.WeaklyEtale f] (D : X.IdealSheafData)
    (hD : IsStrictNormalCrossingsDivisor D) :
    IsStrictNormalCrossingsDivisor (D.comap f) :=
  isStrictNormalCrossingsDivisor_comap_of_flat f
    (fun y ↦ isRegularLocalRing_closedFibre_of_weaklyEtale f y) D hD

/-- A morphism to `X` factoring through a scheme on which `D` restricts to a strict normal
crossings divisor, by a weakly étale morphism, pulls `D` back to a strict normal crossings
divisor. -/
theorem isStrictNormalCrossingsDivisor_comap_comp_of_weaklyEtale {X U Z : Scheme.{u}}
    [IsLocallyNoetherian U] [IsLocallyNoetherian Z] (g : U ⟶ X) (h : Z ⟶ U)
    [AlgebraicGeometry.WeaklyEtale h] (D : X.IdealSheafData)
    (hD : IsStrictNormalCrossingsDivisor (D.comap g)) :
    IsStrictNormalCrossingsDivisor (D.comap (h ≫ g)) := by
  rw [Scheme.IdealSheafData.comap_comp]
  exact isStrictNormalCrossingsDivisor_comap_of_weaklyEtale h (D.comap g) hD

end Stacks.Divisors

end

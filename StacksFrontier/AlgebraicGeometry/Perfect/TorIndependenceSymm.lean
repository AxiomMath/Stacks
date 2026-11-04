module

public import StacksFrontier.AlgebraicGeometry.Perfect.TorIndependence
public import StacksFrontier.RingTheory.Koszul.TorIndependence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tor independence over a field

A consequence of the definition `AlgebraicGeometry.TorIndependent` of
`StacksFrontier.AlgebraicGeometry.Perfect.TorIndependence` ([Stacks, Tag 08IA]) that the Künneth
formulas of [Stacks, Tag 0FXZ] and [Stacks, Tag 0FLQ] consume.

## Main results

* `AlgebraicGeometry.torIndependent_over_field`: any two schemes over a field are Tor
  independent.

## Implementation notes

The symmetry of Tor independence of two schemes over a base, which the same formulas also consume,
is `AlgebraicGeometry.TorIndependent.symm` in
`StacksFrontier.AlgebraicGeometry.Perfect.TorIndependence`.

## References

* [Stacks Project, Tag 08IA](https://stacks.math.columbia.edu/tag/08IA)
* [Stacks Project, Tag 0FXV](https://stacks.math.columbia.edu/tag/0FXV)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Any two schemes over a field are Tor independent.** Every module over a field is flat, so
every morphism to the spectrum of a field is flat, and
`AlgebraicGeometry.torIndependent_of_flat_left` applies. -/
@[sga "6 III 1.5" "special case"]
theorem torIndependent_over_field (k : Type u) [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k)) :
    TorIndependent f g :=
  torIndependent_of_flat_left f g

end AlgebraicGeometry

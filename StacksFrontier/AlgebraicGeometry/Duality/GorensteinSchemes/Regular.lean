module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization

/-!
# Regular schemes are Gorenstein

A regular scheme is Gorenstein: it is locally Noetherian, and each of its local rings, being a
regular local ring, is a Gorenstein local ring.

## Main results

* `AlgebraicGeometry.isGorenstein_of_isRegular`: a regular scheme is Gorenstein.

## Implementation notes

The two conjuncts of the Gorenstein property are supplied by the characterization of regular
schemes as locally Noetherian schemes with regular local rings, so the proof reduces to the
commutative-algebra statement that a regular local ring is Gorenstein.

## References

* [Stacks Project, Tag 0DWG](https://stacks.math.columbia.edu/tag/0DWG)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0DWG.** Every regular scheme is Gorenstein. -/
@[stacks 0DWG]
public theorem isGorenstein_of_isRegular (X : Scheme.{u}) (hX : IsRegular X) :
    IsGorenstein X := by
  obtain ⟨hN, hreg⟩ := ((isRegular_tfae X).out 1 2).mp hX
  refine { toIsLocallyNoetherian := hN, isGorensteinLocalRing := fun x => ?_ }
  let : IsRegularLocalRing (X.presheaf.stalk x) := hreg x
  exact Dualizing.IsRegularLocalRing.isGorensteinLocalRing _

end AlgebraicGeometry

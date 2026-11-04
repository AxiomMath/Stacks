module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.RegularModel
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.FlatSource
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.Regular

/-!
# The structure morphism of a regular model is Gorenstein

The total space of a regular model of a smooth curve over a discrete valuation ring is regular,
hence Gorenstein, and the model morphism is flat onto the spectrum of a Noetherian ring. So the
model morphism is a Gorenstein morphism as soon as one knows that the closed fibre of a flat
local homomorphism of Noetherian local rings with Gorenstein target is Gorenstein.

That last assertion is not proved in this library; it is
`Stacks.Duality.ClosedFibreGorensteinOfFlat`, and it enters the result below as an explicit
hypothesis. Everything else in the chain is unconditional: regularity of the total space gives
Gorensteinness of it by `AlgebraicGeometry.isGorenstein_of_isRegular`, and the passage from a
Gorenstein scheme to a Gorenstein morphism along a flat map is
`AlgebraicGeometry.Scheme.Hom.isGorenstein_of_flat`.

## Main results

* `Stacks.Models.RegularModelSituation.isGorenstein_of_closedFibreGorenstein` — granting the
  closed-fibre statement, the structure morphism of a regular model is Gorenstein.

## Implementation notes

The Gorenstein-morphism predicate needs a proof that every fibre is locally Noetherian, which
follows from local Noetherianity of the total space; it is therefore packaged existentially, as
in `AlgebraicGeometry.Scheme.Hom.isGorenstein_of_flat`.

## References

* [Stacks Project, Tag 0C04](https://stacks.math.columbia.edu/tag/0C04)
* [Stacks Project, Tag 0AWX](https://stacks.math.columbia.edu/tag/0AWX)
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace Stacks.Models

/-- **Granting the closed-fibre statement, the structure morphism of a regular model of a smooth
curve over a discrete valuation ring is a Gorenstein morphism.**

The total space is regular, hence a Gorenstein scheme, and the model morphism is flat with
locally Noetherian target. -/
public theorem RegularModelSituation.isGorenstein_of_closedFibreGorenstein
    (h : Stacks.Duality.ClosedFibreGorensteinOfFlat.{u})
    (S : RegularModelSituation.{u}) :
    ∃ hf : ∀ y : Spec (.of S.R), IsLocallyNoetherian (S.X_to_R.fiber y),
      S.X_to_R.IsGorenstein hf := by
  let : AlgebraicGeometry.IsGorenstein S.X := isGorenstein_of_isRegular S.X S.regular
  let : IsLocallyNoetherian (Spec (CommRingCat.of S.R)) := inferInstance
  exact Scheme.Hom.isGorenstein_of_flat h S.X_to_R

end Stacks.Models

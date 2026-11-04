module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatOpennessOfVersalityOfDiagonal
import StacksCore.Tactic.StacksAttribute

/-!
# The Stacks tag for openness of versality of `Spaces'_{fp, flat, proper}`

This file attaches [Stacks, Tag 0D3X] to `AlgebraicGeometry.openVersalityOf_cartesianProperFlat`.

## Main results

* `AlgebraicGeometry.openVersalityOf_cartesianProperFlat`: the stack `Spaces'_{fp, flat, proper}`
  of finitely presented, flat and proper families of algebraic spaces satisfies openness of
  versality over every locally Noetherian base scheme `S` of the site (Stacks 0D3X). The first
  assertion of the source is the case `S = Spec(ℤ)`; the second, after base change to a Noetherian
  scheme `S` (the stack of Stacks 0D1H), is the case of a Noetherian `S`.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
-/

@[expose] public section

add_to_stacks 0D3X "both assertions: over any locally Noetherian base scheme, in particular \
`Spec(ℤ)` and, after base change, any Noetherian scheme `S`"
  AlgebraicGeometry.openVersalityOf_cartesianProperFlat

end

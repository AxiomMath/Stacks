module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatOpennessOfVersalityOfDiagonal
import StacksCore.Tactic.StacksAttribute

/-!
# The Stacks tags for openness of versality of the stack of curves

This file registers [Stacks, Tag 0D59] on its two assertions: openness of versality for the stack
of curves over `Spec(ℤ)`, and for the stack of `S`-curves over a Noetherian scheme `S` of the site,
the base change of [Stacks, Remark 0D54].

## Main results

* `AlgebraicGeometry.curves_openVersalityOf_specZ`: openness of versality for the stack of curves
  over `Spec(ℤ)` — the first assertion.
* `AlgebraicGeometry.curves_openVersalityOf`: openness of versality for the stack of `S`-curves
  over a Noetherian scheme `S` — the second assertion.

## References

* [Stacks Project, Tag 0D59](https://stacks.math.columbia.edu/tag/0D59)
* [Stacks Project, Remark 0D54](https://stacks.math.columbia.edu/tag/0D54)
-/

@[expose] public section

add_to_stacks 0D59 "the first assertion: the stack of curves satisfies openness of versality \
over `Spec(ℤ)`"
  AlgebraicGeometry.curves_openVersalityOf_specZ

add_to_stacks 0D59 "the second assertion: for a Noetherian scheme `S` of the site, the stack of \
`S`-curves -- the base change of Remark 0D54 -- satisfies openness of versality over `S`"
  AlgebraicGeometry.curves_openVersalityOf

end

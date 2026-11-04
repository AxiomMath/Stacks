module

public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.Dimension.PivotEntry
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.Dimension.QuotientSymbol
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.Dimension.QuotientSymbolSwap
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.Dimension.FinrankEqOne

/-!
# The determinant of a finite length module has dimension one

Let `R` be a local ring and `M` a finite-length `R`-module. The determinant of `M` is a
one-dimensional vector space over the residue field of `R`, and the symbol of any
admissible sequence spanning `M` generates it.

## Main results

* `Module.FiniteLength.finrank_determinant_eq_one` states that the determinant has
  dimension one.

## Implementation notes

Dimension is expressed by `Module.finrank`. Together with the dimension bound of Tag 02P7,
the content of the proof is that the determinant is nonzero, and that is established by
induction on the length: a nonzero element of the socle generates a simple submodule `S`,
and the determinant of `M` is compared with the determinant of `M / S` by the map
`quotientSymbolMap`, which sends the symbol of an admissible sequence to the symbol of the
sequence obtained by deleting the entry that is a unit multiple of the socle generator
modulo the earlier entries. The bulk of the file verifies that this deletion respects the
three determinant relations.

The second assertion of the source lemma, that a spanning symbol generates, is identical to
the generator statement proved for Tag 02P7, so the single declaration
`Module.FiniteLength.span_symbol_eq_top` in `DimensionLeOne` carries the `02P9 "generators"`
clause.

## References

* [Stacks Project, Tag 02P9](https://stacks.math.columbia.edu/tag/02P9)
-/

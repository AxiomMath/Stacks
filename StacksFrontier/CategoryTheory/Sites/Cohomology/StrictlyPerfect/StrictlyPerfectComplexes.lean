module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.ConeOfAMorphism
import StacksCore.Tactic.StacksAttribute

/-!
# Strictly perfect complexes on a ringed site

Let `(C, O)` be a ringed site. A complex `E` of `O`-modules is *strictly perfect* when `Eⁱ` is
zero for all but finitely many `i` and every `Eⁱ` is a direct summand of a finite free
`O`-module. That predicate is `IsStrictlyPerfect`, introduced as the hypothesis of Stacks 08FM
(a cone of strictly perfect complexes is strictly perfect); this file records that it is also
exactly the definition
of Stacks 08FL, so that the tag is carried by the predicate itself rather than by a second copy
of it.

## Main results

* Stacks 08FL is realised by `IsStrictlyPerfect`.

## Implementation notes

Both clauses of the source definition are clauses of `IsStrictlyPerfect`: `bounded` is the
finiteness of `{i | Eⁱ ≠ 0}`, phrased with categorical zero objects, and `termDirectSummand` is
the existence, for each `i`, of a split retraction of `Eⁱ` off `O^{⊕n}` for some `n`. No new
notion is introduced here, since a second predicate would have to be bridged to the one Stacks
08FM is stated about.

The ringed-space analogue is `StrictlyPerfect.IsStrictlyPerfect`, which carries Stacks 08C4;
that one
lives over a `RingedSpace`, this one over a site, and neither specialises to the other inside
Lean.

## References

* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
-/

@[expose] public section

add_to_stacks 08FL "a complex of `O`-modules is strictly perfect" IsStrictlyPerfect

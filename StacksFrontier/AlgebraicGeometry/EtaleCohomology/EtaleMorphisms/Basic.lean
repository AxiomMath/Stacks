module

public import StacksFrontier.RingTheory.Etale.StandardEtale
public import StacksCore.Tactic.StacksAttribute

/-!
# Standard étale algebras and étale ring maps

A ring map étale at a prime is standard étale after localization, and every standard étale
algebra is étale.

## Main results

* `Algebra.exists_isStandardEtale_of_exists_etale` says that étaleness at a prime is witnessed
  by a standard étale localization.
* `Algebra.instEtaleOfIsStandardEtale` says that a standard étale algebra is étale.

## Implementation notes

A standard étale algebra is presented as a localization of `A[x]/(f)` at `g` with `f` monic and
`f'` invertible, which is the shape used in the source.

## References

* [Stacks Project, Tag 03PE](https://stacks.math.columbia.edu/tag/03PE)
-/

@[expose] public section

add_to_stacks 03PE "étale at a prime implies locally standard étale"
  Algebra.exists_isStandardEtale_of_exists_etale

add_to_stacks 03PE "standard étale implies étale" Algebra.instEtaleOfIsStandardEtale
add_to_sga "4½ Arcata 2.1.1" "special case" Algebra.instEtaleOfIsStandardEtale

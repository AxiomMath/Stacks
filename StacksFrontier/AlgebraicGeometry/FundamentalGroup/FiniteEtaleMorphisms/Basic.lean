module

public import Mathlib.RingTheory.Etale.Finite
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite étale covers of a geometric point

Over a separably closed field, finite étale covers of its spectrum are equivalent to finite sets.

## Main definitions

* `CommAlgCat.FiniteEtale.equivOfIsSepClosed` is the equivalence between finite étale covers of
  the spectrum of a separably closed field and finite sets.

## Implementation notes

Finite étale schemes over an affine scheme are affine. Consequently, passing from a finite étale
scheme over `Spec(k)` to its finite étale `k`-algebra of global functions reverses arrows. Thus
the source category is represented by `(CommAlgCat.FiniteEtale k)ᵒᵖ`, while the category of
finite sets is `FintypeCat`. Mathlib's equivalence is stated under the more general hypothesis
that `k` is separably closed, which includes the algebraically closed case in the source.

## References

* [Stacks Project, Tag 0BN8](https://stacks.math.columbia.edu/tag/0BN8)
-/

@[expose] public section

add_to_stacks 0BN8 CommAlgCat.FiniteEtale.equivOfIsSepClosed
add_to_sga "1 IX 1.8" "special case" CommAlgCat.FiniteEtale.equivOfIsSepClosed
add_to_sga "1 IX 1.9" "special case" CommAlgCat.FiniteEtale.equivOfIsSepClosed
add_to_sga "4 VIII 3.2" "partial" CommAlgCat.FiniteEtale.equivOfIsSepClosed
add_to_sga "4½ Arcata 2.4.3" "special case" CommAlgCat.FiniteEtale.equivOfIsSepClosed
add_to_ega "IV 18.3.3" "special case" CommAlgCat.FiniteEtale.equivOfIsSepClosed

module

public import Mathlib.RingTheory.Etale.Finite
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite étale algebras over a separably closed field

Over a separably closed field `k`, the opposite of the category of finite étale `k`-algebras is
equivalent to finite sets.

## Main definitions

* `CommAlgCat.FiniteEtale.equivOfIsSepClosed` (Mathlib) is the equivalence
  `(CommAlgCat.FiniteEtale k)ᵒᵖ ≌ FintypeCat` for `k` separably closed.

## Implementation notes

This is the algebra-level statement. The scheme-level statement of Stacks Tag 0BN8, that
`FÉt_{Spec k}` is equivalent to finite sets, is
`AlgebraicGeometry.finiteEtaleOverSpecEquivOfIsSepClosed` in
`StacksFrontier/AlgebraicGeometry/FundamentalGroup/EtaleFundamental/GaloisCategoryAxioms.lean`, which
composes the equivalence `FÉt_{Spec k} ≌ (CommAlgCat.FiniteEtale k)ᵒᵖ` given by the relative
spectrum with Mathlib's equivalence; the tag is registered there.

## References

* [Stacks Project, Tag 0BN8](https://stacks.math.columbia.edu/tag/0BN8)
-/

@[expose] public section

add_to_sga "1 IX 1.8" "special case" CommAlgCat.FiniteEtale.equivOfIsSepClosed
add_to_sga "1 IX 1.9" "special case" CommAlgCat.FiniteEtale.equivOfIsSepClosed
add_to_sga "4 VIII 3.2" "partial" CommAlgCat.FiniteEtale.equivOfIsSepClosed
add_to_sga "4½ Arcata 2.4.3" "special case" CommAlgCat.FiniteEtale.equivOfIsSepClosed
add_to_ega "IV 18.3.3" "special case" CommAlgCat.FiniteEtale.equivOfIsSepClosed

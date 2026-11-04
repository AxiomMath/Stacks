module

public import Mathlib.AlgebraicGeometry.Scheme
public import StacksCore.Tactic.StacksAttribute

/-!
# Locally finite direct sums over the points of a scheme

For a family of abelian groups indexed by a set of points of a scheme, we define the subgroup
of the product consisting of families whose support meets every quasi-compact open in a finite
set. Cycles on a scheme are the elements of such a group, the index set being the points of a
given dimension and each summand a copy of the integers.

## Main definitions

* `AlgebraicGeometry.locallyFiniteDirectSum` is the locally finite direct sum of a family of
  abelian groups over a set of points of a scheme.

## Implementation notes

The index set is represented by the subtype associated to the given set of points.
Quasi-compact opens are expressed as open subsets whose underlying sets are compact. The
definition is exposed so that downstream constructions can use its membership condition
directly.

## References

* [Stacks Project, Tag 0GU2](https://stacks.math.columbia.edu/tag/0GU2)
-/

@[expose] public section

universe u v

namespace AlgebraicGeometry

/-- The subgroup of pointwise families whose support meets every quasi-compact open subset of
the scheme in a finite set. -/
@[stacks 0GU2 "locally_finite_direct_sum"]
def locallyFiniteDirectSum (X : Scheme.{u}) (T : Set X) (G : T → Type v)
    [∀ x, AddCommGroup (G x)] : AddSubgroup (∀ x, G x) where
  carrier := {a | ∀ (U : X.Opens), IsCompact (U : Set X) →
    {x : T | (x : X) ∈ (U : Set X) ∧ a x ≠ 0}.Finite}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb U hU
    apply ((ha U hU).union (hb U hU)).subset
    intro x ⟨hxU, hab⟩
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    by_cases hax : a x = 0 <;> simp_all
  neg_mem' := by
    intro a ha U hU
    simpa using ha U hU

end AlgebraicGeometry

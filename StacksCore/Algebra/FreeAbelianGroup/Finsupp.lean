module

public import Mathlib.Algebra.FreeAbelianGroup.Finsupp

/-! # Sums of generators of a free abelian group

This file adds to `Mathlib.Algebra.FreeAbelianGroup.Finsupp` two facts about the sum
`(l.map FreeAbelianGroup.of).sum` of the generators of `FreeAbelianGroup X` along a list
`l : List X`:

* `FreeAbelianGroup.coeff_list_sum_map_of`: the coefficient of `x` in this sum is the number
  `l.count x` of occurrences of `x` in `l`;
* `FreeAbelianGroup.list_sum_map_of_eq_list_sum_map_of_iff_perm`: two lists have the same sum of
  generators if and only if one is a permutation of the other.

The second is used in the proof of Stacks 02MX (2). There, an equality between two sums of
generators in the free abelian group on the objects of an abelian category says that both sides
"contain the same objects counted with multiplicity", which Stacks turns into a bijection `τ`
between their terms: here it is a permutation of the two lists of objects, and hence an
isomorphism between their biproducts.
-/

@[expose] public section

namespace FreeAbelianGroup

variable {X : Type*}

/-- The coefficient of `x` in the sum of the generators along a list `l` is the number of
occurrences of `x` in `l`. -/
theorem coeff_list_sum_map_of [BEq X] [LawfulBEq X] (x : X) (l : List X) :
    coeff x (l.map of).sum = l.count x := by
  classical
  induction l with
  | nil => simp
  | cons y l ih =>
    rw [List.map_cons, List.sum_cons, map_add, ih, List.count_cons]
    simp [coeff, Finsupp.single_apply, add_comm]

/-- Two lists have the same sum of generators in `FreeAbelianGroup X` if and only if one is a
permutation of the other. -/
theorem list_sum_map_of_eq_list_sum_map_of_iff_perm {l l' : List X} :
    (l.map of).sum = (l'.map of).sum ↔ l.Perm l' := by
  refine ⟨fun h ↦ ?_, fun h ↦ (h.map _).sum_eq⟩
  classical
  refine List.perm_iff_count.2 fun x ↦ ?_
  have := congrArg (coeff x) h
  rwa [coeff_list_sum_map_of, coeff_list_sum_map_of, Nat.cast_inj] at this

end FreeAbelianGroup

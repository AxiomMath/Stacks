module

public import Mathlib.Data.Fintype.EquivFin

/-!
# The antidiagonal of a natural number is finite

The pairs of natural numbers with a given sum form a finite type. This is needed wherever a
decomposition indexed by such pairs has to be read as a direct sum rather than only as a
coproduct: a coproduct over a finite index in an additive category is a biproduct, and so has
projections, while a bare coproduct has only its injections.

## Main results

* `Stacks.Nat.finite_subtype_add_eq`: `{pq : ℕ × ℕ // pq.1 + pq.2 = n}` is finite.

## Implementation notes

The proof is the injection into `Fin (n + 1)` by the first entry: the first entry is at most the
sum, and together with the sum it determines the second entry. Mathlib's `Finset.antidiagonal`
carries no `Fintype` instance for this subtype, and neither does anything else in Mathlib or in
this repository, so the instance is supplied here.

The `ULift` of a finite type is finite in Mathlib already, so an index type of the shape
`ULift {pq : ℕ × ℕ // pq.1 + pq.2 = n}` — which is how a universe-polymorphic decomposition over
the antidiagonal is indexed — is covered by this instance together with that one.
-/

@[expose] public section

namespace Stacks.Nat

/-- **The pairs of natural numbers with a given sum form a finite type.** The first entry is at
most the sum, so sending a pair to its first entry is a map to `Fin (n + 1)`, and it is injective
because the sum then determines the second entry. -/
instance finite_subtype_add_eq (n : ℕ) : Finite {pq : ℕ × ℕ // pq.1 + pq.2 = n} :=
  Finite.of_injective
    (fun x : {pq : ℕ × ℕ // pq.1 + pq.2 = n} => (⟨x.1.1, by have := x.2; omega⟩ : Fin (n + 1)))
    fun x y h => by
      have h1 : x.1.1 = y.1.1 := congrArg Fin.val h
      have hx := x.2
      have hy := y.2
      refine Subtype.ext (Prod.ext h1 ?_)
      omega

end Stacks.Nat

end

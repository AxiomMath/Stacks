module

public import StacksFrontier.RingTheory.Koszul.Defs

/-!
# Iterated contraction of an exterior algebra by a list of functionals

Contraction `Koszul.contraction φ` of the exterior algebra `⋀(E)` of a module by a functional
`φ : E →ₗ[R] R` lowers the exterior degree by one. Contracting repeatedly, by the successive
entries of a list `l` of functionals, lowers it by the length of `l`. This file introduces that
iterate, `Koszul.listContraction`, and proves the two identities that make it *alternating* in
the list:

* exchanging two adjacent entries of the list negates the iterate, and
* the iterate vanishes when two adjacent entries of the list are equal.

Both come from Mathlib's facts about a single contraction — `CliffordAlgebra.contractLeft_comm`
for the first, `CliffordAlgebra.contractLeft_contractLeft` for the second — and neither follows
from the other: over a ring in which `2` is not invertible the vanishing on a repetition is
strictly stronger than the sign rule it implies.

The point of the alternating property is that it is exactly what
`exteriorPower.alternatingMapLinearEquiv` consumes, so iterated contraction factors through the
exterior power `⋀ⁿ(E*)` of the dual. Mathlib already has the resulting comparison in the shape
`exteriorPower.pairingDual : ⋀ⁿ(E*) →ₗ[R] (⋀ⁿ E)*`, given by the determinant of the matrix of
pairings and bijective for `E` finite free (`exteriorPower.bijective_pairingDual`); what this
file supplies is the contraction-side description of the same pairing, which is the form in which
a composition product on Ext groups presents it.

## Main definitions

* `Koszul.listContraction`: **iterated contraction by the entries of a list of functionals**,
  contracting by the head first.

## Main results

* `Koszul.contraction_contraction_comm`: contraction by two functionals anticommutes.
* `Koszul.listContraction_mem`: iterated contraction lowers the exterior degree by the length of
  the list.
* `Koszul.listContraction_swap_adjacent`: **exchanging two adjacent entries negates the
  iterate.**
* `Koszul.listContraction_eq_zero_of_adjacent_eq`: **the iterate vanishes when two adjacent
  entries are equal.**

## Implementation notes

**The head is contracted first.** `Koszul.listContraction (φ :: l)` is
`Koszul.listContraction l` composed *after* `Koszul.contraction φ`. Both conventions give an
alternating iterate, but this one is the one a composition product has: an element of
`Ext¹` acting on `Extⁿ` acts by precomposition with the contraction it names, so a product
`ξ₁ ⋯ ξₙ` contracts by `ξ₁` first.

**Lists rather than tuples.** The two identities are about *adjacent* entries, and adjacency is
what a list exposes: each is stated for a list of the form `l₁ ++ φ :: ψ :: l₂` and proved by
induction on the prefix `l₁`, where the inductive step is that precomposition with a single
contraction commutes with negation. The same statements for a tuple `Fin n → Module.Dual R E`
would need `Equiv.swap` and a reindexing in place of that induction.

## References

* [Stacks Project, Tag 0622](https://stacks.math.columbia.edu/tag/0622)
* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
-/

@[expose] public section

open scoped ExteriorAlgebra

namespace Koszul

universe u v

variable {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E]

/-- **Contraction by two functionals anticommutes.** This is
`CliffordAlgebra.contractLeft_comm` named for the Koszul differential. It is the sign rule of the
degree `-1` antiderivations `Koszul.contraction`, and it does not imply that contraction by a
single functional squares to zero. -/
theorem contraction_contraction_comm (φ ψ : Module.Dual R E) (x : ExteriorAlgebra R E) :
    contraction φ (contraction ψ x) = -contraction ψ (contraction φ x) :=
  CliffordAlgebra.contractLeft_comm φ ψ x

/-- **Iterated contraction by the entries of a list of functionals**, contracting by the head
first: `listContraction [φ₁, …, φₙ]` is `contraction φₙ ∘ ⋯ ∘ contraction φ₁`. -/
noncomputable def listContraction :
    List (Module.Dual R E) → ExteriorAlgebra R E →ₗ[R] ExteriorAlgebra R E
  | [] => LinearMap.id
  | φ :: l => (listContraction l).comp (contraction φ)

/-- Iterated contraction by the empty list is the identity. -/
@[simp]
theorem listContraction_nil :
    listContraction ([] : List (Module.Dual R E)) = LinearMap.id := rfl

/-- Iterated contraction by `φ :: l` contracts by `φ` first, then by the entries of `l`. -/
@[simp]
theorem listContraction_cons (φ : Module.Dual R E) (l : List (Module.Dual R E)) :
    listContraction (φ :: l) = (listContraction l).comp (contraction φ) := rfl

/-- `Koszul.listContraction_cons`, evaluated at an element of the exterior algebra. -/
theorem listContraction_cons_apply (φ : Module.Dual R E) (l : List (Module.Dual R E))
    (x : ExteriorAlgebra R E) :
    listContraction (φ :: l) x = listContraction l (contraction φ x) := rfl

/-- **Iterated contraction lowers the exterior degree by the length of the list.** -/
theorem listContraction_mem (l : List (Module.Dual R E)) (n : ℕ) {x : ExteriorAlgebra R E}
    (hx : x ∈ ⋀[R]^(n + l.length) E) : listContraction l x ∈ ⋀[R]^n E := by
  induction l generalizing n x with
  | nil => simpa using hx
  | cons φ l ih =>
    have hlen : n + (φ :: l).length = n + l.length + 1 := by
      rw [List.length_cons, Nat.add_assoc]
    exact ih n (contraction_mem φ (n + l.length) (hlen ▸ hx))

/-- Iterated contraction by `l₁ ++ l₂` is contraction by `l₁` followed by contraction by `l₂`. -/
private theorem listContraction_append (l₁ l₂ : List (Module.Dual R E)) :
    listContraction (l₁ ++ l₂) = (listContraction l₂).comp (listContraction l₁) := by
  induction l₁ <;> simp_all [LinearMap.comp_assoc]

/-- **Exchanging two adjacent entries of the list negates the iterated contraction.** -/
theorem listContraction_swap_adjacent (l₁ : List (Module.Dual R E)) (φ ψ : Module.Dual R E)
    (l₂ : List (Module.Dual R E)) :
    listContraction (l₁ ++ φ :: ψ :: l₂) = -listContraction (l₁ ++ ψ :: φ :: l₂) := by
  have h : listContraction (φ :: ψ :: l₂) = -listContraction (ψ :: φ :: l₂) :=
    LinearMap.ext fun x => by
      simp [contraction_contraction_comm φ ψ]
  rw [listContraction_append, listContraction_append, h, LinearMap.neg_comp]

/-- **The iterated contraction vanishes when two adjacent entries of the list are equal.** This
is the vanishing of the square of a single contraction,
`CliffordAlgebra.contractLeft_contractLeft`, and is not a consequence of
`Koszul.listContraction_swap_adjacent`. -/
theorem listContraction_eq_zero_of_adjacent_eq (l₁ : List (Module.Dual R E))
    (φ : Module.Dual R E) (l₂ : List (Module.Dual R E)) :
    listContraction (l₁ ++ φ :: φ :: l₂) = 0 := by
  have h : listContraction (φ :: φ :: l₂) = 0 :=
    LinearMap.ext fun x => by
      simp [CliffordAlgebra.contractLeft_contractLeft]
  rw [listContraction_append, h, LinearMap.zero_comp]

end Koszul

end

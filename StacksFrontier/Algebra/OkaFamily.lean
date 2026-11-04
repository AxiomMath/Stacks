module

public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Ideal.Oka
public import Mathlib.RingTheory.Noetherian.OfPrime
public import Mathlib.RingTheory.PrincipalIdealDomainOfPrime
public import StacksCore.Tactic.StacksAttribute

/-!
# Oka families

Mathlib states four of the five tags that used to live here.

Stacks 05K9, the definition of an Oka family — a family containing the unit ideal and closed
under the passage from `(I : a)` and `(I, a)` to `I` — is `Ideal.IsOka`, phrased as a predicate
on ideals rather than as a set of them. Stacks 05KE, that a maximal element of the complement
of an Oka family is prime, is `Ideal.IsOka.isPrime_of_maximal_not`. Both already carry their
tag upstream, so nothing is recorded for them here.

The Oka-family conclusion of Stacks 05KB, that the finitely generated ideals form an Oka family,
is `Ideal.isOka_fg`, and Stacks 05KC, that the principal ideals do, is `Ideal.isOka_isPrincipal`.
The 05KB record carries that qualifier because the tag claims more: it also exhibits an explicit
generating set of `I` built from generators of `(I : a)` and of `(I, a)`. That construction lives
only inside the proof of `Ideal.isOka_fg`, and is recorded nowhere in this file.

What remains is Stacks 05KA: for a multiplicative subset `S` of `R`, the ideals meeting `S`
form an Oka family.
-/

@[expose] public section

add_to_stacks 05KB "the Oka-family conclusion" Ideal.isOka_fg
add_to_stacks 05KC Ideal.isOka_isPrincipal

namespace Stacks.Algebra.OkaFamily

/-- The family of ideals that intersect a multiplicative set forms an Oka family. -/
theorem Ideal.isOka_intersects_multiplicative_set {R : Type*} [CommSemiring R] (S : Submonoid R) :
    Ideal.IsOka (fun I : Ideal R => ∃ s ∈ S, s ∈ I) where
  top := ⟨1, S.one_mem, Submodule.mem_top⟩
  oka := by
    rintro I a ⟨s, hs, hsI⟩ ⟨t, ht, htI⟩
    obtain ⟨i, hi, _, hr, rfl⟩ := Submodule.mem_sup.1 hsI
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    refine ⟨(i + c * a) * t, S.mul_mem hs ht, ?_⟩
    rw [add_mul, mul_assoc]
    exact I.add_mem (I.mul_mem_right t hi)
      (I.mul_mem_left c (mul_comm t a ▸ Ideal.mem_colon_span_singleton.1 htI))

end Stacks.Algebra.OkaFamily

end

/-!
# The ideals meeting a multiplicative subset form an Oka family

Throughout, `R` is a commutative semiring with `1`. A subset of `R` is a
*multiplicative subset* if it contains `1` and is closed under multiplication;
this is modelled by `Submonoid R`.

For an ideal `I ⊆ R` and an element `a : R`, the ideal `(I, a) = I + R a` is the
smallest ideal containing both `I` and `a`, written `I ⊔ Ideal.span {a}`, and the
colon ideal `(I : a) = {x ∈ R | x a ∈ I}` is written `I.colon (Ideal.span {a})`.

A family `F` of ideals of `R` is an *Oka family* if `R ∈ F` and, for every ideal
`I` and every `a : R`, membership of both `(I : a)` and `(I, a)` in `F` forces
`I ∈ F`.

The main result is that for a multiplicative subset `S ⊆ R` the family
`F = {I | I ∩ S ≠ ∅}` is an Oka family.
-/

@[expose] public section

/-- A set `F` of ideals of a commutative semiring `R` is an *Oka family* if it
contains the whole ring `R` (as a top ideal) and is closed under the Oka
condition: whenever both the colon ideal `(I : a) = I.colon (span {a})` and the
ideal `(I, a) = I ⊔ span {a}` belong to `F`, then `I` belongs to `F`. -/
def IsOkaFamilyUniversal {R : Type*} [CommSemiring R] (F : Set (Ideal R)) : Prop :=
  (⊤ : Ideal R) ∈ F ∧
    ∀ (I : Ideal R) (a : R),
      (I.colon (Ideal.span {a}) ∈ F) → (I ⊔ Ideal.span {a} ∈ F) → I ∈ F

/-- The family of ideals meeting a multiplicative subset `S`: those ideals `I`
with `(I : Set R) ∩ (S : Set R) ≠ ∅`. -/
def meetsSubmonoidFamily {R : Type*} [CommSemiring R] (S : Submonoid R) :
    Set (Ideal R) :=
  {I : Ideal R | ((I : Set R) ∩ (S : Set R)).Nonempty}

/-- **Stacks Tag 05KA.** For a commutative semiring `R` and a multiplicative subset
`S` of `R`, the family of ideals meeting `S` is an Oka family. -/
@[stacks 05KA]
theorem isOkaFamilyUniversal_meetsSubmonoidFamily {R : Type*} [CommSemiring R]
    (S : Submonoid R) : IsOkaFamilyUniversal (meetsSubmonoidFamily S) := by
  have h := Stacks.Algebra.OkaFamily.Ideal.isOka_intersects_multiplicative_set S
  refine ⟨⟨1, trivial, S.one_mem⟩, fun I a ⟨t, htI, htS⟩ ⟨s, hsI, hsS⟩ ↦ ?_⟩
  obtain ⟨u, hu, huI⟩ := h.oka (I := I) (a := a) ⟨s, hsS, hsI⟩ ⟨t, htS, htI⟩
  exact ⟨u, huI, hu⟩

end

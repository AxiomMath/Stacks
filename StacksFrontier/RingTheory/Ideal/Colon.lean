module

public import Mathlib.RingTheory.Ideal.Colon

/-!
# A principal ideal factors out of an ideal it contains

Let `R` be a commutative ring, `J ⊆ R` a principal ideal and `I ⊆ R` an ideal
with `I ⊆ J`. Then `I = J (I : J)`, where `(I : J) = {x ∈ R | x J ⊆ I}` is the
colon ideal and `J (I : J)` is the product ideal.

The notions are Mathlib's: `Submodule.IsPrincipal` for `J = (f) = R f`,
`Ideal.colon I J` for the colon ideal, and the multiplication `A * B` on
`Ideal R` for the product ideal.

The hypothesis that `J` is principal is essential. The inclusion `J (I : J) ⊆ I`
holds for arbitrary ideals; the reverse inclusion `I ⊆ J (I : J)` uses that `J`
is principal together with `I ⊆ J`.
-/

@[expose] public section

open Ideal Submodule

/-- For a commutative ring `R`, a principal ideal `J` and an ideal `I` with
`I ≤ J`, the ideal `I` factors as the product of `J` with the colon ideal
`(I : J)`. -/
@[stacks 05K8]
theorem ideal_eq_mul_colon_of_isPrincipal {R : Type*} [CommRing R]
    (I J : Ideal R) (hJ : J.IsPrincipal) (hIJ : I ≤ J) :
    I = J * (I.colon J) := by
  obtain ⟨f, rfl⟩ := hJ
  rw [Ideal.submodule_span_eq] at hIJ ⊢
  simp only [Ideal.colon_span, Ideal.eq_span_singleton_mul, Submodule.mem_colon_singleton,
    smul_eq_mul]
  refine ⟨fun i hi => ?_, fun z hz => by rwa [mul_comm]⟩
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 (hIJ hi)
  exact ⟨a, hi, mul_comm f a⟩

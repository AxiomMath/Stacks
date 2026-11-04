module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Span

/-!
# The annihilator of a self-annihilating element after flat base change

Let `A` be a commutative ring and `ε ∈ A` an element whose annihilator is the ideal it generates,
as for `ε` in the dual numbers `k[ε]`.  The sequence `A --ε--> A --ε--> A` is then exact, and
it stays exact after tensoring with a flat `A`-algebra `R`: the annihilator of `ε` in `R` is
`εR`.

## Main results

* `Algebra.mem_span_singleton_of_flat_of_mul_eq_zero`.
-/

@[expose] public section

open TensorProduct

namespace Algebra

variable {A R : Type*} [CommRing A] [CommRing R] [Algebra A R] [Module.Flat A R]

/-- **Flat base change preserves the annihilator of a self-annihilating element**: if the
annihilator of `ε` in `A` is `εA` and `R` is flat over `A`, then the annihilator of the image of
`ε` in `R` is `εR`. -/
theorem mem_span_singleton_of_flat_of_mul_eq_zero (ε : A)
    (hε : ∀ a : A, ε * a = 0 ↔ a ∈ Ideal.span {ε}) (x : R)
    (hx : algebraMap A R ε * x = 0) : x ∈ Ideal.span {algebraMap A R ε} := by
  let μ : A →ₗ[A] A := LinearMap.mulLeft A ε
  have hεε : ε * ε = 0 := (hε ε).2 (Ideal.mem_span_singleton_self ε)
  have hexact : Function.Exact μ μ := fun a => by
    refine ⟨fun ha => ?_, ?_⟩
    · obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ((hε a).1 ha)
      exact ⟨b, mul_comm ε b⟩
    · rintro ⟨b, rfl⟩
      simp [μ, ← mul_assoc, hεε]
  have hR := Module.Flat.lTensor_exact R hexact
  let e : R ⊗[A] A ≃ₗ[A] R := _root_.TensorProduct.rid A R
  have he (y : R ⊗[A] A) : e (μ.lTensor R y) = algebraMap A R ε * e y := by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r a => simp [e, μ, mul_smul, Algebra.smul_def ε]
    | add y z hy hz => rw [map_add, map_add, hy, hz, map_add, mul_add]
  obtain ⟨z, hz⟩ := (hR (e.symm x)).1
    (e.injective (by rw [he, LinearEquiv.apply_symm_apply, hx, map_zero]))
  refine Ideal.mem_span_singleton'.2 ⟨e z, ?_⟩
  rw [mul_comm, ← he, hz, LinearEquiv.apply_symm_apply]

end Algebra

end

module

public import Mathlib.RingTheory.Filtration

/-!
# Modules with adically small kernels to zero modules vanish

Let `M` be a finite module over a Noetherian ring `A`, `I ⊆ A` an ideal contained in the Jacobson
radical, and `πₙ : M ⟶ Qₙ` maps to zero modules with `ker πₙ ⊆ Iⁿ⁻ᶜ M` for `n ≥ c`. Then `M = 0`.

## Main results

* `Stacks.subsingleton_of_ker_le_pow_smul_top`: if `I ≤ jacobson ⊥` and the linear maps
  `π n : M →ₗ[A] Q n` to subsingleton modules satisfy `ker (π n) ≤ I ^ (n - c) • ⊤` for `c ≤ n`,
  then `M` is a subsingleton.
-/
@[expose] public section

namespace Stacks

variable {A : Type*} [CommRing A] [IsNoetherianRing A] {M : Type*} [AddCommGroup M] [Module A M]
  [Module.Finite A M]

/-- Let `M` be a finite module over a Noetherian ring `A` and `I ≤ jacobson ⊥` an ideal. If the
linear maps `π n : M →ₗ[A] Q n` to subsingleton modules satisfy
`ker (π n) ≤ I ^ (n - c) • ⊤` for all `n ≥ c`, then `M` is a subsingleton. -/
theorem subsingleton_of_ker_le_pow_smul_top (I : Ideal A) (hI : I ≤ Ideal.jacobson ⊥)
    {Q : ℕ → Type*} [∀ n, AddCommGroup (Q n)] [∀ n, Module A (Q n)]
    (π : ∀ n, M →ₗ[A] Q n) (hQ : ∀ n, Subsingleton (Q n)) (c : ℕ)
    (h : ∀ n, c ≤ n → LinearMap.ker (π n) ≤ I ^ (n - c) • (⊤ : Submodule A M)) :
    Subsingleton M := by
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M) I hI
  refine ⟨fun x y => ?_⟩
  have hmem (z : M) : z ∈ (⨅ i : ℕ, I ^ i • ⊤ : Submodule A M) :=
    Submodule.mem_iInf _ |>.2 fun i => by
      simpa using h (i + c) (Nat.le_add_left c i)
        (show z ∈ LinearMap.ker (π (i + c)) from Subsingleton.elim _ _)
  simp only [hbot, Submodule.mem_bot] at hmem
  rw [hmem x, hmem y]

end Stacks

end

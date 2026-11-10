module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# The orbits of the Frobenius on the embeddings of a finite extension

Let `K` be a finite field with `q` elements, `Ω` an algebraically closed extension of `K` and
`σ` an automorphism of `Ω` over `K` whose inverse is `z ↦ z ^ q` (the geometric Frobenius). For a
finite extension `L` of `K` of degree `e`, `σ` acts on the `K`-embeddings `L → Ω` by composition;
this action is free and transitive modulo `σ ^ e`, which acts trivially: the `e` embeddings
`σ ^ k ∘ ι` for `k < e` are all the embeddings. This is the orbit structure of the geometric
Frobenius of a closed point `y` on the geometric points over `y` of a finite cover, an orbit for
each point `x` above `y`, of length `[κ(x) : κ(y)]`.

## Main results

* `Stacks.Frobenius.symm_pow_comp_eq`: `σ⁻ᵏ ∘ ι = ι ∘ Frob_L ^ k`.
* `Stacks.Frobenius.pow_finrank_comp_eq`: `σ ^ e ∘ ι = ι`.
* `Stacks.Frobenius.bijective_pow_comp`: `k ↦ σ ^ k ∘ ι`, `k < e`, is a bijection onto the
  embeddings.
-/

@[expose] public noncomputable section

namespace Stacks.Frobenius

variable {K : Type*} [Field K] [Fintype K] {Ω : Type*} [Field Ω] [Algebra K Ω]
  {L : Type*} [Field L] [Algebra K L] [Finite L]
  (σ : Ω ≃ₐ[K] Ω) (hσ : ∀ z, σ.symm z = z ^ Fintype.card K) (ι : L →ₐ[K] Ω)

omit [Finite L] in
include hσ in
/-- `σ⁻ᵏ ∘ ι = ι ∘ Frob_L ^ k`. -/
public theorem symm_pow_comp_eq (k : ℕ) :
    ((σ.symm ^ k : Ω ≃ₐ[K] Ω) : Ω →ₐ[K] Ω).comp ι =
      ι.comp (FiniteField.frobeniusAlgHom K L ^ k) := by
  induction k with
  | zero => ext z; simp
  | succ k ih =>
    ext z
    have h := congrArg (fun g : L →ₐ[K] Ω => g z) ih
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] at h
    rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, pow_succ', AlgEquiv.mul_apply, h, hσ,
      AlgHom.comp_apply, pow_succ', AlgHom.mul_apply, FiniteField.coe_frobeniusAlgHom, map_pow]

/-- If `σ ^ n ∘ ι = ι` for an automorphism `σ` of `B`, then `σ⁻ⁿ ∘ ι = ι`. -/
private theorem symm_pow_comp_eq_of_pow_comp_eq {R A B : Type*} [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] (ι : A →ₐ[R] B) (σ : B ≃ₐ[R] B) (n : ℕ)
    (h : ((σ ^ n : B ≃ₐ[R] B) : B →ₐ[R] B).comp ι = ι) :
    ((σ.symm ^ n : B ≃ₐ[R] B) : B →ₐ[R] B).comp ι = ι := by
  rw [show σ.symm ^ n = (σ ^ n)⁻¹ by rw [← inv_pow]; rfl]
  ext z
  exact (σ ^ n).symm_apply_eq.2 (AlgHom.congr_fun h z).symm

include hσ in
/-- **`σ ^ e ∘ ι = ι`** for `e = [L : K]`. -/
public theorem pow_finrank_comp_eq :
    ((σ ^ Module.finrank K L : Ω ≃ₐ[K] Ω) : Ω →ₐ[K] Ω).comp ι = ι := by
  have h := symm_pow_comp_eq σ hσ ι (Module.finrank K L)
  have hfe : FiniteField.frobeniusAlgHom K L ^ Module.finrank K L = 1 := by
    rw [← FiniteField.orderOf_frobeniusAlgHom K L]
    exact pow_orderOf_eq_one _
  rw [hfe] at h
  have h' : ((σ.symm ^ Module.finrank K L : Ω ≃ₐ[K] Ω) : Ω →ₐ[K] Ω).comp ι = ι := by
    rw [h]; rfl
  simpa using symm_pow_comp_eq_of_pow_comp_eq ι σ.symm _ h'

include hσ in
/-- **The embeddings `σ ^ k ∘ ι`, `k < [L : K]`, are all the embeddings of `L` into `Ω`, each
once.** -/
public theorem bijective_pow_comp [IsAlgClosed Ω] :
    Function.Bijective fun k : Fin (Module.finrank K L) =>
      ((σ ^ (k : ℕ) : Ω ≃ₐ[K] Ω) : Ω →ₐ[K] Ω).comp ι := by
  have : FiniteDimensional K L := Module.Finite.of_finite
  refine Function.Injective.bijective_of_nat_card_le ?_ ?_
  · -- injectivity: `σ ^ i ∘ ι = σ ^ j ∘ ι` forces `Frob_L ^ (j - i) = 1`
    suffices h : ∀ i j : Fin (Module.finrank K L), (i : ℕ) ≤ j →
        ((σ ^ (i : ℕ) : Ω ≃ₐ[K] Ω) : Ω →ₐ[K] Ω).comp ι =
          ((σ ^ (j : ℕ) : Ω ≃ₐ[K] Ω) : Ω →ₐ[K] Ω).comp ι → i = j by
      intro i j hij
      rcases le_total (i : ℕ) j with hle | hle
      · exact h i j hle hij
      · exact (h j i hle hij.symm).symm
    intro i j hle hij
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    have h1 : ((σ.symm ^ d : Ω ≃ₐ[K] Ω) : Ω →ₐ[K] Ω).comp ι = ι := by
      have hz : ((σ ^ d : Ω ≃ₐ[K] Ω) : Ω →ₐ[K] Ω).comp ι = ι := by
        ext z
        have hz := congrArg (fun g : L →ₐ[K] Ω => g z) hij
        simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] at hz
        rw [hd, pow_add, AlgEquiv.mul_apply] at hz
        exact ((σ ^ (i : ℕ)).injective hz).symm
      exact symm_pow_comp_eq_of_pow_comp_eq ι σ d hz
    rw [symm_pow_comp_eq σ hσ ι d] at h1
    have h2 : FiniteField.frobeniusAlgHom K L ^ d = 1 := by
      ext z
      have := congrArg (fun g : L →ₐ[K] Ω => g z) h1
      simp only [AlgHom.comp_apply] at this
      exact ι.toRingHom.injective this
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [FiniteField.orderOf_frobeniusAlgHom] at h3
    have hlt : d < Module.finrank K L := by omega
    have hd0 : d = 0 := Nat.eq_zero_of_dvd_of_lt h3 hlt
    exact Fin.ext (by omega)
  · rw [Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin,
      AlgHom.natCard_of_splits K L Ω fun _ => IsAlgClosed.splits _]

end Stacks.Frobenius

end

module

public import StacksFrontier.NumberTheory.BombieriStepanov.ConstantFieldExtension
public import Mathlib.RingTheory.Finiteness.Quotient

/-!
# Points of finite rings and embeddings of finite fields

Two auxiliary facts for lifting points along a constant field extension.

* `Stacks.BombieriStepanov.finite_quotient_ker`: if `S` is finite over `R` and a homomorphism
  `ψ : S → Ω` has finite image on `R`, then `S / ker ψ` is finite.
* `Stacks.BombieriStepanov.exists_algEquiv_comp_eq`: two embeddings of a finite field `E₁/E` into a
  field differ by an automorphism of `E₁/E`.
-/

@[expose] public noncomputable section

namespace Stacks.BombieriStepanov

/-- A homomorphism with finite image on a base ring over which the source is finite has finite
residue ring. -/
theorem finite_quotient_ker {R S Ω : Type*} [CommRing R] [CommRing S] [Field Ω] [Algebra R S]
    [Module.Finite R S] (ψ : S →+* Ω) (h : (Set.range (ψ.comp (algebraMap R S))).Finite) :
    Finite (S ⧸ RingHom.ker ψ) := by
  set p : Ideal R := (RingHom.ker ψ).comap (algebraMap R S)
  have : (RingHom.ker ψ).LiesOver p := ⟨rfl⟩
  have hp : p = RingHom.ker (ψ.comp (algebraMap R S)) := by
    ext r
    simp [p, RingHom.mem_ker]
  have : Finite (R ⧸ p) := by
    rw [hp]
    have : Finite (ψ.comp (algebraMap R S)).range := h
    exact Finite.of_equiv _ (RingHom.quotientKerEquivRange _).symm.toEquiv
  exact Module.finite_of_finite (R ⧸ p)

/-- **Embeddings of a finite field differ by an automorphism.** -/
theorem exists_algEquiv_comp_eq {E E₁ Ω : Type*} [Field E] [Field E₁] [Fintype E₁] [Field Ω]
    [Algebra E E₁] [Algebra E Ω] (u v : E₁ →ₐ[E] Ω) : ∃ τ : E₁ ≃ₐ[E] E₁, ∀ e, v e = u (τ e) := by
  classical
  have hn : 1 < Fintype.card E₁ := Fintype.one_lt_card
  obtain ⟨hfin, hle⟩ := setOf_pow_eq_self_finite_ncard_le (Ω := Ω) hn
  have hrange : ∀ w : E₁ →ₐ[E] Ω, Set.range w = {a : Ω | a ^ Fintype.card E₁ = a} := by
    intro w
    have hsub : Set.range w ⊆ {a : Ω | a ^ Fintype.card E₁ = a} := by
      rintro _ ⟨z, rfl⟩
      simp only [Set.mem_setOf_eq, ← map_pow, FiniteField.pow_card]
    refine Set.eq_of_subset_of_ncard_le hsub ?_ hfin
    rw [Set.ncard_range_of_injective (show Function.Injective w from w.toRingHom.injective),
      Nat.card_eq_fintype_card]
    exact hle
  have hu : Function.Injective u := u.toRingHom.injective
  have hmem : ∀ e, v e ∈ u.range := fun e => by
    rw [← SetLike.mem_coe, AlgHom.coe_range, hrange u, ← hrange v]
    exact ⟨e, rfl⟩
  let eu := AlgEquiv.ofInjective u hu
  let tA : E₁ →ₐ[E] E₁ := eu.symm.toAlgHom.comp (v.codRestrict u.range hmem)
  have hinj : Function.Injective tA := eu.symm.injective.comp fun a b h =>
    v.toRingHom.injective (congrArg Subtype.val h)
  refine ⟨AlgEquiv.ofBijective tA (Finite.injective_iff_bijective.1 hinj), fun e => ?_⟩
  have := eu.apply_symm_apply ⟨v e, hmem e⟩
  exact (congrArg Subtype.val this).symm

end Stacks.BombieriStepanov

end

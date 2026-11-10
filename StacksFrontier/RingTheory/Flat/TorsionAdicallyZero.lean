module

public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Torsion elements lying in every power of an ideal after a flat base change

Let `R` be a Noetherian ring, `I ⊆ R` an ideal and `D` a flat `R`-algebra. An element of `D`
which is killed by a power of `I` and lies in `I ^ n D` for every `n` is zero.

## Main results

* `Ideal.eq_zero_of_mem_map_pow_of_pow_mul_eq_zero`: the statement above.

## Implementation notes

The ideals `ann(I ^ k)` form an ascending chain in the Noetherian ring `R`, so they stabilize at
some `K = ann(I ^ c)`, which then contains every element killed by a power of `I` and satisfies
`I ^ c K = 0`. The Artin–Rees lemma gives `N` with `I ^ N ∩ K ⊆ I ^ c K = 0`. Choosing
generators `b₁, …, bₘ` of `I ^ k`, where `I ^ k` kills the given element, the `R`-linear map
`R → R / I ^ N × Rᵐ`, `a ↦ (ā, (bᵢ a)ᵢ)` has kernel `I ^ N ∩ ann(I ^ k) ⊆ I ^ N ∩ K = 0`, so it is
injective, hence stays injective after tensoring with the flat module `D`; and the tensored map
kills `x ⊗ 1`. No intersection of submodules has to be commuted with the base change.

This is the algebraic step in the proof that two morphisms out of `Spec (Â ⊗_A Â)` agree once
they agree off `V(I)` and on every infinitesimal neighbourhood of `V(I)`, used for the existence
half of [Stacks, Tag 0GI3].

## References

* [Stacks Project, Tag 0GI3](https://stacks.math.columbia.edu/tag/0GI3)
-/

@[expose] public section

open TensorProduct

namespace Ideal

variable {R D : Type*} [CommRing R] [CommRing D] [Algebra R D]

/-- Membership in the annihilator of `I ^ c` is killing every element of `I ^ c`. -/
private theorem mem_annihilator_pow_iff (I : Ideal R) (c : ℕ) (a : R) :
    a ∈ (I ^ c : Submodule R R).annihilator ↔ ∀ b ∈ I ^ c, b * a = 0 := by
  simp [Submodule.mem_annihilator, mul_comm]

/-- In a Noetherian ring the annihilators of the powers of an ideal stabilize: some
`ann(I ^ c)` contains every element killed by a power of `I`. -/
theorem exists_pow_mul_eq_zero_stabilizes [IsNoetherianRing R] (I : Ideal R) :
    ∃ c : ℕ, ∀ (k : ℕ) (a : R), (∀ b ∈ I ^ k, b * a = 0) → ∀ b ∈ I ^ c, b * a = 0 := by
  let K : ℕ →o Ideal R := ⟨fun k => (I ^ k : Submodule R R).annihilator, by
    intro k l hkl a ha
    rw [mem_annihilator_pow_iff] at ha ⊢
    exact fun b hb => ha b (Ideal.pow_le_pow_right hkl hb)⟩
  obtain ⟨c, hc⟩ := (monotone_stabilizes_iff_noetherian.mpr inferInstance) K
  refine ⟨c, fun k a ha b hb => ?_⟩
  have hak : a ∈ K (max c k) := by
    change a ∈ (I ^ max c k : Submodule R R).annihilator
    rw [mem_annihilator_pow_iff]
    exact fun b' hb' => ha b' (Ideal.pow_le_pow_right (le_max_right c k) hb')
  rw [← hc (max c k) (le_max_left c k)] at hak
  exact (mem_annihilator_pow_iff I c a).mp hak b hb

/-- In a Noetherian ring some power of an ideal meets the `I`-power torsion trivially. -/
theorem exists_pow_inf_torsion_eq_zero [IsNoetherianRing R] (I : Ideal R) :
    ∃ N : ℕ, ∀ (k : ℕ) (a : R), a ∈ I ^ N → (∀ b ∈ I ^ k, b * a = 0) → a = 0 := by
  obtain ⟨c, hc⟩ := exists_pow_mul_eq_zero_stabilizes I
  let K : Ideal R := (I ^ c : Submodule R R).annihilator
  obtain ⟨k₀, hk₀⟩ := Ideal.exists_pow_inf_eq_pow_smul I (K : Submodule R R)
  refine ⟨k₀ + c, fun k a haN hak => ?_⟩
  have haK : a ∈ K := by
    exact (mem_annihilator_pow_iff I c a).mpr (hc k a hak)
  have hmem : a ∈ I ^ (k₀ + c) • (⊤ : Submodule R R) ⊓ (K : Submodule R R) :=
    ⟨by rwa [smul_eq_mul, Ideal.mul_top], haK⟩
  rw [hk₀ (k₀ + c) (Nat.le_add_right k₀ c), Nat.add_sub_cancel_left] at hmem
  have hzero : I ^ c • (I ^ k₀ • (⊤ : Submodule R R) ⊓ (K : Submodule R R)) = ⊥ := by
    refine eq_bot_iff.mpr (Submodule.smul_le.mpr fun b hb y hy => ?_)
    simpa [smul_eq_mul] using (mem_annihilator_pow_iff I c y).mp hy.2 b hb
  rw [hzero] at hmem
  simpa using hmem

/-- **A torsion element lying in every `I ^ n D` vanishes.** Let `R` be a Noetherian ring,
`I ⊆ R` an ideal and `D` a flat `R`-algebra. If `x ∈ D` lies in `I ^ n D` for every `n` and is
killed by `I ^ k` for some `k`, then `x = 0`. -/
theorem eq_zero_of_mem_map_pow_of_pow_mul_eq_zero [IsNoetherianRing R] [Module.Flat R D]
    (I : Ideal R) {x : D} (hx : ∀ n : ℕ, x ∈ (I ^ n).map (algebraMap R D)) {k : ℕ}
    (hk : ∀ a ∈ I ^ k, algebraMap R D a * x = 0) : x = 0 := by
  classical
  obtain ⟨N, hN⟩ := exists_pow_inf_torsion_eq_zero I
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (I ^ k : Submodule R R))
  let b : s → R := fun i => (i : R)
  let Ψ : R →ₗ[R] (R ⧸ I ^ N) × (s → R) :=
    LinearMap.prod (Submodule.mkQ (I ^ N)) (LinearMap.pi fun i => LinearMap.mulRight R (b i))
  have hΨ : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro a ha
    rw [LinearMap.mem_ker, Prod.ext_iff] at ha
    obtain ⟨h1, h2⟩ := ha
    have haN : a ∈ I ^ N := (Submodule.Quotient.mk_eq_zero _).mp h1
    have hb : ∀ i : s, a * b i = 0 := fun i => congrFun h2 i
    have hak : ∀ c ∈ I ^ k, c * a = 0 := by
      intro c hc
      rw [← hs] at hc
      refine Submodule.span_induction (fun y hy => ?_) (by simp) (fun y z _ _ hy hz => ?_)
        (fun r y _ hy => ?_) hc
      · rw [mul_comm]; exact hb ⟨y, hy⟩
      · rw [add_mul, hy, hz, add_zero]
      · rw [smul_eq_mul, mul_assoc, hy, mul_zero]
    rw [Submodule.mem_bot]
    exact hN k a haN hak
  have h1 : x ⊗ₜ[R] (Submodule.Quotient.mk 1 : R ⧸ I ^ N) = 0 := by
    refine Submodule.span_induction (p := fun y _ =>
      y ⊗ₜ[R] (Submodule.Quotient.mk 1 : R ⧸ I ^ N) = 0) (fun y hy => ?_) (by simp)
      (fun y z _ _ hy hz => by rw [add_tmul, hy, hz, add_zero]) (fun d y _ hy => ?_) (hx N)
    · obtain ⟨a, ha, rfl⟩ := hy
      rw [Algebra.algebraMap_eq_smul_one, smul_tmul, ← Submodule.Quotient.mk_smul, smul_eq_mul,
        mul_one, (Submodule.Quotient.mk_eq_zero _).mpr ha, tmul_zero]
    · rw [← smul_tmul', hy, smul_zero]
  have h2 : ∀ i : s, x ⊗ₜ[R] (Pi.single i (b i) : s → R) = 0 := by
    intro i
    have hbi : b i ∈ I ^ k := hs ▸ Submodule.subset_span i.2
    have hsingle : (Pi.single i (b i) : s → R) = b i • (Pi.single i 1 : s → R) := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [hsingle, ← smul_tmul, Algebra.smul_def, hk (b i) hbi, zero_tmul]
  have hΨ1 : Ψ 1 = ((Submodule.Quotient.mk 1 : R ⧸ I ^ N), 0) +
      ∑ i : s, ((0 : R ⧸ I ^ N), (Pi.single i (b i) : s → R)) := by
    refine Prod.ext ?_ ?_
    · simp [Ψ, Prod.fst_sum]
    · rw [Prod.snd_add, Prod.snd_sum]
      simp only [zero_add]
      rw [Finset.univ_sum_single]
      ext i
      simp [Ψ, b]
  have hzero : LinearMap.lTensor D Ψ (x ⊗ₜ[R] (1 : R)) = 0 := by
    rw [LinearMap.lTensor_tmul, hΨ1, tmul_add, tmul_sum]
    have e1 : x ⊗ₜ[R] (((Submodule.Quotient.mk 1 : R ⧸ I ^ N), (0 : s → R))) = 0 := by
      simpa using congrArg (LinearMap.lTensor D (LinearMap.inl R (R ⧸ I ^ N) (s → R))) h1
    have e2 : ∀ i : s, x ⊗ₜ[R] (((0 : R ⧸ I ^ N), (Pi.single i (b i) : s → R))) = 0 := fun i => by
      simpa using congrArg (LinearMap.lTensor D (LinearMap.inr R (R ⧸ I ^ N) (s → R))) (h2 i)
    rw [e1, zero_add]
    exact Finset.sum_eq_zero fun i _ => e2 i
  have hx0 : x ⊗ₜ[R] (1 : R) = 0 :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := D) Ψ hΨ (by rw [hzero, map_zero])
  simpa using congrArg (TensorProduct.rid R D) hx0

end Ideal

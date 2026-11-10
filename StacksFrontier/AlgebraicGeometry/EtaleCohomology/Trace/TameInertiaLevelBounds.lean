module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LocalMonodromyGroupTheory
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Mathlib.Topology.LocallyConstant.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Uniform bounds on the local invariants and the local `H¹` of a tame `ℓ`-adic representation

Let `G` be a profinite group, `I ⊆ G` a closed subgroup with a continuous homomorphism
`t : I → ℤ_ℓ` (the `ℓ`-adic tame character of an inertia group) whose kernel `J` is
pro-prime-to-`ℓ`, and `ρ : G → GL_r(ℤ_ℓ)` a continuous representation such that `ρ(I)` fixes no
nonzero vector of `ℚ_ℓ ^ r`. Writing `Mₙ = (ℤ/ℓⁿ⁺¹) ^ r` with the action of `ρ mod ℓⁿ⁺¹`, there
is one `K` such that for every `n`

* every `I`-invariant vector of `Mₙ` is killed by `ℓ ^ K`, and
* `ℓ ^ K` times every continuous `1`-cocycle `I → Mₙ` is a coboundary,

that is, `ℓ ^ K` kills `H⁰(I, Mₙ)` and `H¹(I, Mₙ)` uniformly in `n` (Weil II 1.8, the local terms
at a point at infinity of a curve).

The proof: `ρ(J)` is finite of order prime to `ℓ` (`ρ` kills the pro-prime-to-`ℓ` elements of
`ρ⁻¹(1 + ℓ M_r(ℤ_ℓ))`), so averaging over it gives an idempotent `e` with image the
`J`-invariants, commuting with `ρ(I)`. An element `T ∈ I` whose tame character has the largest
norm generates `I` modulo `J` topologically, so `A = e (ρ T - 1) e + (1 - e)` is invertible over
`ℚ_ℓ`, and `ℓ ^ K = ` the `ℓ`-part of `det A` does the job through the adjugate of `A`. A cocycle
is first made to vanish on `J` by averaging over the finite image of `J` in a finite quotient of
`G`, and then corrected at `T`.

## Main results

* `Stacks.EtaleCohomology.coprime_natCard_of_forall_exists_coprime_pow_eq_one`
* `Stacks.EtaleCohomology.exists_forall_isClosed_subgroup_eq_top_of_ker_le`
* `Stacks.EtaleCohomology.averagingCorrection_spec`
* `Stacks.EtaleCohomology.exists_forall_levelInvariants_and_levelCocycles_killed` — the bounds.
* `Stacks.EtaleCohomology.InertiaLevelsKilledBy`
* `Stacks.EtaleCohomology.exists_inertiaLevelsKilledBy`
-/

@[expose] public noncomputable section

open Matrix Topology

namespace Stacks.EtaleCohomology

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {r : ℕ}

/-- A finite group all of whose elements have order prime to `ℓ` has order prime to `ℓ`
(Cauchy). -/
theorem coprime_natCard_of_forall_exists_coprime_pow_eq_one {X : Type*} [Group X] [Finite X]
    (h : ∀ x : X, ∃ m : ℕ, ℓ.Coprime m ∧ x ^ m = 1) : ℓ.Coprime (Nat.card X) := by
  refine (Nat.Prime.coprime_iff_not_dvd hℓ.out).2 fun hdvd => ?_
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' ℓ hdvd
  obtain ⟨m, hm, hxm⟩ := h x
  have : ℓ ∣ m := hx ▸ orderOf_dvd_of_pow_eq_one hxm
  exact hℓ.out.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hm this)

/-- **Topological generation modulo the kernel of a character to `ℤ_ℓ`.** For a continuous
homomorphism `t` from a compact group `H` to `ℤ_ℓ`, there is `T ∈ H` such that every closed
subgroup of `H` containing `ker t` and `T` is all of `H`: take `T` with `‖t T‖` largest. -/
theorem exists_forall_isClosed_subgroup_eq_top_of_ker_le {H : Type*} [Group H]
    [TopologicalSpace H] [CompactSpace H] (t : H →* Multiplicative ℤ_[ℓ]) (ht : Continuous t) :
    ∃ T : H, ∀ Z : Subgroup H, IsClosed (Z : Set H) → t.ker ≤ Z → T ∈ Z → Z = ⊤ := by
  let f : H → ℤ_[ℓ] := fun σ => Multiplicative.toAdd (t σ)
  have hf : Continuous f := continuous_toAdd.comp ht
  obtain ⟨T, -, hT⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    (continuous_norm.comp hf).continuousOn
  refine ⟨T, fun Z hZ hker hTZ => ?_⟩
  have hfmul : ∀ σ τ : H, f (σ * τ) = f σ + f τ := fun σ τ => by simp [f]
  have hfzpow : ∀ (σ : H) (k : ℤ), f (σ ^ k) = (k : ℤ_[ℓ]) * f σ := fun σ k => by
    simp [f, toAdd_zpow, zsmul_eq_mul]
  have hmemker : ∀ σ : H, f σ = 0 → σ ∈ Z := fun σ h0 => hker (by
    rw [MonoidHom.mem_ker]
    exact Multiplicative.toAdd.injective h0)
  have key : ∀ σ : H, (∃ ζ ∈ Z, f ζ = f σ) → σ ∈ Z := by
    rintro σ ⟨ζ, hζ, hζσ⟩
    have : σ * ζ⁻¹ ∈ Z := hmemker _ (by
      have h1 := hfmul (σ * ζ⁻¹) ζ
      rw [inv_mul_cancel_right, hζσ] at h1
      linear_combination -h1)
    simpa using Z.mul_mem this hζ
  refine eq_top_iff.2 fun σ _ => key σ ?_
  by_cases ha : f T = 0
  · refine ⟨1, Z.one_mem, ?_⟩
    have h1 : ‖f σ‖ ≤ ‖f T‖ := hT (Set.mem_univ σ)
    rw [ha, norm_zero] at h1
    rw [norm_le_zero_iff.1 h1]
    simp [f]
  · -- `f T ∣ f σ`
    obtain ⟨μ, hμ⟩ : f T ∣ f σ := by
      have h1 : ‖f σ‖ ≤ ‖f T‖ := hT (Set.mem_univ σ)
      have hval : (ℓ : ℤ_[ℓ]) ^ (f T).valuation ∣ f σ := by
        rw [pow_dvd_iff_norm_le, ← PadicInt.norm_eq_zpow_neg_valuation ha]
        exact h1
      obtain ⟨u, hu⟩ : ∃ u : ℤ_[ℓ]ˣ, f T = u * (ℓ : ℤ_[ℓ]) ^ (f T).valuation :=
        ⟨_, PadicInt.unitCoeff_spec ha⟩
      refine dvd_trans ⟨(u⁻¹ : ℤ_[ℓ]ˣ), ?_⟩ hval
      calc (ℓ : ℤ_[ℓ]) ^ (f T).valuation = u * (ℓ : ℤ_[ℓ]) ^ (f T).valuation * (u⁻¹ : ℤ_[ℓ]ˣ) := by
            rw [mul_comm (u : ℤ_[ℓ]), mul_assoc, Units.mul_inv, mul_one]
        _ = f T * (u⁻¹ : ℤ_[ℓ]ˣ) := by rw [← hu]
    -- the image of `Z` is closed and contains `ℤ · f T`, hence `ℤ_ℓ · f T`
    have hC : IsClosed (f '' (Z : Set H)) := (hZ.isCompact.image hf).isClosed
    let D : Set ℤ_[ℓ] := (fun x : ℤ_[ℓ] => f T * x) ⁻¹' (f '' (Z : Set H))
    have hD : IsClosed D := hC.preimage (continuous_const.mul continuous_id)
    have hrange : Set.range (Int.cast : ℤ → ℤ_[ℓ]) ⊆ D := by
      rintro _ ⟨k, rfl⟩
      exact ⟨T ^ k, Z.zpow_mem hTZ k, by rw [hfzpow, mul_comm]⟩
    have hμD : μ ∈ D := by
      have := closure_minimal hrange hD
      rw [PadicInt.denseRange_intCast.closure_range] at this
      exact this (Set.mem_univ μ)
    obtain ⟨ζ, hζ, hζμ⟩ := hμD
    exact ⟨ζ, hζ, hζμ.trans hμ.symm⟩

section LinearAlgebra

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

/-- If `A = E (T - 1) E + (1 - E)` sends `x` to a vector `y` fixed by the idempotent `E` (which
commutes with `T`), then `E x = x` and `(T - 1) x = y`. -/
private theorem averaging_eq_of_averaging_mulVec_eq {E T : Matrix n n R} (hE : E * E = E)
    (hTE : T * E = E * T) {x y : n → R} (hy : E *ᵥ y = y)
    (hx : (E * (T - 1) * E + (1 - E)) *ᵥ x = y) : E *ᵥ x = x ∧ (T - 1) *ᵥ x = y := by
  have hEc : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hE, sub_self]
  have hEc' : (1 - E) * (1 - E) = 1 - E := by rw [mul_sub, mul_one, hEc, sub_zero]
  have hEc2 : E * (1 - E) = 0 := by rw [mul_sub, mul_one, hE, sub_self]
  have hT1 : (T - 1) * E = E * (T - 1) := by rw [sub_mul, mul_sub, hTE, one_mul, mul_one]
  have h1 : (1 - E) * (E * (T - 1) * E + (1 - E)) = 1 - E := by
    rw [mul_add, ← mul_assoc, ← mul_assoc, hEc, zero_mul, zero_mul, zero_add, hEc']
  have h2 : E * (E * (T - 1) * E + (1 - E)) = (T - 1) * E := by
    rw [mul_add, hEc2, add_zero, ← mul_assoc, ← mul_assoc, hE, ← hT1, mul_assoc, hE]
  have hEx : E *ᵥ x = x := by
    have : (1 - E) *ᵥ x = 0 := by
      rw [← h1, ← mulVec_mulVec, hx, sub_mulVec, one_mulVec, hy, sub_self]
    rw [sub_mulVec, one_mulVec, sub_eq_zero] at this
    exact this.symm
  refine ⟨hEx, ?_⟩
  rw [← hEx, mulVec_mulVec, ← h2, ← mulVec_mulVec, hx, hy]

/-- **The adjugate correction.** Let `E` be an idempotent matrix commuting with `T`, and
`A = E (T - 1) E + (1 - E)`. For `w` with `E w = w`, the vector `z = adj(A) w` satisfies `E z = z`
and `(T - 1) z = det A • w`. -/
theorem averagingCorrection_spec {E T : Matrix n n R} (hE : E * E = E) (hTE : T * E = E * T)
    {w : n → R} (hw : E *ᵥ w = w) :
    E *ᵥ ((E * (T - 1) * E + (1 - E)).adjugate *ᵥ w) =
        (E * (T - 1) * E + (1 - E)).adjugate *ᵥ w ∧
      (T - 1) *ᵥ ((E * (T - 1) * E + (1 - E)).adjugate *ᵥ w) =
        (E * (T - 1) * E + (1 - E)).det • w :=
  averaging_eq_of_averaging_mulVec_eq hE hTE (by rw [mulVec_smul, hw])
    (by simp only [mulVec_mulVec, mul_adjugate, smul_mulVec, one_mulVec])

/-- With `A = E (T - 1) E + (1 - E)` as in `Stacks.EtaleCohomology.averagingCorrection_spec`,
`det A` kills every `v` with `E v = v` and `T v = v`. -/
theorem det_smul_eq_zero_of_averaging {E T : Matrix n n R}
    {v : n → R} (hv : E *ᵥ v = v) (hTv : T *ᵥ v = v) :
    (E * (T - 1) * E + (1 - E)).det • v = 0 := by
  have hAv : (E * (T - 1) * E + (1 - E)) *ᵥ v = 0 := by
    rw [add_mulVec, sub_mulVec, one_mulVec, hv, sub_self, add_zero, ← mulVec_mulVec, hv,
      ← mulVec_mulVec, sub_mulVec, one_mulVec, hTv, sub_self, mulVec_zero]
  rw [← one_mulVec v, ← smul_mulVec, ← adjugate_mul, ← mulVec_mulVec, hAv, mulVec_zero]

/-- With `A = E (T - 1) E + (1 - E)` as in `Stacks.EtaleCohomology.averagingCorrection_spec`,
a vector killed by `A` is fixed by `E` and by `T`. -/
theorem mulVec_eq_of_averaging_mulVec_eq_zero {E T : Matrix n n R} (hE : E * E = E)
    (hTE : T * E = E * T) {x : n → R} (hx : (E * (T - 1) * E + (1 - E)) *ᵥ x = 0) :
    E *ᵥ x = x ∧ T *ᵥ x = x := by
  obtain ⟨hEx, hTx⟩ := averaging_eq_of_averaging_mulVec_eq hE hTE (mulVec_zero E) hx
  rw [sub_mulVec, one_mulVec, sub_eq_zero] at hTx
  exact ⟨hEx, hTx⟩

end LinearAlgebra

section FiniteImage

/-- **The image of a pro-prime-to-`ℓ` subgroup is finite of order prime to `ℓ`.** If every
element of `J` has, in every open subgroup, a power with exponent prime to `ℓ`, then for a
continuous `ρ : G → GL_r(ℤ_ℓ)` the group `ρ(J)` injects into `GL_r(𝔽_ℓ)` and its elements have
order prime to `ℓ`. -/
@[sga "7 I 1.3" "more general"]
theorem finite_map_and_coprime_natCard_map {G : Type*} [Group G] [TopologicalSpace G]
    {ρ : G →* GL (Fin r) ℤ_[ℓ]} (hρ : Continuous ρ) (J : Subgroup G)
    (hJ : ∀ σ ∈ J, ∀ U : OpenSubgroup G, ∃ m : ℕ, ℓ.Coprime m ∧ σ ^ m ∈ U) :
    Finite (J.map ρ) ∧ ℓ.Coprime (Nat.card (J.map ρ)) := by
  have hone : ∀ σ ∈ J, ρ σ ∈ congruenceSubgroup ℓ r 1 → ρ σ = 1 := fun σ hσ h1 =>
    map_eq_one_of_forall_exists_coprime_pow_mem hρ h1 (hJ σ hσ)
  have hfin : Finite (J.map ρ) := by
    let red : J.map ρ → Matrix (Fin r) (Fin r) (ZMod (ℓ ^ 1)) := fun γ =>
      (PadicInt.toZModPow 1).mapMatrix ((γ : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ])
    refine Finite.of_injective red fun γ₁ γ₂ h => ?_
    obtain ⟨σ₁, h₁, e₁⟩ := Subgroup.mem_map.1 γ₁.2
    obtain ⟨σ₂, h₂, e₂⟩ := Subgroup.mem_map.1 γ₂.2
    have hdvd : ∀ i j, (ℓ : ℤ_[ℓ]) ^ 1 ∣ (((ρ σ₂ : GL (Fin r) ℤ_[ℓ]) :
        Matrix (Fin r) (Fin r) ℤ_[ℓ]) - (ρ σ₁ : GL (Fin r) ℤ_[ℓ])) i j := fun i j => by
      have hij := congrFun (congrFun h i) j
      simp only [red, RingHom.mapMatrix_apply, Matrix.map_apply, ← e₁, ← e₂] at hij
      rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker,
        Matrix.sub_apply, map_sub, hij, sub_self]
    have hmem : ρ (σ₁⁻¹ * σ₂) ∈ congruenceSubgroup ℓ r 1 := by
      rw [mem_congruenceSubgroup]
      intro i j
      have : ((ρ (σ₁⁻¹ * σ₂) : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ]) - 1 =
          ((ρ σ₁)⁻¹ : GL (Fin r) ℤ_[ℓ]) * (((ρ σ₂ : GL (Fin r) ℤ_[ℓ]) :
            Matrix (Fin r) (Fin r) ℤ_[ℓ]) - (ρ σ₁ : GL (Fin r) ℤ_[ℓ])) := by
        rw [map_mul, map_inv, Matrix.mul_sub, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel,
          Units.val_one]
      rw [this]
      exact dvd_mul_apply_of_dvd_right hdvd i j
    have := hone _ (J.mul_mem (J.inv_mem h₁) h₂) hmem
    rw [map_mul, map_inv, inv_mul_eq_one] at this
    exact Subtype.ext (e₁.symm.trans (this.trans e₂))
  refine ⟨hfin, coprime_natCard_of_forall_exists_coprime_pow_eq_one fun γ => ?_⟩
  obtain ⟨σ, hσ, e⟩ := Subgroup.mem_map.1 γ.2
  let U : OpenSubgroup G :=
    { toSubgroup := (congruenceSubgroup ℓ r 1).comap ρ
      isOpen' := (isOpen_congruenceSubgroup 1).preimage hρ }
  obtain ⟨m, hm, hmU⟩ := hJ σ hσ U
  refine ⟨m, hm, Subtype.ext ?_⟩
  have h1 := hone _ (J.pow_mem hσ m) hmU
  rw [map_pow, e] at h1
  simpa using h1

end FiniteImage

section Averaging

/-- **Averaging over a finite group of matrices of order prime to `ℓ`.** For a finite subgroup
`S ⊆ GL_r(ℤ_ℓ)` of order prime to `ℓ`, `e = |S|⁻¹ ∑_{γ ∈ S} γ` is an idempotent absorbing `S`,
commuting with every `g` normalizing `S`, and fixing, after any ring map `φ` out of `ℤ_ℓ`, every
`S`-invariant vector. -/
theorem exists_averaging_idempotent (S : Subgroup (GL (Fin r) ℤ_[ℓ])) [Finite S]
    (hS : ℓ.Coprime (Nat.card S)) :
    ∃ e : Matrix (Fin r) (Fin r) ℤ_[ℓ], e * e = e ∧
      (∀ γ ∈ S, (γ : Matrix (Fin r) (Fin r) ℤ_[ℓ]) * e = e) ∧
      (∀ g : GL (Fin r) ℤ_[ℓ], (∀ γ ∈ S, g * γ * g⁻¹ ∈ S) →
        (g : Matrix (Fin r) (Fin r) ℤ_[ℓ]) * e = e * g) ∧
      ∀ {R : Type*} [CommRing R] (φ : ℤ_[ℓ] →+* R) (v : Fin r → R),
        (∀ γ ∈ S, φ.mapMatrix (γ : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ v = v) →
          φ.mapMatrix e *ᵥ v = v := by
  classical
  have : Fintype S := Fintype.ofFinite S
  have hc : IsUnit (Nat.card S : ℤ_[ℓ]) := by
    rw [PadicInt.isUnit_iff]
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => ?_)
    rw [PadicInt.norm_lt_one_iff_dvd] at h
    exact not_dvd_natCast_of_coprime hS h
  let a : ℤ_[ℓ] := ((hc.unit⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ])
  have ha : a * (Fintype.card S : ℤ_[ℓ]) = 1 := by
    rw [← Nat.card_eq_fintype_card]; exact hc.val_inv_mul
  let Ssum : Matrix (Fin r) (Fin r) ℤ_[ℓ] := ∑ γ : S, ((γ : GL (Fin r) ℤ_[ℓ]) : Matrix _ _ _)
  have hleft : ∀ γ₀ ∈ S, (γ₀ : Matrix (Fin r) (Fin r) ℤ_[ℓ]) * Ssum = Ssum := fun γ₀ h₀ => by
    rw [Finset.mul_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft (⟨γ₀, h₀⟩ : S)) _ _ fun γ => by simp
  have hright : ∀ γ₀ ∈ S, Ssum * (γ₀ : Matrix (Fin r) (Fin r) ℤ_[ℓ]) = Ssum := fun γ₀ h₀ => by
    rw [Finset.sum_mul]
    exact Fintype.sum_equiv (Equiv.mulRight (⟨γ₀, h₀⟩ : S)) _ _ fun γ => by simp
  refine ⟨a • Ssum, ?_, fun γ₀ h₀ => by rw [Matrix.mul_smul, hleft γ₀ h₀], fun g hg => ?_,
    fun {R} _ φ v hv => ?_⟩
  · have hre : ∀ γ₀ ∈ S, a • Ssum * (γ₀ : Matrix (Fin r) (Fin r) ℤ_[ℓ]) = a • Ssum :=
      fun γ₀ h₀ => by rw [Matrix.smul_mul, hright γ₀ h₀]
    calc a • Ssum * (a • Ssum)
        = a • ∑ γ : S, a • Ssum * ((γ : GL (Fin r) ℤ_[ℓ]) : Matrix _ _ _) := by
          rw [Matrix.mul_smul, Finset.mul_sum]
      _ = a • ∑ _γ : S, a • Ssum := by
          congr 1; exact Finset.sum_congr rfl fun γ _ => hre γ γ.2
      _ = a • Ssum := by
          rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℤ_[ℓ], smul_smul,
            smul_smul, ha, one_mul]
  · -- conjugation by `g` permutes `S`
    let c : S → S := fun γ => ⟨g * γ * g⁻¹, hg γ γ.2⟩
    have hcinj : Function.Injective c := fun γ₁ γ₂ h => by
      have := congrArg (fun x : S => (g⁻¹ * (x : GL (Fin r) ℤ_[ℓ]) * g)) h
      exact Subtype.ext (by simpa [c, mul_assoc] using this)
    let ce : S ≃ S := Equiv.ofBijective c hcinj.bijective_of_finite
    have hconj : (g : Matrix (Fin r) (Fin r) ℤ_[ℓ]) * Ssum * ((g⁻¹ : GL (Fin r) ℤ_[ℓ]) :
        Matrix (Fin r) (Fin r) ℤ_[ℓ]) = Ssum := by
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Fintype.sum_equiv ce _ _ fun γ => by simp [ce, c, Equiv.ofBijective, Units.val_mul]
    have hginv : ((g⁻¹ : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *
        (g : Matrix (Fin r) (Fin r) ℤ_[ℓ]) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    calc (g : Matrix (Fin r) (Fin r) ℤ_[ℓ]) * Ssum =
        (g : Matrix (Fin r) (Fin r) ℤ_[ℓ]) * Ssum * (((g⁻¹ : GL (Fin r) ℤ_[ℓ]) :
          Matrix (Fin r) (Fin r) ℤ_[ℓ]) * (g : Matrix (Fin r) (Fin r) ℤ_[ℓ])) := by
          rw [hginv, Matrix.mul_one]
      _ = Ssum * g := by rw [← Matrix.mul_assoc, hconj]
  · have hmap : φ.mapMatrix (a • Ssum) =
        φ a • ∑ γ : S, φ.mapMatrix ((γ : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ]) := by
      ext i j
      simp [Ssum, Matrix.sum_apply, map_sum]
    rw [hmap, Matrix.smul_mulVec, Matrix.sum_mulVec,
      Finset.sum_congr rfl fun (γ : S) _ => hv (γ : GL (Fin r) ℤ_[ℓ]) γ.2, Finset.sum_const,
      Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul R, smul_smul, ← map_natCast φ, ← map_mul, ha, map_one, one_smul]

end Averaging

section Cocycles

/-- **A continuous cocycle is a coboundary on a pro-prime-to-`ℓ` subgroup.** Let `G` be profinite,
`I ⊆ G` a subgroup, `J ⊆ I` a subgroup all of whose elements have, in every open subgroup of
`G`, a power with exponent prime to `ℓ`, and `act : G → M_r(ℤ/ℓ^N)` multiplicative and trivial
near `1`. A locally constant `1`-cocycle `c : I → (ℤ/ℓ^N)^r` agrees on `J` with a coboundary:
`c` factors through the finite image `H` of `J` in `G/N` for an open normal `N`, `H` has order
prime to `ℓ`, and averaging over `H` gives the vector. -/
theorem exists_eq_coboundary_of_forall_exists_coprime_pow_mem {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    {I : Subgroup G} (J : Subgroup I)
    (hJ : ∀ σ ∈ J, ∀ U : OpenSubgroup G, ∃ m : ℕ, ℓ.Coprime m ∧ (σ : G) ^ m ∈ U)
    {N : ℕ} (act : G →* Matrix (Fin r) (Fin r) (ZMod (ℓ ^ N)))
    {W : Set G} (hW : IsOpen W) (h1W : (1 : G) ∈ W) (hWact : ∀ σ ∈ W, act σ = 1)
    (c : I → Fin r → ZMod (ℓ ^ N)) (hc : IsLocallyConstant c)
    (hcoc : ∀ σ τ : I, c (σ * τ) = act σ *ᵥ c τ + c σ) :
    ∃ m : Fin r → ZMod (ℓ ^ N), ∀ σ ∈ J, c σ = act σ *ᵥ m - m := by
  classical
  have hc1 : c 1 = 0 := by
    have h := hcoc 1 1
    simpa using h
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.1 (hc.isOpen_fiber 0)
  have h1O : (1 : G) ∈ O := by
    have : (1 : I) ∈ Subtype.val ⁻¹' O := by rw [hOeq]; exact hc1
    exact this
  have : T1Space G := ⟨fun x => connectedComponent_eq_singleton x ▸ isClosed_connectedComponent⟩
  have : ZeroDimensionalSpace G := inferInstance
  obtain ⟨Nn, hNn⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (hO.inter hW)
    ⟨h1O, h1W⟩
  have : Nn.toSubgroup.Normal := Nn.isNormal'
  have hNc : ∀ ν : I, (ν : G) ∈ Nn → c ν = 0 ∧ act ν = 1 := fun ν hν => by
    have h := hNn hν
    refine ⟨?_, hWact _ h.2⟩
    have : ν ∈ Subtype.val ⁻¹' O := h.1
    rw [hOeq] at this
    exact this
  have : Finite (G ⧸ Nn.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ Nn.isOpen'
  let π : I →* G ⧸ Nn.toSubgroup := (QuotientGroup.mk' Nn.toSubgroup).comp I.subtype
  have hπ : ∀ ν : I, π ν = 1 ↔ (ν : G) ∈ Nn := fun ν => QuotientGroup.eq_one_iff _
  let H := J.map π
  have : Fintype H := Fintype.ofFinite H
  have hH : ℓ.Coprime (Fintype.card H) := by
    rw [← Nat.card_eq_fintype_card]
    refine coprime_natCard_of_forall_exists_coprime_pow_eq_one fun h => ?_
    obtain ⟨σ, hσ, e⟩ := Subgroup.mem_map.1 h.2
    obtain ⟨m, hm, hmN⟩ := hJ σ hσ Nn.toOpenSubgroup
    refine ⟨m, hm, Subtype.ext ?_⟩
    have : π (σ ^ m) = 1 := (hπ _).2 (by rw [SubgroupClass.coe_pow]; exact hmN)
    rw [map_pow, e] at this
    simpa using this
  choose s hsJ hsπ using fun h : H => Subgroup.mem_map.1 h.2
  let Sm : Fin r → ZMod (ℓ ^ N) := ∑ h : H, c (s h)
  have key : ∀ g ∈ J, Sm = act g *ᵥ Sm + Fintype.card H • c g := fun g hg => by
    let gH : H := ⟨π g, Subgroup.mem_map_of_mem π hg⟩
    have hstep : ∀ h : H, c (s (gH * h)) = act g *ᵥ c (s h) + c g := fun h => by
      let ν : I := (g * s h)⁻¹ * s (gH * h)
      have hν : π ν = 1 := by
        simp only [ν, map_mul, map_inv, hsπ]
        change (π g * (h : G ⧸ Nn.toSubgroup))⁻¹ * ((gH : G ⧸ Nn.toSubgroup) * h) = 1
        exact inv_mul_cancel _
      obtain ⟨hcν, -⟩ := hNc ν ((hπ ν).1 hν)
      have hs : s (gH * h) = g * s h * ν := (mul_inv_cancel_left _ _).symm
      rw [hs, hcoc, hcν, mulVec_zero, zero_add, hcoc]
    calc Sm = ∑ h : H, c (s (gH * h)) :=
          (Fintype.sum_equiv (Equiv.mulLeft gH) _ _ fun h => rfl).symm
      _ = ∑ h : H, (act g *ᵥ c (s h) + c g) := Finset.sum_congr rfl fun h _ => hstep h
      _ = act g *ᵥ Sm + Fintype.card H • c g := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Matrix.mulVec_sum]
  have hcop : (Fintype.card H).Coprime (ℓ ^ N) := (Nat.Coprime.pow_left N hH).symm
  let u := ZMod.unitOfCoprime _ hcop
  let a : ZMod (ℓ ^ N) := ((u⁻¹ : (ZMod (ℓ ^ N))ˣ) : ZMod (ℓ ^ N))
  have ha : a * (Fintype.card H : ZMod (ℓ ^ N)) = 1 := by
    rw [← ZMod.coe_unitOfCoprime _ hcop]; exact u.inv_mul
  refine ⟨-(a • Sm), fun g hg => ?_⟩
  have hk : (Fintype.card H : ZMod (ℓ ^ N)) • c g = Sm - act g *ᵥ Sm := by
    rw [Nat.cast_smul_eq_nsmul]
    exact eq_sub_of_add_eq' (key g hg).symm
  rw [mulVec_neg, mulVec_smul, sub_neg_eq_add]
  calc c g = a • ((Fintype.card H : ZMod (ℓ ^ N)) • c g) := by rw [smul_smul, ha, one_smul]
    _ = -(a • act g *ᵥ Sm) + a • Sm := by rw [hk, smul_sub]; abel

end Cocycles

section Main

/-- **Uniform bounds on `H⁰` and `H¹` of a tame inertia group at the levels of an `ℓ`-adic
representation without inertia invariants** (Weil II 1.8). Let `G` be profinite, `I ⊆ G` closed
with a continuous character `t : I → ℤ_ℓ` whose kernel consists of pro-prime-to-`ℓ` elements, and
`ρ : G → GL_r(ℤ_ℓ)` continuous with no nonzero `ρ(I)`-invariant vector. Then there is `K` such
that for every `n`, on `Mₙ = (ℤ/ℓⁿ⁺¹) ^ r`, `ℓ ^ K` kills every `I`-invariant vector, and `ℓ ^ K`
times every locally constant `1`-cocycle `c : I → Mₙ` (`c (σ τ) = σ • c τ + c σ`) is a coboundary
`σ ↦ σ • m - m`. -/
theorem exists_forall_levelInvariants_and_levelCocycles_killed {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (I : Subgroup G) (hI : IsClosed (I : Set G)) (t : I →* Multiplicative ℤ_[ℓ])
    (ht : Continuous t)
    (htame : ∀ σ : I, t σ = 1 → ∀ U : OpenSubgroup G, ∃ m : ℕ, ℓ.Coprime m ∧ (σ : G) ^ m ∈ U)
    (ρ : G →* GL (Fin r) ℤ_[ℓ]) (hρ : Continuous ρ)
    (hinv : ∀ v : Fin r → ℤ_[ℓ],
      (∀ σ ∈ I, (ρ σ : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ v = v) → v = 0) :
    ∃ K : ℕ, ∀ n : ℕ,
      (∀ v : Fin r → ZMod (ℓ ^ (n + 1)), (∀ σ ∈ I, (PadicInt.toZModPow (n + 1)).mapMatrix
          (ρ σ : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ v = v) → ℓ ^ K • v = 0) ∧
      ∀ c : I → Fin r → ZMod (ℓ ^ (n + 1)), IsLocallyConstant c →
        (∀ σ τ : I, c (σ * τ) = (PadicInt.toZModPow (n + 1)).mapMatrix
          (ρ σ : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ c τ + c σ) →
        ∃ m : Fin r → ZMod (ℓ ^ (n + 1)), ∀ σ : I, ℓ ^ K • c σ =
          (PadicInt.toZModPow (n + 1)).mapMatrix (ρ σ : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ m -
            m := by
  classical
  have : CompactSpace I := isCompact_iff_compactSpace.mp hI.isCompact
  let J : Subgroup I := t.ker
  let JG : Subgroup G := J.map I.subtype
  have hJG : ∀ σ ∈ JG, ∀ U : OpenSubgroup G, ∃ m : ℕ, ℓ.Coprime m ∧ σ ^ m ∈ U := by
    rintro _ ⟨σ, hσ, rfl⟩ U
    exact htame σ hσ U
  let S := JG.map ρ
  obtain ⟨hSfin, hScop⟩ := finite_map_and_coprime_natCard_map hρ JG hJG
  obtain ⟨e, he2, heS, heN, heφ⟩ := exists_averaging_idempotent S hScop
  have hJe : ∀ σ : I, σ ∈ J → (ρ σ : Matrix (Fin r) (Fin r) ℤ_[ℓ]) * e = e := fun σ hσ =>
    heS _ (Subgroup.mem_map_of_mem ρ (Subgroup.mem_map_of_mem I.subtype hσ))
  have hIe : ∀ σ : I, (ρ σ : Matrix (Fin r) (Fin r) ℤ_[ℓ]) * e =
      e * (ρ σ : Matrix (Fin r) (Fin r) ℤ_[ℓ]) := fun σ => heN _ (by
    rintro _ ⟨_, ⟨τ, hτ, rfl⟩, rfl⟩
    refine ⟨I.subtype (σ * τ * σ⁻¹), Subgroup.mem_map_of_mem I.subtype ?_, by simp⟩
    have hτ' : t τ = 1 := hτ
    change t (σ * τ * σ⁻¹) = 1
    rw [map_mul, map_mul, hτ', mul_one, map_inv, mul_inv_cancel])
  obtain ⟨T, hT⟩ := exists_forall_isClosed_subgroup_eq_top_of_ker_le t ht
  set A : Matrix (Fin r) (Fin r) ℤ_[ℓ] := e * ((ρ T : Matrix (Fin r) (Fin r) ℤ_[ℓ]) - 1) * e +
    (1 - e) with hA
  have hdet : A.det ≠ 0 := by
    intro h0
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    obtain ⟨hex, hTx⟩ := mulVec_eq_of_averaging_mulVec_eq_zero he2 (hIe T) hx
    let Z : Subgroup I :=
      { carrier := {σ | (ρ σ : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ x = x}
        one_mem' := by simp
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_ofPred_eq] at ha hb ⊢
          rw [Subgroup.coe_mul, map_mul, Units.val_mul, ← mulVec_mulVec, hb, ha]
        inv_mem' := by
          intro a ha
          simp only [Set.mem_ofPred_eq] at ha ⊢
          rw [InvMemClass.coe_inv, map_inv]
          calc (((ρ a)⁻¹ : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ x =
              (((ρ a)⁻¹ : GL (Fin r) ℤ_[ℓ]) : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ
                ((ρ a : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ x) := by rw [ha]
            _ = x := by
              rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec] }
    have hZc : IsClosed (Z : Set I) :=
      isClosed_eq ((Units.continuous_val.comp (hρ.comp continuous_subtype_val)).matrix_mulVec
        continuous_const) continuous_const
    have hZ := hT Z hZc (fun σ hσ => by
      change (ρ σ : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ x = x
      rw [← hex, mulVec_mulVec, hJe σ hσ]) hTx
    refine hx0 (hinv x fun σ hσ => ?_)
    have : (⟨σ, hσ⟩ : I) ∈ Z := hZ ▸ Subgroup.mem_top _
    exact this
  obtain ⟨w, hw⟩ : ∃ w : ℤ_[ℓ]ˣ, A.det = w * (ℓ : ℤ_[ℓ]) ^ A.det.valuation :=
    ⟨_, PadicInt.unitCoeff_spec hdet⟩
  refine ⟨A.det.valuation, fun n => ?_⟩
  set K := A.det.valuation
  let φ := PadicInt.toZModPow (p := ℓ) (n + 1)
  let En := φ.mapMatrix e
  let Tn := φ.mapMatrix (ρ T : Matrix (Fin r) (Fin r) ℤ_[ℓ])
  have hE2 : En * En = En := by simp only [En, ← map_mul, he2]
  have hIEn : ∀ σ : I, φ.mapMatrix (ρ σ : Matrix (Fin r) (Fin r) ℤ_[ℓ]) * En =
      En * φ.mapMatrix (ρ σ : Matrix (Fin r) (Fin r) ℤ_[ℓ]) := fun σ => by
    simp only [En, ← map_mul, hIe σ]
  have hJEn : ∀ σ : I, σ ∈ J → φ.mapMatrix (ρ σ : Matrix (Fin r) (Fin r) ℤ_[ℓ]) * En = En :=
    fun σ hσ => by simp only [En, ← map_mul, hJe σ hσ]
  have hJinv : ∀ v : Fin r → ZMod (ℓ ^ (n + 1)), (∀ σ : I, σ ∈ J →
      φ.mapMatrix (ρ σ : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ v = v) → En *ᵥ v = v :=
    fun v hv => heφ φ v (by
      rintro _ ⟨_, ⟨τ, hτ, rfl⟩, rfl⟩
      exact hv τ hτ)
  have hAn : φ.mapMatrix A = En * (Tn - 1) * En + (1 - En) := by
    simp only [hA, En, Tn, map_add, map_mul, map_sub, map_one]
  have hdetn : (En * (Tn - 1) * En + (1 - En)).det = φ w * (ℓ : ZMod (ℓ ^ (n + 1))) ^ K := by
    rw [← hAn, ← RingHom.map_det, hw, map_mul, map_pow, map_natCast]
  have hwu : φ ((w⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * φ w = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hkill : ∀ v : Fin r → ZMod (ℓ ^ (n + 1)),
      (φ w * (ℓ : ZMod (ℓ ^ (n + 1))) ^ K) • v = 0 → ℓ ^ K • v = 0 := fun v h => by
    have := congrArg (fun y => φ ((w⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • y) h
    simp only [smul_smul, ← mul_assoc, hwu, one_mul, smul_zero] at this
    rw [← Nat.cast_smul_eq_nsmul (ZMod (ℓ ^ (n + 1))), Nat.cast_pow]
    exact this
  refine ⟨fun v hv => hkill v ?_, fun c hc hcoc => ?_⟩
  · have hvJ : En *ᵥ v = v := hJinv v fun σ _ => hv σ σ.2
    rw [← hdetn]
    exact det_smul_eq_zero_of_averaging hvJ (hv T T.2)
  let act : G →* Matrix (Fin r) (Fin r) (ZMod (ℓ ^ (n + 1))) :=
    φ.mapMatrix.toMonoidHom.comp ((Units.coeHom _).comp ρ)
  have hact : ∀ σ : G, act σ = φ.mapMatrix (ρ σ : Matrix (Fin r) (Fin r) ℤ_[ℓ]) := fun _ => rfl
  let W : Set G := ρ ⁻¹' (congruenceSubgroup ℓ r (n + 1) : Set (GL (Fin r) ℤ_[ℓ]))
  have hW : IsOpen W := (isOpen_congruenceSubgroup _).preimage hρ
  have h1W : (1 : G) ∈ W := by
    change ρ 1 ∈ congruenceSubgroup ℓ r (n + 1)
    rw [map_one]
    exact (congruenceSubgroup ℓ r (n + 1)).one_mem
  have hWact : ∀ σ ∈ W, act σ = 1 := fun σ hσ => by
    have h0 : φ.mapMatrix ((ρ σ : Matrix (Fin r) (Fin r) ℤ_[ℓ]) - 1) = 0 := by
      ext i j
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply, ← RingHom.mem_ker,
        PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
      exact (mem_congruenceSubgroup.1 hσ) i j
    rw [hact, ← sub_eq_zero, ← map_one φ.mapMatrix, ← map_sub]
    exact h0
  have hcoc' : ∀ σ τ : I, c (σ * τ) = act σ *ᵥ c τ + c σ := hcoc
  obtain ⟨m', hm'⟩ := exists_eq_coboundary_of_forall_exists_coprime_pow_mem J
    (fun σ hσ U => htame σ hσ U) act hW h1W hWact c hc hcoc'
  let c' : I → Fin r → ZMod (ℓ ^ (n + 1)) := fun σ => c σ - (act σ *ᵥ m' - m')
  have hc'coc : ∀ σ τ : I, c' (σ * τ) = act σ *ᵥ c' τ + c' σ := by
    intro σ τ
    simp only [c', hcoc' σ τ, Subgroup.coe_mul, map_mul, mulVec_sub, ← mulVec_mulVec]
    abel
  have hc'J : ∀ g : I, g ∈ J → c' g = 0 := fun g hg => by
    change c g - (act g *ᵥ m' - m') = 0
    rw [← hm' g hg, sub_self]
  have hc'inv : ∀ σ g : I, g ∈ J → act g *ᵥ c' σ = c' σ := fun σ g hg => by
    have h1 := hc'coc g σ
    rw [hc'J g hg, add_zero] at h1
    have hconj : σ⁻¹ * g * σ ∈ J := by
      have hg' : t g = 1 := hg
      change t (σ⁻¹ * g * σ) = 1
      rw [map_mul, map_mul, hg', mul_one, map_inv, inv_mul_cancel]
    have h2 := hc'coc σ (σ⁻¹ * g * σ)
    rw [hc'J _ hconj, mulVec_zero, zero_add, show σ * (σ⁻¹ * g * σ) = g * σ by group] at h2
    rw [← h1, h2]
  have hc'E : ∀ σ : I, En *ᵥ c' σ = c' σ := fun σ => hJinv _ fun g hg => hc'inv σ g hg
  obtain ⟨hzE, hzT⟩ := averagingCorrection_spec hE2 (hIEn T) (hc'E T)
  set z := (En * (Tn - 1) * En + (1 - En)).adjugate *ᵥ c' T
  let z' := φ ((w⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • z
  have hz'E : En *ᵥ z' = z' := by simp only [z', mulVec_smul, hzE]
  have hdetn' : (En * (φ.mapMatrix (ρ T : Matrix (Fin r) (Fin r) ℤ_[ℓ]) - 1) * En +
      (1 - En)).det = φ w * (ℓ : ZMod (ℓ ^ (n + 1))) ^ K := hdetn
  have hz'T : (Tn - 1) *ᵥ z' = ℓ ^ K • c' T := by
    change (φ.mapMatrix (ρ T : Matrix (Fin r) (Fin r) ℤ_[ℓ]) - 1) *ᵥ
      (φ ((w⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • z) = _
    rw [mulVec_smul, hzT, hdetn', smul_smul, ← mul_assoc, hwu, one_mul,
      ← Nat.cast_smul_eq_nsmul (ZMod (ℓ ^ (n + 1))), Nat.cast_pow]
  have hz'J : ∀ g : I, g ∈ J → act g *ᵥ z' = z' := fun g hg => by
    conv_lhs => rw [← hz'E]
    rw [mulVec_mulVec, hact, hJEn g hg, hz'E]
  let d : I → Fin r → ZMod (ℓ ^ (n + 1)) := fun σ => ℓ ^ K • c' σ - (act σ *ᵥ z' - z')
  have hdcoc : ∀ σ τ : I, d (σ * τ) = act σ *ᵥ d τ + d σ := by
    intro σ τ
    simp only [d, hc'coc σ τ, Subgroup.coe_mul, map_mul, mulVec_sub, mulVec_smul,
      ← mulVec_mulVec, smul_add]
    abel
  have hd1 : d 1 = 0 := by
    have h := hdcoc 1 1
    simpa using h
  let Z : Subgroup I :=
    { carrier := {σ | d σ = 0}
      one_mem' := hd1
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [hdcoc, ha, hb, mulVec_zero, add_zero]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_ofPred_eq] at ha ⊢
        have h := hdcoc a⁻¹ a
        rw [inv_mul_cancel, hd1, ha, mulVec_zero, zero_add] at h
        exact h.symm }
  have hZo : IsOpen (Z : Set I) := by
    refine Subgroup.isOpen_of_mem_nhds Z (g := 1) (Filter.mem_of_superset
      (((hc.isOpen_fiber 0).inter (hW.preimage continuous_subtype_val)).mem_nhds
        ⟨?_, h1W⟩) fun σ hσ => ?_)
    · have h := hcoc' 1 1
      simpa using h
    · obtain ⟨hcσ, hσW⟩ := hσ
      have hcσ' : c σ = 0 := hcσ
      have haσ := hWact _ hσW
      change ℓ ^ K • (c σ - (act σ *ᵥ m' - m')) - (act σ *ᵥ z' - z') = 0
      rw [hcσ', haσ]
      simp
  have hZ := hT Z (Subgroup.isClosed_of_isOpen Z hZo) (fun g hg => by
      change ℓ ^ K • c' g - (act g *ᵥ z' - z') = 0
      rw [hc'J g hg, hz'J g hg, smul_zero, sub_self, sub_self]) (by
      change ℓ ^ K • c' T - (act T *ᵥ z' - z') = 0
      rw [← hz'T, sub_mulVec, one_mulVec, hact, sub_self])
  refine ⟨z' + ℓ ^ K • m', fun σ => ?_⟩
  have hσ : σ ∈ Z := hZ ▸ Subgroup.mem_top σ
  have hdσ : ℓ ^ K • c' σ - (act σ *ᵥ z' - z') = 0 := hσ
  rw [sub_eq_zero] at hdσ
  have hcσ : c σ = c' σ + (act σ *ᵥ m' - m') := by simp [c']
  rw [hcσ, smul_add, hdσ, ← hact]
  simp only [mulVec_add, mulVec_smul, smul_sub]
  abel

/-- **`ℓ ^ e` kills the levels of `H⁰` and `H¹` of `I` with coefficients in `ρ`.** For a subgroup
`I` of a topological group `G` and `ρ : G → GL_r(ℤ_ℓ)`: for every `n`, on `Mₙ = (ℤ/ℓⁿ⁺¹) ^ r`,
`ℓ ^ e` kills every `I`-invariant vector and `ℓ ^ e` times every locally constant `1`-cocycle
`I → Mₙ` is a coboundary. -/
public def InertiaLevelsKilledBy {G : Type*} [Group G] [TopologicalSpace G] (I : Subgroup G)
    (ρ : G →* GL (Fin r) ℤ_[ℓ]) (e : ℕ) : Prop :=
  ∀ n : ℕ,
    (∀ v : Fin r → ZMod (ℓ ^ (n + 1)), (∀ σ ∈ I, (PadicInt.toZModPow (n + 1)).mapMatrix
        (ρ σ : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ v = v) → ℓ ^ e • v = 0) ∧
    ∀ c : I → Fin r → ZMod (ℓ ^ (n + 1)), IsLocallyConstant c →
      (∀ σ τ : I, c (σ * τ) = (PadicInt.toZModPow (n + 1)).mapMatrix
        (ρ σ : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ c τ + c σ) →
      ∃ m : Fin r → ZMod (ℓ ^ (n + 1)), ∀ σ : I, ℓ ^ e • c σ =
        (PadicInt.toZModPow (n + 1)).mapMatrix (ρ σ : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ m - m

/-- `Stacks.EtaleCohomology.exists_forall_levelInvariants_and_levelCocycles_killed` in terms of
`Stacks.EtaleCohomology.InertiaLevelsKilledBy`. -/
theorem exists_inertiaLevelsKilledBy {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (I : Subgroup G) (hI : IsClosed (I : Set G)) (t : I →* Multiplicative ℤ_[ℓ])
    (ht : Continuous t)
    (htame : ∀ σ : I, t σ = 1 → ∀ U : OpenSubgroup G, ∃ m : ℕ, ℓ.Coprime m ∧ (σ : G) ^ m ∈ U)
    (ρ : G →* GL (Fin r) ℤ_[ℓ]) (hρ : Continuous ρ)
    (hinv : ∀ v : Fin r → ℤ_[ℓ],
      (∀ σ ∈ I, (ρ σ : Matrix (Fin r) (Fin r) ℤ_[ℓ]) *ᵥ v = v) → v = 0) :
    ∃ e : ℕ, InertiaLevelsKilledBy I ρ e :=
  exists_forall_levelInvariants_and_levelCocycles_killed I hI t ht htame ρ hρ hinv

end Main

end Stacks.EtaleCohomology

end

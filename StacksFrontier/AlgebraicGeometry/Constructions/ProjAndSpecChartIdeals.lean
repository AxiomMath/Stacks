module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjAndSpecZeroSectionCartesian
public import StacksFrontier.RingTheory.GradedAlgebra.TruncationLocalization

/-!
# The ideals `σ(f)`, `σ(A_d)` and `Ker(τ)` on a standard chart of the cone

Let `A` be an `ℕ`-graded ring, `B = ⨁_{d ≥ 0} A_{≥ d}` its truncation algebra with the maps
`σ, ψ, τ`, `f ∈ A_d` with `d > 0` and `g = ψ(f) ∈ B_d`. On the standard affine open
`D₊(g) = Spec((B[1/g])₀)` of the cone `L = Proj(B)` consider the two ring maps

* `σ : A → (B[1/g])₀`, `a ↦ a⁽⁰⁾ / 1`, through which `D₊(g)` lies over `X = Spec(A)`;
* `τ : (B[1/g])₀ → (A[1/f])₀`, the localization of `τ : B → A`, which defines the zero section
  `0 : P → L` over `D₊(g)`.

We prove the five computations of Stacks, Section 0EKF:

1. `σ(A₊)(B[1/g])₀ ⊆ Ker(τ)`;
2. `σ(f)` is a nonzerodivisor of `(B[1/g])₀`;
3. `σ(f)(B[1/g])₀ = σ(A_d)(B[1/g])₀`;
4. `σ(f)(B[1/g])₀` and `Ker(τ)` have the same radical;
5. if `d = 1` then `σ(f)(B[1/g])₀ = Ker(τ)`;

and their geometric consequence: inside `D₊(g)` the image of the zero section is, set
theoretically, the zero locus of `σ(f)`.

All five are checked through the injective comparison map `(B[1/g])₀ → A[1/f]`,
`a⁽ᵏᵈ⁾ / gᵏ ↦ a / fᵏ` (`Stacks.Truncation.awayToLocalization`), which sends `σ(a)` to `a / 1`.

## References

* [Stacks Project, Tag 0EKF](https://stacks.math.columbia.edu/tag/0EKF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry HomogeneousLocalization Stacks.Truncation
open Stacks.AlgebraicGeometry.ProjAndSpecTruncation

namespace Stacks.AlgebraicGeometry.ProjAndSpecChartIdeals

universe u

variable {A : Type u} {σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The ring map `σ : A → (B[1/ψ f])₀`, `a ↦ a⁽⁰⁾ / 1`. -/
abbrev chartSigma (f : A) : A →+* Away (grading 𝒜) (psi 𝒜 f) :=
  ProjAndSpec.awayFromBase (truncationConeData 𝒜) (psi 𝒜 f)

/-- The ring map `τ : (B[1/ψ f])₀ → (A[1/f])₀` induced by `τ : B → A` (the target is written
`A_{(τ ψ f)}`, and `τ (ψ f) = f`). -/
abbrev chartTau (f : A) : Away (grading 𝒜) (psi 𝒜 f) →+* Away 𝒜 (tau 𝒜 (psi 𝒜 f)) :=
  Away.map (tau 𝒜) (psi 𝒜 f)

variable {𝒜}

/-! ### Computations through the comparison map `(B[1/ψ f])₀ → A[1/f]` -/

section Compare

variable {d : ℕ} {f : A}

/-- The comparison map sends `σ(a)` to `a / 1`. -/
theorem awayToLocalization_chartSigma (a : A) :
    awayToLocalization 𝒜 (chartSigma 𝒜 f a) = algebraMap A (Localization.Away f) a := by
  rw [awayToLocalization, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply]
  change Localization.awayLift ((algebraMap A (Localization.Away f)).comp (forgetDegree 𝒜))
    (psi 𝒜 f) _ (Localization.mk ((sigma 𝒜 a : grading 𝒜 0) : TruncationRing 𝒜) 1) = _
  rw [Localization.mk_one_eq_algebraMap]
  refine (IsLocalization.Away.lift_eq (psi 𝒜 f) _ _).trans ?_
  rw [RingHom.comp_apply, coe_sigma_eq_degElt, forgetDegree_degElt]

/-- Powers of fractions: `(a / fᵏ)ⁿ = aⁿ / fⁿᵏ`. -/
theorem awayFrac_pow (k : ℕ) (a : A) (n : ℕ) :
    awayFrac f k a ^ n = awayFrac f (n * k) (a ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, zero_mul, awayFrac_one]
  | succ n ih => rw [pow_succ, ih, awayFrac_mul, pow_succ, Nat.succ_mul]

/-- The fraction `a⁽ᵏᵈ⁾ / (ψ f)ᵏ` written with `HomogeneousLocalization.Away.mk`. -/
theorem awayElt_eq_away_mk (hf : f ∈ 𝒜 d) (k : ℕ) (a : A) (ha : a ∈ truncation 𝒜 (k * d))
    (h : degElt 𝒜 (k * d) a ha ∈ grading 𝒜 (k • d)) :
    awayElt 𝒜 d hf k a ha =
      Away.mk (grading 𝒜) (GradedRingHom.map_mem (psi 𝒜) hf) k (degElt 𝒜 (k * d) a ha) h :=
  congrArg HomogeneousLocalization.mk
    (HomogeneousLocalization.NumDenSameDeg.ext _ (nsmul_eq_mul k d).symm rfl rfl)

/-- If `τ` kills `a⁽ᵏᵈ⁾ / (ψ f)ᵏ` then a power of `f` kills the degree `kd` component of `a`. -/
theorem exists_pow_mul_proj_eq_zero_of_chartTau_eq_zero (hf : f ∈ 𝒜 d) (k : ℕ) (a : A)
    (ha : a ∈ truncation 𝒜 (k * d)) (h0 : chartTau 𝒜 f (awayElt 𝒜 d hf k a ha) = 0) :
    ∃ N : ℕ, f ^ N * GradedRing.proj 𝒜 (k * d) a = 0 := by
  have hmem : degElt 𝒜 (k * d) a ha ∈ grading 𝒜 (k • d) := by
    rw [smul_eq_mul]
    exact degElt_mem_grading 𝒜 _ a ha
  rw [awayElt_eq_away_mk hf k a ha hmem, chartTau, Away.map_mk] at h0
  have h1 := congrArg HomogeneousLocalization.val h0
  rw [Away.val_mk, val_zero, Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff] at h1
  obtain ⟨⟨_, N, rfl⟩, hN⟩ := h1
  refine ⟨N, ?_⟩
  rw [tau_degElt, tau_psi_apply] at hN
  exact hN

end Compare

/-! ### The five computations -/

section Five

variable {d : ℕ} {f : A}

/-- **(1) `σ(A₊)(B[1/g])₀ ⊆ Ker(τ : (B[1/g])₀ → (A[1/f])₀)`** for `g = ψ(f)`. -/
@[stacks 0EKF "(1): σ(A₊)(B[1/g])₀ ⊆ Ker(τ : (B[1/g])₀ → (A[1/f])₀), g = ψ(f)"]
theorem map_irrelevant_le_ker_chartTau (f : A) :
    Ideal.map (chartSigma 𝒜 f) (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
      RingHom.ker (chartTau 𝒜 f) :=
  ProjAndSpec.map_awayFromBase_le_ker_awayMap_tau (truncationConeData 𝒜) (psi 𝒜 f)

/-- **(2) `σ(f)` is a nonzerodivisor of `(B[1/g])₀`**, for `f ∈ A_d` and `g = ψ(f)`. -/
@[stacks 0EKF "(2): σ(f) is a nonzerodivisor of (B[1/g])₀, g = ψ(f)"]
theorem chartSigma_self_mem_nonZeroDivisors (hf : f ∈ 𝒜 d) :
    chartSigma 𝒜 f f ∈ nonZeroDivisors (Away (grading 𝒜) (psi 𝒜 f)) := by
  refine mem_nonZeroDivisors_iff_right.mpr fun x hx => ?_
  have hinj := awayToLocalization_injective 𝒜 d hf
  have h1 := congrArg (awayToLocalization 𝒜 (f := f)) hx
  rw [map_mul, map_zero, awayToLocalization_chartSigma] at h1
  have hu : IsUnit (algebraMap A (Localization.Away f) f) :=
    IsLocalization.Away.algebraMap_isUnit f
  exact hinj ((hu.mul_left_eq_zero.mp h1).trans (map_zero _).symm)

/-- `σ(a) = σ(f) · a⁽ᵈ⁾ / ψ(f)` in `(B[1/ψ f])₀`, for `a, f ∈ A_d`. -/
theorem chartSigma_eq_mul (hf : f ∈ 𝒜 d) {a : A} (ha : a ∈ 𝒜 d) :
    chartSigma 𝒜 f a = chartSigma 𝒜 f f *
      awayElt 𝒜 d hf 1 a (by rw [one_mul]; exact mem_truncation_of_mem 𝒜 le_rfl ha) := by
  refine awayToLocalization_injective 𝒜 d hf ?_
  rw [map_mul, awayToLocalization_chartSigma, awayToLocalization_chartSigma,
    awayToLocalization_awayElt, ← awayFrac_zero_eq_algebraMap, ← awayFrac_zero_eq_algebraMap,
    awayFrac_mul, awayFrac_shift f 0 1 a, pow_one]

/-- **(3) `σ(f)(B[1/g])₀ = σ(A_d)(B[1/g])₀` as ideals**, for `f ∈ A_d` and `g = ψ(f)`. -/
@[stacks 0EKF "(3): σ(f)(B[1/g])₀ = σ(A_d)(B[1/g])₀ as ideals, g = ψ(f)"]
theorem span_chartSigma_self_eq_map_span (hf : f ∈ 𝒜 d) :
    Ideal.span {chartSigma 𝒜 f f} =
      Ideal.map (chartSigma 𝒜 f) (Ideal.span (𝒜 d : Set A)) := by
  rw [Ideal.map_span]
  refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
  · rintro _ rfl
    exact Ideal.subset_span ⟨f, hf, rfl⟩
  · rintro _ ⟨a, ha, rfl⟩
    rw [chartSigma_eq_mul hf ha]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

/-- An element of `Ker(τ)` is a fraction `c⁽ᵉᵈ⁾ / (ψ f)ᵉ` with `c ∈ A_{≥ ed + 1}`. -/
theorem exists_awayElt_of_mem_ker_chartTau (hf : f ∈ 𝒜 d)
    {x : Away (grading 𝒜) (psi 𝒜 f)} (hx : x ∈ RingHom.ker (chartTau 𝒜 f)) :
    ∃ (e : ℕ) (c : A) (hc : c ∈ truncation 𝒜 (e * d)), c ∈ truncation 𝒜 (e * d + 1) ∧
      x = awayElt 𝒜 d hf e c hc := by
  obtain ⟨k, a, ha, rfl⟩ := awayElt_surjective 𝒜 d hf x
  obtain ⟨N, hN⟩ := exists_pow_mul_proj_eq_zero_of_chartTau_eq_zero hf k a ha hx
  have hfN : f ^ N ∈ truncation 𝒜 (N * d) :=
    pow_mem_truncation 𝒜 (mem_truncation_of_mem 𝒜 le_rfl hf) N
  have hc' : f ^ N * a ∈ truncation 𝒜 (N * d + k * d) := mul_mem_truncation 𝒜 hfN ha
  have hdeg : N * d + k * d = (k + N) * d := by ring
  have hc : f ^ N * a ∈ truncation 𝒜 ((k + N) * d) := hdeg ▸ hc'
  refine ⟨k + N, f ^ N * a, hc, ?_, ?_⟩
  · refine (mem_truncation_iff 𝒜).mpr fun j hj => ?_
    rcases Nat.lt_or_ge j ((k + N) * d) with hj' | hj'
    · exact (mem_truncation_iff 𝒜).mp hc j hj'
    · have hje : j = N * d + k * d := by omega
      have hfN' : f ^ N ∈ 𝒜 (N * d) := by
        simpa only [smul_eq_mul] using SetLike.pow_mem_graded N hf
      rw [hje, proj_mul_of_mem_truncation 𝒜 hfN ha, GradedRing.proj_apply 𝒜 (N * d),
        DirectSum.decompose_of_mem_same 𝒜 hfN']
      exact hN
  · refine awayToLocalization_injective 𝒜 d hf ?_
    rw [awayToLocalization_awayElt, awayToLocalization_awayElt, awayFrac_shift f k N a]

/-- **(4) `σ(f)(B[1/g])₀` and `Ker(τ : (B[1/g])₀ → (A[1/f])₀)` have the same radical**, for
`f ∈ A_d` with `d > 0` and `g = ψ(f)`. -/
@[stacks 0EKF "(4): σ(f)(B[1/g])₀ and Ker(τ : (B[1/g])₀ → (A[1/f])₀) have the same radical, \
g = ψ(f), f ∈ A_d, d > 0"]
theorem radical_span_chartSigma_self_eq_radical_ker (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    (Ideal.span {chartSigma 𝒜 f f}).radical = (RingHom.ker (chartTau 𝒜 f)).radical := by
  refine le_antisymm (Ideal.radical_mono ?_) ?_
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact map_irrelevant_le_ker_chartTau f
      (Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hd hf))
  · refine (Ideal.radical_mono fun x hx => ?_).trans (Ideal.radical_idem _).le
    obtain ⟨e, c, hc, hc1, rfl⟩ := exists_awayElt_of_mem_ker_chartTau hf hx
    have hcd : c ^ d ∈ truncation 𝒜 ((d * e + 1) * d) := by
      have := pow_mem_truncation 𝒜 hc1 d
      rwa [show d * (e * d + 1) = (d * e + 1) * d by ring] at this
    refine ⟨d, ?_⟩
    have heq : awayElt 𝒜 d hf e c hc ^ d =
        chartSigma 𝒜 f f * awayElt 𝒜 d hf (d * e + 1) (c ^ d) hcd := by
      refine awayToLocalization_injective 𝒜 d hf ?_
      rw [map_pow, map_mul, awayToLocalization_awayElt, awayToLocalization_awayElt,
        awayToLocalization_chartSigma, awayFrac_pow, ← awayFrac_zero_eq_algebraMap, awayFrac_mul,
        awayFrac_shift f (d * e) 1, pow_one, zero_add]
    rw [heq]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

/-- **(5) If `d = 1` then `σ(f)(B[1/g])₀ = Ker(τ : (B[1/g])₀ → (A[1/f])₀)`**, for `f ∈ A_1` and
`g = ψ(f)`. -/
@[stacks 0EKF "(5): if d = 1 then σ(f)(B[1/g])₀ = Ker(τ : (B[1/g])₀ → (A[1/f])₀), g = ψ(f)"]
theorem span_chartSigma_self_eq_ker_of_mem_one (hf : f ∈ 𝒜 1) :
    Ideal.span {chartSigma 𝒜 f f} = RingHom.ker (chartTau 𝒜 f) := by
  refine le_antisymm ?_ fun x hx => ?_
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact map_irrelevant_le_ker_chartTau f
      (Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 one_pos hf))
  · obtain ⟨e, c, hc, hc1, rfl⟩ := exists_awayElt_of_mem_ker_chartTau hf hx
    have hc' : c ∈ truncation 𝒜 ((e + 1) * 1) := by simpa only [mul_one] using hc1
    have heq : awayElt 𝒜 1 hf e c hc = chartSigma 𝒜 f f * awayElt 𝒜 1 hf (e + 1) c hc' := by
      refine awayToLocalization_injective 𝒜 1 hf ?_
      rw [map_mul, awayToLocalization_awayElt, awayToLocalization_awayElt,
        awayToLocalization_chartSigma, ← awayFrac_zero_eq_algebraMap, awayFrac_mul,
        awayFrac_shift f e 1, pow_one, zero_add]
    rw [heq]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

end Five

/-! ### The zero section over `D₊(ψ f)` is the zero locus of `σ(f)` -/

/-- **Inside `D₊(g)`, `g = ψ(f)`, the image of the zero section is the zero locus of `σ(f)`**:
`0(D₊(f)) = V(σ(f)) ⊆ D₊(g)` set theoretically, the complement in `D₊(g)` of `D₊(σ(f) g)`. -/
@[stacks 0EKF "0(D₊(f)) = V(σ(f)) ⊆ D₊(g) set theoretically, g = ψ(f)"]
theorem range_zeroSection_inter_basicOpen (f : A) (d : ℕ) (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    Set.range (zeroSection 𝒜) ∩ (Proj.basicOpen (grading 𝒜) (psi 𝒜 f) : Set _) =
      (Proj.basicOpen (grading 𝒜) (psi 𝒜 f) : Set _) \
        (Proj.basicOpen (grading 𝒜) (((sigma 𝒜 f : grading 𝒜 0) : TruncationRing 𝒜) *
          psi 𝒜 f) : Set _) := by
  rw [range_zeroSection, ← openUInL_inf_basicOpen 𝒜 f d hf hd]
  ext y
  simp only [Set.mem_inter_iff, Set.mem_compl_iff, SetLike.mem_coe, Set.mem_sdiff,
    TopologicalSpace.Opens.mem_inf]
  tauto

end Stacks.AlgebraicGeometry.ProjAndSpecChartIdeals

end

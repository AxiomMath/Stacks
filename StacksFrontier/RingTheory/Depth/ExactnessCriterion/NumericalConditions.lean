module


public import StacksFrontier.LinearAlgebra.Matrix.DeterminantalRank
public import StacksFrontier.RingTheory.Depth.Defs.Defs
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.Tactic.Monotonicity.Lemmas
import StacksFrontier.Algebra.Homology.FiniteFreeComplex
import StacksFrontier.RingTheory.Depth.Acyclicity
import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Support
public import StacksFrontier.RingTheory.Depth.Nakayama
public import StacksFrontier.RingTheory.Module.IdealSmulTop
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.Depth.ExactnessCriterion.MinorsAndDepth
public import StacksFrontier.RingTheory.Depth.ExactnessCriterion.DepthZero

/-!
# The Buchsbaum–Eisenbud exactness criterion: the numerical conditions

The numerical conditions of the Buchsbaum–Eisenbud exactness criterion
(`LinearMap.injective_and_exact_iff_forall_rank_eq_and_le_depth_minors`) at the map `φ k`:

* (2)(a) the rank of `φ k` is the alternating sum `n_{k+1} - n_{k+2} + ⋯ ± n_{e+1}`, and
* (2)(b) the ideal `I(φ k)` of `rank × rank` minors of `φ k` satisfies `depth_{I(φ k)}(R) ≥ k + 1`.

This file proves the forward direction: an exact complex satisfies both. For the rank, the
complex is localized at each associated prime `𝔮` of `R`, where `R_𝔮` has depth `0`. The depth
bound is an induction on `e`, over a varying base ring: prime avoidance gives a nonzerodivisor `x`
in every `I(φ k)`, and the complex modulo `x` is exact one spot less far down (`tag_00MZ`).

It also collects the ingredients of the converse direction: the numerical conditions are
inherited by localizations at primes, and the acyclicity step shows that a complex over a ring of
large enough depth which is exact at every non-maximal prime is exact.

## References

* [StacksProject 00N1](https://stacks.math.columbia.edu/tag/00N1)
* D. A. Buchsbaum and D. Eisenbud, *What makes a complex exact?*, Corollary 1

## Tags

exact complex, finite free module, rank, minor, depth, regular sequence
-/

@[expose] public section

namespace Stacks.Depth.BuchsbaumEisenbud

open RingTheory.Sequence Stacks.DeterminantalRank

/-! ## The criterion -/

section Criterion

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- The numerical conditions (2)(a) and (2)(b) at the map `φ k`, in terms of
`Stacks.DeterminantalRank.exteriorRank` and `Stacks.DeterminantalRank.detIdeal`. -/
def Numerical (e : ℕ) (n : ℕ → ℕ)
    (φ : ∀ i, (Fin (n (i + 1)) → R) →ₗ[R] (Fin (n i) → R)) (k : ℕ) : Prop :=
  ((exteriorRank (LinearMap.toMatrix' (φ k)) : ℤ)
      = ∑ t ∈ Finset.range (e + 1 - k), (-1) ^ t * (n (k + 1 + t) : ℤ)) ∧
    ((k + 1 : ℕ) : ℕ∞) ≤ Module.depth R (detIdeal (LinearMap.toMatrix' (φ k))) R

/-- For `e = 0` the alternating sum at `k = 0` is the single term `n 1`. -/
private lemma sum_range_one_eq (n : ℕ → ℕ) :
    ∑ t ∈ Finset.range (0 + 1 - 0), (-1 : ℤ) ^ t * (n (0 + 1 + t) : ℤ) = (n 1 : ℤ) := by
  simp

/-- **The criterion for `e = 0`.** A single map of finite free modules
over a Noetherian local ring is injective exactly when its rank is the rank of its source and its
ideal of maximal minors has depth at least one. -/
lemma numerical_zero_iff (n : ℕ → ℕ)
    (φ : ∀ i, (Fin (n (i + 1)) → R) →ₗ[R] (Fin (n i) → R)) :
    Function.Injective (φ 0) ↔ Numerical 0 n φ 0 := by
  have hmv : (LinearMap.toMatrix' (φ 0)).mulVecLin = φ 0 := Matrix.toLin'_toMatrix' (φ 0)
  have h00MX := injective_iff_rank_eq_and_contains_nonZeroDivisor (LinearMap.toMatrix' (φ 0))
  rw [hmv] at h00MX
  rw [Numerical, sum_range_one_eq, h00MX,
    show ((0 + 1 : ℕ) : ℕ∞) = 1 from by norm_num,
    one_le_depth_self_iff (detIdeal (LinearMap.toMatrix' (φ 0)))]
  exact and_congr_left' (by simp)

omit [IsLocalRing R] in
/-- **An exact complex at a prime whose localization has depth zero.** The complex, localized at
`p`, has at every spot `k ≤ e` rank the alternating sum and unit determinantal ideal. -/
private lemma rank_eq_and_minorIdeal_eq_top_localization (p : Ideal R) [p.IsPrime]
    (hdepth : IsLocalRing.maximalIdeal (Localization.AtPrime p)
      ∈ associatedPrimes (Localization.AtPrime p) (Localization.AtPrime p))
    (e : ℕ) (n : ℕ → ℕ)
    (φ : ∀ i, (Fin (n (i + 1)) → R) →ₗ[R] (Fin (n i) → R))
    (hφ : ∀ k < e, φ k ∘ₗ φ (k + 1) = 0)
    (hinj : Function.Injective (φ e))
    (hex : ∀ k < e, Function.Exact (φ (k + 1)) (φ k)) :
    ∀ k ≤ e, ((StacksComplex.rank ((LinearMap.toMatrix' (φ k)).map
          (algebraMap R (Localization.AtPrime p))) : ℤ)
        = ∑ t ∈ Finset.range (e + 1 - k), (-1) ^ t * (n (k + 1 + t) : ℤ))
      ∧ StacksComplex.minorIdeal ((LinearMap.toMatrix' (φ k)).map
          (algebraMap R (Localization.AtPrime p))) = ⊤ := by
  have hmv : ∀ i, (LinearMap.toMatrix' (φ i)).mulVecLin = φ i :=
    fun i => Matrix.toLin'_toMatrix' (φ i)
  refine rank_eq_and_minorIdeal_eq_top_of_injective_of_exact_of_depthZero hdepth e n
    (fun i => (LinearMap.toMatrix' (φ i)).map (algebraMap R (Localization.AtPrime p)))
    (fun k hk => ?_) ?_ (fun k hk => ?_)
  · rw [← Matrix.map_mul, ← LinearMap.toMatrix'_comp, hφ k hk]
    simp
  · exact injective_map_algebraMap_atPrime p _ (by rwa [hmv])
  · rw [← LinearMap.exact_iff]
    exact exact_map_algebraMap_atPrime p _ _
      (by simpa only [hmv] using hex k hk)

/-- **Condition (2)(a) from exactness.** Over a local Noetherian ring, exactness of
`0 → R^{n_{e+1}} → ⋯ → R^{n_0}` at `R^{n_{e+1}}, …, R^{n_1}` forces the rank of `φ k` to be the
alternating sum `n_{k+1} - n_{k+2} + ⋯ ± n_{e+1}`.

The rank of the map localized at an associated prime is the alternating sum, the localization
having depth `0`, and is at most the rank over `R` (`rank_map_le`); conversely a minor of size one
more than the alternating sum dies in every localization at an associated prime, hence is zero
(`eq_zero_of_forall_algebraMap_atPrime_eq_zero`). -/
lemma rank_eq_of_exact (e : ℕ) (n : ℕ → ℕ)
    (φ : ∀ i, (Fin (n (i + 1)) → R) →ₗ[R] (Fin (n i) → R))
    (hφ : ∀ k < e, φ k ∘ₗ φ (k + 1) = 0)
    (hinj : Function.Injective (φ e))
    (hex : ∀ k < e, Function.Exact (φ (k + 1)) (φ k)) :
    ∀ k ≤ e, (exteriorRank (LinearMap.toMatrix' (φ k)) : ℤ)
      = ∑ t ∈ Finset.range (e + 1 - k), (-1) ^ t * (n (k + 1 + t) : ℤ) := by
  intro k hk
  rw [exteriorRank_eq_rank]
  obtain ⟨q, hq⟩ := associatedPrimes.nonempty R R
  have := hq.isPrime
  have hq0 := rank_eq_and_minorIdeal_eq_top_localization q
    (maximalIdeal_mem_associatedPrimes_atPrime hq) e n φ hφ hinj hex k hk
  have hkey : StacksComplex.rank (LinearMap.toMatrix' (φ k))
      = StacksComplex.rank ((LinearMap.toMatrix' (φ k)).map
        (algebraMap R (Localization.AtPrime q))) := by
    refine le_antisymm (StacksComplex.rank_le _ fun r hr => ?_) (rank_map_le _ _)
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨ρ, γ, hne⟩ := hr
    refine hne (eq_zero_of_forall_algebraMap_atPrime_eq_zero fun q' hq' => ?_)
    have := hq'.isPrime
    rw [det_submatrix_map]
    refine StacksComplex.minor_eq_zero_of_rank_lt _ ?_ ρ γ
    have h1 := (rank_eq_and_minorIdeal_eq_top_localization q'
      (maximalIdeal_mem_associatedPrimes_atPrime hq') e n φ hφ hinj hex k hk).1
    have h2 := h1.trans hq0.1.symm
    omega
  rw [hkey]
  exact hq0.1

/-- **No `I(φ k)` lies in an associated prime.** Over a local Noetherian ring, if the complex is
exact at `R^{n_{e+1}}, …, R^{n_1}` then for every `𝔮 ∈ Ass(R)` and every `k ≤ e` the ideal
`I(φ k)` is not contained in `𝔮`.

With the ranks pinned by `rank_eq_of_exact`, forming `I(φ k)` commutes with localizing at `𝔮`,
so `I(φ k)_𝔮 = I(φ_{k,𝔮})`, and the latter is the unit ideal because `R_𝔮` has depth `0`. -/
private lemma detIdeal_not_le_of_exact (e : ℕ) (n : ℕ → ℕ)
    (φ : ∀ i, (Fin (n (i + 1)) → R) →ₗ[R] (Fin (n i) → R))
    (hφ : ∀ k < e, φ k ∘ₗ φ (k + 1) = 0)
    (hinj : Function.Injective (φ e))
    (hex : ∀ k < e, Function.Exact (φ (k + 1)) (φ k)) :
    ∀ k ≤ e, ∀ q ∈ associatedPrimes R R, ¬ detIdeal (LinearMap.toMatrix' (φ k)) ≤ q := by
  intro k hk q hq hle
  have := hq.isPrime
  have hloc := rank_eq_and_minorIdeal_eq_top_localization q
    (maximalIdeal_mem_associatedPrimes_atPrime hq) e n φ hφ hinj hex k hk
  have hrk : StacksComplex.rank ((LinearMap.toMatrix' (φ k)).map
        (algebraMap R (Localization.AtPrime q)))
      = StacksComplex.rank (LinearMap.toMatrix' (φ k)) := by
    have h2 := rank_eq_of_exact e n φ hφ hinj hex k hk
    rw [exteriorRank_eq_rank] at h2
    have h1 := hloc.1
    omega
  have htop : (detIdeal (LinearMap.toMatrix' (φ k))).map
      (algebraMap R (Localization.AtPrime q)) = ⊤ := by
    rw [detIdeal_eq_minorIdeal, ← minorIdeal_map_of_rank_map_eq _ _ hrk]
    exact hloc.2
  have hle2 : (⊤ : Ideal (Localization.AtPrime q))
      ≤ IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
    rw [← htop, ← IsLocalization.AtPrime.map_eq_maximalIdeal q (Localization.AtPrime q)]
    exact Ideal.map_mono hle
  exact (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime q)).ne_top
    (top_le_iff.mp hle2)

/-- **Condition (2)(b) from exactness.** Over a local Noetherian ring `R`, exactness of
`0 → R^{n_{e+1}} → ⋯ → R^{n_0}` at `R^{n_{e+1}}, …, R^{n_1}` forces
`depth_{I(φ k)}(R) ≥ k + 1` for every `k ≤ e`.

The proof is an induction on `e` over a varying base ring, whence the explicitly quantified ring
`T`: the inductive step passes from `R` to `R/xR`.

At `k = 0` the demand is `depth_{I(φ 0)}(R) ≥ 1`, which is exactly the existence of a
nonzerodivisor in `I(φ 0)`, and prime avoidance over the finitely many associated primes supplies
one as soon as `I(φ 0)` lies in none of them (`detIdeal_not_le_of_exact`,
`one_le_depth_of_forall_not_le_associatedPrimes`). That is the whole of the base case `e = 0`.

For `k = j + 1` the ideals `I(φ 0), …, I(φ (e+1))` all avoid every associated prime, hence so does
their intersection (`iInf_not_le_of_forall_not_le`), and prime avoidance
(`exists_mem_nonZeroDivisors_of_forall_not_le`) produces a nonzerodivisor `x` lying in every one of
them. The complex modulo `x` is exact one spot less far down (`tag_00MZ`), so the complex
`φ (· + 1)` reduced modulo `x` satisfies the hypotheses of the induction over `R/xR` with `e` in
place of `e + 1`, and the induction hypothesis at `j` gives a regular sequence of length
`j + 1 = k` in `I(φ k)/xR` (`exists_length_ge_of_le_depth`); prepending `x` to it
(`succ_le_depth_of_isRegular_quotient`) is the bound `k + 1 ≤ depth_{I(φ k)}(R)`.

The differentials above degree `e + 1` are replaced by zero, so that the family is a complex in
every degree, as `tag_00MZ` requires. The identification `I(φ k)/xR = I(φ k mod x)` needs the rank
not to drop modulo `x` (`minorIdeal_map_of_rank_map_eq`); it does not, because both ranks are
computed by `rank_eq_of_exact` to be the same alternating sum, the shift of the complex being
matched by the shift of the truncation degree. -/
private lemma le_depth_detIdeal_of_exact_aux :
    ∀ (e : ℕ) {T : Type*} [CommRing T] [IsNoetherianRing T] [IsLocalRing T] (n : ℕ → ℕ)
      (φ : ∀ i, (Fin (n (i + 1)) → T) →ₗ[T] (Fin (n i) → T)),
      (∀ k < e, φ k ∘ₗ φ (k + 1) = 0) → Function.Injective (φ e) →
      (∀ k < e, Function.Exact (φ (k + 1)) (φ k)) →
      ∀ k ≤ e, ((k + 1 : ℕ) : ℕ∞)
        ≤ Module.depth T (detIdeal (LinearMap.toMatrix' (φ k))) T := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro T _ _ _ n φ hφ hinj hex k hk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simpa using one_le_depth_of_forall_not_le_associatedPrimes
        (detIdeal_not_le_of_exact e n φ hφ hinj hex 0 hk)
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨e, rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    have hje : j ≤ e := by omega
    have hAmul : ∀ i < e + 1,
        LinearMap.toMatrix' (φ i) * LinearMap.toMatrix' (φ (i + 1)) = 0 := by
      intro i hi
      rw [← LinearMap.toMatrix'_comp, hφ i hi]
      simp
    have hmv : ∀ i, (LinearMap.toMatrix' (φ i)).mulVecLin = φ i :=
      fun i => Matrix.toLin'_toMatrix' (φ i)
    have hAex : ∀ i < e + 1, LinearMap.ker (LinearMap.toMatrix' (φ i)).mulVecLin
        = LinearMap.range (LinearMap.toMatrix' (φ (i + 1))).mulVecLin := by
      intro i hi
      rw [hmv i, hmv (i + 1), ← LinearMap.exact_iff]
      exact hex i hi
    by_cases hItop : detIdeal (LinearMap.toMatrix' (φ (j + 1))) = ⊤
    · rw [hItop, depth_top]
      exact le_top
    obtain ⟨x, hxJ, hx⟩ := exists_mem_nonZeroDivisors_of_forall_not_le
      (I := ⨅ i : Fin (e + 2), detIdeal (LinearMap.toMatrix' (φ (i : ℕ))))
      (fun q hq => by
        have := hq.isPrime
        exact iInf_not_le_of_forall_not_le _ q fun i =>
          detIdeal_not_le_of_exact (e + 1) n φ hφ hinj hex (i : ℕ) i.is_le q hq)
    have hxI : ∀ i ≤ e + 1, x ∈ detIdeal (LinearMap.toMatrix' (φ i)) := fun i hi =>
      (Submodule.mem_iInf _).mp hxJ ⟨i, by omega⟩
    have hxnzd : ∀ r : T, x * r = 0 → r = 0 := fun _ hr =>
      (mul_left_mem_nonZeroDivisors_eq_zero_iff hx).mp hr
    obtain ⟨A, hAle, hAgt⟩ :
        ∃ A : ∀ i, Matrix (Fin (n i)) (Fin (n (i + 1))) T,
          (∀ i ≤ e + 1, A i = LinearMap.toMatrix' (φ i)) ∧ (∀ i, e + 1 < i → A i = 0) :=
      ⟨fun i => if i ≤ e + 1 then LinearMap.toMatrix' (φ i) else 0,
        fun i hi => by simp [hi], fun i hi => by simp [Nat.not_le.mpr hi]⟩
    have hAcomplex : IsMatrixComplex n A := by
      intro i
      by_cases hi : i ≤ e
      · rw [hAle i (by omega), hAle (i + 1) (by omega)]
        exact hAmul i (by omega)
      · rw [hAgt (i + 1) (by omega)]
        simp
    have hAexact : ∀ i, i < e + 2 → ExactAtSucc n A i := by
      intro i hi
      change LinearMap.ker (A i).mulVecLin = LinearMap.range (A (i + 1)).mulVecLin
      rcases Nat.lt_or_ge i (e + 1) with h | h
      · rw [hAle i (by omega), hAle (i + 1) (by omega)]
        exact hAex i h
      · obtain rfl : i = e + 1 := by omega
        rw [hAle (e + 1) le_rfl, hAgt (e + 1 + 1) (by omega), Matrix.mulVecLin_zero,
          LinearMap.range_zero, LinearMap.ker_eq_bot, hmv (e + 1)]
        exact hinj
    have h00MZ := tag_00MZ T (e + 2) n A hAcomplex x hxnzd hAexact
    have hred : ∀ i ≤ e + 1, reduceMat x n A i
        = (LinearMap.toMatrix' (φ i)).map (Ideal.Quotient.mk (Ideal.span {x})) := by
      intro i hi
      change (A i).map (Ideal.Quotient.mk (Ideal.span {x})) = _
      rw [hAle i hi]
    have hred0 : ∀ i, e + 1 < i → reduceMat x n A i = 0 := by
      intro i hi
      change (A i).map (Ideal.Quotient.mk (Ideal.span {x})) = 0
      rw [hAgt i hi]
      simp
    have hspanle : Ideal.span {x} ≤ detIdeal (LinearMap.toMatrix' (φ (j + 1))) :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (hxI (j + 1) hk))
    have hspan : Ideal.span {x} ≠ (⊤ : Ideal T) := fun htop =>
      hItop (top_le_iff.mp (htop ▸ hspanle))
    have : Nontrivial (T ⧸ Ideal.span {x}) := Submodule.Quotient.nontrivial_iff.mpr hspan
    have : IsLocalRing (T ⧸ Ideal.span {x}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
    obtain ⟨ψ, hψ, hψm⟩ :
        ∃ ψ : ∀ i, (Fin (n (i + 1 + 1)) → T ⧸ Ideal.span {x}) →ₗ[T ⧸ Ideal.span {x}]
            (Fin (n (i + 1)) → T ⧸ Ideal.span {x}),
          (∀ i, ψ i = ((LinearMap.toMatrix' (φ (i + 1))).map
              (Ideal.Quotient.mk (Ideal.span {x}))).mulVecLin) ∧
            ∀ i, LinearMap.toMatrix' (ψ i)
              = (LinearMap.toMatrix' (φ (i + 1))).map (Ideal.Quotient.mk (Ideal.span {x})) :=
      ⟨fun i => ((LinearMap.toMatrix' (φ (i + 1))).map
          (Ideal.Quotient.mk (Ideal.span {x}))).mulVecLin,
        fun _ => rfl, fun _ => LinearMap.toMatrix'_toLin' _⟩
    have hψφ : ∀ jj < e, ψ jj ∘ₗ ψ (jj + 1) = 0 := by
      intro jj hjj
      rw [hψ jj, hψ (jj + 1), ← Matrix.mulVecLin_mul, ← Matrix.map_mul,
        hAmul (jj + 1) (by omega)]
      simp
    have hψinj : Function.Injective (ψ e) := by
      have h : LinearMap.ker (reduceMat x n A (e + 1)).mulVecLin
          = LinearMap.range (reduceMat x n A (e + 1 + 1)).mulVecLin :=
        h00MZ (e + 1) (by omega) (by omega)
      rw [hred (e + 1) le_rfl, hred0 (e + 1 + 1) (by omega)] at h
      rw [hψ e, ← LinearMap.ker_eq_bot, h]
      simp
    have hψex : ∀ jj < e, Function.Exact (ψ (jj + 1)) (ψ jj) := by
      intro jj hjj
      have h : LinearMap.ker (reduceMat x n A (jj + 1)).mulVecLin
          = LinearMap.range (reduceMat x n A (jj + 1 + 1)).mulVecLin :=
        h00MZ (jj + 1) (by omega) (by omega)
      rw [hred (jj + 1) (by omega), hred (jj + 1 + 1) (by omega)] at h
      rw [LinearMap.exact_iff, hψ jj, hψ (jj + 1)]
      exact h
    have hrankR := rank_eq_of_exact (e + 1) n φ hφ hinj hex (j + 1) hk
    have hrankS := rank_eq_of_exact e (fun i => n (i + 1)) ψ hψφ hψinj hψex j hje
    have hsum : (∑ t ∈ Finset.range (e + 1 - j), (-1 : ℤ) ^ t * (n (j + 1 + t + 1) : ℤ))
        = ∑ t ∈ Finset.range (e + 1 + 1 - (j + 1)), (-1 : ℤ) ^ t * (n (j + 1 + 1 + t) : ℤ) := by
      rw [show e + 1 + 1 - (j + 1) = e + 1 - j from by omega]
      exact Finset.sum_congr rfl fun t _ => by
        rw [show j + 1 + t + 1 = j + 1 + 1 + t from by omega]
    have hrkZ : (exteriorRank (LinearMap.toMatrix' (ψ j)) : ℤ)
        = (exteriorRank (LinearMap.toMatrix' (φ (j + 1))) : ℤ) := by
      rw [hrankS, hrankR]
      exact hsum
    have hrk : StacksComplex.rank ((LinearMap.toMatrix' (φ (j + 1))).map
          (Ideal.Quotient.mk (Ideal.span {x})))
        = StacksComplex.rank (LinearMap.toMatrix' (φ (j + 1))) := by
      rw [← hψm j, ← exteriorRank_eq_rank, ← exteriorRank_eq_rank]
      exact_mod_cast hrkZ
    have hIeq : detIdeal (LinearMap.toMatrix' (ψ j))
        = (detIdeal (LinearMap.toMatrix' (φ (j + 1)))).map
            (Ideal.Quotient.mk (Ideal.span {x})) := by
      rw [detIdeal_eq_minorIdeal, detIdeal_eq_minorIdeal, hψm j,
        minorIdeal_map_of_rank_map_eq _ _ hrk]
    have hdepthS := ih e (Nat.lt_succ_self e) (fun i => n (i + 1)) ψ hψφ hψinj hψex j hje
    rw [hIeq] at hdepthS
    have hne : ((detIdeal (LinearMap.toMatrix' (φ (j + 1)))).map
          (Ideal.Quotient.mk (Ideal.span {x})))
        • (⊤ : Submodule (T ⧸ Ideal.span {x}) (T ⧸ Ideal.span {x})) ≠ ⊤ := by
      rw [Ideal.smul_top_eq_self]
      exact map_mk_ne_top (hxI (j + 1) hk) hItop
    obtain ⟨rs, hrsI, hrs, hlen⟩ := exists_length_ge_of_le_depth hne (c := j + 1) hdepthS
    calc ((j + 1 + 1 : ℕ) : ℕ∞) ≤ ((rs.length + 1 : ℕ) : ℕ∞) := by
          exact_mod_cast Nat.succ_le_succ hlen
      _ ≤ Module.depth T (detIdeal (LinearMap.toMatrix' (φ (j + 1)))) T :=
          succ_le_depth_of_isRegular_quotient (hxI (j + 1) hk) hx hItop hrsI hrs

/-- **Condition (2)(b) from exactness.** Over a local Noetherian ring, exactness of the complex
at `R^{n_{e+1}}, …, R^{n_1}` forces `depth_{I(φ k)}(R) ≥ k + 1` for every `k ≤ e`. -/
lemma le_depth_detIdeal_of_exact (e : ℕ) (n : ℕ → ℕ)
    (φ : ∀ i, (Fin (n (i + 1)) → R) →ₗ[R] (Fin (n i) → R))
    (hφ : ∀ k < e, φ k ∘ₗ φ (k + 1) = 0)
    (hinj : Function.Injective (φ e))
    (hex : ∀ k < e, Function.Exact (φ (k + 1)) (φ k)) :
    ∀ k ≤ e, ((k + 1 : ℕ) : ℕ∞)
      ≤ Module.depth R (detIdeal (LinearMap.toMatrix' (φ k))) R :=
  le_depth_detIdeal_of_exact_aux e n φ hφ hinj hex

omit [IsNoetherianRing R] in
/-- **Condition (2)(b) bounds the depth of `R`.** If `I(φ e)` lies in the maximal ideal, then
`depth_{I(φ e)}(R) ≥ e + 1` gives `depth R ≥ e + 1`. -/
private lemma le_depth_maximalIdeal_of_numerical (e : ℕ) (n : ℕ → ℕ)
    (φ : ∀ i, (Fin (n (i + 1)) → R) →ₗ[R] (Fin (n i) → R))
    (hle : detIdeal (LinearMap.toMatrix' (φ e)) ≤ IsLocalRing.maximalIdeal R)
    (hnum : Numerical e n φ e) :
    ((e + 1 : ℕ) : ℕ∞) ≤ Module.depth R (IsLocalRing.maximalIdeal R) R :=
  hnum.2.trans (depth_mono_ideal hle R)

/-! ### Ingredients of the converse direction -/

omit [IsLocalRing R] in
/-- **A finite free module has depth at least that of the ring**, from the depth inequality for
the split sequence `0 → R → R × R^m → R^m → 0`. -/
@[ega "0 16.4.5" "prof(A) ≤ prof(A^k)"]
private lemma depth_le_depth_pi_fin (I : Ideal R) (m : ℕ) :
    Module.depth R I R ≤ Module.depth R I (Fin m → R) := by
  induction m with
  | zero =>
    have : Subsingleton (Fin 0 → R) := ⟨fun a b => funext fun i => i.elim0⟩
    exact le_top.trans (Module.depth_eq_top_of_subsingleton I).ge
  | succ m ih =>
    rw [← Module.depth_eq_depth_of_linearEquiv I (Fin.consLinearEquiv R (fun _ : Fin (m + 1) => R))]
    refine (le_min le_rfl ih).trans ?_
    exact (Module.min_depth_le_depth_of_exact I
      (f := (LinearMap.inl R R (Fin m → R))) (g := LinearMap.snd R R (Fin m → R))
      Function.Exact.inl_snd (fun a b h => by simpa using congrArg Prod.fst h)
      (fun y => ⟨(0, y), rfl⟩)).1

omit [IsNoetherianRing R] [IsLocalRing R] in
/-- **Condition (2)(b) is inherited by localizations.** If `I ⊆ 𝔭` then a regular sequence in `I`
stays a regular sequence in `I R_𝔭`, localization being flat and the sequence staying inside the
maximal ideal; and if `I ⊄ 𝔭` then `I R_𝔭` is the unit ideal, whose depth is `∞`. -/
private lemma le_depth_map_algebraMap_atPrime (I : Ideal R) (p : Ideal R) [p.IsPrime] {c : ℕ}
    (hc : (c : ℕ∞) ≤ Module.depth R I R) :
    (c : ℕ∞) ≤ Module.depth (Localization.AtPrime p)
      (I.map (algebraMap R (Localization.AtPrime p))) (Localization.AtPrime p) := by
  by_cases hIp : I ≤ p
  · have hIne : I ≠ ⊤ := fun h => (‹p.IsPrime›).ne_top (top_le_iff.mp (h ▸ hIp))
    have hsm : I • (⊤ : Submodule R R) ≠ ⊤ := by rw [Ideal.smul_top_eq_self]; exact hIne
    obtain ⟨rs, hrsI, hrs, hlen⟩ := exists_length_ge_of_le_depth hsm hc
    have hreg : IsRegular (Localization.AtPrime p)
        (rs.map (algebraMap R (Localization.AtPrime p))) :=
      hrs.toIsWeaklyRegular.isRegular_of_isLocalization_of_mem _ p fun r hr => hIp (hrsI r hr)
    refine le_trans (Nat.cast_le.mpr ?_)
      (Module.le_depth_of_isRegular (I := I.map (algebraMap R (Localization.AtPrime p))) ?_ hreg)
    · simpa using hlen
    · intro r hr
      obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
      exact Ideal.mem_map_of_mem _ (hrsI r' hr')
  · obtain ⟨x, hxI, hxp⟩ := IsConcreteLE.not_le_iff_exists.mp hIp
    have htop : I.map (algebraMap R (Localization.AtPrime p)) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hxI)
        (IsLocalization.map_units (Localization.AtPrime p) ⟨x, hxp⟩ (M := p.primeCompl))
    rw [htop, depth_top]
    exact le_top

omit [IsNoetherianRing R] [IsLocalRing R] in
/-- Condition (2)(b) at `i = 1`, read as the existence of a nonzerodivisor in `I`: the unit-ideal
branch supplies `1`, which is a nonzerodivisor. -/
private lemma exists_nonZeroDivisor_mem_of_one_le_depth {I : Ideal R}
    (h : 1 ≤ Module.depth R I R) : ∃ x ∈ nonZeroDivisors R, x ∈ I := by
  rcases (one_le_depth_self_iff I).mp h with rfl | ⟨x, hx, hxI⟩
  · exact ⟨1, one_mem _, Submodule.mem_top⟩
  · exact ⟨x, hx, hxI⟩

/-- The numerical conditions (2)(a) and (2)(b) at the `k`-th matrix of a complex of finite free
modules: `Numerical` read on the matrices of the differentials. -/
def NumericalMat (E : ℕ) (n : ℕ → ℕ)
    (A : ∀ i, Matrix (Fin (n i)) (Fin (n (i + 1))) R) (k : ℕ) : Prop :=
  ((exteriorRank (A k) : ℤ)
      = ∑ t ∈ Finset.range (E + 1 - k), (-1) ^ t * (n (k + 1 + t) : ℤ)) ∧
    ((k + 1 : ℕ) : ℕ∞) ≤ Module.depth R (detIdeal (A k)) R

omit [IsNoetherianRing R] [IsLocalRing R] in
/-- The two spellings of the numerical conditions agree by definition. -/
lemma numerical_iff_numericalMat (e : ℕ) (n : ℕ → ℕ)
    (φ : ∀ i, (Fin (n (i + 1)) → R) →ₗ[R] (Fin (n i) → R)) (k : ℕ) :
    Numerical e n φ k ↔ NumericalMat e n (fun i => LinearMap.toMatrix' (φ i)) k := Iff.rfl

omit [IsNoetherianRing R] in
/-- **The numerical conditions are inherited by every localization.** Condition (2)(b) at `k`
gives a nonzerodivisor in `I(φ k)`, which survives in `R_𝔭`; so the rank of `φ k` does not drop
there (2)(a) and `I(φ k) R_𝔭 = I(φ_{k,𝔭})`, whose depth is at least `k + 1` because a regular
sequence in `I(φ k)` localizes. -/
lemma numericalMat_map_atPrime (E : ℕ) (n : ℕ → ℕ)
    (A : ∀ i, Matrix (Fin (n i)) (Fin (n (i + 1))) R) (p : Ideal R) [p.IsPrime]
    (hnum : ∀ k ≤ E, NumericalMat E n A k) :
    ∀ k ≤ E,
      NumericalMat E n (fun i => (A i).map (algebraMap R (Localization.AtPrime p))) k := by
  intro k hk
  obtain ⟨hrk, hdep⟩ := hnum k hk
  have hone : (1 : ℕ∞) ≤ Module.depth R (detIdeal (A k)) R :=
    le_trans (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)) hdep
  obtain ⟨x, hx, hxI⟩ := exists_nonZeroDivisor_mem_of_one_le_depth hone
  have hxmin : x ∈ StacksComplex.minorIdeal (A k) := by rwa [← detIdeal_eq_minorIdeal]
  refine ⟨?_, ?_⟩
  · change ((exteriorRank ((A k).map (algebraMap R (Localization.AtPrime p))) : ℤ)) = _
    rw [exteriorRank_eq_rank, rank_map_algebraMap_atPrime_eq p _ hx hxmin,
      ← exteriorRank_eq_rank]
    exact hrk
  · change ((k + 1 : ℕ) : ℕ∞) ≤ Module.depth (Localization.AtPrime p)
      (detIdeal ((A k).map (algebraMap R (Localization.AtPrime p)))) _
    rw [detIdeal_eq_minorIdeal, minorIdeal_map_algebraMap_atPrime p _ hx hxmin,
      ← detIdeal_eq_minorIdeal]
    exact le_depth_map_algebraMap_atPrime _ p hdep

/-- **A nonzero finite module supported at the maximal ideal has depth `0`.** If every element of
`M` is killed by something outside every non-maximal prime, then the associated prime supplied by
`M ≠ 0` can only be `𝔪`, so `𝔪` annihilates a nonzero element and no element of `𝔪` acts
regularly on `M`. -/
@[ega "0 16.4.6" "(iii), special case"]
private lemma not_one_le_depth_of_forall_exists_smul_eq_zero
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (hsupp : ∀ (q : Ideal R) [q.IsPrime], q ≠ IsLocalRing.maximalIdeal R →
      ∀ y : M, ∃ s ∈ q.primeCompl, s • y = 0) :
    ¬ (1 : ℕ∞) ≤ Module.depth R (IsLocalRing.maximalIdeal R) M := by
  intro hdepth
  obtain ⟨rs, hrsI, hrs, hlen⟩ := exists_length_ge_of_le_depth
    (Module.maximalIdeal_smul_top_ne_top M) hdepth
  obtain ⟨x, rest, rfl⟩ : ∃ x rest, rs = x :: rest := by
    cases rs with
    | nil => simp at hlen
    | cons x rest => exact ⟨x, rest, rfl⟩
  have hxreg : IsSMulRegular M x := ((isRegular_cons_iff M x rest).mp hrs).1
  have hxm : x ∈ IsLocalRing.maximalIdeal R := hrsI x (by simp)
  obtain ⟨q, hq⟩ := associatedPrimes.nonempty R M
  obtain ⟨hqp, y, hy⟩ := Submodule.isAssociatedPrime_iff.mp hq
  have hmemq : ∀ r : R, r ∈ q ↔ r • y = 0 := by
    intro r
    rw [hy, Submodule.mem_colon_singleton, Submodule.mem_bot]
  have hyne : y ≠ 0 := fun h0 =>
    hqp.ne_top ((Ideal.eq_top_iff_one q).mpr ((hmemq 1).mpr (by simp [h0])))
  have hqm : q = IsLocalRing.maximalIdeal R := by
    by_contra hne
    obtain ⟨s, hs, hsy⟩ := hsupp q hne y
    exact hs ((hmemq s).mpr hsy)
  have hxy : x • y = x • (0 : M) := by
    rw [smul_zero]
    exact (hmemq x).mp (hqm ▸ hxm)
  exact hyne (hxreg hxy)

/-- **The homology of a complex is of depth `0` where the complex fails to be exact**, provided
the failure is invisible at every non-maximal prime: the quotient `Ker(g₁)/Im(g₂)` is then a
nonzero finite module all of whose elements are killed outside every non-maximal prime. -/
private lemma not_one_le_depth_quotient_ker_range
    {M₀ M₁ M₂ : Type*} [AddCommGroup M₀] [Module R M₀] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [Module.Finite R M₁]
    (g₁ : M₁ →ₗ[R] M₀) (g₂ : M₂ →ₗ[R] M₁) (hg : ∀ v, g₂ v ∈ LinearMap.ker g₁)
    (hne : LinearMap.ker g₁ ≠ LinearMap.range g₂)
    (hsupp : ∀ (q : Ideal R) [q.IsPrime], q ≠ IsLocalRing.maximalIdeal R →
      ∀ y ∈ LinearMap.ker g₁, ∃ s ∈ q.primeCompl, s • y ∈ LinearMap.range g₂) :
    ¬ (1 : ℕ∞) ≤ Module.depth R (IsLocalRing.maximalIdeal R)
      (LinearMap.ker g₁ ⧸ LinearMap.range (g₂.codRestrict (LinearMap.ker g₁) hg)) := by
  have hQ : LinearMap.range (g₂.codRestrict (LinearMap.ker g₁) hg)
      = Submodule.comap (LinearMap.ker g₁).subtype (LinearMap.range g₂) :=
    LinearMap.range_codRestrict _ _ _
  have hmemQ : ∀ z : LinearMap.ker g₁,
      z ∈ LinearMap.range (g₂.codRestrict (LinearMap.ker g₁) hg) ↔
        (z : M₁) ∈ LinearMap.range g₂ := by
    intro z; rw [hQ]; exact Submodule.mem_comap
  have : Nontrivial (LinearMap.ker g₁ ⧸
      LinearMap.range (g₂.codRestrict (LinearMap.ker g₁) hg)) := by
    refine Submodule.Quotient.nontrivial_iff.mpr fun htop => ?_
    refine hne (le_antisymm (fun z hz => ?_) (fun z hz => ?_))
    · exact (hmemQ ⟨z, hz⟩).mp (htop ▸ Submodule.mem_top)
    · obtain ⟨v, rfl⟩ := hz
      exact hg v
  refine not_one_le_depth_of_forall_exists_smul_eq_zero _ ?_
  intro q _ hqm y
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨s, hs, hsz⟩ := hsupp q hqm (z : M₁) z.2
  refine ⟨s, hs, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact (hmemQ (s • z)).mpr hsz

open CategoryTheory CategoryTheory.Limits in
/-- **The acyclicity step of the converse direction.** Let `R` be a local Noetherian ring of depth
at least `E + 1` and let `A` be a complex of finite free modules vanishing above degree `E + 1`.
If the complex localized at every non-maximal prime is exact, then the complex itself is exact at
the spots `1, …, E + 1`.

The set of degrees at which the complex fails to be exact is contained in `{0, …, E + 1}`, the
terms above `E + 1` being zero, so if the complex fails to be exact at a positive degree it has a
greatest such degree `i`, and the acyclicity lemma says the homology there has depth
at least `1`. But the failure at `i` is invisible after localizing at any non-maximal prime, so
that homology is a nonzero finite module supported at the maximal ideal, of depth `0`. -/
lemma ker_eq_range_of_forall_atPrime (E : ℕ) (n : ℕ → ℕ)
    (A : ∀ i, Matrix (Fin (n i)) (Fin (n (i + 1))) R)
    (htop : ∀ i, E + 1 < i → n i = 0)
    (hA : ∀ i, A i * A (i + 1) = 0)
    (hdep : ((E + 1 : ℕ) : ℕ∞) ≤ Module.depth R (IsLocalRing.maximalIdeal R) R)
    (hloc : ∀ (q : Ideal R) [q.IsPrime], q ≠ IsLocalRing.maximalIdeal R →
      ∀ k ≤ E, LinearMap.ker ((A k).map (algebraMap R (Localization.AtPrime q))).mulVecLin
        = LinearMap.range ((A (k + 1)).map (algebraMap R (Localization.AtPrime q))).mulVecLin) :
    ∀ k ≤ E, LinearMap.ker (A k).mulVecLin = LinearMap.range (A (k + 1)).mulVecLin := by
  classical
  have hcomp : ∀ j : ℕ, (A j).mulVecLin ∘ₗ (A (j + 1)).mulVecLin = 0 := by
    intro j
    rw [← Matrix.mulVecLin_mul, hA j, Matrix.mulVecLin_zero]
  set X : ℕ → ModuleCat R := fun j => ModuleCat.of R (Fin (n j) → R) with hXdef
  set d : ∀ j : ℕ, X (j + 1) ⟶ X j := fun j => ModuleCat.ofHom (A j).mulVecLin with hddef
  have hsq : ∀ j : ℕ, d (j + 1) ≫ d j = 0 := by
    intro j
    rw [hddef]
    apply ModuleCat.hom_ext
    simpa using hcomp j
  set C := ChainComplex.of X d hsq with hCdef
  have hCd : ∀ j : ℕ, C.d (j + 1) j = d j := fun j => ChainComplex.of_d X d j
  have : ∀ j, Module.Finite R (C.X j) := fun j =>
    inferInstanceAs (Module.Finite R (Fin (n j) → R))
  have hzero : ∀ j : ℕ, E + 1 < j → IsZero (C.X j) := by
    intro j hj
    refine ModuleCat.isZero_iff_subsingleton.mpr ?_
    have hn0 : n j = 0 := htop j hj
    exact show Subsingleton (Fin (n j) → R) from
      ⟨fun a b => funext fun i => absurd i.isLt (by omega)⟩
  have hexactAt : ∀ k : ℕ, C.ExactAt (k + 1) ↔
      LinearMap.ker (A k).mulVecLin = LinearMap.range (A (k + 1)).mulVecLin := by
    intro k
    rw [C.exactAt_iff' (k + 2) (k + 1) k (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff_range_eq_ker]
    change LinearMap.range (C.d (k + 1 + 1) (k + 1)).hom = LinearMap.ker (C.d (k + 1) k).hom ↔ _
    rw [hCd (k + 1), hCd k, hddef]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  intro k hk
  rw [← hexactAt k]
  by_contra hne
  obtain ⟨i, hiE, hiP, hile⟩ :
      ∃ i, i ≤ E + 1 ∧ ¬ C.ExactAt i ∧ ∀ j, ¬ C.ExactAt j → j ≤ i := by
    refine ⟨Nat.findGreatest (fun j => ¬ C.ExactAt j) (E + 1), Nat.findGreatest_le _,
      Nat.findGreatest_spec (P := fun j => ¬ C.ExactAt j) (m := k + 1) (n := E + 1)
        (by omega) hne, fun j hj => ?_⟩
    by_cases hjE : j ≤ E + 1
    · exact Nat.le_findGreatest hjE hj
    · exact absurd (HomologicalComplex.ExactAt.of_isZero (hzero j (by omega))) hj
  have hik : k + 1 ≤ i := hile (k + 1) hne
  have hgreatest : IsGreatest {j : ℕ | ¬ C.ExactAt j} i := ⟨hiP, fun j hj => hile j hj⟩
  have hdepthX : ∀ j ≤ E + 1, (j : ℕ∞) ≤
      Module.depth R (IsLocalRing.maximalIdeal R) (C.X j) := by
    intro j hj
    refine le_trans ?_ (depth_le_depth_pi_fin (IsLocalRing.maximalIdeal R) (n j))
    exact le_trans (by exact_mod_cast hj) hdep
  have hhom := Module.one_le_depth_homology_of_forall_le_depth_of_isGreatest_not_exactAt
    C (E + 1) hzero hdepthX hgreatest (by omega)
  obtain ⟨t, rfl⟩ : ∃ t, i = t + 1 := ⟨i - 1, by omega⟩
  have hdmem : ∀ v : C.X (t + 2), (C.d (t + 2) (t + 1)).hom v
      ∈ LinearMap.ker (C.d (t + 1) t).hom := by
    intro v
    have h := ModuleCat.hom_ext_iff.1 (C.d_comp_d (t + 2) (t + 1) t)
    exact congrFun (congrArg DFunLike.coe h) v
  have heq : C.homology (t + 1) ≃ₗ[R]
      (LinearMap.ker (C.d (t + 1) t).hom ⧸
        LinearMap.range ((C.d (t + 2) (t + 1)).hom.codRestrict
          (LinearMap.ker (C.d (t + 1) t).hom) hdmem)) :=
    ((C.homologyIsoSc' (t + 2) (t + 1) t (by simp) (by simp)).trans
      (C.sc' (t + 2) (t + 1) t).moduleCatHomologyIso).toLinearEquiv
  rw [Module.depth_eq_depth_of_linearEquiv _ heq] at hhom
  have hdA : ∀ j : ℕ, (C.d (j + 1) j).hom = (A j).mulVecLin := by
    intro j
    rw [hCd j, hddef]
    rfl
  refine not_one_le_depth_quotient_ker_range (C.d (t + 1) t).hom (C.d (t + 2) (t + 1)).hom
    hdmem ?_ ?_ hhom
  · rw [hdA t, show (C.d (t + 1 + 1) (t + 1)).hom = (A (t + 1)).mulVecLin from hdA (t + 1)]
    exact fun h => hiP ((hexactAt t).mpr h)
  · intro q _ hqm y hy
    rw [hdA t] at hy
    rw [show (C.d (t + 1 + 1) (t + 1)).hom = (A (t + 1)).mulVecLin from hdA (t + 1)]
    exact exists_smul_mem_range_of_ker_eq_range_map q (A t) (A (t + 1))
      (hloc q hqm t (by omega)) hy

end Criterion

end Stacks.Depth.BuchsbaumEisenbud

end

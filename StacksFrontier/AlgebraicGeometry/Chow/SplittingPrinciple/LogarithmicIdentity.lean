module

public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.RingTheory.PowerSeries.Log
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.PowerSumPolynomials
public import StacksCore.Tactic.StacksAttribute

/-!
# The logarithmic identity for power-sum polynomials

The logarithm of the universal total Chern class is the signed generating series of the
universal power-sum polynomials. This identity is what lets the splitting principle be applied
one power sum at a time.

## Main definitions

* `AlgebraicGeometry.universalChernClassSum` is the series `c₁ + c₂ + ⋯`.
* `AlgebraicGeometry.powerSumSeries` is the series whose weight-`p` part is `(-1)ᵖ⁻¹ Pₚ / p`.

## Main results

* `AlgebraicGeometry.log_one_add_universalChernClassSum` is the universal logarithmic
  identity.

## Implementation notes

The completed graded ring `ℚ[c₁, c₂, …]^∧`, with `cᵢ` of weight `i`, is represented by
`MvPowerSeries ℕ+ ℚ`. Since every weight is positive, each fixed weighted degree involves only
finitely many monomials. The formal logarithm is obtained by substituting `c₁ + c₂ + ⋯` into
Mathlib's univariate series `PowerSeries.log`.

The proof runs through a derivation `eulerDegree` of the completed ring, which multiplies the
coefficient of each monomial by its weighted degree. Both sides of the identity have zero
constant term, and the derivation is injective on series with zero constant term, so it
suffices to compare the derivations; that comparison is Newton's recurrence.

## References

* [Stacks Project, Tag 0F9B](https://stacks.math.columbia.edu/tag/0F9B)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry

open MvPolynomial MvPowerSeries

/-- The weighted degree of a monomial exponent: each occurrence of the variable `cᵢ`
contributes `i`. -/
private def gradedWeight (d : ℕ+ →₀ ℕ) : ℕ :=
  d.sum fun i n => (i : ℕ) * n

/-- The weighted degree is additive in the monomial exponent. -/
private theorem gradedWeight_add (d e : ℕ+ →₀ ℕ) :
    gradedWeight (d + e) = gradedWeight d + gradedWeight e := by
  simp only [gradedWeight]
  exact Finsupp.sum_add_index' (fun _ => mul_zero _) fun _ _ _ => mul_add _ _ _

/-- The Euler operator of the weighted grading: it multiplies the coefficient of each
monomial by that monomial's weighted degree. -/
private def eulerDegree (f : MvPowerSeries ℕ+ ℚ) : MvPowerSeries ℕ+ ℚ :=
  fun d => (gradedWeight d : ℚ) * f d

/-- The coefficients of `eulerDegree f` in terms of those of `f`. -/
private theorem coeff_eulerDegree (f : MvPowerSeries ℕ+ ℚ) (d : ℕ+ →₀ ℕ) :
    MvPowerSeries.coeff d (eulerDegree f) = (gradedWeight d : ℚ) * MvPowerSeries.coeff d f := by
  simp only [MvPowerSeries.coeff_apply, eulerDegree]

/-- The Euler operator is a derivation. -/
private theorem eulerDegree_mul (f g : MvPowerSeries ℕ+ ℚ) :
    eulerDegree (f * g) = eulerDegree f * g + f * eulerDegree g := by
  classical
  ext d
  show (gradedWeight d : ℚ) * MvPowerSeries.coeff d (f * g) =
    MvPowerSeries.coeff d (eulerDegree f * g) +
      MvPowerSeries.coeff d (f * eulerDegree g)
  rw [MvPowerSeries.coeff_mul (n := d) f g,
    MvPowerSeries.coeff_mul (n := d) (eulerDegree f) g,
    MvPowerSeries.coeff_mul (n := d) f (eulerDegree g)]
  simp_rw [coeff_eulerDegree]
  show (gradedWeight d : ℚ) *
      (∑ x ∈ Finset.antidiagonal d,
        MvPowerSeries.coeff x.1 f * MvPowerSeries.coeff x.2 g) =
    (∑ x ∈ Finset.antidiagonal d,
      (gradedWeight x.1 : ℚ) * MvPowerSeries.coeff x.1 f * MvPowerSeries.coeff x.2 g) +
    ∑ x ∈ Finset.antidiagonal d,
      MvPowerSeries.coeff x.1 f * ((gradedWeight x.2 : ℚ) * MvPowerSeries.coeff x.2 g)
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [← Finset.mem_antidiagonal.mp hx, gradedWeight_add]
  push_cast
  ring

/-- The Euler operator annihilates the unit, which has only a weight-zero monomial. -/
private theorem eulerDegree_one : eulerDegree (1 : MvPowerSeries ℕ+ ℚ) = 0 := by
  ext d
  show (gradedWeight d : ℚ) * MvPowerSeries.coeff d (1 : MvPowerSeries ℕ+ ℚ) = 0
  by_cases hd : d = 0
  · subst d
    simp [gradedWeight]
  · rw [MvPowerSeries.coeff_one]
    simp [hd]

/-- The Euler operator on a power, by the Leibniz rule. -/
private theorem eulerDegree_pow (f : MvPowerSeries ℕ+ ℚ) (n : ℕ) :
    eulerDegree (f ^ n) = (n : ℚ) • (f ^ (n - 1) * eulerDegree f) := by
  induction n with
  | zero => simpa using eulerDegree_one
  | succ n ih =>
      rw [pow_succ, eulerDegree_mul, ih, show n + 1 - 1 = n by omega]
      by_cases hn : n = 0
      · subst n
        simp
      · have hpow : f ^ (n - 1) * f = f ^ n := by
          rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)]
        rw [smul_mul_assoc, show (f ^ (n - 1) * eulerDegree f) * f =
          (f ^ (n - 1) * f) * eulerDegree f by ring, hpow]
        simp only [Nat.cast_succ, add_smul, one_smul]

/-- The positive-degree part `c₁ + c₂ + ⋯` of the universal total Chern class. -/
public def universalChernClassSum : MvPowerSeries ℕ+ ℚ := fun d =>
  if (d.sum fun _ n => n) = 1 then 1 else 0

/-- The signed power-sum series `∑_{p ≥ 1} (-1)^{p-1} Pₚ/p`. -/
public def powerSumSeries : MvPowerSeries ℕ+ ℚ := fun d =>
  ∑ᶠ p : ℕ+, MvPowerSeries.coeff d
    (((-1 : ℚ) ^ ((p : ℕ) - 1) / (p : ℚ)) •
      (((powerSumPolynomial (p : ℕ) :
        MvPolynomial ℕ+ ℤ).map (Int.castRingHom ℚ)).toMvPowerSeries))

/-- The total exponent of a monomial, disregarding the weights. -/
private def exponentMass (d : ℕ+ →₀ ℕ) : ℕ := d.sum fun _ n => n

/-- The total exponent is additive in the monomial exponent. -/
private theorem exponentMass_add (d e : ℕ+ →₀ ℕ) :
    exponentMass (d + e) = exponentMass d + exponentMass e := by
  simp only [exponentMass]
  exact Finsupp.sum_add_index' (fun _ => rfl) fun _ _ _ => rfl

/-- The universal total Chern class has zero constant term. -/
private theorem constantCoeff_universalChernClassSum :
    MvPowerSeries.constantCoeff universalChernClassSum = 0 := by
  show universalChernClassSum (0 : ℕ+ →₀ ℕ) = 0
  simp [universalChernClassSum]

/-- Substitution of the universal total Chern class into power series is well defined. -/
private theorem hasSubst_universalChernClassSum :
    PowerSeries.HasSubst universalChernClassSum :=
  PowerSeries.HasSubst.of_constantCoeff_zero constantCoeff_universalChernClassSum

/-- The coefficient of the universal total Chern class at a single variable is `1`. -/
private theorem coeff_universalChernClassSum_single (i : ℕ+) :
    MvPowerSeries.coeff (Finsupp.single i 1) universalChernClassSum = 1 := by
  show (if exponentMass (Finsupp.single i 1) = 1 then 1 else 0) = 1
  simp [exponentMass]

/-- A power of the universal total Chern class whose exponent exceeds the total exponent of a
monomial contributes nothing to that monomial. -/
private theorem coeff_universalChernClassSum_pow_zero (d : ℕ+ →₀ ℕ) (n : ℕ)
    (hn : exponentMass d < n) :
    MvPowerSeries.coeff d (universalChernClassSum ^ n) = 0 := by
  apply MvPowerSeries.coeff_eq_zero_of_constantCoeff_nilpotent
    (m := 1) (d := d) (n := n)
  · simpa using constantCoeff_universalChernClassSum
  · have hdeg : Finsupp.degree d = exponentMass d := by
      rw [Finsupp.degree_apply]
      symm
      exact Finsupp.sum_of_support_subset d (fun _ h => h) (fun _ n => n) fun _ _ => rfl
    rw [hdeg]
    omega

/-- Substituting the universal total Chern class into a univariate series computes any single
coefficient as a finite sum, because the high powers contribute nothing. -/
private theorem coeff_subst_eq_sum_range (f : PowerSeries ℚ) (d : ℕ+ →₀ ℕ)
    (N : ℕ) (hd : exponentMass d ≤ N) :
    MvPowerSeries.coeff d (PowerSeries.subst universalChernClassSum f) =
      ∑ n ∈ Finset.range (N + 1), PowerSeries.coeff n f *
        MvPowerSeries.coeff d (universalChernClassSum ^ n) := by
  classical
  rw [PowerSeries.coeff_subst hasSubst_universalChernClassSum f d,
    finsum_eq_sum_of_support_subset (s := Finset.range (N + 1))]
  · simp only [smul_eq_mul]
  · intro n hn
    by_contra hnr
    have hle : N + 1 ≤ n := by simpa using hnr
    simp [coeff_universalChernClassSum_pow_zero d n (by omega)] at hn

/-- The Euler operator applied to a power of the universal total Chern class, read off one
coefficient at a time. -/
private theorem coeff_eulerDegree_universalChernClassSum_pow (d : ℕ+ →₀ ℕ) (n : ℕ) :
    (gradedWeight d : ℚ) * MvPowerSeries.coeff d (universalChernClassSum ^ n) =
      (n : ℚ) * MvPowerSeries.coeff d
        (universalChernClassSum ^ (n - 1) * eulerDegree universalChernClassSum) := by
  simpa [coeff_eulerDegree, smul_eq_mul] using congrArg (MvPowerSeries.coeff d)
    (eulerDegree_pow universalChernClassSum n)

/-- A coefficient of a substituted series times the Euler operator of the universal total Chern
class, computed as a finite sum. -/
private theorem coeff_subst_mul_eulerDegree (f : PowerSeries ℚ) (d : ℕ+ →₀ ℕ) :
    MvPowerSeries.coeff d
        (PowerSeries.subst universalChernClassSum f * eulerDegree universalChernClassSum) =
      ∑ n ∈ Finset.range (exponentMass d + 1), PowerSeries.coeff n f *
        MvPowerSeries.coeff d
          (universalChernClassSum ^ n * eulerDegree universalChernClassSum) := by
  classical
  let N := exponentMass d
  have hfst {p : (ℕ+ →₀ ℕ) × (ℕ+ →₀ ℕ)} (hp : p ∈ Finset.antidiagonal d) :
      exponentMass p.1 ≤ N := by
    show exponentMass p.1 ≤ exponentMass d
    rw [← Finset.mem_antidiagonal.mp hp, exponentMass_add]
    omega
  have hright : MvPowerSeries.coeff d
        (PowerSeries.subst universalChernClassSum f * eulerDegree universalChernClassSum) =
      ∑ n ∈ Finset.range (N + 2), PowerSeries.coeff n f *
        MvPowerSeries.coeff d
          (universalChernClassSum ^ n * eulerDegree universalChernClassSum) := by
    rw [MvPowerSeries.coeff_mul]
    calc
      _ = ∑ p ∈ Finset.antidiagonal d,
            (∑ n ∈ Finset.range (N + 2),
              PowerSeries.coeff n f * MvPowerSeries.coeff p.1 (universalChernClassSum ^ n)) *
              ((gradedWeight p.2 : ℚ) * MvPowerSeries.coeff p.2 universalChernClassSum) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [coeff_subst_eq_sum_range _ p.1 (N + 1) ((hfst hp).trans (Nat.le_succ N)),
          coeff_eulerDegree]
      _ = _ := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [MvPowerSeries.coeff_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [coeff_eulerDegree]
        ring
  have htail : MvPowerSeries.coeff d
      (universalChernClassSum ^ (N + 1) * eulerDegree universalChernClassSum) = 0 := by
    rw [MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [coeff_universalChernClassSum_pow_zero p.1 (N + 1) (Nat.lt_succ_of_le (hfst hp)),
      zero_mul]
  rwa [Finset.sum_range_succ, htail, mul_zero, add_zero] at hright

/-- The chain rule for the Euler operator applied to the substituted logarithm. -/
private theorem eulerDegree_logSubst :
    eulerDegree (PowerSeries.subst universalChernClassSum (PowerSeries.log ℚ)) =
      PowerSeries.subst universalChernClassSum
          (PowerSeries.derivative ℚ (PowerSeries.log ℚ)) *
        eulerDegree universalChernClassSum := by
  classical
  ext d
  have hsum : (gradedWeight d : ℚ) * MvPowerSeries.coeff d
        (PowerSeries.subst universalChernClassSum (PowerSeries.log ℚ)) =
      ∑ n ∈ Finset.range (exponentMass d + 1),
        PowerSeries.coeff n (PowerSeries.derivative ℚ (PowerSeries.log ℚ)) *
          MvPowerSeries.coeff d
            (universalChernClassSum ^ n * eulerDegree universalChernClassSum) := by
    rw [coeff_subst_eq_sum_range (PowerSeries.log ℚ) d (exponentMass d + 1) (by omega),
      Finset.sum_range_succ', show PowerSeries.coeff 0 (PowerSeries.log ℚ) *
        MvPowerSeries.coeff d (universalChernClassSum ^ 0) = 0 by simp, add_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    have hp := coeff_eulerDegree_universalChernClassSum_pow d (n + 1)
    rw [show n + 1 - 1 = n by omega] at hp
    rw [PowerSeries.coeff_derivative, mul_left_comm, hp]
    push_cast
    ring
  rw [coeff_eulerDegree, hsum, coeff_subst_mul_eulerDegree]

/-- Truncating the universal total Chern class below a given monomial leaves exactly the sum
of the variables occurring in that monomial. -/
private theorem trunc_universalChernClassSum (d : ℕ+ →₀ ℕ) :
    MvPowerSeries.truncFinset ℚ (Finset.Iic d) universalChernClassSum =
      ∑ i ∈ d.support, (MvPolynomial.X i : MvPolynomial ℕ+ ℚ) := by
  classical
  refine MvPolynomial.ext _ _ fun e => ?_
  rw [MvPowerSeries.coeff_truncFinset]
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_X]
  by_cases hm : exponentMass e = 1
  · obtain ⟨i, rfl⟩ := (Finsupp.sum_eq_one_iff e).mp hm
    rw [coeff_universalChernClassSum_single]
    by_cases hi : i ∈ d.support
    · have hsum : (∑ x ∈ d.support,
          if Finsupp.single x 1 = Finsupp.single i 1 then (1 : ℚ) else 0) = 1 := by
        simp [Finsupp.single_eq_single_iff, hi]
      rw [hsum]
      simp [Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))]
    · have hnotle : ¬ Finsupp.single i 1 ≤ d := fun hle => hi (Finsupp.mem_support_iff.mpr
        (Nat.one_le_iff_ne_zero.mp (Finsupp.single_le_iff.1 hle)))
      have hsum : (∑ x ∈ d.support,
          if Finsupp.single x 1 = Finsupp.single i 1 then (1 : ℚ) else 0) = 0 := by
        simp [Finsupp.single_eq_single_iff, hi]
      rw [hsum]
      simp [hnotle]
  · have hneq (i : ℕ+) : Finsupp.single i 1 ≠ e := by
      rintro rfl
      apply hm
      simp [exponentMass]
    have hsum : (∑ i ∈ d.support, if Finsupp.single i 1 = e then (1 : ℚ) else 0) = 0 :=
      Finset.sum_eq_zero fun i _ => by simp [hneq i]
    have hc : MvPowerSeries.coeff e universalChernClassSum = 0 := by
      show (if exponentMass e = 1 then (1 : ℚ) else 0) = 0
      simp [hm]
    rw [hc, ite_self, hsum]

/-- Multiplying by the universal total Chern class shifts each coefficient down by one in a
single variable, summed over the variables of the monomial. -/
private theorem coeff_universalChernClassSum_mul (f : MvPowerSeries ℕ+ ℚ)
    (d : ℕ+ →₀ ℕ) :
    MvPowerSeries.coeff d (universalChernClassSum * f) =
      ∑ i ∈ d.support, MvPowerSeries.coeff (d - Finsupp.single i 1) f := by
  classical
  have hs : IsLowerSet (Finset.Iic d : Set (ℕ+ →₀ ℕ)) := fun _ _ hba ha =>
    Finset.mem_Iic.mpr (hba.trans (Finset.mem_Iic.mp ha))
  rw [← MvPowerSeries.coeff_truncFinset_mul_truncFinset_eq_coeff_mul hs
    universalChernClassSum f (Finset.mem_Iic.mpr le_rfl), trunc_universalChernClassSum,
    Finset.sum_mul, MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hred : d - Finsupp.single i 1 ∈ Finset.Iic d :=
    Finset.mem_Iic.mpr ((Finsupp.le_iff _ _).mpr fun _ _ => Nat.sub_le _ _)
  rw [MvPolynomial.coeff_X_mul']
  simp [hi, MvPowerSeries.coeff_truncFinset_of_mem, hred]

/-- The universal power-sum polynomial with its coefficients pushed into the rationals. -/
private noncomputable def powerSumPolynomialQ (p : ℕ) : MvPolynomial ℕ+ ℚ :=
  (powerSumPolynomial p : MvPolynomial ℕ+ ℤ).map
    (Int.castRingHom ℚ)

/-- Newton's recurrence for the rational power-sum polynomials. -/
private theorem powerSumPolynomialQ_succ (p : ℕ) :
    powerSumPolynomialQ (p + 1) =
      ∑ j ∈ Finset.range p,
        MvPolynomial.C ((-1 : ℚ) ^ j) * MvPolynomial.X (Nat.succPNat j) *
          powerSumPolynomialQ (p - j) +
        MvPolynomial.C ((-1 : ℚ) ^ p * (p + 1)) * MvPolynomial.X (Nat.succPNat p) := by
  simp [powerSumPolynomialQ, map_sum]

/-- Removing one occurrence of `cᵢ` from a monomial lowers its weighted degree by `i`. -/
private theorem gradedWeight_sub_single_eq (d : ℕ+ →₀ ℕ) (i : ℕ+)
    (hi : i ∈ d.support) :
    gradedWeight (d - Finsupp.single i 1) + (i : ℕ) = gradedWeight d := by
  have hweight := congrArg gradedWeight (add_tsub_cancel_of_le
    (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))))
  rw [gradedWeight_add] at hweight
  simpa [gradedWeight, Nat.add_comm] using hweight

/-- Every variable occurring in a monomial has weight at most the monomial's weighted
degree. -/
private theorem support_index_le_gradedWeight (d : ℕ+ →₀ ℕ) (i : ℕ+)
    (hi : i ∈ d.support) : (i : ℕ) ≤ gradedWeight d :=
  (Nat.le_add_left _ _).trans_eq (gradedWeight_sub_single_eq d i hi)

/-- Reindexing a sum over the variables of weight less than `m` occurring in a monomial by the
natural numbers below `m - 1`. -/
private theorem sum_support_reindex (d : ℕ+ →₀ ℕ) (m : ℕ)
    (hm : m = gradedWeight d) (F : ℕ+ → ℚ) :
    (∑ i ∈ d.support.filter (fun i : ℕ+ => (i : ℕ) < m), F i) =
      ∑ j ∈ (Finset.range (m - 1)).filter (fun j => Nat.succPNat j ∈ d.support),
        F (Nat.succPNat j) := by
  classical
  apply Finset.sum_bij (fun i _ => PNat.natPred i)
  · intro i hi
    obtain ⟨his, him⟩ := Finset.mem_filter.mp hi
    have hp := PNat.natPred_add_one i
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by simpa using his⟩
  · intro i _ j _ h
    apply Subtype.ext
    exact congrArg PNat.val (by simpa using congrArg Nat.succPNat h)
  · intro j hj
    obtain ⟨hjm, hjs⟩ := Finset.mem_filter.mp hj
    have hjlt := Finset.mem_range.mp hjm
    have : (Nat.succPNat j : ℕ) = j + 1 := rfl
    exact ⟨Nat.succPNat j, Finset.mem_filter.mpr ⟨hjs, by omega⟩, by simp⟩
  · exact fun i _ => congrArg F (PNat.succPNat_natPred i).symm

/-- The rational power-sum polynomial of degree `p` has no monomial of weighted degree other
than `p`. -/
private theorem coeff_powerSumPolynomialQ_eq_zero {p : ℕ} (d : ℕ+ →₀ ℕ)
    (hp : gradedWeight d ≠ p) : MvPolynomial.coeff d (powerSumPolynomialQ p) = 0 := by
  have hzero : MvPolynomial.coeff d
      (powerSumPolynomial p : MvPolynomial ℕ+ ℤ) = 0 := by
    by_contra hcoeff
    have hw :=
      isWeightedHomogeneous_powerSumPolynomial p hcoeff
    apply hp
    simpa [gradedWeight, Finsupp.weight_apply, mul_comm] using hw
  rw [powerSumPolynomialQ, MvPolynomial.coeff_map, hzero]
  simp

/-- The coefficients of the Euler operator applied to the signed power-sum series. -/
private theorem coeff_eulerDegree_powerSumSeries (d : ℕ+ →₀ ℕ) :
    MvPowerSeries.coeff d (eulerDegree powerSumSeries) =
      if gradedWeight d = 0 then 0 else
        ((-1 : ℚ) ^ (gradedWeight d - 1)) *
          MvPolynomial.coeff d (powerSumPolynomialQ (gradedWeight d)) := by
  classical
  by_cases hm : gradedWeight d = 0
  · simp [coeff_eulerDegree, hm]
  · let p₀ : ℕ+ := ⟨gradedWeight d, Nat.pos_of_ne_zero hm⟩
    have hsingle : (∑ᶠ p : ℕ+, MvPowerSeries.coeff d
        ((((-1 : ℚ) ^ ((p : ℕ) - 1) / (p : ℚ)) •
          (powerSumPolynomialQ (p : ℕ)).toMvPowerSeries))) =
        MvPowerSeries.coeff d
          ((((-1 : ℚ) ^ ((p₀ : ℕ) - 1) / (p₀ : ℚ)) •
            (powerSumPolynomialQ (p₀ : ℕ)).toMvPowerSeries)) := by
      rw [finsum_eq_single _ p₀ (by
        intro p hp
        have hpval : (p : ℕ) ≠ gradedWeight d := fun heq => hp (Subtype.ext heq)
        have hz := coeff_powerSumPolynomialQ_eq_zero (p := (p : ℕ)) d (Ne.symm hpval)
        show (((-1 : ℚ) ^ ((p : ℕ) - 1) / (p : ℚ)) *
          MvPolynomial.coeff d (powerSumPolynomialQ (p : ℕ))) = 0
        rw [hz]
        simp)]
    have hcoeffPS : MvPowerSeries.coeff d powerSumSeries =
        ((-1 : ℚ) ^ (gradedWeight d - 1) / (gradedWeight d : ℚ)) *
          MvPolynomial.coeff d (powerSumPolynomialQ (gradedWeight d)) := by
      unfold powerSumSeries
      show (∑ᶠ p : ℕ+, MvPowerSeries.coeff d
        (((-1 : ℚ) ^ ((p : ℕ) - 1) / (p : ℚ)) •
          (powerSumPolynomialQ (p : ℕ)).toMvPowerSeries)) = _
      rw [hsingle]
      show (((-1 : ℚ) ^ (gradedWeight d - 1) / (gradedWeight d : ℚ)) *
        MvPolynomial.coeff d (powerSumPolynomialQ (gradedWeight d))) = _
      rfl
    rw [coeff_eulerDegree, hcoeffPS]
    have hmQ : (gradedWeight d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm
    simp only [ite_eq_right hm]
    field_simp [hmQ]

/-- A monomial of weighted degree zero is the unit monomial. -/
private theorem eq_zero_of_gradedWeight_eq_zero (d : ℕ+ →₀ ℕ) (hd : gradedWeight d = 0) :
    d = 0 := by
  refine Finsupp.ext fun i => ?_
  by_contra hi
  have hle := support_index_le_gradedWeight d i (Finsupp.mem_support_iff.mpr hi)
  have hipos : 0 < (i : ℕ) := i.2
  omega

/-- Newton's recurrence for the coefficient of a monomial in the power-sum polynomial of its own
weighted degree. -/
private theorem coeff_powerSumPolynomialQ_gradedWeight (d : ℕ+ →₀ ℕ)
    (hmpos : 0 < gradedWeight d) :
    MvPolynomial.coeff d (powerSumPolynomialQ (gradedWeight d)) =
      (∑ j ∈ Finset.range (gradedWeight d - 1), (-1 : ℚ) ^ j *
        if Nat.succPNat j ∈ d.support then
          MvPolynomial.coeff (d - Finsupp.single (Nat.succPNat j) 1)
            (powerSumPolynomialQ (gradedWeight d - 1 - j))
        else 0) +
      (-1 : ℚ) ^ (gradedWeight d - 1) * ((((gradedWeight d - 1 : ℕ) : ℚ) + 1) *
        MvPolynomial.coeff d (MvPolynomial.X (Nat.succPNat (gradedWeight d - 1)))) := by
  classical
  have hrec : powerSumPolynomialQ (gradedWeight d) =
      ∑ j ∈ Finset.range (gradedWeight d - 1),
        MvPolynomial.C ((-1 : ℚ) ^ j) * MvPolynomial.X (Nat.succPNat j) *
          powerSumPolynomialQ (gradedWeight d - 1 - j) +
        MvPolynomial.C ((-1 : ℚ) ^ (gradedWeight d - 1) * (((gradedWeight d - 1 : ℕ) : ℚ) + 1)) *
          MvPolynomial.X (Nat.succPNat (gradedWeight d - 1)) := by
    simpa [Nat.sub_add_cancel (Nat.one_le_of_lt hmpos)] using
      powerSumPolynomialQ_succ (gradedWeight d - 1)
  simpa only [mul_assoc, MvPolynomial.coeff_add, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_mul'] using
    congrArg (MvPolynomial.coeff d) hrec

/-- The shifted coefficients of the Euler operator of the signed power-sum series, summed over
the variables of a monomial. -/
private theorem sum_coeff_sub_single_eulerDegree_powerSumSeries (d : ℕ+ →₀ ℕ) :
    ∑ i ∈ d.support,
        MvPowerSeries.coeff (d - Finsupp.single i 1) (eulerDegree powerSumSeries) =
      ∑ i ∈ d.support.filter (fun i : ℕ+ => (i : ℕ) < gradedWeight d),
        (-1 : ℚ) ^ (gradedWeight d - (i : ℕ) - 1) *
          MvPolynomial.coeff (d - Finsupp.single i 1)
            (powerSumPolynomialQ (gradedWeight d - (i : ℕ))) := by
  classical
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hwt := gradedWeight_sub_single_eq d i hi
  rw [coeff_eulerDegree_powerSumSeries]
  by_cases hil : (i : ℕ) < gradedWeight d
  · rw [ite_eq_right (show gradedWeight (d - Finsupp.single i 1) ≠ 0 by omega),
      show gradedWeight (d - Finsupp.single i 1) = gradedWeight d - (i : ℕ) by omega,
      ite_eq_left hil]
  · rw [ite_eq_left (show gradedWeight (d - Finsupp.single i 1) = 0 by omega), ite_eq_right hil]

/-- The signed Newton sum, reindexed by the variables of a monomial. -/
private theorem neg_one_pow_mul_sum_coeff_powerSumPolynomialQ (d : ℕ+ →₀ ℕ) :
    (-1 : ℚ) ^ (gradedWeight d - 1) *
        (∑ j ∈ Finset.range (gradedWeight d - 1), (-1 : ℚ) ^ j *
          if Nat.succPNat j ∈ d.support then
            MvPolynomial.coeff (d - Finsupp.single (Nat.succPNat j) 1)
              (powerSumPolynomialQ (gradedWeight d - 1 - j))
          else 0) =
      -∑ i ∈ d.support.filter (fun i : ℕ+ => (i : ℕ) < gradedWeight d),
        (-1 : ℚ) ^ (gradedWeight d - (i : ℕ) - 1) *
          MvPolynomial.coeff (d - Finsupp.single i 1)
            (powerSumPolynomialQ (gradedWeight d - (i : ℕ))) := by
  classical
  rw [sum_support_reindex d _ rfl, ← Finset.sum_neg_distrib]
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjlt : j < gradedWeight d - 1 := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  have hval : (Nat.succPNat j : ℕ) = j + 1 := rfl
  have hsign : (-1 : ℚ) ^ (gradedWeight d - 1) * (-1 : ℚ) ^ j =
      -((-1 : ℚ) ^ (gradedWeight d - (j + 1) - 1)) := by
    rw [← pow_add, show gradedWeight d - 1 + j =
      gradedWeight d - (j + 1) - 1 + (2 * j + 1) by omega, pow_add, pow_add, pow_mul]
    norm_num
  rw [← mul_assoc, hsign, hval, show gradedWeight d - 1 - j = gradedWeight d - (j + 1) by omega]
  ring

/-- The variable indexed by the weighted degree of a monomial has the same coefficient there as
the universal total Chern class. -/
private theorem coeff_X_succPNat_gradedWeight_pred (d : ℕ+ →₀ ℕ) :
    MvPolynomial.coeff d (MvPolynomial.X (Nat.succPNat (gradedWeight d - 1))) =
      MvPowerSeries.coeff d universalChernClassSum := by
  classical
  by_cases hu : exponentMass d = 1
  · obtain ⟨i, rfl⟩ := (Finsupp.sum_eq_one_iff d).mp hu
    have hw : gradedWeight (Finsupp.single i 1) = (i : ℕ) := by simp [gradedWeight]
    have hipos : 0 < (i : ℕ) := i.2
    have hidx : Nat.succPNat (gradedWeight (Finsupp.single i 1) - 1) = i := by
      apply Subtype.ext
      show gradedWeight (Finsupp.single i 1) - 1 + 1 = (i : ℕ)
      omega
    rw [coeff_universalChernClassSum_single, MvPolynomial.coeff_X]
    simp [hidx]
  · have hx : Finsupp.single (Nat.succPNat (gradedWeight d - 1)) 1 ≠ d := by
      intro heq
      apply hu
      rw [← heq]
      simp [exponentMass]
    rw [MvPolynomial.coeff_X, ite_eq_right hx]
    show 0 = (if exponentMass d = 1 then 1 else 0)
    simp [hu]

/-- Newton's recurrence, read as the series identity `(∂ ∑ₚ (-1)^(p-1) Pₚ/p)(1 + c) = ∂c`
where `c` is the universal total Chern class. -/
private theorem eulerPowerSum_mul_one_add :
    eulerDegree powerSumSeries * (1 + universalChernClassSum) =
      eulerDegree universalChernClassSum := by
  classical
  ext d
  rw [mul_add, mul_one, map_add, mul_comm (eulerDegree powerSumSeries),
    coeff_universalChernClassSum_mul]
  by_cases hm0 : gradedWeight d = 0
  · obtain rfl := eq_zero_of_gradedWeight_eq_zero d hm0
    rw [coeff_eulerDegree, coeff_eulerDegree]
    simp [hm0]
  have hmpos : 0 < gradedWeight d := Nat.pos_of_ne_zero hm0
  have hsign : (-1 : ℚ) ^ (gradedWeight d - 1) * (-1 : ℚ) ^ (gradedWeight d - 1) = 1 := by
    rw [← mul_pow]
    norm_num
  have hmcast : (((gradedWeight d - 1 : ℕ) : ℚ) + 1) = (gradedWeight d : ℚ) := by
    norm_num [Nat.cast_sub (show 1 ≤ gradedWeight d by omega)]
  rw [coeff_eulerDegree_powerSumSeries d, ite_eq_right hm0,
    coeff_powerSumPolynomialQ_gradedWeight d hmpos,
    sum_coeff_sub_single_eulerDegree_powerSumSeries d, coeff_eulerDegree,
    coeff_X_succPNat_gradedWeight_pred d, mul_add,
    neg_one_pow_mul_sum_coeff_powerSumPolynomialQ d, ← mul_assoc, hsign, hmcast]
  ring

/-- The signed power-sum series has zero constant term. -/
private theorem coeff_powerSumSeries_zero :
    MvPowerSeries.coeff 0 powerSumSeries = 0 := by
  classical
  unfold powerSumSeries
  apply finsum_eq_zero_of_forall_eq_zero
  intro p
  show (((-1 : ℚ) ^ ((p : ℕ) - 1) / (p : ℚ)) : ℚ) *
      MvPolynomial.coeff 0 (powerSumPolynomialQ (p : ℕ)) = 0
  have hp : gradedWeight (0 : ℕ+ →₀ ℕ) ≠ (p : ℕ) := by
    simp only [gradedWeight, Finsupp.sum_zero_index]
    exact (Nat.ne_of_gt p.2).symm
  rw [coeff_powerSumPolynomialQ_eq_zero 0 hp]
  simp

/-- Substituting the universal total Chern class into `log' · (1 + X) = 1`. -/
private theorem subst_derivative_log_mul_one_add :
    PowerSeries.subst universalChernClassSum (PowerSeries.derivative ℚ (PowerSeries.log ℚ)) *
      (1 + universalChernClassSum) = 1 := by
  have hsubst := hasSubst_universalChernClassSum
  have hone : PowerSeries.subst universalChernClassSum (1 : PowerSeries ℚ) = 1 := by
    rw [← PowerSeries.coe_substAlgHom hsubst]
    exact map_one _
  have h := congrArg (PowerSeries.subst universalChernClassSum)
    (PowerSeries.derivative_log_mul_one_add_X (A := ℚ))
  rw [PowerSeries.subst_mul hsubst, PowerSeries.subst_add hsubst,
    PowerSeries.subst_X hsubst, hone] at h
  simpa using h

/-- In the completed rational graded ring, the logarithm of the universal total Chern class
is the signed generating series of the universal power-sum polynomials. -/
@[stacks 0F9B "logarithmic_identity"]
public theorem log_one_add_universalChernClassSum :
    PowerSeries.subst universalChernClassSum (PowerSeries.log ℚ) = powerSumSeries := by
  classical
  have hcc := constantCoeff_universalChernClassSum
  have hsubst := hasSubst_universalChernClassSum
  have hlogMul :
      eulerDegree (PowerSeries.subst universalChernClassSum (PowerSeries.log ℚ)) *
        (1 + universalChernClassSum) = eulerDegree universalChernClassSum := by
    rw [eulerDegree_logSubst, mul_right_comm, subst_derivative_log_mul_one_add, one_mul]
  have hunit : MvPowerSeries.constantCoeff (1 + universalChernClassSum) ≠ 0 := by
    simp [hcc]
  have hEulerEq :
      eulerDegree (PowerSeries.subst universalChernClassSum (PowerSeries.log ℚ)) =
        eulerDegree powerSumSeries := by
    simpa only [mul_assoc, MvPowerSeries.mul_inv_cancel _ hunit, mul_one] using
      congrArg (fun x : MvPowerSeries ℕ+ ℚ => x * (1 + universalChernClassSum)⁻¹)
        (hlogMul.trans eulerPowerSum_mul_one_add.symm)
  have hlog0 : MvPowerSeries.coeff 0
      (PowerSeries.subst universalChernClassSum (PowerSeries.log ℚ)) = 0 := by
    rw [PowerSeries.coeff_subst hsubst (PowerSeries.log ℚ) 0]
    refine finsum_eq_zero_of_forall_eq_zero fun n => ?_
    by_cases hn : n = 0 <;> simp [hn, hcc]
  ext d
  by_cases hw : gradedWeight d = 0
  · obtain rfl := eq_zero_of_gradedWeight_eq_zero d hw
    simpa [hlog0] using coeff_powerSumSeries_zero.symm
  · have hcoef := congrArg (MvPowerSeries.coeff d) hEulerEq
    rw [coeff_eulerDegree, coeff_eulerDegree] at hcoef
    exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr hw) hcoef

end AlgebraicGeometry

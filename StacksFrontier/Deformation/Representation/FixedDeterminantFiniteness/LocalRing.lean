module

public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Matrix.CharP
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Elementary facts about local rings used for deformation rings

This file collects facts about a local ring `S` used in the proof that the universal deformation
ring of a residual representation with fixed determinant is finite over `ℤ_[ℓ]`.

## Main results

* `IsLocalRing.eq_zero_of_mem_maximalIdeal_of_pow_eq_self` — an element `b` of the maximal ideal
  with `b ^ q = b` for some `q ≥ 2` is zero.
* `IsLocalRing.eq_zero_of_one_add_pow_eq_one` — `1 + x` with `x` in the maximal ideal has no
  `n`-torsion when `n` is invertible.
* `IsLocalRing.eq_algebraMap_of_isIntegral` — in a local domain, an element integral over a
  finite subfield is the image of the element of the subfield with the same residue.
* `Matrix.isIntegral_trace_of_pow_eq_one` — the trace of a matrix of finite multiplicative order
  over a domain is integral over `ℤ`.
-/

@[expose] public section

open IsLocalRing

namespace IsLocalRing

variable {S : Type*} [CommRing S] [IsLocalRing S]

/-- An element `b` of the maximal ideal of a local ring with `b ^ q = b` for some `q ≥ 2` is
zero: `b * (b ^ (q - 1) - 1) = 0` and `b ^ (q - 1) - 1` is a unit. -/
theorem eq_zero_of_mem_maximalIdeal_of_pow_eq_self {b : S} (hb : b ∈ maximalIdeal S) {q : ℕ}
    (hq : 2 ≤ q) (h : b ^ q = b) : b = 0 := by
  have hq1 : b ^ (q - 1) ∈ maximalIdeal S :=
    Ideal.pow_mem_of_mem _ hb _ (by omega)
  have hu : IsUnit (1 - b ^ (q - 1)) :=
    isUnit_one_sub_self_of_mem_nonunits _ ((mem_maximalIdeal _).1 hq1)
  have hzero : b * (1 - b ^ (q - 1)) = 0 := by
    rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ q), h, sub_self]
  exact hu.mul_left_eq_zero.1 hzero

/-- In a local ring in which `n` is invertible, `1 + x` with `x` in the maximal ideal has no
`n`-torsion: `(1 + x) ^ n = 1` forces `x = 0`. -/
theorem eq_zero_of_one_add_pow_eq_one {x : S} (hx : x ∈ maximalIdeal S) {n : ℕ}
    (hn : IsUnit (n : S)) (h : (1 + x) ^ n = 1) : x = 0 := by
  have hgeom : (∑ i ∈ Finset.range n, (1 + x) ^ i) * x = 0 := by
    have := geom_sum_mul (1 + x) n
    rwa [add_sub_cancel_left, h, sub_self] at this
  have hsum : (∑ i ∈ Finset.range n, (1 + x) ^ i) - n ∈ maximalIdeal S := by
    rw [show (∑ i ∈ Finset.range n, (1 + x) ^ i) - n =
        ∑ i ∈ Finset.range n, ((1 + x) ^ i - 1) by simp [Finset.sum_sub_distrib]]
    refine Ideal.sum_mem _ fun i _ => ?_
    have hdvd := sub_dvd_pow_sub_pow (1 + x) 1 i
    rw [one_pow, add_sub_cancel_left] at hdvd
    exact Ideal.mem_of_dvd _ hdvd hx
  have hu : IsUnit (∑ i ∈ Finset.range n, (1 + x) ^ i) := by
    by_contra hnu
    have h1 : (n : S) ∈ maximalIdeal S := by
      simpa using (maximalIdeal S).sub_mem ((mem_maximalIdeal _).2 hnu) hsum
    exact ((mem_maximalIdeal _).1 h1) hn
  exact hu.mul_right_eq_zero.1 hgeom

/-- In a local domain `S` containing a finite field `K`, an element `a` integral over `K` and
congruent modulo the maximal ideal to an element `c` of `K` is equal to `c`: the subalgebra
`K[a]` is a finite domain, hence a finite field, so `b = a - c` satisfies `b ^ q = b` for its
cardinality `q ≥ 2` while lying in the maximal ideal. -/
theorem eq_algebraMap_of_isIntegral [IsDomain S] {K : Type*} [Field K] [Finite K]
    [Algebra K S] {a : S} (ha : IsIntegral K a) {c : K}
    (hc : a - algebraMap K S c ∈ maximalIdeal S) : a = algebraMap K S c := by
  classical
  let T : Subalgebra K S := Algebra.adjoin K {a}
  have : Module.Finite K T := Module.Finite.iff_fg.2 ha.fg_adjoin_singleton
  have : Finite T := Module.finite_of_finite K
  have : Fintype T := Fintype.ofFinite T
  let : Field T := Fintype.fieldOfDomain T
  let b : T := ⟨a, Algebra.subset_adjoin rfl⟩ - algebraMap K T c
  have hcard : 2 ≤ Fintype.card T := Fintype.one_lt_card
  have hpowS : (a - algebraMap K S c) ^ Fintype.card T = a - algebraMap K S c :=
    congrArg Subtype.val (FiniteField.pow_card b)
  exact sub_eq_zero.1 (eq_zero_of_mem_maximalIdeal_of_pow_eq_self hc hcard hpowS)

end IsLocalRing

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Frobenius on traces.** Over a commutative ring of prime characteristic `p`,
`tr (X ^ p) = (tr X) ^ p`. The characteristic polynomial of `X ^ p` is the image of that of `X`
under the Frobenius: both expand to `χ_X ^ p`, since `(t - X) ^ p = t ^ p - X ^ p`. -/
theorem trace_pow_char {S : Type*} [CommRing S] (p : ℕ) [Fact p.Prime] [CharP S p]
    (X : Matrix n n S) : (X ^ p).trace = X.trace ^ p := by
  cases isEmpty_or_nonempty n
  · simp [Matrix.trace, zero_pow (Fact.out : p.Prime).ne_zero]
  have hcharmatrix : (charmatrix X) ^ p =
      (Polynomial.expand S p : Polynomial S →+* Polynomial S).mapMatrix (charmatrix (X ^ p)) := by
    apply matPolyEquiv.injective
    rw [map_pow, matPolyEquiv_charmatrix, matPolyEquiv_eq_X_pow_sub_C,
      sub_pow_char_of_commute (p := p) (h := Polynomial.commute_X _), ← Polynomial.C_pow]
  have hexp : Polynomial.expand S p (X ^ p).charpoly = X.charpoly ^ p := by
    unfold Matrix.charpoly
    rw [← det_pow, hcharmatrix, ← RingHom.map_det]
    rfl
  have hfrob : (X ^ p).charpoly = X.charpoly.map (frobenius S p) := by
    apply Polynomial.expand_injective (Fact.out : p.Prime).pos
    rw [hexp, ← Polynomial.map_frobenius_expand, Polynomial.map_expand]
  rw [trace_eq_neg_charpoly_coeff, trace_eq_neg_charpoly_coeff, hfrob, Polynomial.coeff_map,
    frobenius_def, neg_pow, neg_one_pow_char, neg_one_mul]

/-- Iterated Frobenius on traces: `tr (X ^ p ^ k) = (tr X) ^ p ^ k` in characteristic `p`. -/
theorem trace_pow_char_pow {S : Type*} [CommRing S] (p : ℕ) [Fact p.Prime] [CharP S p]
    (X : Matrix n n S) (k : ℕ) : (X ^ p ^ k).trace = X.trace ^ p ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_mul, trace_pow_char, ih, ← pow_mul]

end Matrix

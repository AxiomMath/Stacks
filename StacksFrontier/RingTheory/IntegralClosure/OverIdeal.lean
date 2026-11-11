module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.IntegralClosure.Algebra.Ideal
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Topology.Sheaves.Init

import StacksCore.Tactic.StacksAttribute

/-!
# Elements integral over an ideal
-/

/-!
# Integral over an ideal

Let `φ : R → S` be a ring map and let `I ⊂ R` be an ideal. An element `g ∈ S` is
*integral over `I`* if there exists a monic polynomial
`P = x^d + ∑_{j < d} a_j x^j` with coefficients `a_j ∈ I^{d-j}` such that
`P^φ(g) = 0` in `S`. This file records the definition and its specialization to ordinary
integrality.
-/

@[expose] public section

namespace RingHom

/-- An element `g ∈ S` is *integral over the ideal `I ⊂ R`* with respect to the
ring map `φ : R →+* S` if there exists a monic polynomial `P ∈ R[X]` of degree
`d` such that every coefficient `P.coeff j` lies in `I ^ (d - j)`, and `P`
evaluated at `g` via `φ` is zero in `S`.

Since `P` is monic with `d = P.natDegree`, the leading coefficient `P.coeff d`
equals `1 ∈ I ^ 0 = ⊤`, and the coefficients above the degree vanish, so the
condition `∀ j, P.coeff j ∈ I ^ (d - j)` is exactly the Stacks requirement on
the non-leading coefficients `a_j ∈ I ^ (d - j)` for `j < d`. -/
@[stacks 00H2]
def IsIntegralElemOverIdeal {R S : Type*} [CommRing R] [Ring S]
    (φ : R →+* S) (I : Ideal R) (g : S) : Prop :=
  ∃ P : Polynomial R, P.Monic ∧
    (∀ j : ℕ, P.coeff j ∈ I ^ (P.natDegree - j)) ∧
    Polynomial.eval₂ φ g P = 0

/-- An element integral over the ideal `I` is, in particular, an integral element of the ring
map `φ` in the sense of `RingHom.IsIntegralElem`. -/
theorem IsIntegralElemOverIdeal.isIntegralElem {R S : Type*} [CommRing R] [Ring S]
    {φ : R →+* S} {I : Ideal R} {g : S} (h : φ.IsIntegralElemOverIdeal I g) :
    φ.IsIntegralElem g :=
  let ⟨P, hMonic, _, hEval⟩ := h
  ⟨P, hMonic, hEval⟩

end RingHom

end

/-!
# Characterization of elements integral over an ideal

Let `φ : R →+* S` be a ring map and `I ⊂ R` an ideal, and let `A = reesAlgebra I ⊂ R[t]` be the
Rees algebra `∑ Iⁿ tⁿ`, viewed inside `S[t]` via the coefficientwise extension of `φ`.
[Stacks, Tag 00H3] characterizes the elements of `S` integral over `I`
(`RingHom.IsIntegralElemOverIdeal`): `s` is integral over `I` if and only if `C s · t ∈ S[t]` is
integral over `A`.

## Main results

* `isIntegralElem_of_isIntegralOverIdeal`: if `s` is integral over `I`, then `C s · t` is
  integral over `A`.
* `isIntegralElemOverIdeal_of_isIntegralElem`: if `C s · t` is integral over `A`, then `s` is
  integral over `I`.
* `isIntegralElemOverIdeal_iff_isIntegralElem`: [Stacks, Tag 00H3], the equivalence.
-/

@[expose] public section

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The image of the Rees algebra of `I` inside `S[X]` under the
coefficient-wise extension of `φ : R →+* S`. -/
noncomputable def reesToPolyS (φ : R →+* S) (I : Ideal R) :
    reesAlgebra I →+* S[X] :=
  (Polynomial.mapRingHom φ).comp (Subalgebra.val (reesAlgebra I)).toRingHom

/-- For `a ∈ I ^ k`, the polynomial `C a * X ^ k` lies in `reesAlgebra I`. -/
lemma C_mul_X_pow_mem_reesAlgebra (I : Ideal R) (k : ℕ) (a : R) (h : a ∈ I ^ k) :
    C a * X ^ k ∈ reesAlgebra I := by
  intro n
  rw [coeff_C_mul_X_pow]
  split_ifs with hn
  · simpa [hn] using h
  · simp

/-! ### Forward direction -/

/-- For each `i < n = p.natDegree`, the coefficient `C (p.coeff i) * X ^ (n - i)`
lies in the Rees algebra (packaged as an element of `reesAlgebra I`). -/
noncomputable def forwardCoeff (I : Ideal R) (p : R[X])
    (hcoeff : ∀ i, i < p.natDegree → p.coeff i ∈ I ^ (p.natDegree - i))
    (i : Fin p.natDegree) : reesAlgebra I :=
  ⟨C (p.coeff i) * X ^ (p.natDegree - i),
    C_mul_X_pow_mem_reesAlgebra I (p.natDegree - i) (p.coeff i) (hcoeff i i.isLt)⟩

/-- The forward witness polynomial: given a witness `p ∈ R[X]` for the
integrality of `s` over `I` (so `p.coeff i ∈ I ^ (n - i)` for `i < n`), this is
the monic polynomial `Y ^ n + ∑_{i < n} C (forwardCoeff … i) * Y ^ i`
in `(reesAlgebra I)[Y]`. -/
noncomputable def forwardWitness (I : Ideal R) (p : R[X])
    (hcoeff : ∀ i, i < p.natDegree → p.coeff i ∈ I ^ (p.natDegree - i)) :
    (reesAlgebra I)[X] :=
  X ^ p.natDegree +
    ∑ i : Fin p.natDegree, C (forwardCoeff I p hcoeff i) * X ^ (i : ℕ)

/-- The forward witness polynomial is monic. -/
lemma forwardWitness_monic (I : Ideal R) (p : R[X])
    (hcoeff : ∀ i, i < p.natDegree → p.coeff i ∈ I ^ (p.natDegree - i))
    (hn : 1 ≤ p.natDegree) :
    (forwardWitness I p hcoeff).Monic := by
  have _ := hn
  exact monic_X_pow_add (degree_sum_fin_lt _)

/-- Pushing `forwardCoeff` through `reesToPolyS φ I` gives back the explicit
polynomial `C (φ (p.coeff i)) * X ^ (n - i)` in `S[X]`. -/
lemma reesToPolyS_forwardCoeff (φ : R →+* S) (I : Ideal R) (p : R[X])
    (hcoeff : ∀ i, i < p.natDegree → p.coeff i ∈ I ^ (p.natDegree - i))
    (i : Fin p.natDegree) :
    reesToPolyS φ I (forwardCoeff I p hcoeff i) =
      C (φ (p.coeff i)) * X ^ (p.natDegree - (i : ℕ)) := by
  unfold reesToPolyS forwardCoeff
  simp [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X]

/-- Evaluation of the forward witness polynomial at `C s * X` equals
`(C s * X) ^ n + ∑_{i < n} C (φ (p.coeff i)) * X ^ (n - i) * (C s * X) ^ i`. -/
lemma forwardWitness_eval₂_eq (φ : R →+* S) (I : Ideal R) (p : R[X]) (s : S)
    (hcoeff : ∀ i, i < p.natDegree → p.coeff i ∈ I ^ (p.natDegree - i)) :
    (forwardWitness I p hcoeff).eval₂ (reesToPolyS φ I) (C s * X) =
      (C s * X) ^ p.natDegree +
        ∑ i : Fin p.natDegree,
          C (φ (p.coeff i)) * X ^ (p.natDegree - (i : ℕ)) * (C s * X) ^ (i : ℕ) := by
  unfold forwardWitness
  rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow,
      reesToPolyS_forwardCoeff]

/-- `(C s * X) ^ k = C (s ^ k) * X ^ k` in `S[X]`. -/
private lemma C_mul_X_pow (s : S) (k : ℕ) : (C s * X) ^ k = C (s ^ k) * X ^ k := by
  rw [mul_pow, Polynomial.C_pow]

/-- Expansion of each summand in `forwardWitness_eval₂_eq`. -/
private lemma forward_summand_eq (φ : R →+* S) (p : R[X]) (s : S) (i : Fin p.natDegree) :
    C (φ (p.coeff i)) * X ^ (p.natDegree - (i : ℕ)) * (C s * X) ^ (i : ℕ) =
      C (φ (p.coeff i) * s ^ (i : ℕ)) * X ^ p.natDegree := by
  have hi : (p.natDegree - (i : ℕ)) + (i : ℕ) = p.natDegree :=
    Nat.sub_add_cancel (le_of_lt i.isLt)
  rw [C_mul_X_pow, show C (φ (p.coeff i)) * X ^ (p.natDegree - (i : ℕ)) *
        (C (s ^ (i : ℕ)) * X ^ (i : ℕ)) =
        C (φ (p.coeff i) * s ^ (i : ℕ)) * (X ^ (p.natDegree - (i : ℕ)) * X ^ (i : ℕ)) from ?_]
  · rw [← pow_add, hi]
  · rw [Polynomial.C_mul]; ring

/-- For a monic polynomial `p ∈ R[X]`,
`p.eval₂ φ s = s ^ n + ∑_{i ∈ range n} φ (p.coeff i) * s ^ i`. -/
lemma monic_eval₂_expand (φ : R →+* S) (p : R[X]) (hp : p.Monic) (s : S) :
    p.eval₂ φ s = s ^ p.natDegree +
      ∑ i ∈ Finset.range p.natDegree, φ (p.coeff i) * s ^ i := by
  conv_lhs => rw [hp.as_sum]
  rw [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]

/-- The forward witness polynomial evaluates to `C (p.eval₂ φ s) * X ^ n` at
`C s * X` in `S[X]`. -/
lemma forwardWitness_eval₂_factor (φ : R →+* S) (I : Ideal R) (p : R[X]) (s : S)
    (hp : p.Monic)
    (hcoeff : ∀ i, i < p.natDegree → p.coeff i ∈ I ^ (p.natDegree - i)) :
    (forwardWitness I p hcoeff).eval₂ (reesToPolyS φ I) (C s * X) =
      C (p.eval₂ φ s) * X ^ p.natDegree := by
  rw [forwardWitness_eval₂_eq, monic_eval₂_expand φ p hp s, C_add, add_mul, map_sum,
    Finset.sum_mul, ← Fin.sum_univ_eq_sum_range
      (fun i => C (φ (p.coeff i) * s ^ i) * X ^ p.natDegree), C_mul_X_pow]
  simp only [forward_summand_eq]

/-- If `s : S` is integral over the ideal `I ⊆ R` with respect to `φ : R →+* S`, then
`C s · X ∈ S[X]` is integral over the Rees subalgebra `reesAlgebra I`, viewed inside `S[X]` along
the coefficientwise extension of `φ`.

A monic witness of degree zero is `1`, whose vanishing at `s` makes `s = 0`, and then `C s · X`
is zero and `X` is a witness; otherwise `forwardWitness` multiplies the `i`-th coefficient by
`X ^ (n - i)` to land in the Rees algebra. -/
theorem isIntegralElem_of_isIntegralOverIdeal (φ : R →+* S) (I : Ideal R) (s : S)
    (h : φ.IsIntegralElemOverIdeal I s) :
    (reesToPolyS φ I).IsIntegralElem (C s * X) := by
  obtain ⟨p, hp, hcoeff, heval⟩ := h
  have hc : ∀ i, i < p.natDegree → p.coeff i ∈ I ^ (p.natDegree - i) := fun i _ => hcoeff i
  rcases Nat.eq_zero_or_pos p.natDegree with h0 | hn
  · rw [hp.natDegree_eq_zero.mp h0, Polynomial.eval₂_one] at heval
    have hs : s = 0 := by rw [← mul_one s, heval, mul_zero]
    refine ⟨X, monic_X, ?_⟩
    rw [Polynomial.eval₂_X, hs, Polynomial.C_0, zero_mul]
  · refine ⟨forwardWitness I p hc, forwardWitness_monic I p hc hn, ?_⟩
    rw [forwardWitness_eval₂_factor φ I p s hp hc, heval, Polynomial.C_0, zero_mul]

/-! ### Converse direction -/

/-- If `C s · X ∈ S[X]` is integral over the Rees subalgebra `reesAlgebra I`, viewed inside `S[X]`
along the coefficientwise extension of `φ`, then `s` is integral over `I`.

Let `Q` be a monic witness of degree `d` with coefficients `Q_i ∈ reesAlgebra I`. The
coefficient of `X ^ d` in `Q (C s · X) = 0` is `∑_{i ≤ d} φ (Q_i)_{d - i} · s ^ i = 0`, and
`(Q_i)_{d - i} ∈ I ^ (d - i)` by definition of the Rees algebra, while `(Q_d)_0 = 1`. So
`∑_{i ≤ d} (Q_i)_{d - i} X ^ i` witnesses that `s` is integral over `I`. -/
theorem isIntegralElemOverIdeal_of_isIntegralElem (φ : R →+* S) (I : Ideal R) (s : S)
    (h : (reesToPolyS φ I).IsIntegralElem (C s * X)) :
    φ.IsIntegralElemOverIdeal I s := by
  rcases subsingleton_or_nontrivial R with _ | _
  · exact ⟨0, Subsingleton.elim _ _, fun j => by rw [coeff_zero]; exact Submodule.zero_mem _,
      Polynomial.eval₂_zero _ _⟩
  obtain ⟨p, hp, e⟩ := h
  let q : R[X] := ∑ i ∈ Finset.range (p.natDegree + 1),
    C ((p.coeff i : R[X]).coeff (p.natDegree - i)) * X ^ i
  have hqc : ∀ i, q.coeff i =
      if i ≤ p.natDegree then (p.coeff i : R[X]).coeff (p.natDegree - i) else 0 := by
    intro i
    simp only [q, finsetSum_coeff, coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range,
      Nat.lt_succ_iff]
  have hq1 : q.coeff p.natDegree = 1 := by
    rw [hqc, ite_eq_left le_rfl, Nat.sub_self, hp.coeff_natDegree]
    simp
  have hq : q.natDegree = p.natDegree := by
    refine natDegree_eq_of_le_of_coeff_ne_zero (natDegree_sum_le_of_forall_le _ _ ?_) ?_
    · exact fun i hi => (natDegree_C_mul_X_pow_le _ _).trans
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    · rw [hq1]
      exact one_ne_zero
  refine ⟨q, ?_, fun j => ?_, ?_⟩
  · rw [Monic, leadingCoeff, hq, hq1]
  · rw [hq, hqc]
    split_ifs
    · exact (p.coeff j).2 (p.natDegree - j)
    · exact Submodule.zero_mem _
  · replace e := congr(($e).coeff p.natDegree)
    rw [eval₂_eq_sum_range, finsetSum_coeff, coeff_zero] at e
    rw [eval₂_eq_sum_range, hq]
    refine (Finset.sum_congr rfl fun i hi => ?_).trans e
    have hi : i ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [hqc, ite_eq_left hi, mul_pow, ← mul_assoc, ← Polynomial.C_pow, coeff_mul_X_pow',
      ite_eq_left hi, coeff_mul_C]
    simp [reesToPolyS, coeff_map]

/-- **[Stacks, Tag 00H3].** Let `φ : R →+* S` be a ring map and `I ⊆ R` an ideal, and let
`A = reesAlgebra I = ∑ Iⁿ Xⁿ ⊆ R[X]`, mapped to `S[X]` along the coefficientwise extension of `φ`.
An element `s : S` is integral over `I` if and only if `C s · X ∈ S[X]` is integral over `A`.

Both directions are proved: `isIntegralElem_of_isIntegralOverIdeal` (forward) and
`isIntegralElemOverIdeal_of_isIntegralElem` (converse, by taking the `X ^ d` coefficient). -/
@[stacks 00H3]
theorem isIntegralElemOverIdeal_iff_isIntegralElem (φ : R →+* S) (I : Ideal R) (s : S) :
    φ.IsIntegralElemOverIdeal I s ↔ (reesToPolyS φ I).IsIntegralElem (C s * X) :=
  ⟨isIntegralElem_of_isIntegralOverIdeal φ I s,
    isIntegralElemOverIdeal_of_isIntegralElem φ I s⟩

end

/-!
# Elements integral over an ideal form a submodule

Let `φ : R → S` be a ring map and let `I ⊂ R` be an ideal. [Stacks, Tag 00H4] asserts that the
set of elements of `S` integral over `I` (`RingHom.IsIntegralElemOverIdeal`) is an
`R`-submodule of `S`, and that it is stable under multiplication by the elements of `S` integral
over `R`.

## Main definitions

* `Ideal.integralClosureSubmodule`: for an `R`-algebra `S`, the `R`-submodule of `S` of elements
  integral over `I`.

## Main results

* `zero_isIntegralElemOverIdeal`, `mul_left_isIntegralElemOverIdeal`: `0` is integral over `I`,
  and so is `φ r * g` whenever `g` is.
* `add_isIntegralElemOverIdeal`: the sum of two elements integral over `I` is integral over `I`,
  through the Rees algebra characterization `isIntegralElemOverIdeal_iff_isIntegralElem`.
* `mul_isIntegralElemOverIdeal_of_isIntegralElem`: if `s` is integral over `R` and `g` is
  integral over `I`, then `s * g` is integral over `I`.
* `Ideal.exists_submodule_and_mul_isIntegralElemOverIdeal`: [Stacks, Tag 00H4].
-/

@[expose] public section

open Polynomial

/-- The zero element of `S` is integral over any ideal `I ⊂ R`, witnessed by
the polynomial `X`. -/
theorem zero_isIntegralElemOverIdeal
    {R : Type*} {S : Type*} [CommRing R] [Ring S]
    (φ : R →+* S) (I : Ideal R) :
    RingHom.IsIntegralElemOverIdeal φ I (0 : S) := by
  refine ⟨X, monic_X, ?_, ?_⟩
  · intro j
    -- `(X : R[X]).coeff j` is either `0` (for `j ≠ 1`) or `1` (for `j = 1`).
    -- In the first case any ideal power contains `0`; in the second case
    -- `(X : R[X]).natDegree - j = 0` so the ambient ideal is `⊤`.
    rw [coeff_X]
    split_ifs with h
    · -- `j = 1`, so `natDegree X - j ≤ 1 - 1 = 0`, hence `I ^ … = ⊤`.
      have : (X : R[X]).natDegree - j = 0 := by
        have := natDegree_X_le (R := R)
        omega
      rw [this, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    · exact Submodule.zero_mem _
  · simp

/-- If `g ∈ S` is integral over the ideal `I` and `r ∈ R`, then `φ r * g` is
integral over `I`, by scaling the roots of a witness by `r`. -/
theorem mul_left_isIntegralElemOverIdeal
    {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (I : Ideal R) (r : R) (g : S)
    (h : RingHom.IsIntegralElemOverIdeal φ I g) :
    RingHom.IsIntegralElemOverIdeal φ I (φ r * g) := by
  obtain ⟨P, hMonic, hCoeff, hEval⟩ := h
  refine ⟨P.scaleRoots r, ?_, ?_, ?_⟩
  · exact (monic_scaleRoots_iff r).mpr hMonic
  · intro j
    have hdeg : (P.scaleRoots r).natDegree = P.natDegree := natDegree_scaleRoots P r
    rw [coeff_scaleRoots, hdeg]
    -- `P.coeff j ∈ I ^ (P.natDegree - j)` and `r ^ (P.natDegree - j) ∈ R`,
    -- so the product lies in `I ^ (P.natDegree - j)` (ideal absorbs ring elements).
    exact Ideal.mul_mem_right _ _ (hCoeff j)
  · -- `scaleRoots_eval₂_eq_zero` : `eval₂ φ r P = 0 → eval₂ φ (φ r * g) (P.scaleRoots r) = 0`.
    exact scaleRoots_eval₂_eq_zero φ hEval

section Closure

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The sum of two elements integral over `I` is integral over `I`: by
`isIntegralElemOverIdeal_iff_isIntegralElem`, `C g · X` and `C g' · X` are integral over the
Rees algebra of `I`, hence so is their sum `C (g + g') · X`. -/
theorem add_isIntegralElemOverIdeal (φ : R →+* S) (I : Ideal R) {g g' : S}
    (hg : φ.IsIntegralElemOverIdeal I g) (hg' : φ.IsIntegralElemOverIdeal I g') :
    φ.IsIntegralElemOverIdeal I (g + g') := by
  rw [isIntegralElemOverIdeal_iff_isIntegralElem] at hg hg' ⊢
  rw [C_add, add_mul]
  exact RingHom.IsIntegralElem.add _ hg hg'

/-- An element `s` of `S` integral over `R` gives the degree-zero element `C s` of `S[X]`
integral over the Rees algebra of `I`, which contains `R`. -/
theorem isIntegralElem_C_of_isIntegralElem (φ : R →+* S) (I : Ideal R) {s : S}
    (hs : φ.IsIntegralElem s) : (reesToPolyS φ I).IsIntegralElem (C s) := by
  obtain ⟨P, hP, hPs⟩ := hs
  refine ⟨P.map (algebraMap R (reesAlgebra I)), hP.map _, ?_⟩
  have hcomp : (reesToPolyS φ I).comp (algebraMap R (reesAlgebra I)) = C.comp φ :=
    RingHom.ext fun r => by simp [reesToPolyS]
  rw [eval₂_map, hcomp, ← Polynomial.hom_eval₂, hPs, map_zero]

/-- If `s` is integral over `R` and `g` is integral over `I`, then `s * g` is integral over `I`:
`C (s * g) · X = C s · (C g · X)` is a product of two elements of `S[X]` integral over the Rees
algebra of `I`. -/
theorem mul_isIntegralElemOverIdeal_of_isIntegralElem (φ : R →+* S) (I : Ideal R) {s g : S}
    (hs : φ.IsIntegralElem s) (hg : φ.IsIntegralElemOverIdeal I g) :
    φ.IsIntegralElemOverIdeal I (s * g) := by
  rw [isIntegralElemOverIdeal_iff_isIntegralElem] at hg ⊢
  rw [C_mul, mul_assoc]
  exact RingHom.IsIntegralElem.mul _ (isIntegralElem_C_of_isIntegralElem φ I hs) hg

variable (S) [Algebra R S]

/-- The `R`-submodule of the `R`-algebra `S` consisting of the elements integral over the ideal
`I ⊆ R` along `algebraMap R S`. -/
def Ideal.integralClosureSubmodule (I : Ideal R) : Submodule R S where
  carrier := {g | (algebraMap R S).IsIntegralElemOverIdeal I g}
  add_mem' := add_isIntegralElemOverIdeal _ I
  zero_mem' := zero_isIntegralElemOverIdeal _ I
  smul_mem' r g hg := by
    rw [Set.mem_ofPred_eq, Algebra.smul_def]
    exact mul_left_isIntegralElemOverIdeal _ I r g hg

variable {S}

/-- Membership in `Ideal.integralClosureSubmodule` is integrality over the ideal. -/
theorem Ideal.mem_integralClosureSubmodule {I : Ideal R} {g : S} :
    g ∈ I.integralClosureSubmodule S ↔ (algebraMap R S).IsIntegralElemOverIdeal I g :=
  Iff.rfl

/-- **[Stacks, Tag 00H4].** Let `S` be an `R`-algebra and `I ⊆ R` an ideal. The elements of `S`
integral over `I` form an `R`-submodule of `S`; furthermore, if `s ∈ S` is integral over `R` and
`g ∈ S` is integral over `I`, then `s * g` is integral over `I`. -/
@[stacks 00H4]
theorem Ideal.exists_submodule_and_mul_isIntegralElemOverIdeal (I : Ideal R) :
    (∃ M : Submodule R S, ∀ g, g ∈ M ↔ (algebraMap R S).IsIntegralElemOverIdeal I g) ∧
      ∀ s g : S, IsIntegral R s → (algebraMap R S).IsIntegralElemOverIdeal I g →
        (algebraMap R S).IsIntegralElemOverIdeal I (s * g) :=
  ⟨⟨I.integralClosureSubmodule S, fun _ => Iff.rfl⟩,
    fun _ _ hs hg => mul_isIntegralElemOverIdeal_of_isIntegralElem _ I hs hg⟩

end Closure

end

/-!
# Elements of an extended ideal are integral over that ideal

Stacks 00H5 — for an integral algebra `R → S` and an ideal `I ⊂ R`, every element of the
extended ideal `I S` is a root of a monic polynomial over `R` whose `j`-th coefficient lies in
`I ^ (n - j)` — is Mathlib's
`Polynomial.exists_monic_aeval_eq_zero_forall_mem_pow_of_mem_map`; Mathlib also carries the tag
on the weaker `Polynomial.exists_monic_aeval_eq_zero_forall_mem_of_mem_map`.
-/

@[expose] public section

-- The former @[stacks 00H5] theorem is the Mathlib theorem.
add_to_stacks 00H5 Polynomial.exists_monic_aeval_eq_zero_forall_mem_pow_of_mem_map

end

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

Let `φ : R →+* S` be a ring map and `I ⊂ R` an ideal. An element `s : S` is
*integral over the ideal `I`* (with respect to `φ`) if there is a monic
polynomial `p ∈ R[X]` of natural degree `n ≥ 1` whose `i`-th coefficient lies
in `I ^ (n - i)` for every `i < n`, and such that `p.eval₂ φ s = 0`.

A standard equivalent characterization is that `C s · X ∈ S[X]` is integral
over the Rees algebra `A = reesAlgebra I ⊂ R[X]`, viewed inside `S[X]` via
the coefficient-wise extension of `φ`. This file formalizes the definition
and the forward direction of this equivalence.
-/

@[expose] public section

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

/-- An element `s : S` is *integral over the ideal* `I ⊂ R` (with respect to a
ring map `φ : R →+* S`) iff there exists a monic polynomial `p ∈ R[X]` of
natural degree `n ≥ 1` whose `i`-th coefficient lies in `I ^ (n - i)` for every
`i < n`, and such that `p.eval₂ φ s = 0`. -/
def IsIntegralOverIdeal (φ : R →+* S) (I : Ideal R) (s : S) : Prop :=
  ∃ p : R[X], p.Monic ∧ 1 ≤ p.natDegree ∧
    (∀ i, i < p.natDegree → p.coeff i ∈ I ^ (p.natDegree - i)) ∧
    p.eval₂ φ s = 0

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

/-- If `s : S` is integral over the ideal `I ⊂ R` (with respect to `φ : R →+* S`),
then `C s · X ∈ S[X]` is integral over the Rees subalgebra `reesAlgebra I`
viewed inside `S[X]` via the coefficient-wise extension of `φ`. -/
@[stacks 00H3 "Forward implication only: integral over I implies C s * X integral over \
reesAlgebra I. The converse half of the equivalence is not formalized."]
theorem isIntegralElem_of_isIntegralOverIdeal (φ : R →+* S) (I : Ideal R) (s : S)
    (h : IsIntegralOverIdeal φ I s) :
    (reesToPolyS φ I).IsIntegralElem (C s * X) := by
  obtain ⟨p, hp, hn, hcoeff, heval⟩ := h
  refine ⟨forwardWitness I p hcoeff, forwardWitness_monic I p hcoeff hn, ?_⟩
  rw [forwardWitness_eval₂_factor φ I p s hp hcoeff, heval, Polynomial.C_0, zero_mul]

end

/-!
# Elements integral over an ideal form a submodule (partial)

Let `φ : R → S` be a ring map and let `I ⊂ R` be an ideal. The Stacks lemma
`00H4` asserts that the set of elements of `S` that are integral over `I` forms
an `R`-submodule of `S`.

The full statement decomposes into three closure properties:

* `0` is integral over `I`,
* if `g` is integral over `I` and `r ∈ R`, then `φ r * g` is integral over `I`,
* if `g, g'` are integral over `I`, then `g + g'` is integral over `I`.

The first two follow directly from witness manipulation: use `X` for the zero element, and
scale roots by `r` for the scalar multiplication. Closure under addition requires the
determinant / Cayley–Hamilton argument inside the module-finite subalgebra `R[g, g']` and is
not treated here.

Integrality over an ideal is `RingHom.IsIntegralElemOverIdeal`.
-/

@[expose] public section

open Polynomial

/-- The zero element of `S` is integral over any ideal `I ⊂ R`, witnessed by
the polynomial `X`. (Partial component of Stacks `00H4`.) -/
@[stacks 00H4 "Partial: only that 0 is integral over I. Closure under addition, and hence \
the submodule conclusion of 00H4, is not formalized."]
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
integral over `I`. (Partial component of Stacks `00H4`: closure under
`R`-scalar multiplication, with the action expressed through the ring map
`φ`.) -/
@[stacks 00H4 "Partial: only closure under R-scalar multiplication. Closure under addition, \
and hence the submodule conclusion of 00H4, is not formalized."]
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

module

public import StacksFrontier.RingTheory.Koszul.Variables.TermBasis

/-!
# The contracting homotopy of the Koszul complex of the variables

Let `A` be a commutative ring and `E` a linearly ordered type.  This file constructs the
contraction of the Koszul complex of the variables of `A[E]` against a single variable, the
chosen contraction against the smallest variable of the multidegree, and proves that the chosen
contraction is a contracting homotopy in positive degree.  It also introduces the filtration of
`K_j` by monomial degree, identifies its `n`-th step with `I ^ n • K_j`, and shows that the
contraction lowers the filtration by one while the differential raises it by one.

## Main definitions

* `MvPolynomial.variableKoszulContractAt`: Contraction against a single variable.
* `MvPolynomial.variableKoszulChosenContract`: The contracting homotopy of the Koszul complex,
  contracting against the smallest variable of the multidegree.
* `MvPolynomial.variableKoszulFiltration`: The filtration of `K_j` by monomial degree.

## Main results

* `MvPolynomial.variableKoszulChosenContract_homotopy`: The contraction is a homotopy in
  positive degree.
* `MvPolynomial.variableKoszulFiltration_eq_idealPower_smul`: The `n`-th filtration step is
  `I ^ n • K_j`.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace MvPolynomial

/-- Contraction against the variable `e`: the `A`-linear map `⋀^j → ⋀^(j+1)` sending `X^m • e_s`
to `(X^m / X e) • (e ∧ e_s)`, where `X^m / X e` is `variableDivX A E e (X^m)`. -/
noncomputable def variableKoszulContractAt
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
    (e : E) (j : ℕ) :
    (⋀[MvPolynomial E A]^j (E →₀ MvPolynomial E A)) →ₗ[A]
      (⋀[MvPolynomial E A]^(j + 1) (E →₀ MvPolynomial E A)) :=
  (variableKoszulTermBasis A E j).constr A
    (fun p ↦ variableDivX A E e ((MvPolynomial.basisMonomials E A) p.1) •
      koszulWedge (Finsupp.single e 1) j
        ((Finsupp.basisSingleOne (R := MvPolynomial E A)
          (ι := E)).exteriorPower j p.2))

/-- Contraction against `e` sends `X^m • e_s` to `(X^m / X e) • (e ∧ e_s)`. -/
lemma variableKoszulContractAt_termBasis
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
    (e : E) (j : ℕ)
    (p : (E →₀ ℕ) × {s : Finset E // s.card = j}) :
    variableKoszulContractAt A E e j (variableKoszulTermBasis A E j p) =
      variableDivX A E e ((MvPolynomial.basisMonomials E A) p.1) •
        koszulWedge (Finsupp.single e 1) j
          ((Finsupp.basisSingleOne (R := MvPolynomial E A)
            (ι := E)).exteriorPower j p.2) :=
  Module.Basis.constr_basis _ _ _ _

/-- If `m e = 0`, contraction against `e` kills `X^m • e_s`. -/
lemma variableKoszulContractAt_termBasis_zero
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
    (e : E) (j : ℕ)
    (p : (E →₀ ℕ) × {s : Finset E // s.card = j})
    (he : p.1 e = 0) :
    variableKoszulContractAt A E e j (variableKoszulTermBasis A E j p) = 0 := by
  rw [variableKoszulContractAt_termBasis]
  simp only [MvPolynomial.coe_basisMonomials]
  rw [show variableDivX A E e (MvPolynomial.monomial p.1 (1 : A)) = 0 from
    variableMonomial_div_X_eq_zero A E p.1 e he]
  simp

/-- If `e ∈ s`, contraction against `e` kills `X^m • e_s` in positive exterior degree. -/
lemma variableKoszulContractAt_termBasis_zero_of_mem
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
    (e : E) (q : ℕ)
    (p : (E →₀ ℕ) × {s : Finset E // s.card = q + 1})
    (he : e ∈ p.2.1) :
    variableKoszulContractAt A E e (q + 1)
      (variableKoszulTermBasis A E (q + 1) p) = 0 := by
  rw [variableKoszulContractAt_termBasis,
    variableWedge_exteriorBasis_eq_zero_of_mem A E e q p.2 he]
  simp

/-- If `e ∈ s`, contraction against `e` kills `X^m • e_s`. -/
lemma variableKoszulContractAt_termBasis_zero_of_mem'
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
    (e : E) (j : ℕ)
    (p : (E →₀ ℕ) × {s : Finset E // s.card = j})
    (he : e ∈ p.2.1) :
    variableKoszulContractAt A E e j (variableKoszulTermBasis A E j p) = 0 := by
  cases j with
  | zero => simp [Finset.card_eq_zero.mp p.2.2] at he
  | succ j =>
    exact variableKoszulContractAt_termBasis_zero_of_mem A E e j p he

/-- If `m e ≠ 0`, contraction against `e` sends `X^m • e_s` to
`X^(m - single e 1) • (e ∧ e_s)`. -/
lemma variableKoszulContractAt_termBasis_nonzero
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
    (e : E) (j : ℕ)
    (p : (E →₀ ℕ) × {s : Finset E // s.card = j})
    (he : p.1 e ≠ 0) :
    variableKoszulContractAt A E e j (variableKoszulTermBasis A E j p) =
      MvPolynomial.monomial (p.1 - Finsupp.single e 1) (1 : A) •
        koszulWedge (Finsupp.single e 1) j
          ((Finsupp.basisSingleOne (R := MvPolynomial E A)
            (ι := E)).exteriorPower j p.2) := by
  rw [variableKoszulContractAt_termBasis]
  simp only [MvPolynomial.coe_basisMonomials]
  exact congrArg (· • _) (variableMonomial_div_X A E p.1 e he)

/-- If `e ∈ s`, contraction against `e` sends the Koszul differential of `X^m • e_s` back to
`X^m • e_s`. -/
lemma variableKoszulContractAt_d_termBasis_of_mem
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
    (e : E) (q : ℕ)
    (p : (E →₀ ℕ) × {s : Finset E // s.card = q + 1})
    (he : e ∈ p.2.1) :
    variableKoszulContractAt A E e q
        (Koszul.d (variableKoszulDual A E) q
          (variableKoszulTermBasis A E (q + 1) p)) =
      variableKoszulTermBasis A E (q + 1) p := by
  classical
  let k : Fin (q + 1) := (p.2.1.orderIsoOfFin p.2.2).symm ⟨e, he⟩
  have hk : p.2.1.orderEmbOfFin p.2.2 k = e := by
    rw [← p.2.1.coe_orderIsoOfFin_apply]
    simp [k]
  rw [variableKoszul_d_termBasis, map_sum, Finset.sum_eq_single k]
  · rw [map_smul]
    have hme : ((p.1 + Finsupp.single e 1) : E →₀ ℕ) e ≠ 0 := by simp
    rw [hk, variableKoszulContractAt_termBasis_nonzero A E e q _ hme]
    rw [add_tsub_cancel_right]
    have hw := variableWedge_exteriorBasis_erase A E e q p.2 he
    change (-1 : MvPolynomial E A) ^ k.val •
      koszulWedge (Finsupp.single e 1) q
        ((Finsupp.basisSingleOne (R := MvPolynomial E A)
          (ι := E)).exteriorPower q (variableEraseIndex p.2 k)) = _ at hw
    calc
      _ = MvPolynomial.monomial p.1 (1 : A) •
          ((-1 : MvPolynomial E A) ^ k.val •
            koszulWedge (Finsupp.single e 1) q
              ((Finsupp.basisSingleOne (R := MvPolynomial E A)
                (ι := E)).exteriorPower q (variableEraseIndex p.2 k))) := by
                  rw [smul_comm, ← algebraMap_smul (MvPolynomial E A) ((-1 : A) ^ k.val)]
                  simp only [map_pow, map_neg, map_one]
      _ = MvPolynomial.monomial p.1 (1 : A) •
          (Finsupp.basisSingleOne (R := MvPolynomial E A)
            (ι := E)).exteriorPower (q + 1) p.2 := by rw [hw]
      _ = _ := (variableKoszulTermBasis_apply A E (q + 1) p).symm
  · intro k' hk' hne
    have hne' : e ≠ p.2.1.orderEmbOfFin p.2.2 k' := fun h =>
      hne ((p.2.1.orderEmbOfFin p.2.2).injective (h.symm.trans hk.symm))
    have heerase : e ∈ (variableEraseIndex p.2 k').1 :=
      Finset.mem_erase.mpr ⟨hne', he⟩
    rw [map_smul, variableKoszulContractAt_termBasis_zero_of_mem' A E e q _ heerase]
    simp
  · exact fun h => (h (Finset.mem_univ k)).elim

/-- If `e ∈ s`, contraction `h` against `e` satisfies `d h x + h d x = x` for
`x = X^m • e_s`. -/
lemma variableKoszulContractAt_homotopy_termBasis_of_mem
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
    (e : E) (q : ℕ)
    (p : (E →₀ ℕ) × {s : Finset E // s.card = q + 1})
    (he : e ∈ p.2.1) :
    Koszul.d (variableKoszulDual A E) (q + 1)
        (variableKoszulContractAt A E e (q + 1)
          (variableKoszulTermBasis A E (q + 1) p)) +
      variableKoszulContractAt A E e q
        (Koszul.d (variableKoszulDual A E) q
          (variableKoszulTermBasis A E (q + 1) p)) =
      variableKoszulTermBasis A E (q + 1) p := by
  rw [variableKoszulContractAt_termBasis_zero_of_mem A E e q p he,
    map_zero, zero_add, variableKoszulContractAt_d_termBasis_of_mem A E e q p he]

/-- If `e ∉ s`, contraction against `e` sends the Koszul differential of `X^m • e_s` to
`(X^m / X e) • (e ∧ d e_s)`. -/
lemma variableKoszulContractAt_d_termBasis_of_not_mem
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
    (e : E) (q : ℕ)
    (p : (E →₀ ℕ) × {s : Finset E // s.card = q + 1})
    (he : e ∉ p.2.1) :
    variableKoszulContractAt A E e q
        (Koszul.d (variableKoszulDual A E) q
          (variableKoszulTermBasis A E (q + 1) p)) =
      variableDivX A E e ((MvPolynomial.basisMonomials E A) p.1) •
        koszulWedge (Finsupp.single e 1) q
          (Koszul.d (variableKoszulDual A E) q
            ((Finsupp.basisSingleOne (R := MvPolynomial E A)
              (ι := E)).exteriorPower (q + 1) p.2)) := by
  classical
  rw [variableKoszul_d_termBasis, map_sum,
    variableKoszul_d_exteriorBasis, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  let f := p.2.1.orderEmbOfFin p.2.2 k
  have hef : e ≠ f := fun h => he (h ▸ p.2.1.orderEmbOfFin_mem p.2.2 k)
  rw [map_smul, variableKoszulContractAt_termBasis]
  simp only [MvPolynomial.coe_basisMonomials]
  have hmon : MvPolynomial.monomial (p.1 + Finsupp.single f 1) (1 : A) =
      MvPolynomial.X f * MvPolynomial.monomial p.1 (1 : A) := by
    simp [MvPolynomial.monomial_add_single, mul_comm]
  rw [hmon, variableDivX_X_mul_other A E e f hef]
  simp only [variableKoszulDual_single, map_smul]
  rw [← algebraMap_smul (MvPolynomial E A) ((-1 : A) ^ k.val)]
  simp only [map_pow, map_neg, map_one, smul_smul]
  congr 1
  ring

/-- If `e ∉ s` and `m e ≠ 0`, contraction `h` against `e` satisfies `d h x + h d x = x` for
`x = X^m • e_s`. -/
lemma variableKoszulContractAt_homotopy_termBasis_of_not_mem
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
    (e : E) (q : ℕ)
    (p : (E →₀ ℕ) × {s : Finset E // s.card = q + 1})
    (he : e ∉ p.2.1) (hm : p.1 e ≠ 0) :
    Koszul.d (variableKoszulDual A E) (q + 1)
        (variableKoszulContractAt A E e (q + 1)
          (variableKoszulTermBasis A E (q + 1) p)) +
      variableKoszulContractAt A E e q
        (Koszul.d (variableKoszulDual A E) q
          (variableKoszulTermBasis A E (q + 1) p)) =
      variableKoszulTermBasis A E (q + 1) p := by
  classical
  rw [variableKoszulContractAt_termBasis_nonzero A E e (q + 1) p hm,
    map_smul, variableKoszulContractAt_d_termBasis_of_not_mem A E e q p he]
  simp only [MvPolynomial.coe_basisMonomials]
  rw [show variableDivX A E e (MvPolynomial.monomial p.1 (1 : A)) =
      MvPolynomial.monomial (p.1 - Finsupp.single e 1) (1 : A) from
    variableMonomial_div_X A E p.1 e hm]
  rw [← smul_add]
  rw [koszul_d_wedge_add_wedge_d]
  rw [variableKoszulDual_single]
  rw [variableKoszulTermBasis_apply]
  simp only [MvPolynomial.coe_basisMonomials, smul_smul]
  congr 1
  calc
    MvPolynomial.monomial (p.1 - Finsupp.single e 1) (1 : A) *
        MvPolynomial.X e =
      MvPolynomial.monomial
        (p.1 - Finsupp.single e 1 + Finsupp.single e 1) (1 : A) := by
          simp [MvPolynomial.monomial_add_single]
    _ = MvPolynomial.monomial p.1 (1 : A) := by
      rw [variableExponent_sub_single_add p.1 e hm]

/-- If `e ∉ s`, the multidegree of `(m, s)` at `e` is `m e`. -/
lemma variableKoszulMultidegree_apply_of_not_mem {E : Type v}
    (j : ℕ) (p : (E →₀ ℕ) × {s : Finset E // s.card = j})
    (e : E) (he : e ∉ p.2.1) : variableKoszulMultidegree j p e = p.1 e := by
  classical
  simp [variableKoszulMultidegree, Finsupp.single_apply,
    Finset.sum_ite_eq', he]

/-- If `e ∉ s` and the multidegree of `(m, s)` is nonzero at `e`, then `m e ≠ 0`. -/
lemma variableKoszulMultidegree_coefficient_ne_zero_of_not_mem
    {E : Type v} (j : ℕ)
    (p : (E →₀ ℕ) × {s : Finset E // s.card = j})
    (e : E) (he : e ∉ p.2.1)
    (hα : variableKoszulMultidegree j p e ≠ 0) : p.1 e ≠ 0 := by
  rwa [variableKoszulMultidegree_apply_of_not_mem j p e he] at hα

/-- If the multidegree of `(m, s)` is nonzero at `e`, contraction `h` against `e` satisfies
`d h x + h d x = x` for `x = X^m • e_s`. -/
lemma variableKoszulContractAt_homotopy_termBasis_of_multidegree
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
    (e : E) (q : ℕ)
    (p : (E →₀ ℕ) × {s : Finset E // s.card = q + 1})
    (hα : variableKoszulMultidegree (q + 1) p e ≠ 0) :
    Koszul.d (variableKoszulDual A E) (q + 1)
        (variableKoszulContractAt A E e (q + 1)
          (variableKoszulTermBasis A E (q + 1) p)) +
      variableKoszulContractAt A E e q
        (Koszul.d (variableKoszulDual A E) q
          (variableKoszulTermBasis A E (q + 1) p)) =
      variableKoszulTermBasis A E (q + 1) p := by
  by_cases he : e ∈ p.2.1
  · exact variableKoszulContractAt_homotopy_termBasis_of_mem A E e q p he
  · exact variableKoszulContractAt_homotopy_termBasis_of_not_mem A E e q p he
      (variableKoszulMultidegree_coefficient_ne_zero_of_not_mem (q + 1) p e he hα)

/-- The `A`-linear map `⋀^j → ⋀^(j+1)` sending `X^m • e_s` to its contraction against the
smallest variable in the support of the multidegree of `(m, s)`, and to `0` when that
multidegree is zero. -/
noncomputable def variableKoszulChosenContract
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E] (j : ℕ) :
    (⋀[MvPolynomial E A]^j (E →₀ MvPolynomial E A)) →ₗ[A]
      (⋀[MvPolynomial E A]^(j + 1) (E →₀ MvPolynomial E A)) :=
  (variableKoszulTermBasis A E j).constr A (fun p ↦
    if h : variableKoszulMultidegree j p = 0 then 0 else
      variableKoszulContractAt A E
        ((variableKoszulMultidegree j p).support.min'
          (Finset.nonempty_iff_ne_empty.mpr
            (mt Finsupp.support_eq_empty.mp h))) j
        (variableKoszulTermBasis A E j p))

/-- The value of `variableKoszulChosenContract` on the basis element indexed by `p`. -/
lemma variableKoszulChosenContract_termBasis
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E] (j : ℕ)
    (p : (E →₀ ℕ) × {s : Finset E // s.card = j}) :
    variableKoszulChosenContract A E j (variableKoszulTermBasis A E j p) =
      if h : variableKoszulMultidegree j p = 0 then 0 else
        variableKoszulContractAt A E
          ((variableKoszulMultidegree j p).support.min'
            (Finset.nonempty_iff_ne_empty.mpr
              (mt Finsupp.support_eq_empty.mp h))) j
          (variableKoszulTermBasis A E j p) :=
  Module.Basis.constr_basis _ _ _ _

/-- If the multidegree of `p` is nonzero, `variableKoszulChosenContract` agrees on the basis
element indexed by `p` with contraction against the smallest variable of that multidegree. -/
lemma variableKoszulChosenContract_termBasis_eq_at
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E] (j : ℕ)
    (p : (E →₀ ℕ) × {s : Finset E // s.card = j})
    (hα : variableKoszulMultidegree j p ≠ 0) :
    variableKoszulChosenContract A E j (variableKoszulTermBasis A E j p) =
      variableKoszulContractAt A E
        ((variableKoszulMultidegree j p).support.min'
          (Finset.nonempty_iff_ne_empty.mpr
            (mt Finsupp.support_eq_empty.mp hα))) j
        (variableKoszulTermBasis A E j p) := by
  rw [variableKoszulChosenContract_termBasis]
  simp only [dite_eq_right hα]

/-- If the multidegree of `p` is nonzero, `variableKoszulChosenContract` agrees on the Koszul
differential of the basis element indexed by `p` with contraction against the smallest
variable of the multidegree of `p`. -/
lemma variableKoszulChosenContract_d_termBasis_eq_at
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E] (q : ℕ)
    (p : (E →₀ ℕ) × {s : Finset E // s.card = q + 1})
    (hα : variableKoszulMultidegree (q + 1) p ≠ 0) :
    let e := (variableKoszulMultidegree (q + 1) p).support.min'
      (Finset.nonempty_iff_ne_empty.mpr
        (mt Finsupp.support_eq_empty.mp hα))
    variableKoszulChosenContract A E q
        (Koszul.d (variableKoszulDual A E) q
          (variableKoszulTermBasis A E (q + 1) p)) =
      variableKoszulContractAt A E e q
        (Koszul.d (variableKoszulDual A E) q
          (variableKoszulTermBasis A E (q + 1) p)) := by
  classical
  dsimp only
  rw [variableKoszul_d_termBasis, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_smul, map_smul, variableKoszulChosenContract_termBasis]
  rw [variableKoszulMultidegree_d]
  simp only [dite_eq_right hα]

/-- The total degree of the multidegree of `(m, s)` is `m.degree + j`. -/
lemma variableKoszulMultidegree_degree {E : Type v}
    [LinearOrder E] (j : ℕ)
    (p : (E →₀ ℕ) × {s : Finset E // s.card = j}) :
    (variableKoszulMultidegree j p).degree = p.1.degree + j := by
  classical
  simp [variableKoszulMultidegree, map_add, map_sum, p.2.2]

/-- In positive exterior degree, the multidegree of a basis element is nonzero. -/
lemma variableKoszulMultidegree_ne_zero {E : Type v}
    [LinearOrder E] (j : ℕ) (hj : 0 < j)
    (p : (E →₀ ℕ) × {s : Finset E // s.card = j}) :
    variableKoszulMultidegree j p ≠ 0 := by
  intro h
  have hdegree := congrArg Finsupp.degree h
  rw [variableKoszulMultidegree_degree, map_zero] at hdegree
  omega

/-- The chosen contraction `h` satisfies `d h x + h d x = x` on every basis element `x` of
positive exterior degree. -/
lemma variableKoszulChosenContract_homotopy_termBasis
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E] (q : ℕ)
    (p : (E →₀ ℕ) × {s : Finset E // s.card = q + 1}) :
    Koszul.d (variableKoszulDual A E) (q + 1)
        (variableKoszulChosenContract A E (q + 1)
          (variableKoszulTermBasis A E (q + 1) p)) +
      variableKoszulChosenContract A E q
        (Koszul.d (variableKoszulDual A E) q
          (variableKoszulTermBasis A E (q + 1) p)) =
      variableKoszulTermBasis A E (q + 1) p := by
  let α := variableKoszulMultidegree (q + 1) p
  have hα : α ≠ 0 := variableKoszulMultidegree_ne_zero (q + 1) (by omega) p
  have hs : α.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (mt Finsupp.support_eq_empty.mp hα)
  let e := α.support.min' hs
  have he : α e ≠ 0 := Finsupp.mem_support_iff.mp (Finset.min'_mem _ _)
  rw [variableKoszulChosenContract_termBasis_eq_at A E (q + 1) p hα,
    variableKoszulChosenContract_d_termBasis_eq_at A E q p hα]
  exact variableKoszulContractAt_homotopy_termBasis_of_multidegree A E e q p he

/-- The chosen contraction `h` is a contracting homotopy in positive degree:
`d h x + h d x = x` for every `x ∈ ⋀^(q+1)`. -/
lemma variableKoszulChosenContract_homotopy
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E] (q : ℕ)
    (x : ⋀[MvPolynomial E A]^(q + 1) (E →₀ MvPolynomial E A)) :
    Koszul.d (variableKoszulDual A E) (q + 1)
        (variableKoszulChosenContract A E (q + 1) x) +
      variableKoszulChosenContract A E q
        (Koszul.d (variableKoszulDual A E) q x) = x := by
  let f : (⋀[MvPolynomial E A]^(q + 1) (E →₀ MvPolynomial E A)) →ₗ[A]
      (⋀[MvPolynomial E A]^(q + 1) (E →₀ MvPolynomial E A)) :=
    ((Koszul.d (variableKoszulDual A E) (q + 1)).restrictScalars A).comp
        (variableKoszulChosenContract A E (q + 1)) +
      (variableKoszulChosenContract A E q).comp
        ((Koszul.d (variableKoszulDual A E) q).restrictScalars A)
  have hf : f = LinearMap.id :=
    (variableKoszulTermBasis A E (q + 1)).ext
      (variableKoszulChosenContract_homotopy_termBasis A E q)
  exact LinearMap.congr_fun hf x

/-- The `A`-submodule of `⋀^j (E →₀ A[E])` spanned by the basis elements `X^m • e_s` with
`n ≤ m.degree`. -/
noncomputable def variableKoszulFiltration
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
    (j n : ℕ) :
    Submodule A (⋀[MvPolynomial E A]^j (E →₀ MvPolynomial E A)) :=
  Submodule.span A
    (Set.range (fun p : {p : (E →₀ ℕ) × {s : Finset E // s.card = j} //
      n ≤ p.1.degree} ↦ variableKoszulTermBasis A E j p.1))

/-- An `A`-linear map sending the basis elements of degree at least `n` into a filtration step
sends that filtration step of the source into it. -/
private theorem map_mem_filtration_of_termBasis
    {A : Type u} [CommRing A] {E : Type v} [LinearOrder E] {j k : ℕ} (n n' : ℕ)
    (f : (⋀[MvPolynomial E A]^j (E →₀ MvPolynomial E A)) →ₗ[A]
      (⋀[MvPolynomial E A]^k (E →₀ MvPolynomial E A)))
    (hf : ∀ p : (E →₀ ℕ) × {s : Finset E // s.card = j}, n ≤ p.1.degree →
      f (variableKoszulTermBasis A E j p) ∈ variableKoszulFiltration A E k n')
    {x : ⋀[MvPolynomial E A]^j (E →₀ MvPolynomial E A)}
    (hx : x ∈ variableKoszulFiltration A E j n) : f x ∈ variableKoszulFiltration A E k n' := by
  have hsub : variableKoszulFiltration A E j n ≤
      Submodule.comap f (variableKoszulFiltration A E k n') :=
    Submodule.span_le.mpr (by rintro _ ⟨p, rfl⟩; exact hf p.1 p.2)
  exact hsub hx

/-- If `n + 1 ≤ m.degree`, the contraction of the basis element indexed by `(m, s)` lies in
the `n`-th filtration step. -/
lemma variableKoszulContractBasis_mem_filtration
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
    (j n : ℕ) (p : (E →₀ ℕ) × {s : Finset E // s.card = j})
    (hp : n + 1 ≤ p.1.degree) :
    variableKoszulContractBasis A E j p ∈
      variableKoszulFiltration A E (j + 1) n := by
  classical
  unfold variableKoszulContractBasis
  let α := variableKoszulMultidegree j p
  by_cases hα : α = 0
  · dsimp only [α] at hα
    simpa only [dite_eq_left hα] using
      (Submodule.zero_mem (variableKoszulFiltration A E (j + 1) n))
  · have hsupport : α.support.Nonempty := by
      by_contra h
      exact hα (Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp h))
    dsimp only [α] at hα hsupport
    simp only [dite_eq_right hα]
    let e := α.support.min' hsupport
    by_cases he : e ∈ p.2.1
    · dsimp only [e, α] at he
      simpa only [dite_eq_left he] using
        (Submodule.zero_mem (variableKoszulFiltration A E (j + 1) n))
    · have he' :
          (variableKoszulMultidegree j p).support.min' hsupport ∉ p.2.1 := by
        simpa only [e, α] using he
      simp only [dite_eq_right he']
      apply Submodule.smul_mem
      apply Submodule.subset_span
      let t : {s : Finset E // s.card = j + 1} :=
        ⟨insert e p.2.1, by simp [Finset.card_insert_of_notMem he, p.2.2]⟩
      have heα : α e ≠ 0 := Finsupp.mem_support_iff.mp (Finset.min'_mem _ _)
      have hem : p.1 e ≠ 0 := by
        rwa [variableKoszulMultidegree_apply_of_not_mem j p e he] at heα
      have hdeg := variableExponent_degree_sub_single p.1 e hem
      refine ⟨⟨(p.1 - Finsupp.single e 1, t), ?_⟩, rfl⟩
      show n ≤ (p.1 - Finsupp.single e 1).degree
      omega

/-- `variableKoszulContract` maps the `(n + 1)`-st filtration step of `⋀^j` into the `n`-th
filtration step of `⋀^(j+1)`. -/
lemma variableKoszulContract_maps_filtration
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
    (j n : ℕ) (x : ⋀[MvPolynomial E A]^j (E →₀ MvPolynomial E A))
    (hx : x ∈ variableKoszulFiltration A E j (n + 1)) :
    variableKoszulContract A E j x ∈ variableKoszulFiltration A E (j + 1) n :=
  map_mem_filtration_of_termBasis _ _ _ (fun p hp ↦ by
    rw [variableKoszulContract_termBasis]
    exact variableKoszulContractBasis_mem_filtration A E j n p hp) hx

/-- The `n`-th filtration step is contained in `I ^ n • ⋀^j`, where `I` is the ideal of
variables. -/
lemma variableKoszulFiltration_mem_idealPower_smul
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
    (j n : ℕ) (x : ⋀[MvPolynomial E A]^j (E →₀ MvPolynomial E A))
    (hx : x ∈ variableKoszulFiltration A E j n) :
    x ∈ (Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ n) •
      (⊤ : Submodule (MvPolynomial E A)
        (⋀[MvPolynomial E A]^j (E →₀ MvPolynomial E A))) := by
  let P := MvPolynomial E A
  let I : Ideal P := Ideal.span (Set.range (MvPolynomial.X : E → P))
  have hsub : variableKoszulFiltration A E j n ≤
      ((I ^ n) • (⊤ : Submodule P (⋀[P]^j (E →₀ P)))).restrictScalars A := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    show variableKoszulTermBasis A E j p.1 ∈ I ^ n •
      (⊤ : Submodule P (⋀[P]^j (E →₀ P)))
    rw [variableKoszulTermBasis_apply]
    have hm : (MvPolynomial.basisMonomials E A) p.1.1 ∈ I ^ n := by
      show MvPolynomial.monomial p.1.1 (1 : A) ∈
        MvPolynomial.idealOfVars E A ^ n
      by_cases hA : (1 : A) = 0
      · simp [hA]
      · exact (MvPolynomial.monomial_mem_pow_idealOfVars_iff n p.1.1 hA).mpr p.2
    exact Submodule.smul_mem_smul hm (by simp)
  exact hsub hx

/-- Each filtration step is stable under multiplication by polynomials. -/
lemma variableKoszulFiltration_smul_mem
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
    (j n : ℕ) (r : MvPolynomial E A)
    (x : ⋀[MvPolynomial E A]^j (E →₀ MvPolynomial E A))
    (hx : x ∈ variableKoszulFiltration A E j n) :
    r • x ∈ variableKoszulFiltration A E j n := by
  induction r using MvPolynomial.induction_on' generalizing x with
  | monomial m a =>
    change x ∈ Submodule.span A _ at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨p, rfl⟩ := hy
      have hdeg : n ≤ (m + p.1.1).degree := by
        simp only [map_add]
        omega
      have hmem : variableKoszulTermBasis A E j
          (m + p.1.1, p.1.2) ∈ variableKoszulFiltration A E j n :=
        Submodule.subset_span ⟨⟨(m + p.1.1, p.1.2), hdeg⟩, rfl⟩
      have heq : MvPolynomial.monomial m a •
          variableKoszulTermBasis A E j p.1 =
          a • variableKoszulTermBasis A E j (m + p.1.1, p.1.2) := by
        rw [variableKoszulTermBasis_apply, variableKoszulTermBasis_apply]
        simp only [coe_basisMonomials, exteriorPower.coe_basis, Finsupp.coe_basisSingleOne]
        rw [← algebraMap_smul (MvPolynomial E A) a]
        simp [smul_smul, MvPolynomial.C_mul_monomial]
      rw [heq]
      exact (variableKoszulFiltration A E j n).smul_mem a hmem
    | zero => simp
    | add x y hx hy ihx ihy =>
      simpa only [smul_add] using (variableKoszulFiltration A E j n).add_mem ihx ihy
    | smul a x hx ih =>
      rw [smul_comm]
      exact (variableKoszulFiltration A E j n).smul_mem a ih
  | add p q hp hq =>
    simpa only [add_smul] using
      (variableKoszulFiltration A E j n).add_mem (hp x hx) (hq x hx)

/-- If `n ≤ m.degree`, then `X^m • x` lies in the `n`-th filtration step for every `x`. -/
lemma variableMonomial_smul_mem_filtration
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
    (j n : ℕ) (m : E →₀ ℕ) (hm : n ≤ m.degree)
    (x : ⋀[MvPolynomial E A]^j (E →₀ MvPolynomial E A)) :
    MvPolynomial.monomial m (1 : A) • x ∈ variableKoszulFiltration A E j n := by
  let b := (Finsupp.basisSingleOne (R := MvPolynomial E A) (ι := E)).exteriorPower j
  have hx : x ∈ Submodule.span (MvPolynomial E A) (Set.range b) := by
    rw [b.span_eq]
    trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨s, rfl⟩ := hy
    have hbase : variableKoszulTermBasis A E j (m, s) ∈
        variableKoszulFiltration A E j n :=
      Submodule.subset_span ⟨⟨(m, s), hm⟩, rfl⟩
    show MvPolynomial.monomial m (1 : A) •
      (Finsupp.basisSingleOne (R := MvPolynomial E A) (ι := E)).exteriorPower j s ∈
        variableKoszulFiltration A E j n
    simpa only [variableKoszulTermBasis_apply,
      MvPolynomial.coe_basisMonomials] using hbase
  | zero => simp
  | add x y hx hy ihx ihy =>
    simpa only [smul_add] using (variableKoszulFiltration A E j n).add_mem ihx ihy
  | smul r x hx ih =>
    rw [smul_comm]
    exact variableKoszulFiltration_smul_mem A E j n r _ ih

/-- If `r ∈ I ^ n`, where `I` is the ideal of variables, then `r • x` lies in the `n`-th
filtration step for every `x`. -/
lemma variableIdealPower_smul_mem_filtration
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
    (j n : ℕ) (r : MvPolynomial E A)
    (hr : r ∈ (Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ n :
      Ideal (MvPolynomial E A)))
    (x : ⋀[MvPolynomial E A]^j (E →₀ MvPolynomial E A)) :
    r • x ∈ variableKoszulFiltration A E j n := by
  classical
  rw [MvPolynomial.as_sum r, Finset.sum_smul]
  apply Submodule.sum_mem
  intro m hm
  have hdegree : n ≤ m.degree :=
    (MvPolynomial.mem_pow_idealOfVars_iff n r).mp hr m hm
  have hmon := variableMonomial_smul_mem_filtration A E j n m hdegree x
  have heq : MvPolynomial.monomial m (r.coeff m) • x =
      r.coeff m • (MvPolynomial.monomial m (1 : A) • x) := by
    calc
      _ = (MvPolynomial.C (r.coeff m) *
          MvPolynomial.monomial m (1 : A)) • x := by
        simp [MvPolynomial.C_mul_monomial]
      _ = _ := by
        rw [mul_smul]
        exact algebraMap_smul (MvPolynomial E A) (r.coeff m) _
  rw [heq]
  exact (variableKoszulFiltration A E j n).smul_mem _ hmon

/-- `I ^ n • ⋀^j` is contained in the `n`-th filtration step, where `I` is the ideal of
variables. -/
lemma variableIdealPower_smul_mem_variableKoszulFiltration
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
    (j n : ℕ) (x : ⋀[MvPolynomial E A]^j (E →₀ MvPolynomial E A))
    (hx : x ∈
      (Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ n) •
        (⊤ : Submodule (MvPolynomial E A)
          (⋀[MvPolynomial E A]^j (E →₀ MvPolynomial E A)))) :
    x ∈ variableKoszulFiltration A E j n := by
  refine Submodule.smul_induction_on hx (fun r hr y _ ↦ ?_) fun _ _ ↦ Submodule.add_mem _
  exact variableIdealPower_smul_mem_filtration A E j n r hr y

/-- The `n`-th filtration step is `I ^ n • ⋀^j`, where `I` is the ideal of variables. -/
lemma variableKoszulFiltration_eq_idealPower_smul
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
    (j n : ℕ) :
    variableKoszulFiltration A E j n =
      (((Ideal.span (Set.range (MvPolynomial.X : E → MvPolynomial E A)) ^ n) •
        (⊤ : Submodule (MvPolynomial E A)
          (⋀[MvPolynomial E A]^j (E →₀ MvPolynomial E A)))).restrictScalars A) :=
  le_antisymm (fun x hx ↦ variableKoszulFiltration_mem_idealPower_smul A E j n x hx)
    (fun x hx ↦ variableIdealPower_smul_mem_variableKoszulFiltration A E j n x hx)

/-- The chosen contraction maps the `(n + 1)`-st filtration step of `⋀^j` into the `n`-th
filtration step of `⋀^(j+1)`. -/
lemma variableKoszulChosenContract_maps_filtration
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
    (j n : ℕ) (x : ⋀[MvPolynomial E A]^j (E →₀ MvPolynomial E A))
    (hx : x ∈ variableKoszulFiltration A E j (n + 1)) :
    variableKoszulChosenContract A E j x ∈
      variableKoszulFiltration A E (j + 1) n := by
  refine map_mem_filtration_of_termBasis _ _ _ (fun p hp ↦ ?_) hx
  rw [variableKoszulChosenContract_termBasis]
  split_ifs with hα
  · exact Submodule.zero_mem _
  · let e := (variableKoszulMultidegree j p).support.min'
      (Finset.nonempty_iff_ne_empty.mpr (mt Finsupp.support_eq_empty.mp hα))
    by_cases he : e ∈ p.2.1
    · rw [variableKoszulContractAt_termBasis_zero_of_mem' A E e j p he]
      exact Submodule.zero_mem _
    · by_cases hm : p.1 e = 0
      · rw [variableKoszulContractAt_termBasis_zero A E e j p hm]
        exact Submodule.zero_mem _
      · rw [variableKoszulContractAt_termBasis_nonzero A E e j p hm]
        have hdeg := variableExponent_degree_sub_single p.1 e hm
        exact variableMonomial_smul_mem_filtration A E (j + 1) n
          (p.1 - Finsupp.single e 1) (by omega) _

/-- The Koszul differential maps the `n`-th filtration step of `⋀^(j+1)` into the
`(n + 1)`-st filtration step of `⋀^j`. -/
lemma variableKoszul_d_maps_filtration
    (A : Type u) [CommRing A] (E : Type v) [LinearOrder E]
    (j n : ℕ)
    (x : ⋀[MvPolynomial E A]^(j + 1) (E →₀ MvPolynomial E A))
    (hx : x ∈ variableKoszulFiltration A E (j + 1) n) :
    Koszul.d (variableKoszulDual A E) j x ∈
      variableKoszulFiltration A E j (n + 1) := by
  refine map_mem_filtration_of_termBasis _ _
    ((Koszul.d (variableKoszulDual A E) j).restrictScalars A) (fun p hp ↦ ?_) hx
  change Koszul.d (variableKoszulDual A E) j (variableKoszulTermBasis A E (j + 1) p) ∈ _
  rw [variableKoszul_d_termBasis]
  refine Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  have hdegree : n + 1 ≤
      (p.1 + Finsupp.single (p.2.1.orderEmbOfFin p.2.2 k) 1).degree := by
    simp only [map_add, Finsupp.degree_single]
    omega
  exact ⟨⟨_, hdegree⟩, rfl⟩

end MvPolynomial

end

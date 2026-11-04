module

import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.FieldTheory.Finite.Basic
public import StacksFrontier.RingTheory.Polynomial.BivariateWeightedDegree
public import StacksFrontier.RingTheory.Polynomial.GaloisResolvent
public import StacksFrontier.RingTheory.Polynomial.PlaneCurveIntersection

/-!
# Points of the factors of the Galois resolvent

Auxiliary facts for counting points on the factors of the Galois resolvent of a plane curve over
a finite field.

## Main results

* `FiniteField.exists_algebraMap_eq_of_pow_card_eq`: an element fixed by the `q`-power map lies
  in the image of the field with `q` elements.
* `Polynomial.Bivariate.WeightedDegreeLE.of_dvd`: a divisor of a nonzero polynomial of total
  degree at most `T` has total degree at most `T`.
* `Polynomial.Bivariate.existsUnique_factor_root`: over a point where the resolvent splits into
  distinct linear factors, each root lies on exactly one factor, and is a simple point of it.
* `Polynomial.evalEval_twistedComp`: the twisted composite at a point.
* `Polynomial.Bivariate.weightedDegreeLE_zero_twistedComp`, `Polynomial.natDegree_twistedComp_le`:
  degree bounds for the twisted composite.
-/

@[expose] public section

open Polynomial Finset
open scoped Polynomial.Bivariate

/-- **Fixed points of the Frobenius are rational.** In an extension `L` of a finite field `F`
with `q` elements, an element `x` with `x ^ q = x` lies in the image of `F`. -/
theorem FiniteField.exists_algebraMap_eq_of_pow_card_eq {F L : Type*} [Field F] [Fintype F]
    [Field L] [Algebra F L] {x : L} (hx : x ^ Fintype.card F = x) :
    ∃ a : F, algebraMap F L a = x := by
  classical
  by_contra hne
  push Not at hne
  set q := Fintype.card F
  have hq : 1 < q := Fintype.one_lt_card
  set p : L[X] := X ^ q - X
  have hp0 : p ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero L hq
  set S := Finset.univ.image (algebraMap F L)
  have hS : S.card = q := by
    rw [Finset.card_image_of_injective _ (algebraMap F L).injective, Finset.card_univ]
  have hsub : insert x S ⊆ p.roots.toFinset := by
    intro y hy
    rw [Multiset.mem_toFinset, mem_roots hp0, IsRoot, eval_sub, eval_pow, eval_X, sub_eq_zero]
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hx
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hy
      rw [← map_pow, FiniteField.pow_card]
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (fun h => by
    obtain ⟨a, -, ha⟩ := Finset.mem_image.mp h; exact hne a ha), hS] at hcard
  have := (Multiset.toFinset_card_le _).trans (card_roots' p)
  rw [natDegree_sub_eq_left_of_natDegree_lt (by simpa using hq), natDegree_X_pow] at this
  omega

namespace Polynomial.Bivariate

variable {R : Type*} [CommRing R]

/-- If `g` has weighted degree at most `T` for the weights `1` on `X` and `1` on `Y`, then the
total degree of `equivMvPolynomial R g` is at most `T`. -/
theorem totalDegree_equivMvPolynomial_le_of_weightedDegreeLE {g : R[X][Y]} {T : ℕ}
    (hg : WeightedDegreeLE 1 T g) : (equivMvPolynomial R g).totalDegree ≤ T := by
  rw [MvPolynomial.totalDegree]
  refine Finset.sup_le fun s hs => ?_
  have hs' : s = Finsupp.single 0 (s 0) + Finsupp.single 1 (s 1) := by
    ext i; fin_cases i <;> simp
  have hcoeff := MvPolynomial.mem_support_iff.mp hs
  rw [hs', coeff_equivMvPolynomial] at hcoeff
  have hj : g.coeff (s 1) ≠ 0 := fun h => hcoeff (by rw [h, coeff_zero])
  have hi : s 0 ≤ (g.coeff (s 1)).natDegree := le_natDegree_of_ne_zero hcoeff
  have := hg (s 1) hj
  rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two]
  omega

/-- A polynomial `g` has weighted degree, for the weights `1` on `X` and `1` on `Y`, at most the
total degree of `equivMvPolynomial R g`. -/
theorem weightedDegreeLE_one_totalDegree (g : R[X][Y]) :
    WeightedDegreeLE 1 (equivMvPolynomial R g).totalDegree g := fun j hj => by
  simpa using natDegree_coeff_add_le_totalDegree g j hj

/-- A divisor of a nonzero polynomial of total degree at most `T` has total degree at most
`T`. -/
theorem WeightedDegreeLE.of_dvd {K : Type*} [Field K] {Ψ Φ : K[X][X]} (hΦ : Φ ≠ 0) (h : Ψ ∣ Φ)
    {T : ℕ} (hT : WeightedDegreeLE 1 T Φ) : WeightedDegreeLE 1 T Ψ := by
  obtain ⟨Q, rfl⟩ := h
  have hQ : Q ≠ 0 := right_ne_zero_of_mul hΦ
  have hΨ : Ψ ≠ 0 := left_ne_zero_of_mul hΦ
  have htot := totalDegree_equivMvPolynomial_le_of_weightedDegreeLE hT
  have hne : ∀ g : K[X][X], g ≠ 0 → equivMvPolynomial K g ≠ 0 := fun g hg => by
    rwa [ne_eq, map_eq_zero_iff _ (equivMvPolynomial K).injective]
  rw [map_mul, MvPolynomial.totalDegree_mul_of_isDomain (hne _ hΨ) (hne _ hQ)] at htot
  exact (weightedDegreeLE_one_totalDegree Ψ).mono (by omega)

end Polynomial.Bivariate

namespace Polynomial.Bivariate

/-- **Each root lies on exactly one factor, simply.** If `∏_{Ψ ∈ 𝒪} Ψ = Φ` and the fibre of `Φ`
over `a` splits into distinct linear factors `X - t i`, then each `t i` is a root of exactly one
`Ψ(a, ·)`, and a simple one. -/
theorem existsUnique_factor_root {K : Type*} [Field K] {𝒪 : Finset K[X][X]} {Φ : K[X][X]}
    (hΦ : ∏ Ψ ∈ 𝒪, Ψ = Φ) {a : K} {ι : Type*} [Fintype ι] {t : ι → K}
    (ht : Function.Injective t) (hspl : Φ.map (evalRingHom a) = ∏ i, (X - C (t i))) (i : ι) :
    (∃! Ψ, Ψ ∈ 𝒪 ∧ Ψ.evalEval a (t i) = 0) ∧
      ∀ Ψ ∈ 𝒪, Ψ.evalEval a (t i) = 0 → (derivative Ψ).evalEval a (t i) ≠ 0 := by
  classical
  set P : K[X][X] → K[X] := fun Ψ => Ψ.map (evalRingHom a)
  have hprod : ∏ Ψ ∈ 𝒪, P Ψ = ∏ j, (X - C (t j)) := by
    rw [← hspl, ← hΦ, Polynomial.map_prod]
  have hne : ∏ j, (X - C (t j)) ≠ 0 := (monic_prod_of_monic _ _ fun j _ => monic_X_sub_C _).ne_zero
  have hPne : ∀ Ψ ∈ 𝒪, P Ψ ≠ 0 := fun Ψ hΨ h =>
    hne (hprod ▸ Finset.prod_eq_zero hΨ h)
  -- multiplicities add up to one
  have hmult_prod : ∀ (s : Finset K[X][X]), s ⊆ 𝒪 →
      (∏ Ψ ∈ s, P Ψ).rootMultiplicity (t i) = ∑ Ψ ∈ s, (P Ψ).rootMultiplicity (t i) := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => simp
    | insert Ψ s hΨ ih =>
      have hs' : s ⊆ 𝒪 := (Finset.subset_insert _ _).trans hs
      rw [Finset.prod_insert hΨ, Finset.sum_insert hΨ, rootMultiplicity_mul, ih hs']
      exact mul_ne_zero (hPne Ψ (hs (Finset.mem_insert_self _ _)))
        (Finset.prod_ne_zero_iff.mpr fun Ψ' h => hPne Ψ' (hs' h))
  have hone : ∑ Ψ ∈ 𝒪, (P Ψ).rootMultiplicity (t i) = 1 := by
    rw [← hmult_prod 𝒪 subset_rfl, hprod, ← count_roots, Finset.prod_eq_multiset_prod,
      show (Finset.univ.val.map fun j => X - C (t j)) =
        (Finset.univ.val.map t).map (fun x => X - C x) by rw [Multiset.map_map]; rfl,
      roots_multiset_prod_X_sub_C]
    rw [Multiset.count_eq_one_of_mem (Multiset.Nodup.map ht Finset.univ.nodup)
      (Multiset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)]
  have hroot : ∀ Ψ, Ψ.evalEval a (t i) = 0 ↔ (P Ψ).IsRoot (t i) := fun Ψ => by
    rw [IsRoot, map_evalRingHom_eval]
  refine ⟨?_, fun Ψ hΨ h0 h1 => ?_⟩
  · obtain ⟨Ψ, hΨ, hpos⟩ : ∃ Ψ ∈ 𝒪, 0 < (P Ψ).rootMultiplicity (t i) := by
      by_contra! h
      rw [Finset.sum_eq_zero fun Ψ hΨ => Nat.le_zero.mp (h Ψ hΨ)] at hone
      exact zero_ne_one hone
    refine ⟨Ψ, ⟨hΨ, (hroot Ψ).mpr ((rootMultiplicity_pos (hPne Ψ hΨ)).mp hpos)⟩, ?_⟩
    rintro Ψ' ⟨hΨ', h'⟩
    by_contra hne'
    have h1 : 0 < (P Ψ').rootMultiplicity (t i) :=
      (rootMultiplicity_pos (hPne Ψ' hΨ')).mpr ((hroot Ψ').mp h')
    have : (P Ψ).rootMultiplicity (t i) + (P Ψ').rootMultiplicity (t i) ≤
        ∑ Ψ ∈ 𝒪, (P Ψ).rootMultiplicity (t i) := by
      rw [← Finset.sum_pair (f := fun Ψ => (P Ψ).rootMultiplicity (t i)) (Ne.symm hne')]
      exact Finset.sum_le_sum_of_subset (by
        intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hΨ
        · rw [Finset.mem_singleton.mp hx]; exact hΨ')
    omega
  · have hlt : 1 < (P Ψ).rootMultiplicity (t i) := by
      rw [one_lt_rootMultiplicity_iff_isRoot (hPne Ψ hΨ)]
      refine ⟨(hroot Ψ).mp h0, ?_⟩
      rw [IsRoot, show derivative (P Ψ) = (derivative Ψ).map (evalRingHom a) from
        derivative_map _ _, map_evalRingHom_eval]
      exact h1
    have := Finset.single_le_sum (f := fun Ψ => (P Ψ).rootMultiplicity (t i))
      (fun _ _ => Nat.zero_le _) hΨ
    omega

end Polynomial.Bivariate

namespace Polynomial

/-- **The twisted composite at a point.** If `fr a = a` and `R(a, u) = Δ(a) fr(u)`, then the
twisted composite `Δ^{deg Ψ} Ψ^{fr}(R / Δ)` takes the value `Δ(a)^{deg Ψ} fr(Ψ(a, u))` at
`(a, u)`. -/
theorem evalEval_twistedComp {K : Type*} [Field K] (fr : K →+* K) (Ψ R : K[X][X]) (Δ : K[X])
    {a u : K} (ha : fr a = a) (hR : R.evalEval a u = Δ.eval a * fr u) :
    (twistedComp fr Ψ R Δ).evalEval a u = Δ.eval a ^ Ψ.natDegree * fr (Ψ.evalEval a u) := by
  have hcoef : ∀ k, ((Ψ.coeff k).map fr).eval a = fr ((Ψ.coeff k).eval a) := fun k => by
    rw [eval_map, eval, hom_eval₂, RingHom.comp_id, ha]
  have hΨ : Ψ.evalEval a u = ∑ k ∈ range (Ψ.natDegree + 1), (Ψ.coeff k).eval a * u ^ k := by
    rw [← map_evalRingHom_eval, eval_eq_sum_range' (Nat.lt_succ_of_le natDegree_map_le)]
    simp [coeff_map]
  rw [twistedComp, evalEval_finsetSum, hΨ, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ Ψ.natDegree := Finset.mem_range_succ_iff.mp hk
  rw [evalEval_mul, evalEval_C, evalEval_pow, hR, eval_mul, eval_pow, hcoef, map_mul, map_pow,
    mul_pow, show Δ.eval a ^ Ψ.natDegree = Δ.eval a ^ (Ψ.natDegree - k) * Δ.eval a ^ k by
      rw [← pow_add, Nat.sub_add_cancel hk']]
  ring

end Polynomial

namespace Polynomial.Bivariate

/-- **Coefficient degrees of the twisted composite.** If the coefficients of `Ψ` and `R` have
degree at most `DΨ` and `DR` and `Δ` has degree at most `DΔ`, then the coefficients of
`twistedComp fr Ψ R Δ` have degree at most `Ψ.natDegree * (DΔ + DR) + DΨ`. -/
theorem weightedDegreeLE_zero_twistedComp {K : Type*} [Field K] (fr : K →+* K) {Ψ R : K[X][X]}
    {Δ : K[X]} {DΨ DR DΔ : ℕ} (hΨ : WeightedDegreeLE 0 DΨ Ψ) (hR : WeightedDegreeLE 0 DR R)
    (hΔ : Δ.natDegree ≤ DΔ) :
    WeightedDegreeLE 0 (Ψ.natDegree * (DΔ + DR) + DΨ) (twistedComp fr Ψ R Δ) := by
  refine WeightedDegreeLE.sum _ fun k hk => ?_
  have hk' : k ≤ Ψ.natDegree := Finset.mem_range_succ_iff.mp hk
  have hC : (Δ ^ (Ψ.natDegree - k) * (Ψ.coeff k).map fr).natDegree ≤
      (Ψ.natDegree - k) * DΔ + DΨ :=
    (natDegree_mul_le).trans (Nat.add_le_add
      ((natDegree_pow_le).trans (Nat.mul_le_mul_left _ hΔ))
      (natDegree_map_le.trans (hΨ.coeff_natDegree_le k)))
  refine ((WeightedDegreeLE.C hC).mul (hR.pow k)).mono ?_
  have : (Ψ.natDegree - k) * DΔ ≤ Ψ.natDegree * DΔ := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have : k * DR ≤ Ψ.natDegree * DR := Nat.mul_le_mul_right _ hk'
  nlinarith

end Polynomial.Bivariate

namespace Polynomial

/-- **The `Y`-degree of the twisted composite.** The degree of `twistedComp fr Ψ R Δ` is at most
`Ψ.natDegree * R.natDegree`. -/
theorem natDegree_twistedComp_le {K : Type*} [Field K] (fr : K →+* K) (Ψ R : K[X][X])
    (Δ : K[X]) : (twistedComp fr Ψ R Δ).natDegree ≤ Ψ.natDegree * R.natDegree := by
  refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  have hk' : k ≤ Ψ.natDegree := Finset.mem_range_succ_iff.mp hk
  refine (natDegree_C_mul_le _ _).trans ((natDegree_pow_le).trans ?_)
  exact Nat.mul_le_mul_right _ hk'

end Polynomial

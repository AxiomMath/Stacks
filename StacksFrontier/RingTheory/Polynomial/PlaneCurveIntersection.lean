module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.Data.Set.Card

/-!
# Common zeros of two plane curves

Let `K` be a field and let `f, g ∈ K[X, Y]` with `f` irreducible and `f ∤ g`. Then `f` and `g`
have only finitely many common zeros in `K²`, and their number is bounded in terms of the degrees
of `f` and `g` alone. We prove the crude bound `2 D³` when every coefficient of `f` and `g`, viewed
as polynomials in `Y` over `K[X]`, has degree at most `D` and both have `Y`-degree at most `D`.
This is a weak form of Bézout's theorem: the `X`-coordinate of a common zero is a root of the
resultant `Res_Y(f, g)`, which is nonzero by Gauss's lemma, and above each such root the fibre of
`f` (or of `g`) is a nonzero polynomial of degree at most `D`.

## Main results

* `Polynomial.Bivariate.card_le_of_evalEval_eq_zero_of_not_dvd`: the bound for bivariate
  polynomials `K[X][Y]` and a finite set of common zeros.
* `MvPolynomial.ncard_zeroSet_inter_le_of_not_dvd`: the bound `2 d³` for `f, g ∈ K[X₀, X₁]` of
  total degree at most `d`.
-/

@[expose] public section

open Polynomial
open scoped Polynomial.Bivariate

namespace Polynomial

/-- The determinant of a square matrix of polynomials whose entries have degree at most `D`
has degree at most `D` times the size of the matrix. -/
theorem natDegree_det_le_card_mul {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (M : Matrix n n R[X]) {D : ℕ} (h : ∀ i j, (M i j).natDegree ≤ D) :
    M.det.natDegree ≤ Fintype.card n * D := by
  rw [Matrix.det_apply]
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  refine natDegree_mul_le.trans ?_
  rw [natDegree_intCast, zero_add]
  refine (natDegree_prod_le _ _).trans ?_
  have := Finset.sum_le_card_nsmul Finset.univ (fun i => (M (σ i) i).natDegree) D
    fun i _ => h _ _
  rwa [Finset.card_univ, smul_eq_mul] at this

/-- The resultant of two polynomials over `R[X]` whose coefficients have degree at most `D` has
degree at most `(m + n) D`. -/
theorem natDegree_resultant_le_add_mul {R : Type*} [CommRing R] (f g : R[X][Y]) (m n : ℕ)
    {D : ℕ} (hf : ∀ i, (f.coeff i).natDegree ≤ D) (hg : ∀ i, (g.coeff i).natDegree ≤ D) :
    (resultant f g m n).natDegree ≤ (m + n) * D := by
  refine (natDegree_det_le_card_mul (D := D) _ fun i j => ?_).trans (by simp)
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
    simp only [sylvester, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right] <;>
    split_ifs <;> simp [hf, hg]

end Polynomial

namespace Polynomial.Bivariate

variable {K : Type*} [Field K]

/-- The fibre of a bivariate polynomial `h` over `x = a` vanishes identically if and only if
`X - a` divides `h`. -/
theorem map_evalRingHom_eq_zero_iff {h : K[X][Y]} {a : K} :
    h.map (evalRingHom a) = 0 ↔ C (X - C a) ∣ h := by
  rw [C_dvd_iff_dvd_coeff, Polynomial.ext_iff]
  simp [dvd_iff_isRoot]

/-- If `f` is irreducible and `f ∤ g`, the fibres of `f` and `g` over a point never both vanish
identically. -/
theorem map_evalRingHom_ne_zero_or {f g : K[X][Y]} (hf : Irreducible f) (hfg : ¬ f ∣ g) (a : K) :
    f.map (evalRingHom a) ≠ 0 ∨ g.map (evalRingHom a) ≠ 0 := by
  by_contra! h
  rw [map_evalRingHom_eq_zero_iff, map_evalRingHom_eq_zero_iff] at h
  have hu : ¬ IsUnit (C (X - C a) : K[X][Y]) := mt isUnit_C.mp (not_isUnit_X_sub_C a)
  obtain ⟨u, hu'⟩ := (hf.dvd_iff.mp h.1).resolve_left hu
  exact hfg (Units.mul_right_dvd.mp (hu' ▸ h.2))

/-- A polynomial of degree at most `D` has at most `D` distinct roots. -/
private theorem card_roots_toFinset_le [DecidableEq K] (p : K[X]) {D : ℕ} (h : p.natDegree ≤ D) :
    p.roots.toFinset.card ≤ D :=
  (Multiset.toFinset_card_le _).trans ((card_roots' _).trans h)

/-- A finite set of points, each lying over a point of `A` and on the zero set of a nonzero
polynomial of degree at most `D` attached to that point, has at most `#A * D` elements. -/
theorem card_le_card_mul_of_fibres [DecidableEq K] (A : Finset K) (T : Finset (K × K))
    (h : K → K[X]) {D : ℕ} (hA : ∀ P ∈ T, P.1 ∈ A ∧ h P.1 ≠ 0 ∧ (h P.1).IsRoot P.2)
    (hD : ∀ a ∈ A, (h a).natDegree ≤ D) : T.card ≤ A.card * D := by
  classical
  have hT : T ⊆ A.biUnion fun a => {a} ×ˢ (h a).roots.toFinset := by
    intro P hP
    obtain ⟨h1, h2, h3⟩ := hA P hP
    exact Finset.mem_biUnion.mpr ⟨P.1, h1, Finset.mem_product.mpr
      ⟨Finset.mem_singleton_self _, Multiset.mem_toFinset.mpr ((mem_roots h2).mpr h3)⟩⟩
  refine (Finset.card_le_card hT).trans (Finset.card_biUnion_le.trans ?_)
  rw [← smul_eq_mul]
  refine Finset.sum_le_card_nsmul A _ D fun a ha => ?_
  rw [Finset.card_product, Finset.card_singleton, one_mul]
  exact card_roots_toFinset_le _ (hD a ha)

end Polynomial.Bivariate

namespace Polynomial.Bivariate

variable {K : Type*} [Field K]

/-- If `f` is irreducible of positive `Y`-degree and `f ∤ g`, the resultant `Res_Y(f, g)` is
nonzero. -/
theorem resultant_ne_zero_of_irreducible_of_not_dvd {f g : K[X][Y]} (hf : Irreducible f)
    (hpos : f.natDegree ≠ 0) (hfg : ¬ f ∣ g) : resultant f g ≠ 0 := by
  let L := FractionRing K[X]
  have hinj : Function.Injective (algebraMap K[X] L) := IsFractionRing.injective _ _
  have hprim : f.IsPrimitive := hf.isPrimitive hpos
  have hfL : Irreducible (f.map (algebraMap K[X] L)) :=
    hprim.irreducible_iff_irreducible_map_fraction_map.mp hf
  have hcop : IsCoprime (f.map (algebraMap K[X] L)) (g.map (algebraMap K[X] L)) :=
    (Irreducible.coprime_iff_not_dvd hfL).mpr
      (hfg ∘ (hprim.dvd_iff_fraction_map_dvd_fraction_map L).mpr)
  have hres := mt resultant_eq_zero_iff.mp (fun h => h.2 hcop)
  rw [natDegree_map_eq_of_injective hinj, natDegree_map_eq_of_injective hinj,
    resultant_map_map] at hres
  exact fun h => hres (by rw [h, map_zero])

/-- **A weak Bézout bound.** Let `f, g ∈ K[X][Y]` with `f` irreducible and `f ∤ g`, and suppose
that `f` and `g` have `Y`-degree at most `D` and coefficients of degree at most `D`. Then any
finite set of common zeros of `f` and `g` in `K²` has at most `2 D³` elements. -/
theorem card_le_of_evalEval_eq_zero_of_not_dvd [DecidableEq K] {f g : K[X][Y]}
    (hf : Irreducible f) (hfg : ¬ f ∣ g) {D : ℕ} (hfD : ∀ i, (f.coeff i).natDegree ≤ D)
    (hgD : ∀ i, (g.coeff i).natDegree ≤ D) (hfn : f.natDegree ≤ D) (hgn : g.natDegree ≤ D)
    (T : Finset (K × K)) (hT : ∀ P ∈ T, f.evalEval P.1 P.2 = 0 ∧ g.evalEval P.1 P.2 = 0) :
    T.card ≤ 2 * D ^ 3 := by
  by_cases h0 : f.natDegree = 0
  · obtain ⟨p, rfl⟩ : ∃ p, f = C p := ⟨_, eq_C_of_natDegree_eq_zero h0⟩
    have hp0 : p ≠ 0 := C_ne_zero.mp hf.ne_zero
    refine (card_le_card_mul_of_fibres p.roots.toFinset T (fun a => g.map (evalRingHom a))
      (D := D) (fun P hP => ?_) (fun a _ => natDegree_map_le.trans hgn)).trans ?_
    · have h1 : p.eval P.1 = 0 := by simpa [evalEval_C] using (hT P hP).1
      refine ⟨Multiset.mem_toFinset.mpr ((mem_roots hp0).mpr h1),
        (map_evalRingHom_ne_zero_or hf hfg P.1).resolve_left (not_not.mpr (by simp [h1])), ?_⟩
      simpa [IsRoot, map_evalRingHom_eval] using (hT P hP).2
    · have hp : p.natDegree ≤ D := by simpa using hfD 0
      calc p.roots.toFinset.card * D ≤ D * D :=
            Nat.mul_le_mul_right _ (card_roots_toFinset_le _ hp)
        _ ≤ 2 * D ^ 3 := by
            rcases Nat.eq_zero_or_pos D with rfl | hD
            · simp
            · nlinarith [Nat.one_le_pow 1 D hD]
  · have hr := resultant_ne_zero_of_irreducible_of_not_dvd hf h0 hfg
    obtain ⟨u, v, -, -, huv⟩ :=
      exists_mul_add_mul_eq_C_resultant f g le_rfl le_rfl (Or.inl h0)
    refine (card_le_card_mul_of_fibres (resultant f g).roots.toFinset T
      (fun a => f.map (evalRingHom a)) (D := D) (fun P hP => ?_)
      (fun a _ => natDegree_map_le.trans hfn)).trans ?_
    · have h1 : (resultant f g).eval P.1 = 0 := by
        simpa [evalEval_add, evalEval_mul, evalEval_C, (hT P hP).1, (hT P hP).2] using
          (congrArg (evalEval P.1 P.2) huv).symm
      refine ⟨Multiset.mem_toFinset.mpr ((mem_roots hr).mpr h1), fun hz => ?_, ?_⟩
      · obtain ⟨w, hw⟩ := (map_evalRingHom_eq_zero_iff).mp hz
        have hw0 : w ≠ 0 := by rintro rfl; exact hf.ne_zero (by simpa using hw)
        apply h0
        rw [hw, natDegree_mul (C_ne_zero.mpr (X_sub_C_ne_zero _)) hw0, natDegree_C, zero_add]
        exact natDegree_eq_zero_of_isUnit
          ((hf.isUnit_or_isUnit hw).resolve_left (mt isUnit_C.mp (not_isUnit_X_sub_C _)))
      · simpa [IsRoot, map_evalRingHom_eval] using (hT P hP).1
    · have hdeg : (resultant f g).natDegree ≤ (D + D) * D :=
        (natDegree_resultant_le_add_mul f g _ _ hfD hgD).trans
          (Nat.mul_le_mul_right _ (Nat.add_le_add hfn hgn))
      calc (resultant f g).roots.toFinset.card * D ≤ (D + D) * D * D :=
            Nat.mul_le_mul_right _ (card_roots_toFinset_le _ hdeg)
        _ = 2 * D ^ 3 := by ring

end Polynomial.Bivariate

namespace Polynomial.Bivariate

variable {R : Type*} [CommRing R]

/-- Evaluating `equivMvPolynomial R f` at `p` is evaluating `f` at `(p 0, p 1)`. -/
theorem eval_equivMvPolynomial (f : R[X][Y]) (p : Fin 2 → R) :
    MvPolynomial.eval p (equivMvPolynomial R f) = f.evalEval (p 0) (p 1) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp [hf, hg, evalEval_add]
  | monomial n a =>
    induction a using Polynomial.induction_on' with
    | add a b ha hb => simp [map_add, evalEval_add, ha, hb]
    | monomial m c =>
      simp [equivMvPolynomial, ← C_mul_X_pow_eq_monomial, evalEval_mul, evalEval_pow,
        evalEval_X, evalEval_C]

/-- The coefficient of `X₀ⁱ X₁ʲ` in `equivMvPolynomial R f` is the coefficient of `Xⁱ` in the
coefficient of `Yʲ` in `f`. -/
theorem coeff_equivMvPolynomial (f : R[X][Y]) (i j : ℕ) :
    (equivMvPolynomial R f).coeff (Finsupp.single 0 i + Finsupp.single 1 j) =
      (f.coeff j).coeff i := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp [hf, hg]
  | monomial n a =>
    induction a using Polynomial.induction_on' with
    | add a b ha hb => simp [map_add, ha, hb]
    | monomial m c =>
      have hmon : equivMvPolynomial R (monomial n (monomial m c)) =
          MvPolynomial.monomial (Finsupp.single 0 m + Finsupp.single 1 n) c := by
        simp [equivMvPolynomial, ← C_mul_X_pow_eq_monomial, MvPolynomial.monomial_eq, mul_assoc]
      rw [hmon, MvPolynomial.coeff_monomial, coeff_monomial]
      by_cases hn : n = j
      · subst hn
        rw [if_pos rfl, coeff_monomial]
        by_cases hm : m = i
        · simp [hm]
        · rw [if_neg, if_neg hm]
          intro h
          exact hm (by simpa using congrArg (· 0) h)
      · rw [if_neg hn, coeff_zero, if_neg]
        intro h
        exact hn (by simpa using congrArg (· 1) h)

/-- The coefficients of `f`, and its `Y`-degree, are bounded by the total degree of the
corresponding polynomial in two variables. -/
theorem natDegree_coeff_add_le_totalDegree (f : R[X][Y]) (j : ℕ) (hj : f.coeff j ≠ 0) :
    (f.coeff j).natDegree + j ≤ (equivMvPolynomial R f).totalDegree := by
  have h := coeff_equivMvPolynomial f (f.coeff j).natDegree j
  rw [coeff_natDegree] at h
  have hne : (equivMvPolynomial R f).coeff
      (Finsupp.single 0 (f.coeff j).natDegree + Finsupp.single 1 j) ≠ 0 := by
    rw [h]
    exact leadingCoeff_ne_zero.mpr hj
  simpa [Finsupp.sum_add_index, Finsupp.sum_single_index] using
    MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hne)

/-- The degree of each coefficient of `f` is at most the total degree of the corresponding
polynomial in two variables. -/
theorem natDegree_coeff_le_totalDegree (f : R[X][Y]) (j : ℕ) :
    (f.coeff j).natDegree ≤ (equivMvPolynomial R f).totalDegree := by
  by_cases hj : f.coeff j = 0
  · simp [hj]
  · exact (Nat.le_add_right _ _).trans (natDegree_coeff_add_le_totalDegree f j hj)

/-- The `Y`-degree of `f` is at most the total degree of the corresponding polynomial in two
variables. -/
theorem natDegree_le_totalDegree (f : R[X][Y]) :
    f.natDegree ≤ (equivMvPolynomial R f).totalDegree := by
  by_cases hf : f = 0
  · simp [hf]
  · exact (Nat.le_add_left _ _).trans
      (natDegree_coeff_add_le_totalDegree f _ (leadingCoeff_ne_zero.mpr hf))

end Polynomial.Bivariate

namespace MvPolynomial

open Polynomial.Bivariate

variable {K : Type*} [Field K]

/-- **A weak Bézout bound.** If `f, g ∈ K[X₀, X₁]` have total degree at most `d`, `f` is
irreducible and `f ∤ g`, then `f` and `g` have finitely many common zeros in `K²`, at most
`2 d³` of them. -/
theorem finite_zeroSet_inter_of_not_dvd {f g : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hfg : ¬ f ∣ g) {d : ℕ} (hdf : f.totalDegree ≤ d) (hdg : g.totalDegree ≤ d) :
    {p : Fin 2 → K | eval p f = 0 ∧ eval p g = 0}.Finite ∧
      {p : Fin 2 → K | eval p f = 0 ∧ eval p g = 0}.ncard ≤ 2 * d ^ 3 := by
  classical
  set e := equivMvPolynomial K
  set Z := {p : Fin 2 → K | eval p f = 0 ∧ eval p g = 0}
  have key : ∀ T : Finset (Fin 2 → K), ↑T ⊆ Z → T.card ≤ 2 * d ^ 3 := by
    intro T hT
    have hf' : Irreducible (e.symm f) := (MulEquiv.irreducible_iff e.symm.toMulEquiv).mpr hf
    have hfg' : ¬ e.symm f ∣ e.symm g := fun h => hfg (by simpa using map_dvd e h)
    have hdf' : (e (e.symm f)).totalDegree ≤ d := by simpa using hdf
    have hdg' : (e (e.symm g)).totalDegree ≤ d := by simpa using hdg
    have hinj : Function.Injective fun p : Fin 2 → K => (p 0, p 1) := by
      intro p q h
      simp only [Prod.mk.injEq] at h
      funext i
      fin_cases i <;> simp [h.1, h.2]
    rw [← Finset.card_image_of_injective T hinj]
    refine card_le_of_evalEval_eq_zero_of_not_dvd hf' hfg'
      (fun i => (natDegree_coeff_le_totalDegree _ i).trans hdf')
      (fun i => (natDegree_coeff_le_totalDegree _ i).trans hdg')
      ((natDegree_le_totalDegree _).trans hdf') ((natDegree_le_totalDegree _).trans hdg') _ ?_
    simp only [Finset.mem_image]
    rintro _ ⟨p, hp, rfl⟩
    have := hT hp
    simp only [Set.mem_setOf_eq, Z] at this
    rw [← eval_equivMvPolynomial, ← eval_equivMvPolynomial]
    simpa [e] using this
  have hfin : Z.Finite := by
    by_contra hinf
    obtain ⟨T, hT, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (2 * d ^ 3 + 1)
    have := key T hT
    omega
  refine ⟨hfin, ?_⟩
  rw [← hfin.coe_toFinset, Set.ncard_coe_finset]
  exact key _ (by simp)

end MvPolynomial

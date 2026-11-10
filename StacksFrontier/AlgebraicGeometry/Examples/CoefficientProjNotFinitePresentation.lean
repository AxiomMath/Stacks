module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Examples.CoefficientProjFamily
public import StacksFrontier.AlgebraicGeometry.ProjClosedImmersion.Basic

/-!
# The coefficientwise projective family is not of finite presentation

Fix a variable `X j` and an ideal `I` of `R` which is the ideal the family `K` attaches to the
monomial `X j`, and which it attaches to no power of `X j` without `I` containing it. The chart
`D₊(X j)` of the family is then a quotient of a polynomial ring over `R` whose kernel maps onto
`I` under the evaluation of every variable at zero, and the family is not locally of finite
presentation when `I` is not finitely generated.

## Main definitions

* `Stacks.CoefficientProj.chartHom`: the presentation of the chart `D₊(X j)` as a quotient of a
  polynomial ring over `R` in `m` variables.
* `Stacks.CoefficientProj.chartEval`: the specialization of the chart sending `X j` to `1` and
  every other variable to `0`, with values in `R ⧸ I`.

## Main results

* `Stacks.CoefficientProj.surjective_chartHom`: the presentation is surjective.
* `Stacks.CoefficientProj.map_ker_chartHom`: evaluating the kernel of the presentation at zero
  gives back `I`.
* `Stacks.CoefficientProj.not_locallyOfFinitePresentation`: the family is not locally of finite
  presentation when `I` is not finitely generated.
-/

@[expose] public noncomputable section

namespace Stacks.CoefficientProj

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open Stacks.GradedModel

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {m : ℕ} {R : Type u} [CommRing R] (K : (Fin (m + 1) →₀ ℕ) → Ideal R)
  (j : Fin (m + 1)) (I : Ideal R)

/-! ### The specialization of the chart at `X j = 1` -/

/-- Evaluating `X j` at `1` and every other variable at `0`, with values in `R ⧸ I`. -/
def evalAway : MvPolynomial (Fin (m + 1)) R →ₐ[R] R ⧸ I :=
  MvPolynomial.aeval fun i => if i = j then 1 else 0

/-- The specialization `evalAway` sends `X j` to `1` and every other variable to `0`. -/
@[simp]
theorem evalAway_X (i : Fin (m + 1)) :
    evalAway j I (X i) = if i = j then 1 else 0 := by simp [evalAway]

/-- The coefficient ideal of `K` lies in the kernel of `evalAway` when `I` contains every ideal
`K` attaches to a power of `X j`. -/
theorem coefficientIdeal_le_ker_evalAway (hKj : ∀ k : ℕ, K (Finsupp.single j k) ≤ I) :
    coefficientIdeal K ≤ RingHom.ker (evalAway j I).toRingHom := by
  classical
  rw [coefficientIdeal, Ideal.span_le]
  rintro q ⟨d, a, ha, rfl⟩
  simp only [SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [evalAway, aeval_monomial]
  by_cases hd : ∀ i, i ≠ j → d i = 0
  · have hds : d = Finsupp.single j (d j) := by
      ext i
      by_cases hij : i = j
      · subst hij; simp
      · simp [Ne.symm hij, hd i hij]
    have hprod : (d.prod fun i k => (if i = j then (1 : R ⧸ I) else 0) ^ k) = 1 := by
      refine Finset.prod_eq_one fun i hi => ?_
      have hij : i = j := by_contra fun hij => Finsupp.mem_support_iff.mp hi (hd i hij)
      simp [hij]
    rw [hprod, mul_one, Ideal.Quotient.algebraMap_eq]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hKj (d j) (hds ▸ ha))
  · push Not at hd
    obtain ⟨i, hij, hdi⟩ := hd
    have hprod : (d.prod fun i k => (if i = j then (1 : R ⧸ I) else 0) ^ k) = 0 := by
      refine Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hdi) ?_
      simp [hij, hdi]
    rw [hprod, mul_zero]

/-- The specialization of the graded quotient at `X j = 1`, the other variables at `0`. -/
def quotientEval (hKj : ∀ k : ℕ, K (Finsupp.single j k) ≤ I) :
    (MvPolynomial (Fin (m + 1)) R ⧸ coefficientIdeal K) →ₐ[R] R ⧸ I :=
  Ideal.Quotient.liftₐ _ (evalAway j I) fun _ hp =>
    RingHom.mem_ker.mp (coefficientIdeal_le_ker_evalAway K j I hKj hp)

/-- On the class of a polynomial, `quotientEval` is `evalAway`. -/
@[simp]
theorem quotientEval_mk (hKj : ∀ k : ℕ, K (Finsupp.single j k) ≤ I)
    (p : MvPolynomial (Fin (m + 1)) R) :
    quotientEval K j I hKj (Ideal.Quotient.mk _ p) = evalAway j I p := rfl

/-- The specialization `quotientEval` sends the class of `X j` to `1`. -/
theorem quotientEval_mkX (hKj : ∀ k : ℕ, K (Finsupp.single j k) ≤ I) :
    quotientEval K j I hKj (mkX K j) = 1 := by simp [mkX]

/-- The specialization of the chart `D₊(X j)`, obtained from `Stacks.CoefficientProj.quotientEval`
by inverting `X j`, which it sends to `1`. -/
def chartEval (hKj : ∀ k : ℕ, K (Finsupp.single j k) ≤ I) :
    Away (projGrading K) (mkX K j) →+* R ⧸ I :=
  (Localization.awayLift (quotientEval K j I hKj).toRingHom (mkX K j)
      (isUnit_iff_exists_inv.mpr ⟨1, by rw [mul_one]; exact quotientEval_mkX K j I hKj⟩)).comp
    (algebraMap (Away (projGrading K) (mkX K j)) (Localization.Away (mkX K j)))

/-- On a fraction `b / X j ^ n` of the chart, `chartEval` is the value of `quotientEval` at `b`. -/
theorem chartEval_mk (hKj : ∀ k : ℕ, K (Finsupp.single j k) ≤ I) (n : ℕ)
    (b : MvPolynomial (Fin (m + 1)) R ⧸ coefficientIdeal K) (hb : b ∈ projGrading K (n • 1)) :
    chartEval K j I hKj (Away.mk (projGrading K) (mkX_mem_one K j) n b hb) =
      quotientEval K j I hKj b := by
  rw [chartEval, RingHom.comp_apply]
  change Localization.awayLift _ _ _ (Away.mk (projGrading K) (mkX_mem_one K j) n b hb).val = _
  rw [Away.val_mk, Localization.awayLift_mk (quotientEval K j I hKj).toRingHom (mkX K j) b 1
    (by rw [mul_one]; exact quotientEval_mkX K j I hKj) n, one_pow, mul_one]
  rfl

/-! ### The chart as a quotient of a polynomial ring -/

/-- The degree-zero part of the quotient contains the image of a constant. -/
private theorem algebraMap_mem_projGrading_zero (r : R) :
    algebraMap R (MvPolynomial (Fin (m + 1)) R ⧸ coefficientIdeal K) r ∈ projGrading K 0 :=
  mk_mem_quotientGrading ((mem_homogeneousSubmodule 0 _).2 (isHomogeneous_C _ r))

/-- A constant, read in the chart, is the fraction with that numerator and denominator `1`. -/
theorem algebraMap_chart_eq (r : R) :
    algebraMap R (Away (projGrading K) (mkX K j)) r =
      Away.mk (projGrading K) (mkX_mem_one K j) 0
        (algebraMap R (MvPolynomial (Fin (m + 1)) R ⧸ coefficientIdeal K) r)
        (by simpa using algebraMap_mem_projGrading_zero K r) := by
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk, HomogeneousLocalization.val_algebraMap, IsScalarTower.algebraMap_apply R
      (MvPolynomial (Fin (m + 1)) R ⧸ coefficientIdeal K) (Localization.Away (mkX K j)),
    ← Localization.mk_one_eq_algebraMap, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp⟩

/-- The presentation of the chart `D₊(X j)`: the `i`-th variable goes to the fraction
`X (j.succAbove i) / X j`. -/
def chartHom : MvPolynomial (Fin m) R →ₐ[R] Away (projGrading K) (mkX K j) :=
  MvPolynomial.aeval fun k =>
    Away.mk (projGrading K) (mkX_mem_one K j) 1 (mkX K (j.succAbove k))
      (by simpa using mkX_mem_one K (j.succAbove k))

/-- The presentation `chartHom` sends the `k`-th variable to `X (j.succAbove k) / X j`. -/
@[simp]
theorem chartHom_X (k : Fin m) :
    chartHom K j (X k) =
      Away.mk (projGrading K) (mkX_mem_one K j) 1 (mkX K (j.succAbove k))
        (by simpa using mkX_mem_one K (j.succAbove k)) := by
  simp [chartHom]

/-- The presentation of the chart is the chart of projective space followed by the quotient
map. -/
theorem chartHom_eq :
    (chartHom K j).toRingHom =
      (Away.map (quotientMkGraded K) (X j)).comp
        (((Stacks.SymmetricAway.toChart j).toRingHom).comp
          (MvPolynomial.rename ((finSuccAboveEquiv j : Fin m ≃ _) ·) :
            MvPolynomial (Fin m) R →ₐ[R] MvPolynomial {x : Fin (m + 1) // x ≠ j} R).toRingHom) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_)
  · change chartHom K j (C r) = Away.map (quotientMkGraded K) (X j)
      (Stacks.SymmetricAway.toChart j (MvPolynomial.rename _ (C r)))
    rw [MvPolynomial.algHom_C, algebraMap_chart_eq, rename_C, Stacks.SymmetricAway.toChart_C,
      Stacks.SymmetricAway.algebraMap_eq_mkChart]
    simp only [Stacks.SymmetricAway.mkChart, Away.map_mk]
    rfl
  · change chartHom K j (X k) = Away.map (quotientMkGraded K) (X j)
      (Stacks.SymmetricAway.toChart j (MvPolynomial.rename _ (X k)))
    rw [chartHom_X, rename_X, Stacks.SymmetricAway.toChart_X]
    simp only [Stacks.SymmetricAway.mkChart, Away.map_mk]
    rfl

/-- The presentation `chartHom` of the chart `D₊(X j)` is surjective. -/
theorem surjective_chartHom : Function.Surjective (chartHom K j) := by
  intro z
  obtain ⟨y, hy⟩ := Proj.surjective_awayMap (quotientMkGraded K)
    (.of_surjective (surjective_quotientMkGraded K)) Nat.one_pos (X j)
    ((mem_homogeneousSubmodule 1 _).2 (isHomogeneous_X R j)) z
  obtain ⟨q, rfl⟩ := Stacks.SymmetricAway.toChart_surjective j y
  obtain ⟨p, rfl⟩ := MvPolynomial.rename_surjective ((finSuccAboveEquiv j : Fin m ≃ _) ·)
    (finSuccAboveEquiv j).surjective q
  exact ⟨p, (RingHom.congr_fun (chartHom_eq K j) p).trans hy⟩

/-! ### The kernel of the presentation -/

/-- Evaluating every variable of the presentation at zero. -/
def evalZero : MvPolynomial (Fin m) R →ₐ[R] R :=
  MvPolynomial.aeval fun _ => 0

/-- The specialization of the chart, read through the presentation, is the evaluation of every
variable at zero followed by the quotient map of `I`. -/
theorem chartEval_comp_chartHom (hKj : ∀ k : ℕ, K (Finsupp.single j k) ≤ I) :
    (chartEval K j I hKj).comp (chartHom K j).toRingHom =
      (Ideal.Quotient.mk I).comp (evalZero (m := m) (R := R)).toRingHom := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_)
  · change chartEval K j I hKj (chartHom K j (C r)) = Ideal.Quotient.mk I (evalZero (C r))
    rw [MvPolynomial.algHom_C, algebraMap_chart_eq, chartEval_mk, evalZero, aeval_C]
    simp [AlgHom.commutes, Ideal.Quotient.algebraMap_eq]
  · change chartEval K j I hKj (chartHom K j (X k)) = Ideal.Quotient.mk I (evalZero (X k))
    rw [chartHom_X, chartEval_mk, evalZero, aeval_X, map_zero, mkX, quotientEval_mk,
      evalAway_X, ite_eq_right (Fin.succAbove_ne j k)]

/-- A constant from `I`, read in the chart, vanishes. -/
theorem algebraMap_chart_eq_zero (hIK : I ≤ K (Finsupp.single j 1)) {a : R} (ha : a ∈ I) :
    algebraMap R (Away (projGrading K) (mkX K j)) a = 0 := by
  rw [algebraMap_chart_eq]
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk, HomogeneousLocalization.val_zero, ← Localization.mk_zero 1,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨⟨mkX K j, 1, pow_one _⟩, ?_⟩
  have h0 : mkX K j * algebraMap R (MvPolynomial (Fin (m + 1)) R ⧸ coefficientIdeal K) a = 0 := by
    rw [show algebraMap R (MvPolynomial (Fin (m + 1)) R ⧸ coefficientIdeal K) a
        = Ideal.Quotient.mk (coefficientIdeal K) (C a) from rfl, ← map_mul]
    refine Ideal.Quotient.eq_zero_iff_mem.mpr ?_
    rw [show (X j : MvPolynomial (Fin (m + 1)) R) * C a = monomial (Finsupp.single j 1) a by
      rw [mul_comm, C_mul_X_eq_monomial]]
    exact monomial_mem_coefficientIdeal K (hIK ha)
  simpa using h0

/-- **Evaluating the kernel of the presentation at zero gives back `I`.** -/
theorem map_ker_chartHom (hKj : ∀ k : ℕ, K (Finsupp.single j k) ≤ I)
    (hIK : I ≤ K (Finsupp.single j 1)) :
    (RingHom.ker (chartHom K j).toRingHom).map (evalZero (m := m) (R := R)).toRingHom = I := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun x hx => ?_) fun a ha => ?_
  · have h := RingHom.congr_fun (chartEval_comp_chartHom K j I hKj) x
    simp only [RingHom.comp_apply] at h
    rw [RingHom.mem_ker.mp hx, map_zero] at h
    exact Ideal.mem_comap.mpr (Ideal.Quotient.eq_zero_iff_mem.mp h.symm)
  · have hker : (C a : MvPolynomial (Fin m) R) ∈ RingHom.ker (chartHom K j).toRingHom :=
      RingHom.mem_ker.mpr
        ((MvPolynomial.algHom_C _ a).trans (algebraMap_chart_eq_zero K j I hIK ha))
    simpa [evalZero] using Ideal.mem_map_of_mem (evalZero (m := m) (R := R)).toRingHom hker

/-- **The family is not locally of finite presentation** when `I` is not finitely generated. -/
theorem not_locallyOfFinitePresentation (hKj : ∀ k : ℕ, K (Finsupp.single j k) ≤ I)
    (hIK : I ≤ K (Finsupp.single j 1)) (hI : ¬ I.FG) :
    ¬ LocallyOfFinitePresentation (toSpecBase K) := by
  intro hlfp
  have hcomp : Proj.awayι (projGrading K) (mkX K j) (mkX_mem_one K j) Nat.one_pos ≫
      toSpecBase K =
      Spec.map (CommRingCat.ofHom (algebraMap R (Away (projGrading K) (mkX K j)))) := by
    rw [toSpecBase, ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
    rfl
  have hfp : Algebra.FinitePresentation R (Away (projGrading K) (mkX K j)) := by
    have h1 : LocallyOfFinitePresentation
        (Proj.awayι (projGrading K) (mkX K j) (mkX_mem_one K j) Nat.one_pos ≫ toSpecBase K) :=
      inferInstance
    rw [hcomp, LocallyOfFinitePresentation.SpecMap_iff] at h1
    simpa using h1
  exact hI (map_ker_chartHom K j I hKj hIK ▸
    (Algebra.FinitePresentation.ker_fg_of_mvPolynomial (chartHom K j)
      (surjective_chartHom K j)).map _)

end Stacks.CoefficientProj

end

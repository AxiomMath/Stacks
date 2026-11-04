module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.InseparableModel.Basic

/-!
# A regular model with an inseparable component: the charts are the explicit rings

The ring `(A_{(z)})₀` of the standard chart `D₊(z)` of `X = Proj (R[z] ⧸ J)`, for `z` one of
`z₀₀`, `z₀₁`, `z₁₁`, is isomorphic to the explicit ring `R[s][T] ⧸ (x T - y)` of
`Stacks.Models.InseparableModel.chartRing`, compatibly with the structure maps from `R`; and the
three charts cover `X`.

## Main definitions

* `Stacks.Models.InseparableModel.chartEquiv` — `R[s][T] ⧸ (x T - y) ≃ (A_{(z)})₀`.

## Main results

* `Stacks.Models.InseparableModel.chartEquiv_algebraMap` — compatibility with `R`.
* `Stacks.Models.InseparableModel.iSup_basicOpen_chartVar` — the three charts cover `X`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace Stacks.Models.InseparableModel

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The localization `A_z` of which `(A_{(z)})₀` is the degree-zero part. -/
abbrev chartLoc (c : Fin 3) : Type := Localization.Away (zA (chartVar c))

/-- The ratio `zᵢ / z` in the chart ring `(A_{(z)})₀`. -/
def chartRatio (c : Fin 3) (i : Fin 4) : Away c :=
  HomogeneousLocalization.Away.isLocalizationElem (zA_mem (chartVar c)) (zA_mem i)

/-- In `A_z`, the ratio `zᵢ / z` times `z` is `zᵢ`. -/
theorem val_chartRatio_mul (c : Fin 3) (i : Fin 4) :
    (chartRatio c i).val * algebraMap A (chartLoc c) (zA (chartVar c)) =
      algebraMap A (chartLoc c) (zA i) := by
  simp only [chartRatio, HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
  have := IsLocalization.mk'_spec (chartLoc c) (zA i ^ 1)
    (⟨zA (chartVar c) ^ 1, 1, rfl⟩ : Submonoid.powers (zA (chartVar c)))
  simp only [pow_one] at this ⊢
  exact this

/-- In `A_z`, the image of `r : R` in `(A_{(z)})₀` is the image of `r` under `R → A → A_z`. -/
theorem val_awayBase (c : Fin 3) (r : R) :
    (awayBase c r).val = algebraMap A (chartLoc c) (algebraMap R A r) := by
  simp only [awayBase, RingHom.comp_apply, HomogeneousLocalization.fromZeroRingHom]
  exact Localization.mk_one_eq_algebraMap _

/-- The ratio `z / z` is `1`. -/
theorem chartRatio_self (c : Fin 3) : chartRatio c (chartVar c) = 1 := by
  apply HomogeneousLocalization.val_injective
  have hu : IsUnit (algebraMap A (chartLoc c) (zA (chartVar c))) :=
    IsLocalization.Away.algebraMap_isUnit _
  apply hu.mul_right_cancel
  rw [val_chartRatio_mul, HomogeneousLocalization.val_one, one_mul]

/-- In `A_z`, the ratio `zᵢ / z` is `zᵢ · z⁻¹`. -/
theorem val_chartRatio (c : Fin 3) (i : Fin 4) :
    (chartRatio c i).val =
      algebraMap A (chartLoc c) (zA i) * IsLocalization.Away.invSelf (zA (chartVar c)) := by
  rw [← val_chartRatio_mul, mul_assoc, IsLocalization.Away.mul_invSelf, mul_one]

/-- The relation `q₀` between the ratios. -/
theorem chartRatio_rel₀ (c : Fin 3) :
    chartRatio c 0 * chartRatio c 3 = chartRatio c 1 * chartRatio c 2 := by
  apply HomogeneousLocalization.val_injective
  have h := congrArg (algebraMap A (chartLoc c)) zA_rel₀
  simp only [map_mul] at h
  simp only [HomogeneousLocalization.val_mul, val_chartRatio]
  linear_combination (IsLocalization.Away.invSelf (zA (chartVar c))) ^ 2 * h

/-- The relation `q₁` between the ratios. -/
theorem chartRatio_rel₁ (c : Fin 3) :
    awayBase c π * chartRatio c 0 * chartRatio c 1 + awayBase c tR * chartRatio c 0 ^ 2 =
      chartRatio c 2 ^ 2 := by
  apply HomogeneousLocalization.val_injective
  have h := congrArg (algebraMap A (chartLoc c)) zA_rel₁
  simp only [map_mul, map_add, map_pow] at h
  simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_add,
    HomogeneousLocalization.val_pow, val_chartRatio, val_awayBase]
  linear_combination (IsLocalization.Away.invSelf (zA (chartVar c))) ^ 2 * h

/-- The relation `q₂` between the ratios. -/
theorem chartRatio_rel₂ (c : Fin 3) :
    awayBase c π * chartRatio c 1 ^ 2 + awayBase c tR * chartRatio c 0 * chartRatio c 1 =
      chartRatio c 2 * chartRatio c 3 := by
  apply HomogeneousLocalization.val_injective
  have h := congrArg (algebraMap A (chartLoc c)) zA_rel₂
  simp only [map_mul, map_add, map_pow] at h
  simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_add,
    HomogeneousLocalization.val_pow, val_chartRatio, val_awayBase]
  linear_combination (IsLocalization.Away.invSelf (zA (chartVar c))) ^ 2 * h

/-- The index of the variable whose ratio is the coordinate `s` of a chart. -/
def chartSVar : Fin 3 → Fin 4 := ![2, 3, 1]

/-- The index of the variable whose ratio is the coordinate `T` of a chart. -/
def chartTVar : Fin 3 → Fin 4 := ![1, 0, 2]

/-- `R[s][T] → (A_{(z)})₀`, sending `s` and `T` to the ratios they stand for. -/
def chartPolyHom (c : Fin 3) : Polynomial (Polynomial R) →+* Away c :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (awayBase c) (chartRatio c (chartSVar c)))
    (chartRatio c (chartTVar c))

/-- `chartPolyHom c` sends the chart equation `x T - y` to `0`. -/
theorem chartPolyHom_chartEq (c : Fin 3) : chartPolyHom c (chartEq c) = 0 := by
  have h₀ := chartRatio_rel₀ c
  have h₁ := chartRatio_rel₁ c
  have h₂ := chartRatio_rel₂ c
  have h₃ := chartRatio_self c
  fin_cases c <;>
    simp only [chartVar, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one] at h₃ ⊢ <;>
    simp [chartPolyHom, chartEq, chartX, chartY, chartSVar, chartTVar, Polynomial.eval₂_pow, h₃]
      at h₀ h₁ h₂ ⊢
  · linear_combination h₁
  · linear_combination chartRatio 1 3 * h₀ - h₂
  · linear_combination -h₂ + awayBase 2 tR * chartRatio 2 1 * h₀

/-- `R[s][T] ⧸ (x T - y) → (A_{(z)})₀`. -/
def chartHom (c : Fin 3) : chartRing c →+* Away c :=
  Ideal.Quotient.lift _ (chartPolyHom c) fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, chartPolyHom_chartEq, mul_zero]

/-- The polynomial in `R[s][T]` standing for the ratio `zᵢ / z`: `1`, `s`, `T` or `s T`. -/
def dehomVal (c : Fin 3) (i : Fin 4) : Polynomial (Polynomial R) :=
  if i = chartVar c then 1 else if i = chartSVar c then Polynomial.C Polynomial.X
    else if i = chartTVar c then Polynomial.X else Polynomial.C Polynomial.X * Polynomial.X

/-- Dehomogenization `R[z] → R[s][T] ⧸ (x T - y)`, setting `z = 1`. -/
def dehomPoly (c : Fin 3) : P →+* chartRing c :=
  (Ideal.Quotient.mk _).comp (MvPolynomial.eval₂Hom (Polynomial.C.comp Polynomial.C) (dehomVal c))

/-- Dehomogenization sends each of the generators `q₀`, `q₁`, `q₂` of `J` to `0`. -/
theorem dehomPoly_gens (c : Fin 3) : ∀ q ∈ gens, dehomPoly c q = 0 := by
  rintro q (rfl | rfl | rfl) <;>
    refine Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 ?_) <;>
    fin_cases c <;>
    simp only [chartEq, chartX, chartY, tR, q₀, q₁, q₂, dehomVal, chartVar, chartSVar, chartTVar,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, Matrix.cons_val,
      Matrix.cons_val_zero, Matrix.cons_val_one, map_sub, map_pow, map_one, map_mul,
      MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_X, MvPolynomial.eval₂_C, MvPolynomial.eval₂_pow,
      RingHom.coe_comp, Function.comp_apply, ↓reduceIte, one_ne_zero, zero_ne_one, one_mul,
      mul_one, one_pow, Polynomial.X_mul_C, sub_self, dvd_zero]
  exacts [⟨1, by ring⟩, ⟨-Polynomial.X, by ring⟩, ⟨-Polynomial.X, by ring⟩,
    ⟨Polynomial.X, by ring⟩, ⟨-1, by ring⟩, ⟨-1, by ring⟩]

/-- Dehomogenization `A → R[s][T] ⧸ (x T - y)`. -/
def dehomA (c : Fin 3) : A →+* chartRing c :=
  Ideal.Quotient.lift _ (dehomPoly c) fun a ha => by
    change a ∈ Ideal.span gens at ha
    exact (Ideal.span_le (I := RingHom.ker (dehomPoly c)).2 (dehomPoly_gens c)) ha

/-- Dehomogenization sends `zᵢ` to the class of `dehomVal c i`. -/
theorem dehomA_zA (c : Fin 3) (i : Fin 4) :
    dehomA c (zA i) = Ideal.Quotient.mk _ (dehomVal c i) := by
  simp [dehomA, zA, dehomPoly]

/-- The structure map `R → R[s][T] ⧸ (x T - y)` sends `r` to the class of the constant `r`. -/
theorem chartRing_algebraMap_eq_mk (c : Fin 3) (r : R) :
    algebraMap R (chartRing c) r = Ideal.Quotient.mk _ (Polynomial.C (Polynomial.C r)) := by
  rw [IsScalarTower.algebraMap_apply R (Polynomial (Polynomial R)) (chartRing c),
    Ideal.Quotient.algebraMap_eq, Polynomial.algebraMap_apply, Polynomial.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply]

/-- Dehomogenization `A → R[s][T] ⧸ (x T - y)` commutes with the structure maps from `R`. -/
theorem dehomA_algebraMap (c : Fin 3) (r : R) :
    dehomA c (algebraMap R A r) = algebraMap R (chartRing c) r := by
  simp [dehomA, A_algebraMap_eq_mk, dehomPoly, chartRing_algebraMap_eq_mk]

/-- Dehomogenization sends the chart variable `z` to a unit. -/
theorem isUnit_dehomA_chartVar (c : Fin 3) : IsUnit (dehomA c (zA (chartVar c))) := by
  simp [dehomA_zA, dehomVal]

/-- `(A_{(z)})₀ → R[s][T] ⧸ (x T - y)`, inverse to `chartHom`. -/
def chartInv (c : Fin 3) : Away c →+* chartRing c :=
  (IsLocalization.Away.lift (zA (chartVar c)) (S := chartLoc c) (isUnit_dehomA_chartVar c)).comp
    (algebraMap (Away c) (chartLoc c))

/-- `chartInv c` sends the ratio `zᵢ / z` to the class of `dehomVal c i`. -/
theorem chartInv_chartRatio (c : Fin 3) (i : Fin 4) :
    chartInv c (chartRatio c i) = Ideal.Quotient.mk _ (dehomVal c i) := by
  have h := congrArg (IsLocalization.Away.lift (zA (chartVar c)) (S := chartLoc c)
    (isUnit_dehomA_chartVar c)) (val_chartRatio_mul c i)
  rw [map_mul, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq] at h
  simp only [chartInv, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply]
  simpa [dehomA_zA, dehomVal] using h

/-- `chartInv c` commutes with the structure maps from `R`. -/
theorem chartInv_awayBase (c : Fin 3) (r : R) :
    chartInv c (awayBase c r) = algebraMap R (chartRing c) r := by
  simp only [chartInv, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, val_awayBase,
    IsLocalization.Away.lift_eq, dehomA_algebraMap]

/-- `chartInv c` is a left inverse of `chartHom c`. -/
theorem chartInv_chartHom (c : Fin 3) : (chartInv c).comp (chartHom c) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  refine Polynomial.ringHom_ext' (Polynomial.ringHom_ext (fun r => ?_) ?_) ?_
  · simp [chartHom, chartPolyHom, chartInv_awayBase, chartRing_algebraMap_eq_mk]
  all_goals
    fin_cases c <;> simp [chartHom, chartPolyHom, chartInv_chartRatio, dehomVal, chartVar,
      chartSVar, chartTVar]

/-- `chartHom c` is injective. -/
theorem injective_chartHom (c : Fin 3) : Function.Injective (chartHom c) :=
  Function.LeftInverse.injective (g := chartInv c) fun x =>
    RingHom.congr_fun (chartInv_chartHom c) x

/-- `chartHom c` sends the class of `dehomVal c i` to the ratio `zᵢ / z`. -/
theorem chartHom_dehomVal (c : Fin 3) (i : Fin 4) :
    chartHom c (Ideal.Quotient.mk _ (dehomVal c i)) = chartRatio c i := by
  have h₀ := chartRatio_rel₀ c
  have h₃ := chartRatio_self c
  fin_cases c <;>
    simp only [chartVar, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val,
      Matrix.cons_val_zero, Matrix.cons_val_one] at h₃ <;>
    fin_cases i <;>
    simp only [chartHom, chartPolyHom, dehomVal, chartVar, chartSVar, chartTVar, h₃, Fin.zero_eta,
      Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, Matrix.cons_val, Matrix.cons_val_zero,
      Matrix.cons_val_one, ↓reduceIte, one_ne_zero, zero_ne_one, map_one, map_mul, one_mul, mul_one,
      Ideal.Quotient.lift_mk, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
      Polynomial.eval₂_C] at h₀ ⊢
  all_goals first | linear_combination h₀ | linear_combination -h₀

/-- The variables `zᵢ` generate `A` as an algebra over its degree-zero part. -/
theorem adjoin_zA : Algebra.adjoin (grading 0) (Set.range zA) = ⊤ := by
  apply top_unique
  intro a ha
  clear ha
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  induction p using MvPolynomial.induction_on with
  | C r =>
    have : Ideal.Quotient.mk J.toIdeal (MvPolynomial.C r) =
        algebraMap (grading 0) A (algebraMap R (grading 0) r) := by
      rw [← A_algebraMap_eq_mk]; rfl
    rw [this]
    exact Subalgebra.algebraMap_mem _ _
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p i hp => rw [map_mul]; exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)

/-- `chartHom c` is surjective. -/
theorem surjective_chartHom (c : Fin 3) : Function.Surjective (chartHom c) := by
  classical
  let S : Subalgebra (grading 0) (Away c) :=
    { (chartHom c).range.toSubsemiring with
      algebraMap_mem' := fun b => by
        obtain ⟨r, rfl⟩ := bijective_algebraMap_grading_zero.2 b
        exact ⟨algebraMap R (chartRing c) r, by
          simp [chartHom, chartPolyHom, chartRing_algebraMap_eq_mk, awayBase,
            HomogeneousLocalization.algebraMap_eq]⟩ }
  have hS : S = ⊤ := by
    apply top_unique
    rw [← HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top (zA_mem (chartVar c)) (Fin 4)
      zA adjoin_zA (fun _ => 1) zA_mem]
    apply Algebra.adjoin_le_iff.mpr
    rintro z ⟨a, ai, hai, -, rfl⟩
    have he : HomogeneousLocalization.Away.mk _ (zA_mem (chartVar c)) a (∏ i, zA i ^ ai i)
        (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun i _ => zA_mem i) =
        ∏ i, chartRatio c i ^ ai i := by
      apply HomogeneousLocalization.val_injective
      rw [← HomogeneousLocalization.algebraMap_apply, ← HomogeneousLocalization.algebraMap_apply,
        map_prod (algebraMap (Away c) (chartLoc c))]
      simp only [map_pow, HomogeneousLocalization.algebraMap_apply, chartRatio,
        HomogeneousLocalization.Away.isLocalizationElem, HomogeneousLocalization.Away.val_mk,
        pow_one, Localization.mk_pow, Localization.mk_prod]
      congr 1
      apply Subtype.ext
      simp only [smul_eq_mul, mul_one] at hai
      simp [Finset.prod_pow_eq_pow_sum, hai]
    rw [he]
    exact prod_mem fun i _ =>
      pow_mem (show chartRatio c i ∈ S from ⟨_, chartHom_dehomVal c i⟩) _
  intro w
  have hw : w ∈ S := hS ▸ Algebra.mem_top
  exact hw

/-- **The chart ring is the explicit ring.** -/
def chartEquiv (c : Fin 3) : chartRing c ≃+* Away c :=
  RingEquiv.ofBijective (chartHom c) ⟨injective_chartHom c, surjective_chartHom c⟩

/-- `chartEquiv c` commutes with the structure maps from `R`. -/
theorem chartEquiv_algebraMap (c : Fin 3) (r : R) :
    chartEquiv c (algebraMap R (chartRing c) r) = awayBase c r := by
  simp [chartEquiv, chartHom, chartPolyHom, chartRing_algebraMap_eq_mk]

/-- **The three charts `D₊(z₀₀)`, `D₊(z₀₁)`, `D₊(z₁₁)` cover `X`**: a homogeneous prime containing
`z₀₀`, `z₀₁`, `z₁₁` contains `z₁₀² = π z₀₀ z₀₁ + t z₀₀² - q₁`, hence every variable. -/
theorem iSup_basicOpen_chartVar :
    ⨆ c : Fin 3, Proj.basicOpen grading (zA (chartVar c)) = ⊤ := by
  have h4 := Proj.iSup_basicOpen_eq_top' grading zA (fun i => ⟨1, zA_mem i⟩) adjoin_zA
  refine top_unique (h4 ▸ iSup_le fun i => ?_)
  fin_cases i
  · exact le_iSup_of_le (0 : Fin 3) le_rfl
  · exact le_iSup_of_le (1 : Fin 3) le_rfl
  · intro x hx
    rw [TopologicalSpace.Opens.mem_iSup]
    by_contra! H
    simp only [Proj.mem_basicOpen, not_not] at H hx
    have h0 : zA 0 ∈ x.asHomogeneousIdeal := H 0
    have h1 : zA 1 ∈ x.asHomogeneousIdeal := H 1
    have h2 : zA 2 ^ 2 ∈ x.asHomogeneousIdeal := by
      rw [← zA_rel₁]
      exact add_mem (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ h0))
        (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ h0 2 two_pos))
    exact hx (x.isPrime.mem_of_pow_mem 2 h2)
  · exact le_iSup_of_le (2 : Fin 3) le_rfl

end Stacks.Models.InseparableModel

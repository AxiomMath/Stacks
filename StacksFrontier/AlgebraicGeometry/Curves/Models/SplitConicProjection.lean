module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.SplitConicModel
public import StacksFrontier.AlgebraicGeometry.Curves.Models.GenusZeroMinimalModels

/-!
# The two projections of the split conic to the projective line

Let `R` be a ring and `π ∈ R`, and let `X = V(T₁T₂ - πT₀²) ⊆ ℙ²_R`. The projections from the
points `(0 : 0 : 1)` and `(0 : 1 : 0)` of `ℙ²_R` define morphisms `X ⟶ ℙ¹_R`,

`[T₀ : T₁ : T₂] ↦ [T₀ : T₁]`  and  `[T₀ : T₁ : T₂] ↦ [T₂ : T₀]`,

corresponding to the graded maps `R[S₀, S₁] → R[T₀, T₁, T₂]/(T₁T₂ - πT₀²)` sending `(S₀, S₁)` to
`(T₀, T₁)` and to `(T₂, T₀)`. Neither graded map is defined on all of `X`: the first is not
defined at `(0 : 0 : 1)` and the second not at `(0 : 1 : 0)`. On `X` the relation
`T₁T₂ = πT₀²` gives `[T₀ : T₁] = [T₂ : πT₀]` and `[T₂ : T₀] = [πT₀ : T₁]`, which are defined
there, and the morphisms are glued from these descriptions on the three standard charts.

## Main definitions

* `Stacks.Models.GenusZero.vecHom`: the homomorphism `ℤ[S₀, S₁] → C` evaluating at `(a, b)`.
* `Stacks.Models.GenusZero.firstProjectionZ` and `Stacks.Models.GenusZero.secondProjectionZ`:
  the two projections, to the integral model of `ℙ¹`.
* `Stacks.Models.GenusZero.firstProjection` and `Stacks.Models.GenusZero.secondProjection`: the
  two projections `X ⟶ ℙ¹_R`, over `R`.

## Main results

* `Stacks.Models.GenusZero.point_vecHom_eq_of_mul_eq`: two points `[a : b]` and `[a' : b']` of
  `ℙ¹` agree when `a b' = a' b`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial HomogeneousLocalization

universe u

namespace Stacks.Models.GenusZero

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### Points `[a : b]` of the projective line -/

section Vec

variable (C : Type u) [CommRing C]

/-- The homomorphism `ℤ[S₀, S₁] → C` evaluating at `(a, b)`. -/
def vecHom (a b : C) : MvPolynomial (Fin (1 + 1)) (ULift.{u} ℤ) →+* C :=
  eval₂Hom ((Int.castRingHom C).comp ULift.ringEquiv.toRingHom) ![a, b]

/-- `vecHom C a b` sends `S₀` to `a`. -/
@[simp] theorem vecHom_X_zero (a b : C) : vecHom C a b (X 0) = a := by simp [vecHom]

/-- `vecHom C a b` sends `S₁` to `b`. -/
@[simp] theorem vecHom_X_one (a b : C) : vecHom C a b (X 1) = b := by simp [vecHom]

/-- `vecHom` is natural in the ring of values. -/
theorem comp_vecHom {D : Type u} [CommRing D] (g : C →+* D) (a b : C) :
    g.comp (vecHom C a b) = vecHom D (g a) (g b) := by
  refine MvPolynomial.ringHom_ext (fun n => ?_) (fun i => ?_)
  · simp [vecHom]
  · fin_cases i <;> simp [vecHom]

/-- `coordHom` is `vecHom` with second coordinate one. -/
theorem coordHom_eq_vecHom (b : C) : coordHom C b = vecHom C b 1 := rfl

/-- Rescaling both coordinates by `μ` rescales a form of degree `n` by `μⁿ`. -/
theorem vecHom_mul (μ a b : C) {n : ℕ} {p : MvPolynomial (Fin (1 + 1)) (ULift.{u} ℤ)}
    (hp : p ∈ Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading (ULift.{u} ℤ) 1 n) :
    vecHom C (μ * a) (μ * b) p = μ ^ n * vecHom C a b p := by
  have hp' : p.IsHomogeneous n := (mem_homogeneousSubmodule _ _).1 hp
  simp only [vecHom, coe_eval₂Hom, eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i, d i = n := by
    have := hp' (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
  have hv : ∀ i, (![μ * a, μ * b] : Fin (1 + 1) → C) i = μ * (![a, b] : Fin (1 + 1) → C) i := by
    intro i; fin_cases i <;> rfl
  simp only [hv, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

/-- **Two points `[a : b]`, `[a' : b']` of `ℙ¹` agree when `a b' = a' b`.** -/
theorem point_vecHom_eq_of_mul_eq {a b a' b' : C} (h : a * b' = a' * b) (s s' : Fin 2)
    (hu : IsUnit (vecHom C a b (X s))) (hu' : IsUnit (vecHom C a' b' (X s'))) :
    ProjPoint.point (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading (ULift.{u} ℤ) 1)
        (vecHom C a b) (X s) (X_mem _ s) one_pos hu =
      ProjPoint.point (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading (ULift.{u} ℤ) 1)
        (vecHom C a' b') (X s') (X_mem _ s') one_pos hu' := by
  have key : ∀ {a b a' b' : C}, a * b' = a' * b → IsUnit a → IsUnit a' →
      ∃ μ : Cˣ, a' = μ * a ∧ b' = μ * b := by
    intro a b a' b' h hu hu'
    refine ⟨hu'.unit * hu.unit⁻¹, by rw [Units.val_mul, IsUnit.unit_spec, mul_assoc,
      IsUnit.val_inv_mul, mul_one], ?_⟩
    calc b' = hu.unit⁻¹ * (a * b') := by rw [← mul_assoc, IsUnit.val_inv_mul, one_mul]
      _ = _ := by rw [h]; simp; ring
  obtain ⟨μ, ha', hb'⟩ : ∃ μ : Cˣ, a' = μ * a ∧ b' = μ * b := by
    fin_cases s <;> fin_cases s' <;>
      simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, vecHom_X_zero, Fin.mk_one,
        vecHom_X_one] at hu hu'
    · exact key h hu hu'
    · exact key h hu (isUnit_of_mul_isUnit_left (h ▸ hu.mul hu' : IsUnit (a' * b)))
    · obtain ⟨μ, h1, h2⟩ := key (a := b) (b := a) (a' := b') (b' := a') (by rw [mul_comm b, ← h,
        mul_comm]) hu (isUnit_of_mul_isUnit_right (h.symm ▸ hu'.mul hu : IsUnit (a * b')))
      exact ⟨μ, h2, h1⟩
    · obtain ⟨μ, h1, h2⟩ := key (a := b) (b := a) (a' := b') (b' := a') (by rw [mul_comm b, ← h,
        mul_comm]) hu hu'
      exact ⟨μ, h2, h1⟩
  subst ha' hb'
  have hscale := ProjPoint.point_eq_of_scale
    (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading (ULift.{u} ℤ) 1) μ
    (φ := vecHom C a b) (φ' := vecHom C (μ * a) (μ * b))
    (fun n p hp => vecHom_mul C μ a b hp) (X s') (X_mem _ s') one_pos
  have hus' : IsUnit (vecHom C a b (X s')) := by
    have := (μ⁻¹).isUnit.mul hu'
    rwa [vecHom_mul C μ a b (X_mem _ s'), pow_one, ← mul_assoc, Units.inv_mul, one_mul] at this
  rw [← hscale hus' hu']
  exact ProjPoint.point_indep _ _ _ _ _ _ _ _

end Vec

/-! ### The charts of the conic -/

section Charts

variable {R : Type u} [CommRing R] (π : R)

/-- The grading of the homogeneous coordinate ring of the conic. -/
abbrev conicGrading := PlaneCurveModel.grading (conicEquation π) (isHomogeneous_conicEquation π)

/-- Each coordinate `Tᵢ` is homogeneous of degree one. -/
theorem conicCoord_mem (i : Fin 3) : conicCoord π i ∈ conicGrading π 1 :=
  Stacks.HomogeneousIdeal.mk_mem_quotientGrading _
    ((mem_homogeneousSubmodule _ _).2 (isHomogeneous_X R i))

/-- Each coordinate `Tᵢ` is homogeneous of degree `1 • 1`. -/
theorem conicCoord_mem' (i : Fin 3) : conicCoord π i ∈ conicGrading π (1 • 1) := by
  simpa using conicCoord_mem π i

/-- The image of the uniformizer in the homogeneous coordinate ring. -/
abbrev conicConst : MvPolynomial (Fin 3) R ⧸ conicIdeal π := Ideal.Quotient.mk (conicIdeal π) (C π)

/-- **The equation of the conic** in its homogeneous coordinate ring: `T₁T₂ = πT₀²`. -/
theorem conic_relation :
    conicCoord π 1 * conicCoord π 2 = conicConst π * conicCoord π 0 ^ 2 := by
  rw [← sub_eq_zero]
  change Ideal.Quotient.mk (conicIdeal π) (X 1) * Ideal.Quotient.mk (conicIdeal π) (X 2) -
    Ideal.Quotient.mk (conicIdeal π) (C π) * Ideal.Quotient.mk (conicIdeal π) (X 0) ^ 2 = 0
  rw [← map_mul, ← map_pow, ← map_mul, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl

/-- The fraction `Tⱼ / Tᵢ` on the chart `D₊(Tᵢ)`. -/
def frac (i j : Fin 3) : Away (conicGrading π) (conicCoord π i) :=
  Away.mk (conicGrading π) (conicCoord_mem π i) 1 (conicCoord π j) (conicCoord_mem' π j)

/-- The uniformizer on the chart `D₊(Tᵢ)`. -/
def constEl (i : Fin 3) : Away (conicGrading π) (conicCoord π i) :=
  fromZeroRingHom (conicGrading π) _
    (PlaneCurveModel.toGradingZero (conicEquation π) (isHomogeneous_conicEquation π) π)

/-- The map from the chart `D₊(Tᵢ)` to the overlap `D₊(TᵢTⱼ)`. -/
abbrev leftMap (i j : Fin 3) :
    Away (conicGrading π) (conicCoord π i) →+*
      Away (conicGrading π) (conicCoord π i * conicCoord π j) :=
  awayMap (conicGrading π) (conicCoord_mem π j) rfl

/-- The map from the chart `D₊(Tⱼ)` to the overlap `D₊(TᵢTⱼ)`. -/
abbrev rightMap (i j : Fin 3) :
    Away (conicGrading π) (conicCoord π j) →+*
      Away (conicGrading π) (conicCoord π i * conicCoord π j) :=
  awayMap (conicGrading π) (conicCoord_mem π i) (mul_comm _ _)

variable {π}

/-- The value of a transported fraction on the overlap, in the localization. -/
theorem val_awayMap_frac {i j : Fin 3} {g : MvPolynomial (Fin 3) R ⧸ conicIdeal π}
    (hg : g ∈ conicGrading π 1) {x : MvPolynomial (Fin 3) R ⧸ conicIdeal π}
    (hx : x = conicCoord π i * g) (v : Localization.Away x)
    (hv : algebraMap _ (Localization.Away x) (conicCoord π i) * v = 1) :
    (awayMap (conicGrading π) hg hx (frac π i j)).val =
      algebraMap _ (Localization.Away x) (conicCoord π j) * v := by
  rw [val_awayMap]
  exact (Localization.awayLift_mk (algebraMap _ (Localization.Away x)) (conicCoord π i)
    (conicCoord π j) v hv 1).trans (by rw [pow_one])

/-- The value of the transported uniformizer on the overlap, in the localization. -/
theorem val_awayMap_constEl {i : Fin 3} {g : MvPolynomial (Fin 3) R ⧸ conicIdeal π}
    (hg : g ∈ conicGrading π 1) {x : MvPolynomial (Fin 3) R ⧸ conicIdeal π}
    (hx : x = conicCoord π i * g) :
    (awayMap (conicGrading π) hg hx (constEl π i)).val =
      algebraMap _ (Localization.Away x) (conicConst π) := by
  rw [constEl, awayMap_fromZeroRingHom]
  change (HomogeneousLocalization.mk ⟨0, PlaneCurveModel.toGradingZero _ _ π, 1,
    one_mem _⟩).val = _
  rw [HomogeneousLocalization.val_mk]
  exact Localization.mk_one_eq_algebraMap _

/-- The inverse of `Tᵢ` on the overlap `D₊(TᵢTⱼ)`. -/
theorem exists_inv_left (i j : Fin 3) : ∃ v : Localization.Away (conicCoord π i * conicCoord π j),
    algebraMap _ _ (conicCoord π i) * v = 1 :=
  isUnit_iff_exists_inv.mp (isUnit_of_dvd_unit
    (map_dvd (algebraMap _ _) (dvd_mul_right (conicCoord π i) (conicCoord π j)))
    (IsLocalization.Away.algebraMap_isUnit (conicCoord π i * conicCoord π j)))

/-- The inverse of `Tⱼ` on the overlap `D₊(TᵢTⱼ)`. -/
theorem exists_inv_right (i j : Fin 3) :
    ∃ v : Localization.Away (conicCoord π i * conicCoord π j),
      algebraMap _ _ (conicCoord π j) * v = 1 :=
  isUnit_iff_exists_inv.mp (isUnit_of_dvd_unit
    (map_dvd (algebraMap _ _) (dvd_mul_left (conicCoord π j) (conicCoord π i)))
    (IsLocalization.Away.algebraMap_isUnit (conicCoord π i * conicCoord π j)))

/-- The inverse of `Tᵢ` in the localization at `TᵢTⱼ`. -/
def invLeft (i j : Fin 3) : Localization.Away (conicCoord π i * conicCoord π j) :=
  (exists_inv_left i j).choose

/-- The inverse of `Tⱼ` in the localization at `TᵢTⱼ`. -/
def invRight (i j : Fin 3) : Localization.Away (conicCoord π i * conicCoord π j) :=
  (exists_inv_right i j).choose

/-- `invLeft i j` is an inverse of `Tᵢ` in the localization at `TᵢTⱼ`. -/
theorem mul_invLeft (i j : Fin 3) :
    algebraMap _ _ (conicCoord π i) * invLeft (π := π) i j = 1 :=
  (exists_inv_left i j).choose_spec

/-- `invRight i j` is an inverse of `Tⱼ` in the localization at `TᵢTⱼ`. -/
theorem mul_invRight (i j : Fin 3) :
    algebraMap _ _ (conicCoord π j) * invRight (π := π) i j = 1 :=
  (exists_inv_right i j).choose_spec

/-- On the overlap `D₊(TᵢTⱼ)`, the fraction `Tₖ / Tᵢ` has value `Tₖ · Tᵢ⁻¹`. -/
theorem val_leftMap_frac (i j k : Fin 3) :
    (leftMap π i j (frac π i k)).val = algebraMap _ _ (conicCoord π k) * invLeft i j :=
  val_awayMap_frac _ _ _ (mul_invLeft i j)

/-- On the overlap `D₊(TᵢTⱼ)`, the fraction `Tₖ / Tⱼ` has value `Tₖ · Tⱼ⁻¹`. -/
theorem val_rightMap_frac (i j k : Fin 3) :
    (rightMap π i j (frac π j k)).val = algebraMap _ _ (conicCoord π k) * invRight i j :=
  val_awayMap_frac _ _ _ (mul_invRight i j)

/-- The uniformizer of `D₊(Tᵢ)` has value `π` on the overlap `D₊(TᵢTⱼ)`. -/
theorem val_leftMap_constEl (i j : Fin 3) :
    (leftMap π i j (constEl π i)).val = algebraMap _ _ (conicConst π) :=
  val_awayMap_constEl _ _

/-- The uniformizer of `D₊(Tⱼ)` has value `π` on the overlap `D₊(TᵢTⱼ)`. -/
theorem val_rightMap_constEl (i j : Fin 3) :
    (rightMap π i j (constEl π j)).val = algebraMap _ _ (conicConst π) :=
  val_awayMap_constEl _ _

/-- The equation of the conic on the overlap `D₊(TᵢTⱼ)`. -/
theorem conic_relation_loc (i j : Fin 3) :
    algebraMap _ (Localization.Away (conicCoord π i * conicCoord π j)) (conicCoord π 1) *
        algebraMap _ _ (conicCoord π 2) =
      algebraMap _ _ (conicConst π) * algebraMap _ _ (conicCoord π 0) ^ 2 := by
  have := congrArg (algebraMap _ (Localization.Away (conicCoord π i * conicCoord π j)))
    (conic_relation π)
  simpa only [map_mul, map_pow] using this

/-- **The compatibility criterion for glued maps to `ℙ¹`.** Points `[aᵢ : bᵢ]` on `D₊(Tᵢ)` and
`[aⱼ : bⱼ]` on `D₊(Tⱼ)` agree on the overlap when their cross products agree there. -/
theorem compat_of_cross {i j : Fin 3} (ai bi : Away (conicGrading π) (conicCoord π i))
    (aj bj : Away (conicGrading π) (conicCoord π j)) (si sj : Fin 2)
    (hui : IsUnit (vecHom _ ai bi (X si))) (huj : IsUnit (vecHom _ aj bj (X sj)))
    (hcross : (leftMap π i j ai * rightMap π i j bj) = (rightMap π i j aj * leftMap π i j bi)) :
    Spec.map (CommRingCat.ofHom (leftMap π i j)) ≫
        ProjPoint.point (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading (ULift.{u} ℤ) 1)
          (vecHom _ ai bi) (X si) (X_mem _ si) one_pos hui =
      Spec.map (CommRingCat.ofHom (rightMap π i j)) ≫
        ProjPoint.point (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading (ULift.{u} ℤ) 1)
          (vecHom _ aj bj) (X sj) (X_mem _ sj) one_pos huj := by
  rw [ProjPoint.SpecMap_comp_point, ProjPoint.SpecMap_comp_point,
    ProjPoint.point_congr_ringHom _ (comp_vecHom _ (leftMap π i j) ai bi) _ _ _ _
      (by rw [← comp_vecHom, RingHom.comp_apply]; exact hui.map (leftMap π i j)),
    ProjPoint.point_congr_ringHom _ (comp_vecHom _ (rightMap π i j) aj bj) _ _ _ _
      (by rw [← comp_vecHom, RingHom.comp_apply]; exact huj.map (rightMap π i j))]
  exact point_vecHom_eq_of_mul_eq _ hcross _ _ _ _

end Charts

/-! ### The first projection `[T₀ : T₁]` -/

section First

variable {R : Type u} [CommRing R] (π : R)

/-- The first coordinate of the first projection on the chart `D₊(Tᵢ)`. -/
def firstA : (i : Fin 3) → Away (conicGrading π) (conicCoord π i)
  | 0 => 1
  | 1 => frac π 1 0
  | 2 => 1

/-- The second coordinate of the first projection on the chart `D₊(Tᵢ)`: `[T₀ : T₁]`, and
`[T₂ : πT₀]` on `D₊(T₂)`. -/
def firstB : (i : Fin 3) → Away (conicGrading π) (conicCoord π i)
  | 0 => frac π 0 1
  | 1 => 1
  | 2 => constEl π 2 * frac π 2 0

/-- The coordinate of `ℙ¹` that is a unit on the image of `D₊(Tᵢ)` under the first projection. -/
def firstS : Fin 3 → Fin 2 := ![0, 1, 0]

/-- The coordinate `firstS i` of the first projection is a unit on `D₊(Tᵢ)`. -/
theorem isUnit_first (i : Fin 3) :
    IsUnit (vecHom _ (firstA π i) (firstB π i) (X (firstS i))) := by
  fin_cases i <;> simp [firstA, firstB, firstS]

/-- The first projection on the chart `D₊(Tᵢ)`. -/
def firstChart (i : Fin 3) :
    Spec (.of (Away (conicGrading π) (conicCoord π i))) ⟶
      AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading (ULift.{u} ℤ) 1) :=
  ProjPoint.point _ (vecHom _ (firstA π i) (firstB π i)) (X (firstS i)) (X_mem _ _) one_pos
    (isUnit_first π i)

variable {π}

/-- The local descriptions of the first projection have equal cross products on every overlap
`D₊(TᵢTⱼ)`. -/
theorem first_cross : ∀ i j : Fin 3,
    leftMap π i j (firstA π i) * rightMap π i j (firstB π j) =
      rightMap π i j (firstA π j) * leftMap π i j (firstB π i)
  | 0, 0 => rfl
  | 1, 1 => rfl
  | 2, 2 => rfl
  | 0, 1 => by
    have h0 := mul_invLeft (π := π) 0 1
    have h1 := mul_invRight (π := π) 0 1
    apply HomogeneousLocalization.val_injective
    simp only [firstA, firstB, map_one, HomogeneousLocalization.val_mul,
      HomogeneousLocalization.val_one, val_leftMap_frac, val_rightMap_frac]
    linear_combination (-(algebraMap _ _ (conicCoord π 0) * invLeft (π := π) 0 1)) * h1 - h0
  | 1, 0 => by
    have h1 := mul_invLeft (π := π) 1 0
    have h0 := mul_invRight (π := π) 1 0
    apply HomogeneousLocalization.val_injective
    simp only [firstA, firstB, map_one, HomogeneousLocalization.val_mul,
      HomogeneousLocalization.val_one, val_leftMap_frac, val_rightMap_frac]
    linear_combination (algebraMap _ _ (conicCoord π 0) * invRight (π := π) 1 0) * h1 + h0
  | 0, 2 => by
    have h0 := mul_invLeft (π := π) 0 2
    have h2 := mul_invRight (π := π) 0 2
    have hrel := conic_relation_loc (π := π) 0 2
    apply HomogeneousLocalization.val_injective
    simp only [firstA, firstB, map_one, map_mul, HomogeneousLocalization.val_mul,
      HomogeneousLocalization.val_one, val_leftMap_frac, val_rightMap_frac, val_rightMap_constEl]
    linear_combination (-(algebraMap _ _ (conicConst π) * algebraMap _ _ (conicCoord π 0) *
      invRight (π := π) 0 2)) * h0 + (algebraMap _ _ (conicCoord π 1) * invLeft (π := π) 0 2) * h2 -
      (invLeft (π := π) 0 2 * invRight (π := π) 0 2) * hrel
  | 2, 0 => by
    have h2 := mul_invLeft (π := π) 2 0
    have h0 := mul_invRight (π := π) 2 0
    have hrel := conic_relation_loc (π := π) 2 0
    apply HomogeneousLocalization.val_injective
    simp only [firstA, firstB, map_one, map_mul, HomogeneousLocalization.val_mul,
      HomogeneousLocalization.val_one, val_leftMap_frac, val_rightMap_frac, val_leftMap_constEl]
    linear_combination (algebraMap _ _ (conicConst π) * algebraMap _ _ (conicCoord π 0) *
      invLeft (π := π) 2 0) * h0 - (algebraMap _ _ (conicCoord π 1) * invRight (π := π) 2 0) * h2 +
      (invLeft (π := π) 2 0 * invRight (π := π) 2 0) * hrel
  | 1, 2 => by
    have h1 := mul_invLeft (π := π) 1 2
    have h2 := mul_invRight (π := π) 1 2
    have hrel := conic_relation_loc (π := π) 1 2
    apply HomogeneousLocalization.val_injective
    simp only [firstA, firstB, map_one, map_mul, HomogeneousLocalization.val_mul,
      HomogeneousLocalization.val_one, val_leftMap_frac, val_rightMap_frac, val_rightMap_constEl]
    linear_combination (-(invLeft (π := π) 1 2 * invRight (π := π) 1 2)) * hrel +
      (algebraMap _ _ (conicCoord π 1) * invLeft (π := π) 1 2) * h2 + h1
  | 2, 1 => by
    have h2 := mul_invLeft (π := π) 2 1
    have h1 := mul_invRight (π := π) 2 1
    have hrel := conic_relation_loc (π := π) 2 1
    apply HomogeneousLocalization.val_injective
    simp only [firstA, firstB, map_one, map_mul, HomogeneousLocalization.val_mul,
      HomogeneousLocalization.val_one, val_leftMap_frac, val_rightMap_frac, val_leftMap_constEl]
    linear_combination (invLeft (π := π) 2 1 * invRight (π := π) 2 1) * hrel -
      (algebraMap _ _ (conicCoord π 1) * invRight (π := π) 2 1) * h2 - h1

end First

/-! ### The second projection `[T₂ : T₀]` -/

section Second

variable {R : Type u} [CommRing R] (π : R)

/-- The first coordinate of the second projection on the chart `D₊(Tᵢ)`: `[T₂ : T₀]`, and
`[πT₀ : T₁]` on `D₊(T₁)`. -/
def secondA : (i : Fin 3) → Away (conicGrading π) (conicCoord π i)
  | 0 => frac π 0 2
  | 1 => constEl π 1 * frac π 1 0
  | 2 => 1

/-- The second coordinate of the second projection on the chart `D₊(Tᵢ)`. -/
def secondB : (i : Fin 3) → Away (conicGrading π) (conicCoord π i)
  | 0 => 1
  | 1 => 1
  | 2 => frac π 2 0

/-- The coordinate of `ℙ¹` that is a unit on the image of `D₊(Tᵢ)` under the second projection. -/
def secondS : Fin 3 → Fin 2 := ![1, 1, 0]

/-- The coordinate `secondS i` of the second projection is a unit on `D₊(Tᵢ)`. -/
theorem isUnit_second (i : Fin 3) :
    IsUnit (vecHom _ (secondA π i) (secondB π i) (X (secondS i))) := by
  fin_cases i <;> simp [secondA, secondB, secondS]

/-- The second projection on the chart `D₊(Tᵢ)`. -/
def secondChart (i : Fin 3) :
    Spec (.of (Away (conicGrading π) (conicCoord π i))) ⟶
      AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading (ULift.{u} ℤ) 1) :=
  ProjPoint.point _ (vecHom _ (secondA π i) (secondB π i)) (X (secondS i)) (X_mem _ _) one_pos
    (isUnit_second π i)

variable {π}

/-- The local descriptions of the second projection have equal cross products on every overlap
`D₊(TᵢTⱼ)`. -/
theorem second_cross : ∀ i j : Fin 3,
    leftMap π i j (secondA π i) * rightMap π i j (secondB π j) =
      rightMap π i j (secondA π j) * leftMap π i j (secondB π i)
  | 0, 0 => rfl
  | 1, 1 => rfl
  | 2, 2 => rfl
  | 0, 1 => by
    have hL := mul_invLeft (π := π) 0 1
    have hR := mul_invRight (π := π) 0 1
    have hrel := conic_relation_loc (π := π) 0 1
    apply HomogeneousLocalization.val_injective
    simp only [secondA, secondB, map_one, map_mul, HomogeneousLocalization.val_mul,
      HomogeneousLocalization.val_one, val_leftMap_frac, val_rightMap_frac,
      val_rightMap_constEl]
    linear_combination (-(algebraMap _ _ (conicCoord π 2) * invLeft (π := π) 0 1)) * hR +
      (invLeft (π := π) 0 1 * invRight (π := π) 0 1) * hrel +
      (algebraMap _ _ (conicConst π) * algebraMap _ _ (conicCoord π 0) *
        invRight (π := π) 0 1) * hL
  | 1, 0 => by
    have hL := mul_invLeft (π := π) 1 0
    have hR := mul_invRight (π := π) 1 0
    have hrel := conic_relation_loc (π := π) 1 0
    apply HomogeneousLocalization.val_injective
    simp only [secondA, secondB, map_one, map_mul, HomogeneousLocalization.val_mul,
      HomogeneousLocalization.val_one, val_leftMap_frac, val_rightMap_frac, val_leftMap_constEl]
    linear_combination (algebraMap _ _ (conicCoord π 2) * invRight (π := π) 1 0) * hL -
      (invLeft (π := π) 1 0 * invRight (π := π) 1 0) * hrel -
      (algebraMap _ _ (conicConst π) * algebraMap _ _ (conicCoord π 0) *
        invLeft (π := π) 1 0) * hR
  | 0, 2 => by
    have hL := mul_invLeft (π := π) 0 2
    have hR := mul_invRight (π := π) 0 2
    have hrel := conic_relation_loc (π := π) 0 2
    apply HomogeneousLocalization.val_injective
    simp only [secondA, secondB, map_one, HomogeneousLocalization.val_mul,
      HomogeneousLocalization.val_one, val_leftMap_frac, val_rightMap_frac]
    linear_combination (algebraMap _ _ (conicCoord π 2) * invRight (π := π) 0 2) * hL + hR
  | 2, 0 => by
    have hL := mul_invLeft (π := π) 2 0
    have hR := mul_invRight (π := π) 2 0
    have hrel := conic_relation_loc (π := π) 2 0
    apply HomogeneousLocalization.val_injective
    simp only [secondA, secondB, map_one, HomogeneousLocalization.val_mul,
      HomogeneousLocalization.val_one, val_leftMap_frac, val_rightMap_frac]
    linear_combination (-(algebraMap _ _ (conicCoord π 2) * invLeft (π := π) 2 0)) * hR - hL
  | 1, 2 => by
    have hL := mul_invLeft (π := π) 1 2
    have hR := mul_invRight (π := π) 1 2
    have hrel := conic_relation_loc (π := π) 1 2
    apply HomogeneousLocalization.val_injective
    simp only [secondA, secondB, map_one, map_mul, HomogeneousLocalization.val_mul,
      HomogeneousLocalization.val_one, val_leftMap_frac, val_rightMap_frac, val_leftMap_constEl]
    linear_combination (-(invLeft (π := π) 1 2 * invRight (π := π) 1 2)) * hrel +
      (algebraMap _ _ (conicCoord π 1) * invLeft (π := π) 1 2) * hR + hL
  | 2, 1 => by
    have hL := mul_invLeft (π := π) 2 1
    have hR := mul_invRight (π := π) 2 1
    have hrel := conic_relation_loc (π := π) 2 1
    apply HomogeneousLocalization.val_injective
    simp only [secondA, secondB, map_one, map_mul, HomogeneousLocalization.val_mul,
      HomogeneousLocalization.val_one, val_leftMap_frac, val_rightMap_frac,
      val_rightMap_constEl]
    linear_combination (invLeft (π := π) 2 1 * invRight (π := π) 2 1) * hrel -
      (algebraMap _ _ (conicCoord π 1) * invRight (π := π) 2 1) * hL - hR

end Second

/-! ### The glued projections -/

section Glued

variable {R : Type u} [CommRing R] (π : R)

/-- **The first projection `[T₀ : T₁]` of the conic**, to the integral model of `ℙ¹`. -/
def firstProjectionZ : conicScheme π ⟶ projectiveSpaceAtUniverse.{u} 1 :=
  ProjPoint.glue (conicGrading π) (conicCoord π) (conicCoord_mem π) (fun _ => one_pos)
    (irrelevant_le_span_mk_X _) (firstChart π)
    (fun i j => compat_of_cross _ _ _ _ _ _ _ _ (first_cross i j))

/-- **The second projection `[T₂ : T₀]` of the conic**, to the integral model of `ℙ¹`. -/
def secondProjectionZ : conicScheme π ⟶ projectiveSpaceAtUniverse.{u} 1 :=
  ProjPoint.glue (conicGrading π) (conicCoord π) (conicCoord_mem π) (fun _ => one_pos)
    (irrelevant_le_span_mk_X _) (secondChart π)
    (fun i j => compat_of_cross _ _ _ _ _ _ _ _ (second_cross i j))

/-- **The first projection `X ⟶ ℙ¹_R`**, over `R`. -/
def firstProjection : conicScheme π ⟶ projectiveSpaceOverRing 1 (.of R) :=
  pullback.lift (conicToSpec π) (firstProjectionZ π) (terminal.hom_ext _ _)

/-- **The second projection `X ⟶ ℙ¹_R`**, over `R`. -/
def secondProjection : conicScheme π ⟶ projectiveSpaceOverRing 1 (.of R) :=
  pullback.lift (conicToSpec π) (secondProjectionZ π) (terminal.hom_ext _ _)

/-- The first projection is a morphism over `Spec R`. -/
@[simp] theorem firstProjection_comp_structure :
    firstProjection π ≫ (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R)) = conicToSpec π :=
  pullback.lift_fst _ _ _

/-- The second projection is a morphism over `Spec R`. -/
@[simp] theorem secondProjection_comp_structure :
    secondProjection π ≫ (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R)) = conicToSpec π :=
  pullback.lift_fst _ _ _

end Glued

/-! ### Points followed by the projections -/

section PointComp

variable {R : Type u} [CommRing R] {π : R} {L : Type u} [CommRing L]

/-- The structure morphism of the conic, on points. -/
theorem point_comp_conicToSpec (χ : MvPolynomial (Fin 3) R ⧸ conicIdeal π →+* L) (s : Fin 3)
    (hu : IsUnit (χ (conicCoord π s))) :
    ProjPoint.point (conicGrading π) χ (conicCoord π s) (conicCoord_mem π s) one_pos hu ≫
        conicToSpec π =
      Spec.map (CommRingCat.ofHom (χ.comp ((Ideal.Quotient.mk (conicIdeal π)).comp C))) := by
  unfold conicToSpec
  rw [PlaneCurveModel.toSpec_eq, ← Category.assoc, ProjPoint.point_comp_toSpecZero,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- A point on a chart, followed by the projection glued from local descriptions `[Aᵢ : Bᵢ]`. -/
private theorem point_comp_lift_glue (A B : (i : Fin 3) → Away (conicGrading π) (conicCoord π i))
    (S : Fin 3 → Fin 2) (hU : ∀ i, IsUnit (vecHom _ (A i) (B i) (X (S i))))
    (ch : (i : Fin 3) → Spec (.of (Away (conicGrading π) (conicCoord π i))) ⟶
      AlgebraicGeometry.Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading (ULift.{u} ℤ) 1))
    (hch : ∀ i, ch i = ProjPoint.point _ (vecHom _ (A i) (B i)) (X (S i)) (X_mem _ _) one_pos
      (hU i))
    (hc : ∀ i j, Spec.map (CommRingCat.ofHom (leftMap π i j)) ≫ ch i =
      Spec.map (CommRingCat.ofHom (rightMap π i j)) ≫ ch j)
    (χ : MvPolynomial (Fin 3) R ⧸ conicIdeal π →+* L) (s : Fin 3)
    (hu : IsUnit (χ (conicCoord π s))) :
    ProjPoint.point (conicGrading π) χ (conicCoord π s) (conicCoord_mem π s) one_pos hu ≫
        (pullback.lift (conicToSpec π)
          (ProjPoint.glue (conicGrading π) (conicCoord π) (conicCoord_mem π) (fun _ => one_pos)
            (irrelevant_le_span_mk_X _) ch hc) (terminal.hom_ext _ _) :
          conicScheme π ⟶ projectiveSpaceOverRing 1 (.of R)) =
      pullback.lift
        (Spec.map (CommRingCat.ofHom (χ.comp ((Ideal.Quotient.mk (conicIdeal π)).comp C))))
        (intPointOf (vecHom L (ProjPoint.awayEval _ χ _ hu (A s))
          (ProjPoint.awayEval _ χ _ hu (B s))) (S s)
          (by rw [← comp_vecHom, RingHom.comp_apply]; exact (hU s).map _))
        (terminal.hom_ext _ _) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
    exact point_comp_conicToSpec χ s hu
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
    exact ((ProjPoint.point_comp_glue (conicGrading π) (conicCoord π) (conicCoord_mem π)
      (fun _ => one_pos) (irrelevant_le_span_mk_X _) ch _ χ s hu).trans
      (by rw [hch s]; exact ProjPoint.SpecMap_comp_point _ _ _ _ _ _ _)).trans
      (ProjPoint.point_congr_ringHom _ (comp_vecHom _ _ _ _) _ _ _ _ _)

/-- **The first projection, on points.** -/
theorem point_comp_firstProjection (χ : MvPolynomial (Fin 3) R ⧸ conicIdeal π →+* L) (s : Fin 3)
    (hu : IsUnit (χ (conicCoord π s))) :
    ProjPoint.point (conicGrading π) χ (conicCoord π s) (conicCoord_mem π s) one_pos hu ≫
        firstProjection π =
      pullback.lift
        (Spec.map (CommRingCat.ofHom (χ.comp ((Ideal.Quotient.mk (conicIdeal π)).comp C))))
        (intPointOf (vecHom L (ProjPoint.awayEval _ χ _ hu (firstA π s))
          (ProjPoint.awayEval _ χ _ hu (firstB π s))) (firstS s)
          (by rw [← comp_vecHom, RingHom.comp_apply]; exact (isUnit_first π s).map _))
        (terminal.hom_ext _ _) :=
  point_comp_lift_glue _ _ _ (isUnit_first π) (firstChart π) (fun _ => rfl) _ χ s hu

/-- **The second projection, on points.** -/
theorem point_comp_secondProjection (χ : MvPolynomial (Fin 3) R ⧸ conicIdeal π →+* L) (s : Fin 3)
    (hu : IsUnit (χ (conicCoord π s))) :
    ProjPoint.point (conicGrading π) χ (conicCoord π s) (conicCoord_mem π s) one_pos hu ≫
        secondProjection π =
      pullback.lift
        (Spec.map (CommRingCat.ofHom (χ.comp ((Ideal.Quotient.mk (conicIdeal π)).comp C))))
        (intPointOf (vecHom L (ProjPoint.awayEval _ χ _ hu (secondA π s))
          (ProjPoint.awayEval _ χ _ hu (secondB π s))) (secondS s)
          (by rw [← comp_vecHom, RingHom.comp_apply]; exact (isUnit_second π s).map _))
        (terminal.hom_ext _ _) :=
  point_comp_lift_glue _ _ _ (isUnit_second π) (secondChart π) (fun _ => rfl) _ χ s hu

/-- The value of `awayEval` on a fraction `Tⱼ/Tᵢ`. -/
theorem awayEval_frac (χ : MvPolynomial (Fin 3) R ⧸ conicIdeal π →+* L) (i j : Fin 3)
    (hu : IsUnit (χ (conicCoord π i))) :
    ProjPoint.awayEval _ χ _ hu (frac π i j) = χ (conicCoord π j) * ↑hu.unit⁻¹ := by
  rw [frac, ProjPoint.awayEval_mk, pow_one]

/-- The value of `awayEval` on the uniformizer. -/
theorem awayEval_constEl (χ : MvPolynomial (Fin 3) R ⧸ conicIdeal π →+* L) (i : Fin 3)
    (hu : IsUnit (χ (conicCoord π i))) :
    ProjPoint.awayEval _ χ _ hu (constEl π i) = χ (conicConst π) := by
  rw [constEl, ProjPoint.awayEval_fromZeroRingHom _ _ _ (conicCoord_mem π i)]
  rfl

end PointComp

end Stacks.Models.GenusZero

end

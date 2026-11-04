module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.ChartOrigin
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.ChartNormalizationExplicit
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.ChartDehomogenizedSquare
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.GoodCoordinateExistence

/-!
# A good coordinate stays good at the singular point of the blowup

Let `x₁` be a good coordinate of a Noetherian local ring `A` (generators `x₁, x₂, x₃` of the
maximal ideal with a quadratic relation whose form `q` has `q(0, t₂, t₃)` not a scalar times a
square), and let `𝔪'` be a maximal ideal of the chart `A[𝔪/x₁]` containing `x₁` at which the local
ring has dimension two and is not regular. Then the residue field there is that of `A`, and the
image of `x₁` is a good coordinate of the local ring there.

This is the case I argument of [Stacks, Section 54.12]: the singular point is `κ`-rational (the
Claim); moving it to the origin of the chart makes the first row of the quadratic form vanish; and
the quadratic form at the point, for the generators `x₁, x₂'/x₁, x₃'/x₁`, has the same restriction
to `t₁ = 0` as the quadratic form of `A`.

## Main results

* `AlgebraicGeometry.surjective_and_isGoodCoordinate_of_chart`
-/

@[expose] public noncomputable section

open IsLocalRing MvPolynomial

universe u

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A] [IsLocalRing A] {x : Fin 3 → A}
  (S : Type u) [CommRing S] [Algebra A S] [IsLocalization.Away (x 0) S]

/-- **(A2) of [Stacks, Section 54.12] at a point of the first chart.** If `x 0` is a good
coordinate of `A` and `z` is a maximal ideal of the chart `A[𝔪/x 0]` containing `x 0` at which the
local ring has dimension at least two and is not regular, then every element of the residue field
at `z` is the residue of an element of `A`, and the image of `x 0` is the first generator of a good
relation of the local ring at `z`. -/
theorem surjective_and_isGoodCoordinate_of_chart [IsNoetherianRing A]
    (hspan : Ideal.span (Set.range x) = maximalIdeal A)
    (a : Fin 3 → Fin 3 → A) (b : Fin 3 → Fin 3 → Fin 3 → A) (hupper : ∀ p q, q < p → a p q = 0)
    (hunit : ∃ p q, p ≤ q ∧ a p q ∉ maximalIdeal A)
    (hrel : ∑ p, ∑ q, a p q * (x p * x q) = ∑ p, ∑ q, ∑ r, b p q r * (x p * x q * x r))
    (hgood : IsGoodCoordinateForm fun p q => residue A (a p q))
    (z : Ideal (affineBlowupAlgebra (maximalIdeal A) (x 0) S)) [hz : z.IsMaximal]
    (h0 : algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (x 0) ∈ z)
    [IsNoetherianRing (Localization.AtPrime z)]
    (hdim : 2 ≤ ringKrullDim (Localization.AtPrime z))
    (hsing : ¬ IsRegularLocalRing (Localization.AtPrime z)) :
    let φ := (algebraMap (affineBlowupAlgebra (maximalIdeal A) (x 0) S)
      (Localization.AtPrime z)).comp (algebraMap A _)
    Function.Surjective ((residue (Localization.AtPrime z)).comp φ) ∧
      IsFirstGeneratorOfGoodRelation (Localization.AtPrime z) (φ (x 0)) := by
  intro φ
  have hx : ∀ i, x i ∈ maximalIdeal A := fun i => hspan ▸ Ideal.subset_span ⟨i, rfl⟩
  have hcase := hgood.not_isScalarSqLinear
  have hrel3 : ∑ p, ∑ q, a p q * (x p * x q) ∈ maximalIdeal A ^ 3 := by
    rw [hrel]; exact cubicExpansion_mem_pow_three hspan b
  obtain ⟨hM, hmem⟩ := dehomogenized_mem_sq_of_not_isRegularLocalRing S hx hspan a hupper hrel3 z
    h0 hdim hsing
  set M := Ideal.comap (chartPresentation S hx)
    (Ideal.map (Ideal.Quotient.mk (Ideal.span
      {algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (x 0)})) z) with hMdef
  have hunitk : ∃ p q, p ≤ q ∧ residue A (a p q) ≠ 0 := by
    obtain ⟨p, q, hpq, hne⟩ := hunit
    exact ⟨p, q, hpq, fun h => hne ((residue_eq_zero_iff _).mp h)⟩
  obtain ⟨c, hc⟩ := exists_eval_eq_zero_of_bijective_algebraMap_quotient M
    (bijective_algebraMap_quotient_of_not_isScalarSqLinear (fun p q => residue A (a p q))
      (fun p q h => by rw [hupper p q h, map_zero]) hunitk hcase M hM.ne_top hmem)
  -- the point is singular on the exceptional quadric
  have hconst : residue A (a 0 0) + residue A (a 0 1) * c 0 + residue A (a 0 2) * c 1 +
      residue A (a 1 1) * (c 0 * c 0) + residue A (a 1 2) * (c 0 * c 1) +
      residue A (a 2 2) * (c 1 * c 1) = 0 := by
    have h := hc _ (Ideal.pow_le_self (by norm_num) hmem)
    simp only [map_add, map_mul, map_pow, eval_C, eval_X] at h
    linear_combination h
  have hlin₂ : residue A (a 0 1) + 2 * (residue A (a 1 1) * c 0) + residue A (a 1 2) * c 1 = 0 := by
    have h := hc _ ((MvPolynomial.pderiv (0 : Fin 2)).map_mem_of_mem_ideal_sq M hmem)
    simp [mul_comm, mul_left_comm, mul_assoc] at h
    linear_combination h
  have hlin₃ : residue A (a 0 2) + residue A (a 1 2) * c 0 + 2 * (residue A (a 2 2) * c 1) = 0 := by
    have h := hc _ ((MvPolynomial.pderiv (1 : Fin 2)).map_mem_of_mem_ideal_sq M hmem)
    simp [mul_comm, mul_left_comm, mul_assoc] at h
    linear_combination h
  -- the coordinates of the point lie in its ideal
  have hker : M = RingHom.ker (MvPolynomial.eval c) := by
    refine hM.eq_of_le (RingHom.ker_ne_top _) fun f hf => ?_
    rw [RingHom.mem_ker]; exact hc f hf
  have hXc : ∀ i : Fin 2, MvPolynomial.X i - MvPolynomial.C (c i) ∈ M := by
    intro i; rw [hker, RingHom.mem_ker]; simp
  -- move the point to the origin
  obtain ⟨y, a', b', hspan', hupper', ha00, ha01, ha02, hrestrict, -, hrel', -, hy0, u, v, hu, hv,
    hy1, hy2⟩ := exists_quadraticRelation_vanishing_first_row_explicit x hspan a b hupper hrel hcase
      c hconst hlin₂ hlin₃
  let A' := affineBlowupAlgebra (maximalIdeal A) (x 0) S
  let J : Ideal A' := Ideal.span {algebraMap A A' (x 0)}
  have hJz : J ≤ z := (Ideal.span_singleton_le_iff_mem _).mpr h0
  have hcomapz : Ideal.comap (Ideal.Quotient.mk J) (Ideal.map (Ideal.Quotient.mk J) z) = z := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.mpr hJz]
  have hFz : ∀ (i : Fin 2) (w : A), residue A w = c i →
      chartFraction S hx i.succ - algebraMap A A' w ∈ z := by
    intro i w hw
    have h := hXc i
    rw [hMdef, Ideal.mem_comap, map_sub] at h
    have e1 : chartPresentation S hx (MvPolynomial.X i) =
        Ideal.Quotient.mk J (chartFraction S hx i.succ) := by
      rw [chartPresentation, MvPolynomial.eval₂Hom_X']
    have e2 : chartPresentation S hx (MvPolynomial.C (c i)) =
        Ideal.Quotient.mk J (algebraMap A A' w) := by
      rw [← hw, chartPresentation, MvPolynomial.eval₂Hom_C, chartResidue_residue]
    rw [e1, e2, ← map_sub] at h
    rw [← hcomapz]
    exact h
  -- the fractions of the new generators
  let f : Fin 3 → A' := ![1, chartFraction S hx 1 - algebraMap A A' u,
    chartFraction S hx 2 - algebraMap A A' v]
  have hf : ∀ i, algebraMap A A' (x 0) * f i = algebraMap A A' (y i) := by
    have e0 : algebraMap A A' (x 0) * f 0 = algebraMap A A' (y 0) := by
      change algebraMap A A' (x 0) * 1 = _
      rw [mul_one, hy0]
    have e1 : algebraMap A A' (x 0) * f 1 = algebraMap A A' (y 1) := by
      change algebraMap A A' (x 0) * (chartFraction S hx 1 - algebraMap A A' u) = _
      rw [mul_sub, algebraMap_mul_chartFraction, hy1, map_sub, map_mul]
      ring
    have e2 : algebraMap A A' (x 0) * f 2 = algebraMap A A' (y 2) := by
      change algebraMap A A' (x 0) * (chartFraction S hx 2 - algebraMap A A' v) = _
      rw [mul_sub, algebraMap_mul_chartFraction, hy2, map_sub, map_mul]
      ring
    intro i
    fin_cases i
    exacts [e0, e1, e2]
  have h1 : f 1 ∈ z := hFz 0 u hu
  have h2 : f 2 ∈ z := hFz 1 v hv
  obtain ⟨hXspan, hres, c', hupper'', hrestr, hrel''⟩ :=
    exists_relation_at_chart_origin' (x 0) hy0 S hspan' a' b' hupper' ha00 ha01 ha02 hrel' z h0 f
      hf h1 h2 hdim hsing
  refine ⟨hres, ?_⟩
  -- the residue field map is bijective
  have : IsLocalHom φ := by
    refine ⟨fun r hr => ?_⟩
    by_contra hn
    have hrm : r ∈ maximalIdeal A := (mem_nonunits_iff.mpr hn)
    have : algebraMap A A' r ∈ z := by
      have : algebraMap A A' r ∈ J := by
        change _ ∈ Ideal.span {algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x 0) S) (x 0)}
        rw [← affineBlowupAlgebra.map_ideal_eq_span_singleton (maximalIdeal A) (x 0) (hx 0)]
        exact Ideal.mem_map_of_mem _ hrm
      exact hJz this
    have hmem' : φ r ∈ maximalIdeal (Localization.AtPrime z) := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ this
    exact (mem_maximalIdeal _).mp hmem' hr
  have hbij : Function.Bijective (ResidueField.map φ) := by
    refine ⟨(ResidueField.map φ).injective, fun t => ?_⟩
    obtain ⟨r, hr⟩ := hres t
    exact ⟨residue A r, by rw [ResidueField.map_residue]; exact hr⟩
  refine ⟨_, c', rfl, hXspan, hupper'', hrel'', ?_⟩
  refine IsGoodCoordinateForm.of_restrictFirstVar_eq (a := fun p q => ResidueField.map φ
    (residue A (a p q))) (fun p q => ?_) ((isGoodCoordinateForm_map_iff _ hbij _).mpr hgood)
  rw [hrestr p q, hrestrict p q]
  exact (ResidueField.map_residue φ _).symm

end AlgebraicGeometry

end

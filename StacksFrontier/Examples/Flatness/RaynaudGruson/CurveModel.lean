module

public import Mathlib.RingTheory.Localization.FractionRing
public import StacksFrontier.Examples.Flatness.RaynaudGruson.Structure

/-!
# The plane curve model of the Raynaud--Gruson construction

Killing the variables `z₁, z₂, …` turns `C` into a localization of `k[X][V]`, the coordinate
ring of the plane curve `x z² + z + y = 0` written with `x = X` and `z = V`. Over that model
`qₙ` contains `X V + X^{n+1} + 1`, which vanishes at the point `V = -X⁻¹ - Xⁿ` of `k(X)`, a
point depending injectively on `n`.

## Main results

* `Stacks.Examples.RaynaudGruson.exists_not_mem_idealQ`: an element of `C` outside `q_C` lies
  outside `qₙ` for some `n`.

## Implementation notes

A nonzero polynomial has finitely many roots, so an element of the curve model killed by every
one of the evaluations `V ↦ -X⁻¹ - Xⁿ` vanishes; and the kernel of the model map is contained
in `q_C` because evaluation of the model at the origin is a residue map of `q_C`.

## References

* [Stacks Project, Tag 05G2](https://stacks.math.columbia.edu/tag/05G2)
-/

@[expose] public section

noncomputable section

namespace Stacks.Examples.RaynaudGruson

universe u

variable (k : Type u) [Field k]

attribute [local instance] baseRingCommRing

/-- Polynomials in `V` over `k[X]`. -/
private abbrev CurvePolynomial := Polynomial (Polynomial k)

/-- The coordinate `X` of `k[X][V]`. -/
private def cX : CurvePolynomial k := Polynomial.C Polynomial.X

/-- The coordinate `V` of `k[X][V]`. -/
private def cV : CurvePolynomial k := Polynomial.X

/-- The map `k[x,y] → k[X][V]` sending `x` to `X` and `y` to `-X V² - V`. -/
private def planeToCurve : PlanePolynomial k →+* CurvePolynomial k :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp Polynomial.C)
    ![cX k, -(cX k * cV k ^ 2) - cV k]

/-- The elements of `k[X][V]` that are inverted in the curve model. -/
private def curveSubmonoid : Submonoid (CurvePolynomial k) :=
  Submonoid.closure (planeToCurve k '' originSubmonoid k ∪ {2 * cX k * cV k + 1})

/-- The curve model, a localization of `k[X][V]` receiving `C`. -/
private abbrev curveModel := Localization (curveSubmonoid k)

/-- The localization map of the curve model. -/
private abbrev toCurveModel : CurvePolynomial k →+* curveModel k :=
  algebraMap (CurvePolynomial k) (curveModel k)

private lemma planeToCurve_mem (s : originSubmonoid k) :
    planeToCurve k (s : PlanePolynomial k) ∈ curveSubmonoid k :=
  Submonoid.subset_closure (Or.inl ⟨s, s.2, rfl⟩)

private lemma curveDenominator_mem : 2 * cX k * cV k + 1 ∈ curveSubmonoid k :=
  Submonoid.subset_closure (Or.inr rfl)

@[simp]
private lemma planeToCurve_X_zero : planeToCurve k (MvPolynomial.X 0) = cX k := by
  simp [planeToCurve]

@[simp]
private lemma planeToCurve_X_one :
    planeToCurve k (MvPolynomial.X 1) = -(cX k * cV k ^ 2) - cV k := by
  simp [planeToCurve]

/-- The map `A₀ → C/IC` of the curve model. -/
private def baseToCurve : baseRing k →+* curveModel k :=
  IsLocalization.lift (M := originSubmonoid k)
    (g := (toCurveModel k).comp (planeToCurve k))
    fun s => IsLocalization.map_units (curveModel k)
      (⟨planeToCurve k (s : PlanePolynomial k), planeToCurve_mem k s⟩ : curveSubmonoid k)

private lemma baseToCurve_algebraMap (p : PlanePolynomial k) :
    baseToCurve k (algebraMap (PlanePolynomial k) (baseRing k) p) =
      toCurveModel k (planeToCurve k p) :=
  IsLocalization.lift_eq _ _

private lemma relationIdeal_le_ker :
    relationIdeal k ≤
      RingHom.ker (MvPolynomial.eval₂Hom (baseToCurve k) fun _ : PNat => (0 : curveModel k)) := by
  refine Ideal.span_le.mpr ?_
  rintro _ (⟨⟨i, j⟩, rfl⟩ | ⟨i, rfl⟩) <;> simp [RingHom.mem_ker]

/-- The map `A → C/IC` of the curve model, which kills every `zₙ`. -/
private def aToCurve : ringA k →+* curveModel k :=
  Ideal.Quotient.lift (relationIdeal k)
    (MvPolynomial.eval₂Hom (baseToCurve k) fun _ => 0)
    fun _ ha => relationIdeal_le_ker k ha

private lemma aToCurve_mk (p : MvPolynomial PNat (baseRing k)) :
    aToCurve k (Ideal.Quotient.mk (relationIdeal k) p) =
      MvPolynomial.eval₂Hom (baseToCurve k) (fun _ => 0) p :=
  Ideal.Quotient.lift_mk _ _ _

@[simp]
private lemma aToCurve_zA (n : PNat) : aToCurve k (zA k n) = 0 := by
  rw [zA, aToCurve_mk]
  simp

private lemma aToCurve_baseToA (a : baseRing k) :
    aToCurve k (baseToA k a) = baseToCurve k a := by
  show aToCurve k (Ideal.Quotient.mk (relationIdeal k) (MvPolynomial.C a)) = _
  rw [aToCurve_mk]
  simp

@[simp]
private lemma aToCurve_xA : aToCurve k (xA k) = toCurveModel k (cX k) := by
  rw [xA, aToCurve_baseToA, x0, baseToCurve_algebraMap, planeToCurve_X_zero]

@[simp]
private lemma aToCurve_yA :
    aToCurve k (yA k) = toCurveModel k (-(cX k * cV k ^ 2) - cV k) := by
  rw [yA, aToCurve_baseToA, y0, baseToCurve_algebraMap, planeToCurve_X_one]

/-- The polynomial `y + xⁿ + x^{2n+1}` of `k[x,y]`. -/
private def fPlane (n : PNat) : PlanePolynomial k :=
  MvPolynomial.X 1 + MvPolynomial.X 0 ^ (n : ℕ) + MvPolynomial.X 0 ^ (2 * (n : ℕ) + 1)

private lemma f_eq_algebraMap (n : PNat) :
    f k n = algebraMap (PlanePolynomial k) (baseRing k) (fPlane k n) := by
  simp [f, fPlane, x0, y0]

private lemma aToCurve_fA (n : PNat) :
    aToCurve k (fA k n) = toCurveModel k (planeToCurve k (fPlane k n)) := by
  rw [fA, aToCurve_baseToA, f_eq_algebraMap, baseToCurve_algebraMap]

private lemma cRelationIdeal_le_ker :
    cRelationIdeal k ≤
      RingHom.ker (MvPolynomial.eval₂Hom (aToCurve k)
        fun _ : Unit => toCurveModel k (cV k)) := by
  refine Ideal.span_le.mpr ?_
  rintro _ rfl
  rw [SetLike.mem_coe, RingHom.mem_ker]
  simp only [cRelation, map_add, map_mul, map_pow, MvPolynomial.eval₂Hom_C,
    MvPolynomial.eval₂Hom_X', aToCurve_xA, aToCurve_yA]
  rw [← map_pow, ← map_mul, ← map_add, ← map_add,
    show cX k * cV k ^ 2 + cV k + (-(cX k * cV k ^ 2) - cV k) = 0 from by ring]
  exact map_zero _

/-- The map `A[z]/(xz²+z+y) → C/IC` of the curve model. -/
private def cQuotientToCurve : cQuotient k →+* curveModel k :=
  Ideal.Quotient.lift (cRelationIdeal k)
    (MvPolynomial.eval₂Hom (aToCurve k) fun _ => toCurveModel k (cV k))
    fun _ ha => cRelationIdeal_le_ker k ha

private lemma cQuotientToCurve_mk (p : MvPolynomial Unit (ringA k)) :
    cQuotientToCurve k (Ideal.Quotient.mk (cRelationIdeal k) p) =
      MvPolynomial.eval₂Hom (aToCurve k) (fun _ => toCurveModel k (cV k)) p :=
  Ideal.Quotient.lift_mk _ _ _

private lemma cQuotientToCurve_cDenominator :
    cQuotientToCurve k (cDenominator k) = toCurveModel k (2 * cX k * cV k + 1) := by
  rw [cDenominator, cQuotientToCurve_mk]
  simp only [map_add, map_mul, map_one, map_ofNat, MvPolynomial.eval₂Hom_C,
    MvPolynomial.eval₂Hom_X', aToCurve_xA]

/-- The map `C → C/IC` of the curve model. -/
private def ringCToCurve : ringC k →+* curveModel k :=
  IsLocalization.Away.lift (cDenominator k)
    (show IsUnit (cQuotientToCurve k (cDenominator k)) by
      rw [cQuotientToCurve_cDenominator]
      exact IsLocalization.map_units (curveModel k)
        (⟨2 * cX k * cV k + 1, curveDenominator_mem k⟩ : curveSubmonoid k))

private lemma ringCToCurve_algebraMap (c : cQuotient k) :
    ringCToCurve k (algebraMap (cQuotient k) (ringC k) c) = cQuotientToCurve k c :=
  IsLocalization.Away.lift_eq _ _ _

private lemma ringCToCurve_aToC (a : ringA k) :
    ringCToCurve k (aToC k a) = aToCurve k a := by
  show ringCToCurve k (algebraMap (cQuotient k) (ringC k)
    (Ideal.Quotient.mk (cRelationIdeal k) (MvPolynomial.C a))) = _
  rw [ringCToCurve_algebraMap, cQuotientToCurve_mk]
  simp

@[simp]
private lemma ringCToCurve_zC : ringCToCurve k (zC k) = toCurveModel k (cV k) := by
  rw [zC, ringCToCurve_algebraMap, cQuotientToCurve_mk]
  simp

@[simp]
private lemma ringCToCurve_xC : ringCToCurve k (xC k) = toCurveModel k (cX k) := by
  rw [xC, ringCToCurve_aToC, aToCurve_xA]

@[simp]
private lemma ringCToCurve_yC :
    ringCToCurve k (yC k) = toCurveModel k (-(cX k * cV k ^ 2) - cV k) := by
  rw [yC, ringCToCurve_aToC, aToCurve_yA]

@[simp]
private lemma ringCToCurve_zCIndex (n : PNat) : ringCToCurve k (zCIndex k n) = 0 := by
  rw [zCIndex, ringCToCurve_aToC, aToCurve_zA]

/-- Evaluation of `k[X][V]` at the origin. -/
private def curveEvalOrigin : CurvePolynomial k →+* k :=
  (Polynomial.evalRingHom (0 : k)).comp (Polynomial.evalRingHom (0 : Polynomial k))

@[simp]
private lemma curveEvalOrigin_cX : curveEvalOrigin k (cX k) = 0 := by
  simp [curveEvalOrigin, cX]

@[simp]
private lemma curveEvalOrigin_cV : curveEvalOrigin k (cV k) = 0 := by
  simp [curveEvalOrigin, cV]

private lemma curveEvalOrigin_comp_planeToCurve :
    (curveEvalOrigin k).comp (planeToCurve k) = MvPolynomial.eval (0 : Fin 2 → k) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · simp [planeToCurve, curveEvalOrigin]
  · fin_cases i <;> simp [planeToCurve]

/-- The residue map of the curve model at the origin. -/
private def curveToResidue : curveModel k →+* k :=
  IsLocalization.lift (M := curveSubmonoid k) (g := curveEvalOrigin k) <| by
    have hle : curveSubmonoid k ≤ Submonoid.comap (curveEvalOrigin k) (nonZeroDivisors k) := by
      refine Submonoid.closure_le.mpr ?_
      rintro _ (⟨p, hp, rfl⟩ | rfl)
      · have h : curveEvalOrigin k (planeToCurve k p) = MvPolynomial.eval (0 : Fin 2 → k) p :=
          RingHom.congr_fun (curveEvalOrigin_comp_planeToCurve k) p
        exact Submonoid.mem_comap.mpr (h ▸ hp)
      · simp
    exact fun s => isUnit_of_mem_nonZeroDivisors (hle s.2)

private lemma curveToResidue_algebraMap (p : CurvePolynomial k) :
    curveToResidue k (toCurveModel k p) = curveEvalOrigin k p :=
  IsLocalization.lift_eq _ _

/-- The composite of the curve model with its residue at the origin. -/
private def residueViaCurve : ringC k →+* k := (curveToResidue k).comp (ringCToCurve k)

private lemma ker_residueViaCurve : RingHom.ker (residueViaCurve k) = idealQC k := by
  refine ((idealQC_isMaximal k).eq_of_le ?_ ?_).symm
  · intro htop
    have h : residueViaCurve k 1 = 0 := by
      simpa [RingHom.mem_ker] using (Ideal.eq_top_iff_one _).mp htop
    simp at h
  · refine Ideal.span_le.mpr ?_
    rintro c (rfl | rfl | rfl | ⟨n, rfl⟩) <;>
      simp [SetLike.mem_coe, RingHom.mem_ker, residueViaCurve, curveToResidue_algebraMap]

/-- The point `V = -X⁻¹ - Xⁿ` of the curve lying over `qₙ`. -/
private def curvePoint (n : PNat) : FractionRing (Polynomial k) :=
  -(algebraMap (Polynomial k) (FractionRing (Polynomial k)) Polynomial.X)⁻¹ -
    (algebraMap (Polynomial k) (FractionRing (Polynomial k)) Polynomial.X) ^ (n : ℕ)

private lemma algebraMap_X_ne_zero :
    algebraMap (Polynomial k) (FractionRing (Polynomial k)) Polynomial.X ≠ 0 := by
  rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)]
  exact Polynomial.X_ne_zero

private lemma curvePoint_injective : Function.Injective (curvePoint k) := by
  intro n m h
  have h' : (algebraMap (Polynomial k) (FractionRing (Polynomial k)) Polynomial.X) ^ (n : ℕ) =
      (algebraMap (Polynomial k) (FractionRing (Polynomial k)) Polynomial.X) ^ (m : ℕ) := by
    have := sub_right_injective h
    simpa using this
  rw [← map_pow, ← map_pow] at h'
  have hp : (Polynomial.X : Polynomial k) ^ (n : ℕ) = Polynomial.X ^ (m : ℕ) :=
    FaithfulSMul.algebraMap_injective (Polynomial k) (FractionRing (Polynomial k)) h'
  have hd : (n : ℕ) = (m : ℕ) := by simpa using congrArg Polynomial.natDegree hp
  exact PNat.coe_injective hd

/-- Evaluation of `k[X][V]` at the point `V = -X⁻¹ - Xⁿ` of `k(X)`. -/
private def curvePolyToFraction (n : PNat) :
    CurvePolynomial k →+* FractionRing (Polynomial k) :=
  (Polynomial.evalRingHom (curvePoint k n)).comp
    (Polynomial.mapRingHom (algebraMap (Polynomial k) (FractionRing (Polynomial k))))

@[simp]
private lemma curvePolyToFraction_cX (n : PNat) :
    curvePolyToFraction k n (cX k) =
      algebraMap (Polynomial k) (FractionRing (Polynomial k)) Polynomial.X := by
  simp [curvePolyToFraction, cX]

@[simp]
private lemma curvePolyToFraction_cV (n : PNat) :
    curvePolyToFraction k n (cV k) = curvePoint k n := by
  simp [curvePolyToFraction, cV]

private lemma curvePolyToFraction_comp_planeToCurve (n : PNat) :
    (curvePolyToFraction k n).comp (planeToCurve k) =
      (algebraMap (Polynomial k) (FractionRing (Polynomial k))).comp (curveEval k n) := by
  have hx := algebraMap_X_ne_zero k
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · simp [planeToCurve, curveEval, curvePolyToFraction]
  · fin_cases i
    · simp [planeToCurve, curveEval]
    · simp only [RingHom.comp_apply, planeToCurve, curveEval, MvPolynomial.eval₂Hom_X']
      show curvePolyToFraction k n (-(cX k * cV k ^ 2) - cV k) =
        algebraMap (Polynomial k) (FractionRing (Polynomial k))
          (-(Polynomial.X ^ (n : ℕ)) - Polynomial.X ^ (2 * (n : ℕ) + 1))
      simp only [map_sub, map_neg, map_mul, map_pow, curvePolyToFraction_cX,
        curvePolyToFraction_cV, curvePoint]
      field_simp
      ring

private lemma curvePolyToFraction_planeToCurve (n : PNat) (p : PlanePolynomial k) :
    curvePolyToFraction k n (planeToCurve k p) =
      algebraMap (Polynomial k) (FractionRing (Polynomial k)) (curveEval k n p) :=
  RingHom.congr_fun (curvePolyToFraction_comp_planeToCurve k n) p

private lemma curvePolyToFraction_denominator_ne_zero (n : PNat) :
    curvePolyToFraction k n (2 * cX k * cV k + 1) ≠ 0 := by
  have hx := algebraMap_X_ne_zero k
  have key : curvePolyToFraction k n (2 * cX k * cV k + 1) =
      algebraMap (Polynomial k) (FractionRing (Polynomial k))
        (-1 - 2 * Polynomial.X ^ ((n : ℕ) + 1)) := by
    simp only [map_add, map_mul, map_one, map_ofNat, curvePolyToFraction_cX,
      curvePolyToFraction_cV, curvePoint, map_sub, map_neg, map_pow]
    field_simp
    ring
  rw [key, Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)]
  intro h0
  have h1 := congrArg (Polynomial.eval (0 : k)) h0
  simp at h1

/-- Evaluation of the curve model at the point `V = -X⁻¹ - Xⁿ`. -/
private def curveToFraction (n : PNat) : curveModel k →+* FractionRing (Polynomial k) :=
  IsLocalization.lift (M := curveSubmonoid k) (g := curvePolyToFraction k n) <| by
    have hle : curveSubmonoid k ≤
        Submonoid.comap (curvePolyToFraction k n) (nonZeroDivisors _) := by
      refine Submonoid.closure_le.mpr ?_
      rintro _ (⟨p, hp, rfl⟩ | rfl)
      · refine Submonoid.mem_comap.mpr (mem_nonZeroDivisors_of_ne_zero ?_)
        rw [curvePolyToFraction_planeToCurve, Ne,
          map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)]
        intro h0
        have hz := curveEval_eval_zero k n p
        rw [h0] at hz
        refine (mem_nonZeroDivisors_iff_ne_zero.mp hp) ?_
        simpa using hz.symm
      · exact Submonoid.mem_comap.mpr
          (mem_nonZeroDivisors_of_ne_zero (curvePolyToFraction_denominator_ne_zero k n))
    exact fun s => isUnit_of_mem_nonZeroDivisors (hle s.2)

private lemma curveToFraction_algebraMap (n : PNat) (p : CurvePolynomial k) :
    curveToFraction k n (toCurveModel k p) = curvePolyToFraction k n p :=
  IsLocalization.lift_eq _ _

private lemma eq_zero_of_forall_curveToFraction (w : curveModel k)
    (h : ∀ n : PNat, curveToFraction k n w = 0) : w = 0 := by
  obtain ⟨a, s, hs⟩ : ∃ (a : CurvePolynomial k) (s : curveSubmonoid k),
      w * toCurveModel k (s : CurvePolynomial k) = toCurveModel k a := by
    obtain ⟨⟨a, s⟩, h'⟩ := IsLocalization.surj (curveSubmonoid k) w
    exact ⟨a, s, h'⟩
  have hroot : ∀ n : PNat,
      (a.map (algebraMap (Polynomial k) (FractionRing (Polynomial k)))).IsRoot
        (curvePoint k n) := by
    intro n
    have hn := congrArg (curveToFraction k n) hs
    rw [map_mul, h n, zero_mul, curveToFraction_algebraMap] at hn
    simpa [Polynomial.IsRoot, curvePolyToFraction] using hn.symm
  have hAzero : a.map (algebraMap (Polynomial k) (FractionRing (Polynomial k))) = 0 := by
    by_contra hne
    exact (Polynomial.finite_setOfPred_isRoot hne).not_infinite
      (Set.infinite_of_injective_forall_mem (curvePoint_injective k) hroot)
  have ha : a = 0 :=
    Polynomial.map_injective _ (FaithfulSMul.algebraMap_injective _ _) (by simpa using hAzero)
  rw [ha, map_zero] at hs
  exact (IsUnit.mul_left_eq_zero (IsLocalization.map_units (curveModel k) s)).mp hs

/-- Restricting `C` to the curve model and evaluating at the `n`-th curve point is the
restriction `Stacks.Examples.RaynaudGruson.rationalCurveC` of `C` to that point. -/
private lemma curveToFraction_comp_ringCToCurve (n : PNat) :
    (curveToFraction k n).comp (ringCToCurve k) = rationalCurveC k n := by
  refine ringC_hom_ext k (Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun a => ?_)
    (fun i => ?_))) ?_
  · have hb : ((curveToFraction k n).comp (ringCToCurve k)).comp ((aToC k).comp (baseToA k)) =
        (rationalCurveC k n).comp ((aToC k).comp (baseToA k)) := by
      refine IsLocalization.ringHom_ext (originSubmonoid k) (RingHom.ext fun p => ?_)
      simp only [RingHom.comp_apply]
      rw [rationalCurveC_aToC_baseToA_algebraMap, ringCToCurve_aToC, aToCurve_baseToA,
        baseToCurve_algebraMap, curveToFraction_algebraMap, curvePolyToFraction_planeToCurve]
    exact RingHom.congr_fun hb a
  · show curveToFraction k n (ringCToCurve k (zCIndex k i)) = rationalCurveC k n (zCIndex k i)
    rw [ringCToCurve_zCIndex, rationalCurveC_zCIndex, map_zero]
  · rw [RingHom.comp_apply, ringCToCurve_zC, curveToFraction_algebraMap, curvePolyToFraction_cV,
      rationalCurveC_zC_eq, curvePoint]
    ring

/-- An element of `C` outside the distinguished prime `q_C` lies outside `qₙ` for some `n`. -/
theorem exists_not_mem_idealQ (c : ringC k) (hc : c ∉ idealQC k) :
    ∃ n : PNat, c ∉ idealQ k n := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have hzero : ringCToCurve k c = 0 :=
    eq_zero_of_forall_curveToFraction k _ fun n => by
      rw [← RingHom.comp_apply, curveToFraction_comp_ringCToCurve]
      exact RingHom.mem_ker.mp (idealQ_le_ker_rationalCurveC k n (hcon n))
  refine hc ?_
  rw [← ker_residueViaCurve k, RingHom.mem_ker, residueViaCurve, RingHom.comp_apply, hzero,
    map_zero]

end Stacks.Examples.RaynaudGruson

end

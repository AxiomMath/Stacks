module

public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.DimensionDropCycles
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GenericFibreCurve
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.OrdPreimmersion
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullbackCycles.SchemeTheoreticImage

/-!
# Proper pushforward of a principal divisor when the image drops dimension

Let `p : X ⟶ Y` be a proper morphism over the base with `X` integral of delta-dimension `n`. If the
scheme-theoretic image of `p` does not have delta-dimension `n`, then the proper pushforward of the
principal divisor of every rational function on `X` is zero.

## Main results

* `Stacks.Chow.residueDegree_genericFibreCurveToSpec`: the residue degree of a point of the generic
  fibre curve of `p` equals the residue degree of `p` at its image in `X`.
* `Stacks.Chow.properPushforward_principalDivisorCycle_eq_zero_of_isDominant`: for a proper
  dominant `p` of integral schemes with `dim_δ(X) = n` and `dim_δ(Y) = n - 1`, the proper
  pushforward of every principal divisor on `X` vanishes.
* `Stacks.Chow.properPushforward_principalDivisorCycle_eq_zero_of_schemeDeltaDimension_image_ne`:
  for a proper `p` whose scheme-theoretic image does not have delta-dimension `n`, the proper
  pushforward of every principal divisor on `X` vanishes.

## References

* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
* [Stacks Project, Tag 02RT](https://stacks.math.columbia.edu/tag/02RT)
* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
* [Stacks Project, Tag 02R5](https://stacks.math.columbia.edu/tag/02R5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-- The residue degree of `genericFibreCurveToSpec p` at a point `z` of the generic fibre curve
equals the residue degree of `p` at the image of `z` in `X`. -/
theorem residueDegree_genericFibreCurveToSpec {X Y : Scheme.{u}} (p : X ⟶ Y) [IsIntegral X]
    (z : (genericFibreCurve p).subscheme) :
    (genericFibreCurveToSpec p).residueDegree z =
      p.residueDegree ((genericFibreCurveι p).base z) := by
  have h := congrArg (fun h : (genericFibreCurve p).subscheme ⟶ Y ↦ h.residueDegree z)
    (genericFibreCurveι_fac p)
  rw [residueDegree_comp (genericFibreCurveι p) p z,
    residueDegree_comp (genericFibreCurveToSpec p) (genericFibreFromSpec p) z,
    residueDegree_eq_one_of_isPreimmersion (genericFibreCurveι p) z,
    residueDegree_eq_one_of_isPreimmersion (genericFibreFromSpec p)
      ((genericFibreCurveToSpec p).base z), mul_one, one_mul] at h
  exact h.symm

/-- For a proper dominant `p : X ⟶ Y` of integral schemes over the base with `dim_δ(X) = n` and
`dim_δ(Y) = n - 1`, the proper pushforward of the principal divisor of any rational function on `X`
is zero. -/
theorem properPushforward_principalDivisorCycle_eq_zero_of_isDominant
    (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] [IsIntegral X] [IsIntegral Y] {n : ℤ}
    (hnX : schemeDeltaDimension C sX = (n : EInt))
    (hnY : schemeDeltaDimension C sY = ((n - 1 : ℤ) : EInt))
    (p : X ⟶ Y) [IsProper p] [IsDominant p] (hp : p ≫ sY = sX) (g : X.functionField) :
    properPushforward C sX sY p hp (n - 1) (principalDivisorCycle C sX hnX g) = 0 := by
  classical
  have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  by_cases hg : g = 0
  · have hzero : principalDivisorCycle C sX hnX (0 : X.functionField) = 0 := by
      refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
      rw [principalDivisorCycle_apply, Scheme.ord_zero]
      rfl
    rw [hg, hzero, properPushforward_zero]
  have hpcomp : LocallyOfFiniteType (p ≫ sY) := by rw [hp]; infer_instance
  have _ : LocallyOfFiniteType p := locallyOfFiniteType_of_comp p sY
  have _ : Subsingleton
      ((fieldChowSituation ↥(Y.residueField (p.base (genericPoint X)))).S) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum _))
  have _ : IsLocallyNoetherian (genericFibreCurve p).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (genericFibreCurveToSpec p)
  have hgenY : p.base (genericPoint X) = genericPoint Y :=
    ((tfae_isDominant_of_isIntegral p).out 1 2).mp (inferInstance : IsDominant p)
  have hyrel : relativeDimension C.dimensionFunction sY (genericPoint Y) = n - 1 :=
    WithBotTop.coe_injective ((schemeDeltaDimension_eq_genericPoint C sY).symm.trans hnY)
  have hdim1 : schemeDeltaDimension
      (fieldChowSituation ↥(Y.residueField (p.base (genericPoint X))))
      (genericFibreCurveToSpec p) = (1 : EInt) :=
    schemeDeltaDimension_genericFibreCurve_eq_one p C sX sY hp hnX hnY
  have hgD : dominantFunctionFieldMap (genericFibreCurveι p) g ≠ 0 := fun h ↦
    hg ((dominantFunctionFieldMap (genericFibreCurveι p)).injective (by rw [h, map_zero]))
  obtain ⟨u, hu⟩ : ∃ u : (rationalFunctions (genericFibreCurve p).subscheme)ˣ,
      (rationalFunctionsEquivFunctionField (genericFibreCurve p).subscheme).1 ↑u =
        dominantFunctionFieldMap (genericFibreCurveι p) g :=
    ⟨Units.mapEquiv
      (rationalFunctionsEquivFunctionField (genericFibreCurve p).subscheme).1.symm.toMulEquiv
      (isUnit_iff_ne_zero.mpr hgD).unit, by simp⟩
  have h02RU := properPushforward_principalDivisorCycle_eq_zero_fieldChowSituation
    ↥(Y.residueField (p.base (genericPoint X))) (genericFibreCurveToSpec p) hdim1 u
  rw [hu] at h02RU
  have hb0 : relativeDimension
      (fieldChowSituation ↥(Y.residueField (p.base (genericPoint X)))).dimensionFunction
      (𝟙 (fieldChowSituation ↥(Y.residueField (p.base (genericPoint X)))).S)
      ((genericFibreCurveToSpec p).base
        (genericPoint (genericFibreCurve p).subscheme)) = 0 := by
    rw [relativeDimension_id, fieldChowSituation_dimensionFunction]
  have hsum : (properPushforward
      (fieldChowSituation ↥(Y.residueField (p.base (genericPoint X))))
      (genericFibreCurveToSpec p)
      (𝟙 (fieldChowSituation ↥(Y.residueField (p.base (genericPoint X)))).S)
      (genericFibreCurveToSpec p) (by simp) 0
      (principalDivisorCycle
        (fieldChowSituation ↥(Y.residueField (p.base (genericPoint X))))
        (genericFibreCurveToSpec p) hdim1
        (dominantFunctionFieldMap (genericFibreCurveι p) g))).1
      ((genericFibreCurveToSpec p).base
        (genericPoint (genericFibreCurve p).subscheme)) = 0 := by
    rw [h02RU]
    rfl
  rw [properPushforward_apply_of_relativeDimension_eq _ _ _ _ _ 0 _ _ hb0,
    show (genericFibreCurveToSpec p).base ⁻¹'
        {(genericFibreCurveToSpec p).base (genericPoint (genericFibreCurve p).subscheme)} =
        Set.univ from by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      exact Subsingleton.elim _ _,
    finsum_mem_univ] at hsum
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
  by_cases hy : y = genericPoint Y
  · rw [hy, properPushforward_apply_of_relativeDimension_eq C sX sY p hp (n - 1) _ _ hyrel,
      ← hgenY, ← range_genericFibreCurveι p,
      finsum_mem_range (genericFibreCurveι p).isEmbedding.injective]
    refine Eq.trans (finsum_congr fun z ↦ ?_) hsum
    rw [principalDivisorCycle_apply,
      ← ord_dominantFunctionFieldMap_of_isPreimmersion (genericFibreCurveι p) g z,
      residueDegree_genericFibreCurveToSpec p z]
    rfl
  · exact properPushforward_principalDivisorCycle_apply_eq_zero_of_ne_genericPoint C sX sY hnX
      hnY p hp g hy

/-- For a proper `p : X ⟶ Y` over the base with `X` integral of delta-dimension `n`, if the
scheme-theoretic image of `p` does not have delta-dimension `n` then the proper pushforward of the
principal divisor of any rational function on `X` vanishes. -/
theorem properPushforward_principalDivisorCycle_eq_zero_of_schemeDeltaDimension_image_ne
    (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] [IsIntegral X] {n : ℤ}
    (hnX : schemeDeltaDimension C sX = (n : EInt))
    (p : X ⟶ Y) [IsProper p] (hp : p ≫ sY = sX)
    (hne : schemeDeltaDimension C (p.imageι ≫ sY) ≠ (n : EInt))
    (g : X.functionField) :
    properPushforward C sX sY p hp (n - 1) (principalDivisorCycle C sX hnX g) = 0 := by
  have _ : IsIntegral p.image := isIntegral_image p
  have _ : IsProper p.toImage := isProper_toImage p
  have hfactor : p.toImage ≫ (p.imageι ≫ sY) = sX := by
    rw [← Category.assoc, p.toImage_imageι, hp]
  have hft : LocallyOfFiniteType (p.toImage ≫ (p.imageι ≫ sY)) := by rw [hfactor]; infer_instance
  have _ : LocallyOfFiniteType p.toImage := locallyOfFiniteType_of_comp p.toImage (p.imageι ≫ sY)
  have hle := schemeDeltaDimension_le_of_isDominant C sX (p.imageι ≫ sY) p.toImage hfactor
  rw [hnX] at hle
  have hgen := schemeDeltaDimension_eq_genericPoint C (p.imageι ≫ sY)
  have hmn : relativeDimension C.dimensionFunction (p.imageι ≫ sY)
      (genericPoint p.image) < n :=
    WithBotTop.coe_lt_coe.mp (hgen ▸ lt_of_le_of_ne hle hne)
  have hzero : properPushforward C sX (p.imageι ≫ sY) p.toImage hfactor (n - 1)
      (principalDivisorCycle C sX hnX g) = 0 := by
    by_cases hm : relativeDimension C.dimensionFunction (p.imageι ≫ sY)
        (genericPoint p.image) = n - 1
    · exact properPushforward_principalDivisorCycle_eq_zero_of_isDominant C sX
        (p.imageι ≫ sY) hnX (by rw [hgen, hm]) p.toImage hfactor g
    · refine eq_zero_of_schemeDeltaDimension_lt C (p.imageι ≫ sY) (n - 1) ?_ _
      rw [hgen]
      exact WithBotTop.coe_lt_coe.mpr (by omega)
  have hcomp := congrFun (properPushforward_comp C sX (p.imageι ≫ sY) sY p.toImage p.imageι
    hfactor rfl (n - 1)) (principalDivisorCycle C sX hnX g)
  rw [Function.comp_apply, hzero, properPushforward_zero] at hcomp
  simpa only [p.toImage_imageι] using hcomp.symm

end Stacks.Chow

end

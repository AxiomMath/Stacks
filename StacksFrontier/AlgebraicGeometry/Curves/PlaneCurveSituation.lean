module

public import StacksFrontier.AlgebraicGeometry.Curves.PlaneCurveDifferential
public import StacksFrontier.AlgebraicGeometry.Curves.PlaneCurveIrreducibleEquation
public import StacksFrontier.AlgebraicGeometry.Curves.PlaneCurveProjectiveSmoothPoint
public import StacksFrontier.AlgebraicGeometry.Curves.DivisorOfRationalDifferential
public import StacksFrontier.AlgebraicGeometry.Curves.ModelNormalization
public import StacksFrontier.AlgebraicGeometry.Morphisms.SingularLocus.DimensionOne
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Basic
public import StacksFrontier.AlgebraicGeometry.NormalProperModel.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen

/-!
# The plane-curve situation (Stacks 09U0)

Let `k` be a field, `F ∈ k[T₀, T₁, T₂]` irreducible and homogeneous of degree `d`, not a scalar
multiple of `T₀`, `D = V(F) ⊆ 𝐏²_k`, `f = F(1, x, y)` and `K` the fraction field of
`k[x, y]/(f)`. This file builds every object of [Stacks, Tag 09U0] and proves every property the
source states about them:

* `D` is a projective curve over `k`, with function field `K`;
* the abstract curve `C` corresponding to `K` is the normalization of `D`, a nonsingular
  projective curve over `k` with function field `K`;
* the normalization morphism `C ⟶ D` is surjective, bijective over the nonsingular locus of `D`
  (indeed an isomorphism over it), and an isomorphism if `D` is nonsingular;
* over a perfect field the differential `ω = dx/f_y = -dy/f_x` of
  `AlgebraicGeometry.AffinePlaneCurve.differential` is nonzero and has a unique divisor of zeros
  and poles `K_C` on `C`.

## Main definitions

* `AlgebraicGeometry.ProjectivePlaneCurve.ofEquation`: the situation built from `F` alone.
* `AlgebraicGeometry.ProjectivePlaneCurve.toSpec`: the structure morphism `D ⟶ Spec k`.
* `AlgebraicGeometry.ProjectivePlaneCurve.functionFieldAlgEquiv`: `K ≃ₐ[k] R(D)`.
* `AlgebraicGeometry.ProjectivePlaneCurve.abstractCurve`: the abstract curve `C`.
* `AlgebraicGeometry.ProjectivePlaneCurve.abstractCurveMap`: the map `C ⟶ D`.
* `AlgebraicGeometry.ProjectivePlaneCurve.functionFieldEquivAbstractCurve`: `K ≃ₐ[k] R(C)`.
* `AlgebraicGeometry.ProjectivePlaneCurve.canonicalDivisor`: `K_C = div(ω)` on `C`.

## Main results

* `AlgebraicGeometry.ProjectivePlaneCurve.irreducible_dehomCoeff`: `f` is irreducible.
* `AlgebraicGeometry.ProjectivePlaneCurve.isCurve_toSpec`: `V(F)` is a curve over `k`.
* `AlgebraicGeometry.ProjectivePlaneCurve.surjective_abstractCurveMap`,
  `AlgebraicGeometry.ProjectivePlaneCurve.existsUnique_abstractCurveMap_eq`,
  `AlgebraicGeometry.ProjectivePlaneCurve.isIso_abstractCurveMap_restrict_regularOpen` and
  `AlgebraicGeometry.ProjectivePlaneCurve.isIso_abstractCurveMap`: the properties of `C ⟶ D`.
* `AlgebraicGeometry.ProjectivePlaneCurve.eq_canonicalDivisor_iff`: `K_C` is the unique divisor
  of zeros and poles of `ω`.
* `AlgebraicGeometry.ProjectivePlaneCurve.situation`: **Stacks 09U0**, everything together.

## Implementation notes

"The abstract curve corresponding to `K`" is the normal projective model of `K`; it is taken to
be the normalization of `D`, `AlgebraicGeometry.normalizationModel'`, which is a nonsingular
projective model of `D` and so has function field `K`. Any other normal projective curve with
function field `K` is isomorphic to it by Stacks 0BXZ and 0BY1. The map `C ⟶ D` is the
normalization morphism. It is finite and dominant, hence surjective; it is an isomorphism over
every normal open of `D`, and the nonsingular locus of `D` is open because `D` is a Nagata
scheme of dimension one, so the map is an isomorphism, in particular bijective, over it.

The nonsingular locus is `AlgebraicGeometry.regularLocus`, the points with regular local ring,
and "`D` is nonsingular" is `AlgebraicGeometry.IsRegular`.

The divisor of zeros and poles is the predicate `Stacks.Divisors.IsDivisorOfRationalDifferential`
read through the `k`-linear identification of `K` with the function field of `C`; existence and
uniqueness on a normal curve over a perfect field is
`AlgebraicGeometry.existsUnique_isDivisorOfRationalDifferential`. The source takes `k`
algebraically closed; nothing about `C ⟶ D` needs any assumption on `k`, and the statements
about `ω` and `K_C` need `k` perfect, which an algebraically closed field is.

That `V(F)` is integral is read off `Proj` of the graded domain `k[T₀, T₁, T₂]/(F)`, which is
nonempty because the zero ideal is a relevant prime (the class of `T₀` is nonzero); its dimension
is that of its standard chart, the affine plane curve of `f`.

## References

* [Stacks Project, Tag 09U0](https://stacks.math.columbia.edu/tag/09U0)
* [Stacks Project, Tag 0BXR](https://stacks.math.columbia.edu/tag/0BXR)
* [Stacks Project, Tag 0BY1](https://stacks.math.columbia.edu/tag/0BY1)
-/

@[expose] public noncomputable section

open CategoryTheory MvPolynomial

universe u

namespace AlgebraicGeometry.ProjectivePlaneCurve

attribute [local instance] MvPolynomial.gradedAlgebra

section Equation

variable {k : Type u} [Field k] (F : MvPolynomial (Fin 3) k) {d : ℕ} (hF : F.IsHomogeneous d)

/-- An irreducible polynomial which is not a scalar multiple of the first coordinate is not
divisible by it. -/
theorem not_X_zero_dvd_of_irreducible (hirr : Irreducible F)
    (hX : ∀ a : k, F ≠ MvPolynomial.C a * MvPolynomial.X (0 : Fin 3)) :
    ¬ (X 0 : MvPolynomial (Fin 3) k) ∣ F := by
  rintro ⟨q, hq⟩
  rcases hirr.isUnit_or_isUnit hq with h | h
  · exact (MvPolynomial.X_prime (R := k) (i := (0 : Fin 3))).not_isUnit h
  · obtain ⟨r, -, rfl⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp h
    exact hX r (by rw [hq, mul_comm])

/-- The equation of the standard affine chart is the dehomogenization of `F` at the first
coordinate. -/
theorem aeval_eq_dehomCoeff :
    MvPolynomial.aeval ![1, MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)] F =
      Stacks.ProjectiveChart.dehomCoeff k 0 F := by
  rw [Stacks.ProjectiveChart.dehomCoeff_eq_aeval]
  have h : (![1, MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)] :
      Fin 3 → MvPolynomial (Fin 2) k) =
        fun i => (finSuccEquiv' (0 : Fin 3) i).elim 1 MvPolynomial.X := by
    funext i
    fin_cases i <;> rfl
  rw [h]

variable (hirr : Irreducible F)
  (hX : ∀ a : k, F ≠ MvPolynomial.C a * MvPolynomial.X (0 : Fin 3))

include hirr hX in
/-- The first coordinate is nonzero in the homogeneous coordinate ring `k[T₀, T₁, T₂]/(F)`. -/
theorem mk_X_zero_ne_zero :
    Ideal.Quotient.mk (Stacks.Models.PlaneCurveModel.equationIdeal F hF).toIdeal
      (X 0 : MvPolynomial (Fin 3) k) ≠ 0 := by
  rw [Ne, Ideal.Quotient.eq_zero_iff_mem, Stacks.Models.PlaneCurveModel.toIdeal_equationIdeal,
    Ideal.mem_span_singleton]
  rintro ⟨q, hq⟩
  rcases (MvPolynomial.X_prime (R := k) (i := (0 : Fin 3))).irreducible.isUnit_or_isUnit hq
    with h | h
  · exact hirr.not_isUnit h
  · obtain ⟨r, hr, rfl⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp h
    refine hX (r⁻¹) ?_
    rw [hq, mul_comm (MvPolynomial.C r⁻¹), mul_assoc, ← MvPolynomial.C_mul,
      mul_inv_cancel₀ hr.ne_zero, MvPolynomial.C_1, mul_one]

include hirr in
/-- The homogeneous coordinate ring `k[T₀, T₁, T₂]/(F)` of an irreducible `F` is a domain. -/
theorem isDomain_quotient_equationIdeal :
    IsDomain (MvPolynomial (Fin 3) k ⧸
      (Stacks.Models.PlaneCurveModel.equationIdeal F hF).toIdeal) := by
  have : (Stacks.Models.PlaneCurveModel.equationIdeal F hF).toIdeal.IsPrime := by
    rw [Stacks.Models.PlaneCurveModel.toIdeal_equationIdeal,
      Ideal.span_singleton_prime hirr.ne_zero]
    exact UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
  exact Ideal.Quotient.isDomain _

include hirr hX in
/-- The generic point of `V(F)`: the zero ideal of `k[T₀, T₁, T₂]/(F)`, a relevant homogeneous
prime because the class of the first coordinate is nonzero. -/
def genericPointOfEquation : Stacks.Models.PlaneCurveModel.scheme F hF := by
  haveI := isDomain_quotient_equationIdeal F hF hirr
  refine ⟨⊥, ?_, fun h => mk_X_zero_ne_zero F hF hirr hX ?_⟩
  · simpa using (inferInstance : (⊥ : Ideal _).IsPrime)
  · have hmem := h (HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.one_pos
      (Stacks.HomogeneousIdeal.mk_mem_quotientGrading _ (MvPolynomial.isHomogeneous_X k 0)))
    change _ ∈ (⊥ : HomogeneousIdeal _).toIdeal at hmem
    rw [HomogeneousIdeal.toIdeal_bot] at hmem
    exact Ideal.mem_bot.mp hmem

include hirr hX in
theorem genericPointOfEquation_mem_chart :
    genericPointOfEquation F hF hirr hX ∈ Stacks.Models.PlaneCurveModel.chart F hF 0 := by
  intro hmem
  apply mk_X_zero_ne_zero F hF hirr hX
  change Stacks.HomogeneousIdeal.quotientMk (Stacks.Models.PlaneCurveModel.equationIdeal F hF)
    (X 0) ∈ (⊥ : HomogeneousIdeal (Stacks.Models.PlaneCurveModel.grading F hF)).toIdeal at hmem
  rw [HomogeneousIdeal.toIdeal_bot] at hmem
  exact Ideal.mem_bot.mp hmem

include hirr hX in
/-- The plane curve `V(F)` of an irreducible `F` is integral. -/
theorem isIntegral_scheme : IsIntegral (Stacks.Models.PlaneCurveModel.scheme F hF) := by
  have := isDomain_quotient_equationIdeal F hF hirr
  have : Nonempty (Stacks.Models.PlaneCurveModel.scheme F hF) :=
    ⟨genericPointOfEquation F hF hirr hX⟩
  exact ProjectiveSpectrum.Proj.isIntegral_proj_of_isDomain _

include hirr hX in
/-- The standard chart `V(F) ∩ D₊(T₀)` is nonempty. -/
theorem nonempty_chart : Nonempty (Stacks.Models.PlaneCurveModel.chart F hF 0) :=
  ⟨⟨_, genericPointOfEquation_mem_chart F hF hirr hX⟩⟩

include hF hirr hX in
/-- **The dehomogenization `F(1, x, y)` of an irreducible `F` not divisible by `T₀` is
irreducible.** Its quotient ring is the ring of the standard chart of the integral scheme
`V(F)`, which is a domain since the chart is nonempty. -/
theorem irreducible_dehomCoeff : Irreducible (Stacks.ProjectiveChart.dehomCoeff k 0 F) := by
  have := isIntegral_scheme F hF hirr hX
  have := nonempty_chart F hF hirr hX
  have hdom : IsDomain (MvPolynomial (Fin 2) k ⧸
      Ideal.span {Stacks.ProjectiveChart.dehomCoeff k 0 F}) :=
    Function.Injective.isDomain
      (Stacks.Models.PlaneCurveModel.chartEquiv F hF 0
        (not_X_zero_dvd_of_irreducible F hirr hX) 0).toRingHom
      (Stacks.Models.PlaneCurveModel.chartEquiv F hF 0
        (not_X_zero_dvd_of_irreducible F hirr hX) 0).injective
  have hprime : (Ideal.span {Stacks.ProjectiveChart.dehomCoeff k 0 F}).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp hdom
  have hne : Stacks.ProjectiveChart.dehomCoeff k 0 F ≠ 0 :=
    Stacks.Curves.dehomCoeff_ne_zero 0 F
      (Stacks.Models.PlaneCurveModel.mem_homogeneousSubmodule_smul_one F hF) hirr.ne_zero
  exact ((Ideal.span_singleton_prime hne).mp hprime).irreducible

include hF hirr hX in
/-- The affine plane curve cut out on the standard chart by the dehomogenization of `F`. -/
def chartCurve : AffinePlaneCurve k :=
  ⟨Stacks.ProjectiveChart.dehomCoeff k 0 F, irreducible_dehomCoeff F hF hirr hX⟩

/-- **The projective plane curve of an irreducible homogeneous `F`** which is not a scalar multiple
of the first coordinate. The affine chart is the affine plane curve of the dehomogenization
`f = F(1, x, y)`, whose irreducibility is `irreducible_dehomCoeff`, so every irreducible
homogeneous `F` with `T₀ ∤ F` gives a `ProjectivePlaneCurve`. -/
def ofEquation : ProjectivePlaneCurve k where
  equation := F
  degree := d
  irreducible_equation := hirr
  isHomogeneous_equation := hF
  not_smul_X₀ := hX
  affineChart :=
    ⟨MvPolynomial.aeval ![1, MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)] F, by
      rw [aeval_eq_dehomCoeff]
      exact irreducible_dehomCoeff F hF hirr hX⟩
  affineChart_equation := rfl

/-- The equation of `ofEquation F hF hirr hX` is `F`. -/
@[simp]
theorem ofEquation_equation : (ofEquation F hF hirr hX).equation = F := rfl

include hirr hX in
/-- The structure morphism of `V(F)` is locally of finite type. -/
theorem locallyOfFiniteType_toSpec :
    LocallyOfFiniteType (Stacks.Models.PlaneCurveModel.toSpec F hF) := by
  have := Stacks.Models.PlaneCurveModel.locallyOfFinitePresentation_toSpec F hF 0
    (not_X_zero_dvd_of_irreducible F hirr hX)
  infer_instance

include hirr hX in
/-- **The plane curve `V(F)` has dimension one**: its standard chart is the affine plane curve
`Spec k[x, y]/(F(1, x, y))`, which has dimension one, and a nonempty open of an irreducible
scheme of finite type over a field has the dimension of the whole scheme. -/
theorem topologicalKrullDim_scheme :
    topologicalKrullDim (Stacks.Models.PlaneCurveModel.scheme F hF) = 1 := by
  have := isIntegral_scheme F hF hirr hX
  have := locallyOfFiniteType_toSpec F hF hirr hX
  have hU := Stacks.Models.PlaneCurveModel.isAffineOpen_chart F hF 0
  rw [topologicalKrullDim_eq_of_isOpen k _ (Stacks.Models.PlaneCurveModel.toSpec F hF) _
    (Stacks.Models.PlaneCurveModel.chart F hF 0).isOpen
    ⟨_, genericPointOfEquation_mem_chart F hF hirr hX⟩]
  have heq : topologicalKrullDim (Stacks.Models.PlaneCurveModel.chart F hF 0) =
      ringKrullDim Γ(Stacks.Models.PlaneCurveModel.scheme F hF,
        Stacks.Models.PlaneCurveModel.chart F hF 0) := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph
  refine heq.trans ?_
  rw [← ringKrullDim_eq_of_ringEquiv (Stacks.Models.PlaneCurveModel.chartEquiv F hF 0
    (not_X_zero_dvd_of_irreducible F hirr hX) 0)]
  have h1 := (chartCurve F hF hirr hX).isCurve_structureMap.topologicalKrullDim_eq_one
  rw [show topologicalKrullDim (Spec (.of (chartCurve F hF hirr hX).coordinateRing)) =
    ringKrullDim (chartCurve F hF hirr hX).coordinateRing from
      PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _] at h1
  exact h1

include hirr hX in
/-- **The plane curve `V(F)` of an irreducible `F` is a curve over `k`** in the sense of
Stacks 0A23. -/
theorem isCurve_toSpec : IsCurve k (Stacks.Models.PlaneCurveModel.toSpec F hF) := by
  have := isIntegral_scheme F hF hirr hX
  exact { toIsVariety := ProjectiveSpectrum.Proj.projectivePlane_isVariety_of_isIntegral k
            (Stacks.Models.PlaneCurveModel.embedding F hF)
          topologicalKrullDim_eq_one := topologicalKrullDim_scheme F hF hirr hX }

end Equation

/-! ### The projective plane curve `D` as a curve over `k` -/

section Curve

variable {k : Type u} [Field k] (D : ProjectivePlaneCurve k)

/-- The structure morphism `D ⟶ Spec k` of the projective plane curve. -/
def toSpec : D.curve ⟶ Spec (.of k) :=
  Stacks.Models.PlaneCurveModel.toSpec D.equation D.isHomogeneous_equation

/-- The first homogeneous coordinate does not divide the equation of `D`. -/
theorem not_X_zero_dvd_equation : ¬ (X 0 : MvPolynomial (Fin 3) k) ∣ D.equation :=
  not_X_zero_dvd_of_irreducible _ D.irreducible_equation D.not_smul_X₀

/-- The projective plane curve `D` is integral. -/
instance isIntegral_curve : IsIntegral D.curve :=
  isIntegral_scheme _ _ D.irreducible_equation D.not_smul_X₀

/-- The projective plane curve `D` is a curve over `k`. -/
instance isCurve_toSpec' : IsCurve k D.toSpec :=
  isCurve_toSpec _ _ D.irreducible_equation D.not_smul_X₀

/-- The projective plane curve `D` is proper over `k`. -/
instance isProper_toSpec : IsProper D.toSpec :=
  Stacks.Models.PlaneCurveModel.isProper_toSpec _ _

/-- The projective plane curve `D` is locally Noetherian. -/
instance isLocallyNoetherian_curve : IsLocallyNoetherian D.curve :=
  LocallyOfFiniteType.isLocallyNoetherian D.toSpec

/-- The standard chart `D ∩ D₊(T₀)` of the projective plane curve. -/
abbrev chart : D.curve.Opens :=
  Stacks.Models.PlaneCurveModel.chart D.equation D.isHomogeneous_equation 0

instance nonempty_chart' : Nonempty D.chart :=
  nonempty_chart _ _ D.irreducible_equation D.not_smul_X₀

/-- The standard chart of `D` is affine. -/
theorem isAffineOpen_chart : IsAffineOpen D.chart :=
  Stacks.Models.PlaneCurveModel.isAffineOpen_chart _ _ 0

/-- The equation of the affine chart of `D` is the dehomogenization of `F`. -/
theorem affineChart_equation_eq_dehomCoeff :
    D.affineChart.equation = Stacks.ProjectiveChart.dehomCoeff k 0 D.equation := by
  rw [D.affineChart_equation, aeval_eq_dehomCoeff]

/-- **The coordinate ring `k[x, y]/(f)` is the ring of the standard chart of `D`.** -/
def coordinateRingEquiv : D.affineChart.coordinateRing ≃+* Γ(D.curve, D.chart) :=
  (Ideal.quotEquivOfEq (by rw [AffinePlaneCurve.ideal, D.affineChart_equation_eq_dehomCoeff])).trans
    (Stacks.Models.PlaneCurveModel.chartEquiv D.equation D.isHomogeneous_equation 0
      D.not_X_zero_dvd_equation 0)

/-- The identification of the coordinate ring with the ring of the chart carries constants to
the functions pulled back from `Spec k`. -/
theorem coordinateRingEquiv_algebraMap (a : k) :
    D.coordinateRingEquiv (algebraMap k D.affineChart.coordinateRing a) =
      (D.toSpec.appLE ⊤ D.chart le_top).hom ((Scheme.ΓSpecIso (.of k)).inv.hom a) := by
  simp only [coordinateRingEquiv, RingEquiv.trans_apply]
  exact Stacks.Models.PlaneCurveModel.chartEquiv_mk_C _ _ 0 D.not_X_zero_dvd_equation 0 a

instance isFractionRing_chart : IsFractionRing Γ(D.curve, D.chart) D.curve.functionField :=
  functionField_isFractionRing_of_isAffineOpen _ _ D.isAffineOpen_chart

/-- The function field `K` of the affine chart, as a ring, is the function field of `D`. -/
def functionFieldRingEquiv : D.affineChart.FunctionField ≃+* D.curve.functionField :=
  IsFractionRing.ringEquivOfRingEquiv D.coordinateRingEquiv

/-- The identification of function fields is `k`-linear. -/
theorem functionFieldRingEquiv_algebraMap (a : k) :
    D.functionFieldRingEquiv (algebraMap k D.affineChart.FunctionField a) =
      @algebraMap k _ _ _ (functionFieldAlgebra k D.toSpec) a := by
  rw [IsScalarTower.algebraMap_apply k D.affineChart.coordinateRing,
    functionFieldRingEquiv, IsFractionRing.ringEquivOfRingEquiv_algebraMap,
    coordinateRingEquiv_algebraMap]
  simp only [Scheme.Hom.appLE, CommRingCat.comp_apply, RingHom.algebraMap_toAlgebra,
    TopCat.Presheaf.germ_res_apply]
  rfl

/-- **The function field `K` of the source is the function field of `D`**, as `k`-algebras. -/
def functionFieldAlgEquiv :
    letI := functionFieldAlgebra k D.toSpec
    D.affineChart.FunctionField ≃ₐ[k] D.curve.functionField :=
  letI := functionFieldAlgebra k D.toSpec
  AlgEquiv.ofRingEquiv (f := D.functionFieldRingEquiv) D.functionFieldRingEquiv_algebraMap

end Curve

/-! ### The abstract curve `C` and the map `C ⟶ D` -/

section AbstractCurve

variable {k : Type u} [Field k] (D : ProjectivePlaneCurve k)

/-- The nonsingular projective model of `D` given by its normalization. -/
def model : NonsingularProjectiveModel k D.curve D.toSpec :=
  normalizationModel' k D.toSpec

/-- **Stacks 09U0.** The abstract curve `C` corresponding to `K`: the normalization of `D`, a
nonsingular projective curve over `k` whose function field is `K`. -/
abbrev abstractCurve : Scheme.{u} := D.model.Y

/-- The structure morphism of the abstract curve `C` over `k`. -/
abbrev abstractCurveToSpec : D.abstractCurve ⟶ Spec (.of k) := D.model.structureMap

instance isCurve_abstractCurveToSpec : IsCurve k D.abstractCurveToSpec := D.model.isCurve

instance isProjectiveVariety_abstractCurveToSpec :
    IsProjectiveVariety k D.abstractCurveToSpec :=
  D.model.isProjectiveVariety

/-- The abstract curve `C` is nonsingular. -/
theorem isRegular_abstractCurve : IsRegular D.abstractCurve := D.model.isRegular

instance isNormal_abstractCurve : IsNormal D.abstractCurve :=
  isNormal_of_isRegular _ D.isRegular_abstractCurve

instance isLocallyNoetherian_abstractCurve : IsLocallyNoetherian D.abstractCurve :=
  LocallyOfFiniteType.isLocallyNoetherian D.abstractCurveToSpec

/-- **Stacks 09U0.** The map `C ⟶ D` from the abstract curve to the plane curve: the
normalization morphism. -/
def abstractCurveMap : D.abstractCurve ⟶ D.curve := normalizationOverField k D.toSpec

/-- The map `C ⟶ D` is a morphism over `k`. -/
theorem abstractCurveMap_comp_toSpec :
    D.abstractCurveMap ≫ D.toSpec = D.abstractCurveToSpec := rfl

instance isFinite_abstractCurveMap : IsFinite D.abstractCurveMap :=
  isFinite_normalizationOverField k D.toSpec

instance isDominant_abstractCurveMap : IsDominant D.abstractCurveMap :=
  isDominant_normalizationOverField k D.toSpec

/-- **Stacks 09U0.** The map `C ⟶ D` is surjective: it is finite, hence closed, and dominant. -/
theorem surjective_abstractCurveMap : Function.Surjective D.abstractCurveMap := by
  have hcl : IsClosed (Set.range D.abstractCurveMap) :=
    D.abstractCurveMap.isClosedMap.isClosed_range
  intro x
  have hx : x ∈ closure (Set.range D.abstractCurveMap) := by
    rw [D.abstractCurveMap.denseRange.closure_range]
    trivial
  rwa [hcl.closure_eq] at hx

/-- The nonsingular locus of `D`, as an open subscheme. -/
def regularOpen : D.curve.Opens :=
  ⟨regularLocus D.curve, isOpen_regularLocus_of_isNagataScheme D.curve
    (isNagataScheme_of_locallyOfFiniteType_over_field k D.toSpec)
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := D.toSpec)).le⟩

/-- The nonsingular locus of `D` is normal. -/
instance isNormal_regularOpen : IsNormal D.regularOpen.toScheme := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  all_goals
    have hreg : IsRegularLocalRing (D.curve.presheaf.stalk x.1) := x.2
    let e := (D.regularOpen.stalkIso x).commRingCatIsoToRingEquiv
  · have := IsRegularLocalRing.isDomain (D.curve.presheaf.stalk x.1)
    exact Function.Injective.isDomain e.toRingHom e.injective
  · have := IsRegularLocalRing.isDomain (D.curve.presheaf.stalk x.1)
    have := isIntegrallyClosed_of_isRegularLocalRing (D.curve.presheaf.stalk x.1)
    exact IsIntegrallyClosed.of_equiv e.symm

/-- **Stacks 09U0.** The map `C ⟶ D` is an isomorphism over the nonsingular locus of `D`. -/
theorem isIso_abstractCurveMap_restrict_regularOpen :
    IsIso (D.abstractCurveMap ∣_ D.regularOpen) :=
  Scheme.isIso_normalization_restrict_of_isNormal D.curve
    (finite_irreducibleComponents_of_locallyOfFiniteType k D.toSpec) D.regularOpen inferInstance

/-- **Stacks 09U0.** The map `C ⟶ D` is bijective over the nonsingular locus of `D`: every
nonsingular point of `D` has exactly one preimage in `C`. -/
theorem existsUnique_abstractCurveMap_eq {x : D.curve} (hx : x ∈ regularLocus D.curve) :
    ∃! c : D.abstractCurve, D.abstractCurveMap c = x := by
  obtain ⟨c, rfl⟩ := D.surjective_abstractCurveMap x
  refine ⟨c, rfl, fun c' hc' => ?_⟩
  have := D.isIso_abstractCurveMap_restrict_regularOpen
  have hinj := (D.abstractCurveMap ∣_ D.regularOpen).isOpenEmbedding.injective
  have h1 : c' ∈ D.abstractCurveMap ⁻¹ᵁ D.regularOpen := by
    change D.abstractCurveMap c' ∈ regularLocus D.curve
    rw [hc']
    exact hx
  have h2 : c ∈ D.abstractCurveMap ⁻¹ᵁ D.regularOpen := hx
  let y' : (D.abstractCurveMap ⁻¹ᵁ D.regularOpen).toScheme := ⟨c', h1⟩
  let y : (D.abstractCurveMap ⁻¹ᵁ D.regularOpen).toScheme := ⟨c, h2⟩
  have hyy : y' = y := hinj (Subtype.ext ((morphismRestrict_base_coe _ _ y').trans
    (hc'.trans (morphismRestrict_base_coe _ _ y).symm)))
  exact congrArg Subtype.val hyy

/-- **Stacks 09U0.** If `D` is nonsingular, the map `C ⟶ D` is an isomorphism. -/
theorem isIso_abstractCurveMap (hD : IsRegular D.curve) : IsIso D.abstractCurveMap :=
  (Scheme.isIso_normalization_iff_isNormal D.curve
    (finite_irreducibleComponents_of_locallyOfFiniteType k D.toSpec)).mpr
      (isNormal_of_isRegular _ hD)

/-- **The function field of `C` is `K`**, as `k`-algebras: the function field of the affine chart
is the function field of `D`, which the normalization identifies with that of `C`. -/
def functionFieldEquivAbstractCurve :
    letI := functionFieldAlgebra k D.abstractCurveToSpec
    D.affineChart.FunctionField ≃ₐ[k] D.abstractCurve.functionField :=
  letI := functionFieldAlgebra k D.toSpec
  letI := functionFieldAlgebra k D.abstractCurveToSpec
  D.functionFieldAlgEquiv.trans D.model.functionFieldEquiv

end AbstractCurve

/-! ### The differential `ω` and the canonical divisor `K_C = div(ω)` on `C` -/

section CanonicalDivisor

variable {k : Type u} [Field k] (D : ProjectivePlaneCurve k)

/-- The identification of `K` with the function field of `C`, as a ring isomorphism. -/
def functionFieldRingEquivAbstractCurve :
    D.affineChart.FunctionField ≃+* D.abstractCurve.functionField :=
  letI := functionFieldAlgebra k D.abstractCurveToSpec
  D.functionFieldEquivAbstractCurve.toRingEquiv

/-- The identification of `K` with the function field of `C` is `k`-linear. -/
theorem functionFieldRingEquivAbstractCurve_algebraMap (a : k) :
    D.functionFieldRingEquivAbstractCurve (algebraMap k D.affineChart.FunctionField a) =
      @algebraMap k _ _ _ (functionFieldAlgebra k D.abstractCurveToSpec) a :=
  letI := functionFieldAlgebra k D.abstractCurveToSpec
  D.functionFieldEquivAbstractCurve.commutes a

variable [PerfectField k]

/-- **Stacks 09U0.** The divisor of zeros and poles of `ω` on `C` exists and is unique. -/
theorem existsUnique_isDivisorOfRationalDifferential_differential :
    ∃! KC : Stacks.Divisors.WeilDivisor D.abstractCurve,
      Stacks.Divisors.IsDivisorOfRationalDifferential D.abstractCurve
        D.functionFieldRingEquivAbstractCurve D.differential KC :=
  existsUnique_isDivisorOfRationalDifferential k D.abstractCurveToSpec
    D.functionFieldRingEquivAbstractCurve D.functionFieldRingEquivAbstractCurve_algebraMap
    D.differential D.affineChart.differential_ne_zero

/-- **Stacks 09U0.** The canonical divisor `K_C`: the divisor of zeros and poles of `ω` on the
abstract curve `C`. -/
def canonicalDivisor : Stacks.Divisors.WeilDivisor D.abstractCurve :=
  D.existsUnique_isDivisorOfRationalDifferential_differential.exists.choose

/-- `K_C` is the divisor of zeros and poles of `ω`. -/
theorem isDivisorOfRationalDifferential_canonicalDivisor :
    Stacks.Divisors.IsDivisorOfRationalDifferential D.abstractCurve
      D.functionFieldRingEquivAbstractCurve D.differential D.canonicalDivisor :=
  D.existsUnique_isDivisorOfRationalDifferential_differential.exists.choose_spec

/-- `K_C` is the unique divisor of zeros and poles of `ω`. -/
theorem eq_canonicalDivisor_iff (KC : Stacks.Divisors.WeilDivisor D.abstractCurve) :
    KC = D.canonicalDivisor ↔
      Stacks.Divisors.IsDivisorOfRationalDifferential D.abstractCurve
        D.functionFieldRingEquivAbstractCurve D.differential KC :=
  ⟨fun h => h ▸ D.isDivisorOfRationalDifferential_canonicalDivisor, fun h =>
    D.existsUnique_isDivisorOfRationalDifferential_differential.unique h
      D.isDivisorOfRationalDifferential_canonicalDivisor⟩

/-- **Stacks Project, Tag 09U0** (Situation: notation for a plane curve). Let `k` be a perfect
field (the source takes `k` algebraically closed; perfect suffices), `F ∈ k[T₀, T₁, T₂]`
irreducible and homogeneous of degree `d` with `T₀ ∤ F`, `D = V(F) ⊆ 𝐏²_k`,
`f = F(1, x, y)`, and `K` the fraction field of `k[x, y]/(f)`. Then:

* `D` is a projective curve over `k`;
* the abstract curve `C` of `K` (`abstractCurve`, the normalization of `D`) is a nonsingular
  projective curve over `k` whose function field is `K` (`functionFieldEquivAbstractCurve`);
* the map `C ⟶ D` (`abstractCurveMap`) is a surjective morphism over `k`, bijective over the
  nonsingular locus of `D`, and an isomorphism if `D` is nonsingular;
* `ω = dx/f_y = -dy/f_x ∈ Ω_{K/k}` (`differential`) is well defined and nonzero;
* `K_C` (`canonicalDivisor`) is the unique divisor of zeros and poles of `ω` on `C`.

All of these are proved here; nothing about `C`, the map `C ⟶ D` or `K_C` is assumed. -/
@[stacks 09U0 "the full situation: D, K, the abstract curve C with the map C → D and its \
  properties, ω and K_C = div(ω) on C"]
theorem situation :
    IsCurve k D.toSpec ∧ IsProper D.toSpec ∧
    IsCurve k D.abstractCurveToSpec ∧ IsProjectiveVariety k D.abstractCurveToSpec ∧
    IsRegular D.abstractCurve ∧
    D.abstractCurveMap ≫ D.toSpec = D.abstractCurveToSpec ∧
    Function.Surjective D.abstractCurveMap ∧
    (∀ x ∈ regularLocus D.curve, ∃! c : D.abstractCurve, D.abstractCurveMap c = x) ∧
    (IsRegular D.curve → IsIso D.abstractCurveMap) ∧
    (D.affineChart.partialY ≠ 0 →
      D.differential = D.affineChart.partialY⁻¹ •
        KaehlerDifferential.D k D.affineChart.FunctionField D.affineChart.x) ∧
    (D.affineChart.partialX ≠ 0 →
      D.differential = -(D.affineChart.partialX⁻¹ •
        KaehlerDifferential.D k D.affineChart.FunctionField D.affineChart.y)) ∧
    D.differential ≠ 0 ∧
    ∃! KC : Stacks.Divisors.WeilDivisor D.abstractCurve,
      Stacks.Divisors.IsDivisorOfRationalDifferential D.abstractCurve
        D.functionFieldRingEquivAbstractCurve D.differential KC :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, D.isRegular_abstractCurve,
    D.abstractCurveMap_comp_toSpec, D.surjective_abstractCurveMap,
    fun _ hx => D.existsUnique_abstractCurveMap_eq hx, D.isIso_abstractCurveMap,
    D.affineChart.differential_eq_inv_partialY_smul_D_x,
    D.affineChart.differential_eq_neg_inv_partialX_smul_D_y,
    D.affineChart.differential_ne_zero, D.existsUnique_isDivisorOfRationalDifferential_differential⟩

end CanonicalDivisor

end AlgebraicGeometry.ProjectivePlaneCurve

end

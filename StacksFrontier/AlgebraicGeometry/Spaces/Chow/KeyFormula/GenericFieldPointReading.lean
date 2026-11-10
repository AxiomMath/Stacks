module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormula.GenericFieldValue
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaLocal.PrimeDivisorChart

/-!
# Reading rational functions of a prime divisor at a point over its generic point

Let `X` be a decent algebraic space, `Z ⊂ X` a prime divisor with generic point `ξ`, and let
`θ_Z : κ(u) ≃+* R(Z)` be the identification `PrimeDivisor.genericResidueFieldEquivFunctionField`,
whose inverse is evaluation at the monomorphic field point `ρ_Z : Spec κ(u) → Z`.

Every other field-valued point `p : Spec K → Z` over the generic point of `Z` factors uniquely
through `ρ_Z` (Stacks 0H2X), which gives a field homomorphism `κ(u) → K`; this file shows that
**evaluating rational functions of `Z` at `p` is `θ_Z⁻¹` followed by that homomorphism.**

The case of interest is an étale chart `V` of `X` and a point `q'` of the base-change chart
`W' = V ×_X Z` of `Z` over `ξ`: the canonical field point `Spec κ(q') → W' → Z` is such a `p`, and
the value at `q'` of a rational function of `Z` is the image of `θ_Z⁻¹` of it in `κ(q')`.

## Main definitions

All declarations are in the namespace `AlgebraicGeometry.Space`.

* `PrimeDivisor.genericFieldPointFactor`: the factorization of a field point over the generic
  point of `Z` through `ρ_Z`, and `PrimeDivisor.genericResidueFieldToFieldPoint` the field
  homomorphism `κ(u) → K` it induces.
* `PrimeDivisor.baseChangeChartFieldPoint`: the field point `Spec κ(q') → Z` at a point of
  `V ×_X Z` over `ξ`.
* `PrimeDivisor.baseChangeChartRationalReading`: the value `R(Z) → κ(q')` of rational functions
  of `Z` at `q'`.

## Main results

* `PrimeDivisor.evalRingHom_eq_genericResidueFieldToFieldPoint`: evaluation at `p` is `θ_Z⁻¹`
  followed by `κ(u) → K`.
* `PrimeDivisor.baseChangeChartRationalReading_genericResidueFieldEquivFunctionField`: the value
  at `q'` of `θ_Z(c)` is the image of `c` in `κ(q')`.

## References

* [Stacks Project, Section 0EQU](https://stacks.math.columbia.edu/tag/0EQU)
* [Stacks Project, Tag 0H2X](https://stacks.math.columbia.edu/tag/0H2X)
* [Stacks Project, Tag 0END](https://stacks.math.columbia.edu/tag/0END)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)
    (p : FieldValuedPoint B S hS Z.subspace.toFunctor)
    (hp : p.class B S hS Z.subspace.toFunctor = Space.genericPoint B S hS Z.closed.1 Z.integral)

/-! ### Field points over the generic point factor through `ρ_Z` -/

/-- **The factorization of a field point over the generic point of `Z` through `ρ_Z`**, which
exists and is unique by Stacks 0H2X, `ρ_Z` being a monomorphic representative of that point. -/
def PrimeDivisor.genericFieldPointFactor :
    p.siteObject B S hS Z.subspace.toFunctor ⟶ Z.genericFieldSpec B S hS hX hdec :=
  haveI : Mono (yonedaEquiv.symm (Z.genericFieldPoint B S hS hX hdec).value) :=
    Z.mono_fieldMorphism_genericFieldPoint B S hS hX hdec
  (FieldValuedPoint.existsUnique_factor_of_class_eq_of_mono B S hS Z.subspace.toFunctor Z.closed.1
    (Z.genericFieldPoint B S hS hX hdec) p
    ((Z.class_genericFieldPoint B S hS hX hdec).trans hp.symm)).exists.choose

/-- The factorization of a field point through `ρ_Z` is a factorization. -/
theorem PrimeDivisor.yoneda_map_genericFieldPointFactor_comp :
    yoneda.map (Z.genericFieldPointFactor B S hS hX hdec p hp) ≫
        fieldMorphism B S hS Z.subspace.toFunctor (Z.genericFieldPoint B S hS hX hdec) =
      fieldMorphism B S hS Z.subspace.toFunctor p := by
  have : Mono (yonedaEquiv.symm (Z.genericFieldPoint B S hS hX hdec).value) :=
    Z.mono_fieldMorphism_genericFieldPoint B S hS hX hdec
  have h := (FieldValuedPoint.existsUnique_factor_of_class_eq_of_mono B S hS Z.subspace.toFunctor
    Z.closed.1 (Z.genericFieldPoint B S hS hX hdec) p
    ((Z.class_genericFieldPoint B S hS hX hdec).trans hp.symm)).exists.choose_spec
  change yoneda.map _ ≫ yonedaEquiv.symm _ = yonedaEquiv.symm _
  rw [yonedaEquiv_symm_naturality_left]
  exact congrArg yonedaEquiv.symm h

/-- **The field homomorphism `κ(u) → K`** induced by the factorization of a field point
`Spec K → Z` over the generic point of `Z` through `ρ_Z`. -/
def PrimeDivisor.genericResidueFieldToFieldPoint :
    Z.genericResidueField B S hS hX hdec →+* p.carrier :=
  fieldValuedPointHom B S hS Z.subspace.toFunctor p (Z.genericFieldPoint B S hS hX hdec)
    (Z.genericFieldPointFactor B S hS hX hdec p hp)

/-- **Evaluation of rational functions of `Z` at a field point over its generic point is `θ_Z⁻¹`
followed by `κ(u) → K`.** -/
theorem PrimeDivisor.evalRingHom_eq_genericResidueFieldToFieldPoint
    (x : rationalFunctions B S hS Z.closed.1) :
    evalRingHom B S hS Z.closed.1 Z.integral p hp x =
      Z.genericResidueFieldToFieldPoint B S hS hX hdec p hp
        ((Z.genericResidueFieldEquivFunctionField B S hS hX hdec).symm x) := by
  obtain ⟨f, rfl⟩ := RationalMap.exists_rep B S hS x
  obtain ⟨j, hj⟩ := exists_genericLift B S hS Z.closed.1 Z.integral
    (Z.genericFieldPoint B S hS hX hdec) (Z.class_genericFieldPoint B S hS hX hdec)
    f.dense_open_domain
  have hg : yoneda.map (Z.genericFieldPointFactor B S hS hX hdec p hp) ≫ j ≫ f.domain.ι =
      fieldMorphism B S hS Z.subspace.toFunctor p := by
    rw [hj]
    exact Z.yoneda_map_genericFieldPointFactor_comp B S hS hX hdec p hp
  rw [evalRingHom_eq_appTop B S hS Z.closed.1 Z.integral p hp f _ j _ hg,
    Z.genericResidueFieldEquivFunctionField_symm_toRationalMap B S hS hX hdec f j hj]
  have hspec := spec_fieldValuedPointHom B S hS Z.subspace.toFunctor p
    (Z.genericFieldPoint B S hS hX hdec) (Z.genericFieldPointFactor B S hS hX hdec p hp)
  have hnat := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom
    (Z.genericResidueFieldToFieldPoint B S hS hX hdec p hp)))
    (affineLineCoordinate B S hS (op ((Z.genericFieldPoint B S hS hX hdec).siteObject B S hS
      Z.subspace.toFunctor)) (yonedaEquiv (j ≫ f.hom)))
  refine Eq.trans ?_ hnat
  change (Scheme.ΓSpecIso (CommRingCat.of p.carrier)).hom.hom
      ((B.inclusion.map (Z.genericFieldPointFactor B S hS hX hdec p hp).left).appTop _) = _
  rw [← hspec]
  rfl

/-! ### The value of a rational function at a point of `V ×_X Z` over the generic point -/

variable (V : SmallEtale B S hS X) (q' : chartScheme (Z.baseChangeChart B S hS hX V))
    (hq' : chartSchemeToPoints B S hS X V (Z.baseChangeChartProj B S hS hX V q') =
      Z.genericPoint B S hS X)

/-- **The field point `Spec κ(q') → Z`** at a point `q'` of the base-change chart `V ×_X Z`. -/
abbrev PrimeDivisor.baseChangeChartFieldPoint : FieldValuedPoint B S hS Z.subspace.toFunctor :=
  chartSchemeFieldValuedPoint B S hS Z.subspace.toFunctor (Z.baseChangeChart B S hS hX V) q'

include hq' in
/-- A point of `V ×_X Z` over the generic point of the prime divisor represents the generic point
of the integral space `Z`: the inclusion of `Z` is injective on points. -/
theorem PrimeDivisor.class_baseChangeChartFieldPoint :
    (Z.baseChangeChartFieldPoint B S hS hX V q').class B S hS Z.subspace.toFunctor =
      Space.genericPoint B S hS Z.closed.1 Z.integral := by
  apply pointsMap_injective_of_mono B S hS Z.subspace.ι
  rw [← Z.genericPoint_eq_pointsMap_ι B S hS hX, ← hq',
    Z.chartSchemeToPoints_baseChangeChartProj B S hS hX V q']
  rfl

/-- **The value at `q'` of the rational functions of `Z`**, a point of the base-change chart
`V ×_X Z` over the generic point of `Z`: evaluation at the field point `Spec κ(q') → Z`. -/
def PrimeDivisor.baseChangeChartRationalReading :
    rationalFunctions B S hS Z.closed.1 →+*
      (chartScheme (Z.baseChangeChart B S hS hX V)).residueField q' :=
  evalRingHom B S hS Z.closed.1 Z.integral (Z.baseChangeChartFieldPoint B S hS hX V q')
    (Z.class_baseChangeChartFieldPoint B S hS hX V q' hq')

/-- **The θ-compatibility at a point of `V ×_X Z`**: the value at `q'` of `θ_Z(c)`, for
`c ∈ κ(u)`, is the image of `c` in `κ(q')` under the field homomorphism induced by the
factorization of `Spec κ(q') → Z` through `ρ_Z`. -/
theorem PrimeDivisor.baseChangeChartRationalReading_genericResidueFieldEquivFunctionField
    (c : Z.genericResidueField B S hS hX hdec) :
    Z.baseChangeChartRationalReading B S hS hX V q' hq'
        (Z.genericResidueFieldEquivFunctionField B S hS hX hdec c) =
      Z.genericResidueFieldToFieldPoint B S hS hX hdec (Z.baseChangeChartFieldPoint B S hS hX V q')
        (Z.class_baseChangeChartFieldPoint B S hS hX V q' hq') c :=
  (Z.evalRingHom_eq_genericResidueFieldToFieldPoint B S hS hX hdec _ _ _).trans
    (congrArg _ ((Z.genericResidueFieldEquivFunctionField B S hS hX hdec).symm_apply_apply c))

end AlgebraicGeometry.Space

end

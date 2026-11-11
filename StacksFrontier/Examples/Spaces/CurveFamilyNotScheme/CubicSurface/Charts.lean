module

public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.CubicSurface.Proper
public import StacksFrontier.AlgebraicGeometry.Curves.Models.PlaneCurveModelBaseChange

/-!
# The standard charts of the cubic surface

The surface `Y : T₀ ^ 3 + T₁ ^ 3 + T₂ ^ 3 - t * T₀ * T₁ * T₂ = 0` of Stacks 0D5E is the plane curve
`V(F) ⊆ ℙ²_{k[t]}` of `Stacks.Models.PlaneCurveModel` for the cubic `F`, over the base `k[t]`.
This file records that identification, over the affine line, and reads off the three standard
charts of `Y`. Since `F` is symmetric in `T₀, T₁, T₂`, setting any one coordinate to `1` gives the
same affine equation

```
  1 + x ^ 3 + y ^ 3 - t * x * y = 0
```

so all three charts are `Spec k[t][x, y]/(1 + x³ + y³ - t x y)`.

## Main definitions

* `Stacks.Examples.CurveFamilyNotScheme.cubicModel`: `V(F)` as a plane curve over `k[t]`, and
  `Stacks.Examples.CurveFamilyNotScheme.cubicSurfaceIso` its identification with `Y`.
* `Stacks.Examples.CurveFamilyNotScheme.cubicChartEquation`: the affine equation
  `1 + x³ + y³ - t x y`, and `Stacks.Examples.CurveFamilyNotScheme.CubicChartRing` its coordinate
  ring `k[t][x, y]/(1 + x³ + y³ - t x y)`.
* `Stacks.Examples.CurveFamilyNotScheme.cubicChartEquiv`: the ring of the chart `Y ∩ D₊(Tⱼ)`
  is `CubicChartRing k`.
* `Stacks.Examples.CurveFamilyNotScheme.cubicChart`: the chart as an open immersion
  `Spec k[t][x, y]/(1 + x³ + y³ - t x y) ⟶ Y`.

## Main results

* `Stacks.Examples.CurveFamilyNotScheme.cubicSurfaceIso_hom_toSpec`: the identification lies over
  the affine line.
* `Stacks.Examples.CurveFamilyNotScheme.dehomCoeff_cubicEquation`: each dehomogenization of `F`
  is `1 + x³ + y³ - t x y`.
* `Stacks.Examples.CurveFamilyNotScheme.iSup_opensRange_cubicChart`: the three charts cover `Y`.
* `Stacks.Examples.CurveFamilyNotScheme.cubicChart_comp_cubicSurfaceToLine`: each chart lies over
  the affine line, through `k[t] → k[t][x, y]/(1 + x³ + y³ - t x y)`.

## References

* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial Stacks.AlgebraicGeometry.ProjPolyChart
  Stacks.RingTheory.HomogeneousQuotient

universe u

namespace Stacks.Examples.CurveFamilyNotScheme

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

/-! ### The cubic surface as a plane curve over `k[t]` -/

/-- The cubic `F` is homogeneous of degree three. -/
theorem isHomogeneous_cubicEquation : (cubicEquation k).IsHomogeneous 3 :=
  (mem_homogeneousSubmodule _ _).1 (cubicEquation_mem k)

/-- The cubic surface as the plane curve `V(F) ⊆ ℙ²_{k[t]}` of `Stacks.Models.PlaneCurveModel`. -/
abbrev cubicModel : Scheme.{u} :=
  Stacks.Models.PlaneCurveModel.scheme (cubicEquation k) (isHomogeneous_cubicEquation k)

/-- The structure morphism `V(F) ⟶ A¹_k` of the plane curve model. -/
abbrev cubicModelToLine : cubicModel k ⟶ affineLine k :=
  Stacks.Models.PlaneCurveModel.toSpec (cubicEquation k) (isHomogeneous_cubicEquation k)

/-- The cubic surface is the plane curve `V(F)`: the two are `Proj` of the same ring, graded by
the same pieces, once by submodules and once by additive subgroups. -/
def cubicSurfaceIso : cubicSurface k ≅ cubicModel k :=
  Stacks.Models.PlaneCurveModel.moduleGradingIso (cubicEquation k) (isHomogeneous_cubicEquation k)

/-- The structure map `k[t] → (k[t][T₀, T₁, T₂]/(F))₀` is the algebra map into the degree-zero
part. -/
theorem algebraMap_cubicGrading_zero :
    algebraMap (Polynomial k) (cubicGrading k 0) = cubicDegreeZero k :=
  RingHom.ext fun a => Subtype.ext (coe_cubicDegreeZero k a).symm

/-- **The identification of `Y` with `V(F)` lies over the affine line.** -/
@[reassoc]
theorem cubicSurfaceIso_hom_toSpec :
    (cubicSurfaceIso k).hom ≫ cubicModelToLine k = cubicSurfaceToLine k :=
  (Stacks.Models.PlaneCurveModel.moduleGradingIso_hom_toSpec (cubicEquation k)
    (isHomogeneous_cubicEquation k)).trans
    (congrArg (fun φ => Proj.toSpecZero (cubicGrading k) ≫ Spec.map (CommRingCat.ofHom φ))
      (algebraMap_cubicGrading_zero k))

/-- The structure morphism of `Y` through the identification with `V(F)`. -/
@[reassoc]
theorem cubicSurfaceIso_inv_toLine :
    (cubicSurfaceIso k).inv ≫ cubicSurfaceToLine k = cubicModelToLine k := by
  rw [← cubicSurfaceIso_hom_toSpec, Iso.inv_hom_id_assoc]

/-! ### The affine equation of the charts -/

/-- The affine equation `1 + x³ + y³ - t x y` of each standard chart of the cubic surface. -/
def cubicChartEquation : MvPolynomial (Fin 2) (Polynomial k) :=
  1 + X 0 ^ 3 + X 1 ^ 3 - C Polynomial.X * (X 0 * X 1)

/-- The coordinate ring `k[t][x, y]/(1 + x³ + y³ - t x y)` of each standard chart of the cubic
surface. -/
abbrev CubicChartRing : Type u :=
  MvPolynomial (Fin 2) (Polynomial k) ⧸ Ideal.span {cubicChartEquation k}

/-- The dehomogenization of the cubic at `T₀` is `1 + x³ + y³ - t x y`. -/
theorem dehomCoeff_cubicEquation_zero :
    Stacks.ProjectiveChart.dehomCoeff (Polynomial k) 0 (cubicEquation k) =
      cubicChartEquation k := by
  rw [Stacks.ProjectiveChart.dehomCoeff_eq_aeval]
  simp only [cubicEquation, map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C,
    MvPolynomial.algebraMap_eq]
  rw [show finSuccEquiv' (0 : Fin 3) 0 = none from rfl,
    show finSuccEquiv' (0 : Fin 3) 1 = some 0 from rfl,
    show finSuccEquiv' (0 : Fin 3) 2 = some 1 from rfl]
  simp only [Option.elim_none, Option.elim_some, cubicChartEquation]
  ring

/-- The dehomogenization of the cubic at `T₁` is `1 + x³ + y³ - t x y`. -/
theorem dehomCoeff_cubicEquation_one :
    Stacks.ProjectiveChart.dehomCoeff (Polynomial k) 1 (cubicEquation k) =
      cubicChartEquation k := by
  rw [Stacks.ProjectiveChart.dehomCoeff_eq_aeval]
  simp only [cubicEquation, map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C,
    MvPolynomial.algebraMap_eq]
  rw [show finSuccEquiv' (1 : Fin 3) 0 = some 0 from rfl,
    show finSuccEquiv' (1 : Fin 3) 1 = none from rfl,
    show finSuccEquiv' (1 : Fin 3) 2 = some 1 from rfl]
  simp only [Option.elim_none, Option.elim_some, cubicChartEquation]
  ring

/-- The dehomogenization of the cubic at `T₂` is `1 + x³ + y³ - t x y`. -/
theorem dehomCoeff_cubicEquation_two :
    Stacks.ProjectiveChart.dehomCoeff (Polynomial k) 2 (cubicEquation k) =
      cubicChartEquation k := by
  rw [Stacks.ProjectiveChart.dehomCoeff_eq_aeval]
  simp only [cubicEquation, map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C,
    MvPolynomial.algebraMap_eq]
  rw [show finSuccEquiv' (2 : Fin 3) 0 = some 0 from rfl,
    show finSuccEquiv' (2 : Fin 3) 1 = some 1 from rfl,
    show finSuccEquiv' (2 : Fin 3) 2 = none from rfl]
  simp only [Option.elim_none, Option.elim_some, cubicChartEquation]
  ring

/-- **Each dehomogenization of the cubic is `1 + x³ + y³ - t x y`**: `F` is symmetric in the three
coordinates, so setting any one of them to `1` gives the same affine equation. -/
theorem dehomCoeff_cubicEquation (j : Fin 3) :
    Stacks.ProjectiveChart.dehomCoeff (Polynomial k) j (cubicEquation k) =
      cubicChartEquation k := by
  fin_cases j
  exacts [dehomCoeff_cubicEquation_zero k, dehomCoeff_cubicEquation_one k,
    dehomCoeff_cubicEquation_two k]

/-- The coordinate `T₀` does not divide the cubic: `F(0, 1, 0) = 1`. -/
theorem not_X_zero_dvd_cubicEquation :
    ¬ (X 0 : MvPolynomial (Fin 3) (Polynomial k)) ∣ cubicEquation k :=
  Stacks.Models.PlaneCurveModel.not_X_dvd_of_eval_ne_zero (cubicEquation k)
    (v := ![0, 1, 0]) rfl (by simp [cubicEquation])

/-- The chart `V(F) ∩ D₊(Tⱼ)` of the plane curve model. -/
abbrev cubicModelChart (j : Fin 3) : (cubicModel k).Opens :=
  Stacks.Models.PlaneCurveModel.chart (cubicEquation k) (isHomogeneous_cubicEquation k) j

/-- The chart `V(F) ∩ D₊(Tⱼ)` is an affine open. -/
theorem isAffineOpen_cubicModelChart (j : Fin 3) : IsAffineOpen (cubicModelChart k j) :=
  Stacks.Models.PlaneCurveModel.isAffineOpen_chart _ _ j

/-- The three charts `V(F) ∩ D₊(Tⱼ)` cover `V(F)`. -/
theorem iSup_cubicModelChart : ⨆ j : Fin 3, cubicModelChart k j = ⊤ :=
  Stacks.Models.PlaneCurveModel.iSup_chart_eq_top _ _

/-- **The ring of each chart is `k[t][x, y]/(1 + x³ + y³ - t x y)`.** -/
def cubicChartEquiv (j : Fin 3) : CubicChartRing k ≃+* Γ(cubicModel k, cubicModelChart k j) :=
  (Ideal.quotEquivOfEq (by rw [dehomCoeff_cubicEquation])).trans
    (Stacks.Models.PlaneCurveModel.chartEquiv (cubicEquation k) (isHomogeneous_cubicEquation k) 0
      (not_X_zero_dvd_cubicEquation k) j)

/-- The chart identification carries the class of a constant `C r` to the pullback of `r` along
the structure morphism. -/
theorem cubicChartEquiv_mk_C (j : Fin 3) (r : Polynomial k) :
    cubicChartEquiv k j (Ideal.Quotient.mk _ (C r)) =
      ((cubicModelToLine k).appLE ⊤ (cubicModelChart k j) le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv.hom r) := by
  rw [cubicChartEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  exact Stacks.Models.PlaneCurveModel.chartEquiv_mk_C _ _ 0 _ j r

/-- The chart identification is `k[t]`-linear: on constants it is the structure map. -/
theorem appLE_cubicModelToLine_eq (j : Fin 3) :
    (Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv ≫
        (cubicModelToLine k).appLE ⊤ (cubicModelChart k j) le_top ≫
          (cubicChartEquiv k j).toCommRingCatIso.inv =
      CommRingCat.ofHom (algebraMap (Polynomial k) (CubicChartRing k)) := by
  refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
  change (cubicChartEquiv k j).symm
      (((cubicModelToLine k).appLE ⊤ (cubicModelChart k j) le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv.hom r)) =
    algebraMap (Polynomial k) (CubicChartRing k) r
  rw [← cubicChartEquiv_mk_C, RingEquiv.symm_apply_apply, ← Ideal.Quotient.mk_algebraMap,
    MvPolynomial.algebraMap_eq]

/-! ### The charts as open immersions -/

/-- **The standard chart `Y ∩ D₊(Tⱼ)`** as an open immersion
`Spec k[t][x, y]/(1 + x³ + y³ - t x y) ⟶ Y`. -/
def cubicChart (j : Fin 3) : Spec (CommRingCat.of (CubicChartRing k)) ⟶ cubicSurface k :=
  Spec.map (cubicChartEquiv k j).toCommRingCatIso.inv ≫
    (isAffineOpen_cubicModelChart k j).fromSpec ≫ (cubicSurfaceIso k).inv

/-- Each chart is an open immersion. -/
instance (j : Fin 3) : IsOpenImmersion (cubicChart k j) := by
  have := (isAffineOpen_cubicModelChart k j).isOpenImmersion_fromSpec
  unfold cubicChart
  infer_instance

/-- The image of the chart `j` is the inverse image of `V(F) ∩ D₊(Tⱼ)` under `Y ≅ V(F)`. -/
theorem opensRange_cubicChart (j : Fin 3) :
    (cubicChart k j).opensRange = (cubicSurfaceIso k).hom ⁻¹ᵁ cubicModelChart k j := by
  have := (isAffineOpen_cubicModelChart k j).isOpenImmersion_fromSpec
  change (Spec.map (cubicChartEquiv k j).toCommRingCatIso.inv ≫
    (isAffineOpen_cubicModelChart k j).fromSpec ≫ (cubicSurfaceIso k).inv).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_comp,
    IsAffineOpen.opensRange_fromSpec]
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    change (cubicSurfaceIso k).hom ((cubicSurfaceIso k).inv z) ∈ cubicModelChart k j
    rwa [Scheme.inv_hom_apply]
  · intro hy
    exact ⟨(cubicSurfaceIso k).hom y, hy, Scheme.hom_inv_apply (cubicSurfaceIso k) y⟩

/-- **The three standard charts cover the cubic surface.** -/
theorem iSup_opensRange_cubicChart : ⨆ j : Fin 3, (cubicChart k j).opensRange = ⊤ := by
  simp_rw [opensRange_cubicChart]
  rw [← Scheme.Hom.preimage_iSup, iSup_cubicModelChart, Scheme.Hom.preimage_top]

/-- **Each chart lies over the affine line**, through the structure map
`k[t] → k[t][x, y]/(1 + x³ + y³ - t x y)`. -/
@[reassoc]
theorem cubicChart_comp_cubicSurfaceToLine (j : Fin 3) :
    cubicChart k j ≫ cubicSurfaceToLine k =
      Spec.map (CommRingCat.ofHom (algebraMap (Polynomial k) (CubicChartRing k))) := by
  rw [cubicChart, Category.assoc, Category.assoc, cubicSurfaceIso_inv_toLine,
    ← IsAffineOpen.SpecMap_appLE_fromSpec (cubicModelToLine k) (isAffineOpen_top _)
      (isAffineOpen_cubicModelChart k j) le_top,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp, ← Spec.map_comp,
    ← appLE_cubicModelToLine_eq k j, Category.assoc]

end Stacks.Examples.CurveFamilyNotScheme

end

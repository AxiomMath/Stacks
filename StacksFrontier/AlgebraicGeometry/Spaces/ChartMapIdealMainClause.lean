module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangeAffineTest
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartMapIdealBaseChangeVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleChartSections

/-!
# The ideal of the main clause of Stacks 083K

Let `S = \Spec(R)` be an affine scheme of a big fppf site, let `X` be an algebraic space over
`S` and let `u : ℱ ⟶ 𝒢` be a map of quasi-coherent `𝒪_X`-modules with `𝒢` flat over `S`, as in
Stacks 0CWA. Let `T` be an affine object of the big fppf category over `S` such that the base
change `u_T` vanishes. Then over every affine étale chart `V` of `X`, every value of `u` lies in
`I · 𝒢(V)`, where `I = \ker(\Gamma(S, ⊤) ⟶ \Gamma(T, ⊤))` is the ideal of the smallest closed
subscheme of `S` through which `T ⟶ S` factors.

## Main results

* `AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.val_app_mem_ker_smul_top_of_isZeroAt`:
  the values of `u` over an affine chart `V` lie in `\ker(\Gamma(S, ⊤) ⟶ \Gamma(T, ⊤)) · 𝒢(V)`.

## References

* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
* [Stacks Project, Tag 0CWA](https://stacks.math.columbia.edu/tag/0CWA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) [IsAffine S]

namespace ModuleMapFlatTargetSituation

section ChartSpace

variable (D : ModuleMapFlatTargetSituation B S hS) (T : BigFppfOver B S hS)
    (V : SmallEtale B S hS (D.toModuleMapSituation B S hS).X.1)

/-- The ring of functions of the base change of the chart `V` by the test object. -/
private abbrev baseTestChartRing : Type u :=
  chartRing B S hS
    ((D.toModuleMapSituation B S hS).baseChangeSpace (D.baseTest B S hS T)).1
    ((D.toModuleMapSituation B S hS).baseChangeSpace (D.baseTest B S hS T)).2
    (D.baseTestChartDiagram B S hS T V).U

/-- The ring of functions of the chart `V`, in the chart-space spelling: the ring of the
identity chart of the algebraic space represented by `V`. -/
private abbrev baseTestChartSpaceRing : Type u :=
  chartRing B S hS
    (chartSpace B S hS (D.toModuleMapSituation B S hS).X
      (D.baseTestChartDiagram B S hS T V).V).1
    (chartSpace B S hS (D.toModuleMapSituation B S hS).X
      (D.baseTestChartDiagram B S hS T V).V).2
    (chartSpaceIdChartDiagram B S hS
      ((D.toModuleMapSituation B S hS).baseChangeProjection (D.baseTest B S hS T))
      (D.baseTestChartDiagram B S hS T V)).V

/-- The `\Gamma(S, ⊤)`-algebra structure on the ring of functions of the chart `V`, in the
chart-space spelling. -/
private abbrev baseTestChartSpaceBaseAlgebra :
    Algebra Γ(S, ⊤) (baseTestChartSpaceRing B S hS D T V) :=
  chartBaseAlgebra B S hS
    (chartSpace B S hS (D.toModuleMapSituation B S hS).X
      (D.baseTestChartDiagram B S hS T V).V)
    (chartSpaceIdChartDiagram B S hS
      ((D.toModuleMapSituation B S hS).baseChangeProjection (D.baseTest B S hS T))
      (D.baseTestChartDiagram B S hS T V)).V

/-- The `\Gamma(S, ⊤)`-module structure on the sections of a module over the chart `V`, in the
chart-space spelling: restriction of scalars along the pullback of functions by the structure
morphism of the chart to the base. -/
private abbrev baseTestChartSpaceBaseModule
    (M : Modules.{u, u} B S hS (D.toModuleMapSituation B S hS).X.1
      (D.toModuleMapSituation B S hS).X.2) :
    Module Γ(S, ⊤) (chartSpaceIdSections B S hS
      ((D.toModuleMapSituation B S hS).baseChangeProjection (D.baseTest B S hS T)) M
      (D.baseTestChartDiagram B S hS T V)) :=
  Module.compHom _ (chartToBaseRingHom B S hS
    (chartSpace B S hS (D.toModuleMapSituation B S hS).X
      (D.baseTestChartDiagram B S hS T V).V)
    (chartSpaceIdChartDiagram B S hS
      ((D.toModuleMapSituation B S hS).baseChangeProjection (D.baseTest B S hS T))
      (D.baseTestChartDiagram B S hS T V)).V)

/-- The ring of functions of the base change of the chart `V` by `T` is, as an algebra over the
ring of functions of `V` in the chart-space spelling, the tensor product of that ring with
`\Gamma(T, ⊤)` over `\Gamma(S, ⊤)`. -/
private def baseTestChartSpaceAlgEquiv
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hV : IsAffine (chartScheme V)) :
    letI : Algebra Γ(S, ⊤) (Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) : Type u) :=
      siteObjectBaseAlgebra B S hS T
    letI := baseTestChartSpaceBaseAlgebra B S hS D T V
    letI : Algebra (baseTestChartSpaceRing B S hS D T V)
        (baseTestChartRing B S hS D T V) :=
      chartDiagramAlgebra B S hS
        ((D.toModuleMapSituation B S hS).baseChangeProjection (D.baseTest B S hS T))
        (D.baseTestChartDiagram B S hS T V)
    baseTestChartRing B S hS D T V ≃ₐ[baseTestChartSpaceRing B S hS D T V]
      TensorProduct Γ(S, ⊤) (baseTestChartSpaceRing B S hS D T V)
        (Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) : Type u) :=
  D.chartRingBaseTestAlgEquiv B S hS T V hT hV

/-- If the base change of `u` to `T` vanishes, then the values of `u` over the chart `V` vanish
in `𝒢(V) ⊗_{\Gamma(S, ⊤)} \Gamma(T, ⊤)`, in the chart-space spelling. -/
private theorem tmul_one_eq_zero_chartSpace_of_isZeroAt
    (hzero : (D.toModuleMapSituation B S hS).IsZeroAt (modulePullbackSystem B S hS)
      (D.baseTest B S hS T))
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hV : IsAffine (chartScheme V)) :
    letI : Algebra Γ(S, ⊤) (Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) : Type u) :=
      siteObjectBaseAlgebra B S hS T
    letI := baseTestChartSpaceBaseModule B S hS D T V (D.toModuleMapSituation B S hS).G
    ∀ m : chartSpaceIdSections B S hS
        ((D.toModuleMapSituation B S hS).baseChangeProjection (D.baseTest B S hS T))
        (D.toModuleMapSituation B S hS).F (D.baseTestChartDiagram B S hS T V),
      (((etaleModulePullback B S hS
              (chartToSpace B S hS (D.toModuleMapSituation B S hS).X
                (D.baseTestChartDiagram B S hS T V).V)
              (isEtale_chartToSpace B S hS (D.toModuleMapSituation B S hS).X
                (D.baseTestChartDiagram B S hS T V).V)).map
            (D.toModuleMapSituation B S hS).u).val.app
          (op (chartSpaceIdChartDiagram B S hS
            ((D.toModuleMapSituation B S hS).baseChangeProjection (D.baseTest B S hS T))
            (D.baseTestChartDiagram B S hS T V)).V)).hom m ⊗ₜ[Γ(S, ⊤)]
        (1 : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) = 0 := by
  let : Algebra Γ(S, ⊤) (Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) : Type u) :=
    siteObjectBaseAlgebra B S hS T
  let := baseTestChartSpaceBaseAlgebra B S hS D T V
  let : Algebra (baseTestChartSpaceRing B S hS D T V)
      (baseTestChartRing B S hS D T V) :=
    chartDiagramAlgebra B S hS
      ((D.toModuleMapSituation B S hS).baseChangeProjection (D.baseTest B S hS T))
      (D.baseTestChartDiagram B S hS T V)
  let := baseTestChartSpaceBaseModule B S hS D T V (D.toModuleMapSituation B S hS).G
  have := isScalarTower_chartRing_sections B S hS
    (chartSpace B S hS (D.toModuleMapSituation B S hS).X
      (D.baseTestChartDiagram B S hS T V).V)
    ((etaleModulePullback B S hS
        (chartToSpace B S hS (D.toModuleMapSituation B S hS).X
          (D.baseTestChartDiagram B S hS T V).V)
        (isEtale_chartToSpace B S hS (D.toModuleMapSituation B S hS).X
          (D.baseTestChartDiagram B S hS T V).V)).obj (D.toModuleMapSituation B S hS).G)
    (chartSpaceIdChartDiagram B S hS
      ((D.toModuleMapSituation B S hS).baseChangeProjection (D.baseTest B S hS T))
      (D.baseTestChartDiagram B S hS T V)).V
  exact Stacks.Flattening.tmul_one_eq_zero_of_lTensor_eq_zero
    (baseTestChartSpaceAlgEquiv B S hS D T V hT hV) _
    (D.lTensor_val_app_eq_zero_of_isZeroAt B S hS T V hzero hT hV)

/-- If the base change of `u` to `T` vanishes, then the values of `u` over the chart `V` lie in
`\ker(\Gamma(S, ⊤) ⟶ \Gamma(T, ⊤)) · 𝒢(V)`, in the chart-space spelling. -/
private theorem mem_ker_smul_top_chartSpace_of_isZeroAt
    (hzero : (D.toModuleMapSituation B S hS).IsZeroAt (modulePullbackSystem B S hS)
      (D.baseTest B S hS T))
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hV : IsAffine (chartScheme V)) :
    letI := baseTestChartSpaceBaseModule B S hS D T V (D.toModuleMapSituation B S hS).G
    ∀ m : chartSpaceIdSections B S hS
        ((D.toModuleMapSituation B S hS).baseChangeProjection (D.baseTest B S hS T))
        (D.toModuleMapSituation B S hS).F (D.baseTestChartDiagram B S hS T V),
      (((etaleModulePullback B S hS
              (chartToSpace B S hS (D.toModuleMapSituation B S hS).X
                (D.baseTestChartDiagram B S hS T V).V)
              (isEtale_chartToSpace B S hS (D.toModuleMapSituation B S hS).X
                (D.baseTestChartDiagram B S hS T V).V)).map
            (D.toModuleMapSituation B S hS).u).val.app
          (op (chartSpaceIdChartDiagram B S hS
            ((D.toModuleMapSituation B S hS).baseChangeProjection (D.baseTest B S hS T))
            (D.baseTestChartDiagram B S hS T V)).V)).hom m ∈
        RingHom.ker (show Γ(S, ⊤) →+*
            (Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) : Type u) from
          (B.inclusion.map T.hom).appTop.hom) •
          (⊤ : Submodule Γ(S, ⊤) (chartSpaceIdSections B S hS
            ((D.toModuleMapSituation B S hS).baseChangeProjection (D.baseTest B S hS T))
            (D.toModuleMapSituation B S hS).G (D.baseTestChartDiagram B S hS T V))) := by
  let : Algebra Γ(S, ⊤) (Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) : Type u) :=
    siteObjectBaseAlgebra B S hS T
  let := baseTestChartSpaceBaseModule B S hS D T V (D.toModuleMapSituation B S hS).G
  have : Module.Flat Γ(S, ⊤) (chartSpaceIdSections B S hS
      ((D.toModuleMapSituation B S hS).baseChangeProjection (D.baseTest B S hS T))
      (D.toModuleMapSituation B S hS).G (D.baseTestChartDiagram B S hS T V)) :=
    flat_sections_G B S hS D V hV
  intro m
  exact Stacks.Flattening.mem_ker_smul_top_of_tmul_eq_zero
    (R' := (Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) : Type u))
    (tmul_one_eq_zero_chartSpace_of_isZeroAt B S hS D T V hzero hT hV m)

end ChartSpace

section Chart

variable (D : ModuleMapFlatTargetSituation B S hS) (T : BigFppfOver B S hS)
    (V : SmallEtale B S hS D.X.1)

/-- Let `u : ℱ ⟶ 𝒢` be a map of quasi-coherent modules on an algebraic space `X` over an affine
base `S`, with `𝒢` flat over `S`, and let `T` be an affine test object over `S` at which the base
change of `u` vanishes. Then over every affine étale chart `V` of `X`, every value of `u` lies
in `I · 𝒢(V)`, where `I = \ker(\Gamma(S, ⊤) ⟶ \Gamma(T, ⊤))`. -/
theorem val_app_mem_ker_smul_top_of_isZeroAt
    (hzero : (D.toModuleMapSituation B S hS).IsZeroAt (modulePullbackSystem B S hS)
      (D.baseTest B S hS T))
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hV : IsAffine (chartScheme V)) :
    letI : Module Γ(S, ⊤) (D.G.val.obj (op V) : Type u) :=
      Module.compHom _ (chartToBaseRingHom B S hS D.X V)
    ∀ m : D.F.val.obj (op V),
      (D.u.val.app (op V)).hom m ∈
        RingHom.ker (show Γ(S, ⊤) →+*
            (Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) : Type u) from
          (B.inclusion.map T.hom).appTop.hom) •
          (⊤ : Submodule Γ(S, ⊤) (D.G.val.obj (op V) : Type u)) :=
  mem_ker_smul_top_chartSpace_of_isZeroAt B S hS D T V hzero hT hV

end Chart

end ModuleMapFlatTargetSituation

end AlgebraicGeometry.Space

end

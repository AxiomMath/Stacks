module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartMapIdealBaseChangeVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartMapIdealTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartMapVanishingOffSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOverSpecQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeChartSections

/-!
# The finitely generated ideal of the finite-presentation clause of Stacks 083K

Let `S = \Spec(R)` be an affine scheme of a big fppf site, let `X` be an algebraic space over
`S` and let `u : ℱ ⟶ 𝒢` be a map of quasi-coherent `𝒪_X`-modules with `𝒢` flat over `S`
(Stacks 0CWA).  Assume `ℱ` is of finite type.  At an affine étale chart `Z₀` of `X` the sections
of `ℱ` are a finite module over the ring of the chart
(`AlgebraicGeometry.Space.module_finite_sections_of_isFiniteTypeOnSite`) and the sections of `𝒢`
are flat over `R` (`AlgebraicGeometry.Space.flat_sections_of_isFlatOver`), so the commutative
algebra of `StacksFrontier/RingTheory/Flat/MakeMapZeroIdeal.lean` produces a **finitely generated**
ideal `J ⊆ R` which already kills the image of `u` there; the closed subscheme
`Z = \Spec(R/J) ⊆ S` it cuts out is then of finite presentation over `S`, and the test scheme
factors through it.

This is the ideal of the finite-presentation clause of Stacks 083K.  Being finitely generated it
cannot be recomputed chart by chart, and
`AlgebraicGeometry.Space.val_app_mem_smul_top_of_forall_mem_smul_top` is what carries it from
`Z₀` to every affine chart over `Z₀`.

## Main definitions

* `AlgebraicGeometry.Space.testSchemeBaseAlgebra`: the `Γ(S, ⊤)`-algebra of global functions on
  an object of the big fppf category over `S`, through its structure morphism.

## Main results

* `AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.exists_fg_ideal_mem_smul_top_chart`: **a
  finitely generated ideal of the functions on the base, inside the kernel of the test algebra,
  which kills the image of `u` over a fixed affine chart.**
* `AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.val_app_mem_smul_top_of_hom`: such an
  ideal kills the image of `u` over every affine chart over that one.
* `AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.exists_fg_ideal_specQuotient`: **the
  geometric package** — a finitely generated ideal whose closed subscheme
  `Z = \Spec(Γ(S, ⊤)/J) ⊆ S` is locally of finite presentation over `S` and affine over `S`
  (hence of finite presentation), through which the test object factors, and whose ideal kills
  the image of `u` over the fixed affine chart and over every affine chart over it.
* `modulePullback_map_val_app_specQuotient_eq_zero`, in the same namespace: **`u_Z` vanishes on
  the sections over every affine chart of `X ×_S Z` lying above an affine chart of `X` over
  `Z₀`.**
* `modulePullback_map_val_app_specQuotient_eq_zero_of_subsingleton`, in the same namespace:
  **`u_Z` vanishes on the sections over every affine chart of `X ×_S Z` lying above a chart of
  `X` carrying no nonzero sections of `ℱ`** — in particular above a chart missing the support of
  `ℱ`, by
  `AlgebraicGeometry.Space.exists_chart_forall_val_app_eq_zero_of_notMem_supportOfSheaf`.

## Implementation notes

The hypothesis taken is the vanishing of the base change of `u` *at the chart* `Z₀`, in the ring
form `LinearMap.rTensor R' (u(Z₀))`: that is the shape in which
`Stacks.Flattening.exists_fg_ideal_rTensor_quotient_eq_zero` consumes it.  Reading the vanishing
of the base change `u_T` on the algebraic space `X ×_S T` as this ring statement at a chart is
the content of the unconditional clause of Stacks 083K and is not done here.

The `Γ(S, ⊤)`-module structures on the sections are restriction of scalars along
`AlgebraicGeometry.Space.chartToBaseRingHom`, the pullback of functions by the structure morphism
of the chart, as `AlgebraicGeometry.Space.flat_sections_of_isFlatOver` and
`AlgebraicGeometry.Space.isScalarTower_chartRing_sections` fix them; all four instances the ring
statement needs — the algebra, the two module structures, the two towers — are introduced
explicitly, since none of them is a global instance.

What this file does **not** do is reach the vanishing of `u_Z` as a map of sheaves of modules on
`X ×_S Z`.  Both chartwise halves are here: the charts of `X ×_S Z` above a chart of `X` over `Z₀`
and the charts above a chart of `X` carrying no nonzero sections of `ℱ`.  The support hypothesis
of the clause provides one affine chart `Z₀` whose image contains the support of `ℱ`
(`AlgebraicGeometry.Space.isCompact_supportOfSheaf_of_compactSpace` and
`AlgebraicGeometry.Space.exists_affine_etale_chart_of_isCompact`), and
`AlgebraicGeometry.Space.exists_chart_forall_val_app_eq_zero_of_notMem_supportOfSheaf` provides a
chart with no nonzero sections of `ℱ` around every point off the support.  What is missing is that
those two families *cover*: that every affine chart of `X ×_S Z` is covered by charts each of
which lies above a chart of `X` of one of the two kinds, together with the locality statement that
a map of sheaves of modules vanishing on a covering vanishes.

## References

* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
* [Stacks Project, Tag 0CWA](https://stacks.math.columbia.edu/tag/0CWA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The `Γ(S, ⊤)`-algebra of global functions on an object of the big fppf category over `S`,
through the pullback of functions by its structure morphism.  Not an instance: it depends on the
object. -/
@[instance_reducible]
def testSchemeBaseAlgebra (T : BigFppfOver B S hS) :
    Algebra Γ(S, ⊤) Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
  ((B.inclusion.map T.hom).appTop.hom).toAlgebra

/-- The algebra map of `testSchemeBaseAlgebra` is the pullback of global functions along the
structure morphism of the object. -/
@[simp]
theorem algebraMap_testSchemeBaseAlgebra (T : BigFppfOver B S hS) :
    letI := testSchemeBaseAlgebra B S hS T
    algebraMap Γ(S, ⊤) Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) =
      (B.inclusion.map T.hom).appTop.hom := rfl

namespace ModuleMapFlatTargetSituation

variable [IsAffine S] (D : ModuleMapFlatTargetSituation B S hS)

/-- **A finitely generated ideal of the functions on the base which kills the image of `u` over a
fixed affine chart.**

At an affine étale chart `Z₀` the sections of `ℱ` are a finite module over the ring of the chart
and the sections of `𝒢` are flat over `Γ(S, ⊤)`, so
`Stacks.Flattening.exists_fg_ideal_rTensor_quotient_eq_zero` applies to the map on sections: the
ideal it produces is finitely generated, lies in the kernel of the test algebra, and every value
of `u` over `Z₀` lies in `J · 𝒢(Z₀)`.

The hypothesis is the vanishing of the base change of the map on sections to the test algebra. -/
theorem exists_fg_ideal_mem_smul_top_chart
    (hFft : SheafOfModules.IsFiniteTypeOnSite D.F) (Z₀ : SmallEtale B S hS D.X.1)
    (hZ₀ : IsAffine ((SmallEtale.toOver B S hS D.X.1 ⋙ BigFppfOver.toScheme B S hS).obj Z₀))
    (R' : Type u) [CommRing R'] [Algebra Γ(S, ⊤) R'] :
    letI := chartBaseAlgebra B S hS D.X Z₀
    letI : Module Γ(S, ⊤) (D.F.val.obj (op Z₀) : Type u) :=
      Module.compHom _ (chartToBaseRingHom B S hS D.X Z₀)
    letI : Module Γ(S, ⊤) (D.G.val.obj (op Z₀) : Type u) :=
      Module.compHom _ (chartToBaseRingHom B S hS D.X Z₀)
    haveI := isScalarTower_chartRing_sections B S hS D.X D.F Z₀
    haveI := isScalarTower_chartRing_sections B S hS D.X D.G Z₀
    LinearMap.rTensor R' ((D.u.val.app (op Z₀)).hom.restrictScalars Γ(S, ⊤)) = 0 →
      ∃ J : Ideal Γ(S, ⊤), J.FG ∧ J ≤ RingHom.ker (algebraMap Γ(S, ⊤) R') ∧
        ∀ z : D.F.val.obj (op Z₀), D.u.val.app (op Z₀) z ∈
          J • (⊤ : Submodule Γ(S, ⊤) (D.G.val.obj (op Z₀) : Type u)) := by
  let := chartBaseAlgebra B S hS D.X Z₀
  let : Module Γ(S, ⊤) (D.F.val.obj (op Z₀) : Type u) :=
    Module.compHom _ (chartToBaseRingHom B S hS D.X Z₀)
  let : Module Γ(S, ⊤) (D.G.val.obj (op Z₀) : Type u) :=
    Module.compHom _ (chartToBaseRingHom B S hS D.X Z₀)
  have := isScalarTower_chartRing_sections B S hS D.X D.F Z₀
  have := isScalarTower_chartRing_sections B S hS D.X D.G Z₀
  have : Module.Flat Γ(S, ⊤) (D.G.val.obj (op Z₀) : Type u) :=
    flat_sections_G B S hS D Z₀ hZ₀
  have : Module.Finite (chartRing B S hS D.X.1 D.X.2 Z₀)
      (D.F.val.obj (op Z₀) : Type u) :=
    module_finite_sections_of_isFiniteTypeOnSite D.F D.quasicoherent_F hFft Z₀ hZ₀
  intro hzero
  obtain ⟨J, hJfg, hJle, hJ⟩ :=
    Stacks.Flattening.exists_fg_ideal_rTensor_quotient_eq_zero (R' := R')
      (D.u.val.app (op Z₀)).hom hzero
  exact ⟨J, hJfg, hJle,
    (Stacks.Flattening.rTensor_quotient_eq_zero_iff_forall_mem_smul_top _).1 hJ⟩

/-- **An ideal of the functions on the base which kills the image of `u` over an affine chart
kills it over every affine chart over that one.**

This is `AlgebraicGeometry.Space.val_app_mem_smul_top_of_forall_mem_smul_top`, whose
cartesian-ness hypothesis on the source module is supplied by quasi-coherence through
Stacks 03DX(2). -/
theorem val_app_mem_smul_top_of_hom {Z₀ V : SmallEtale B S hS D.X.1}
    (hZ₀ : IsAffine ((SmallEtale.toOver B S hS D.X.1 ⋙ BigFppfOver.toScheme B S hS).obj Z₀))
    (hV : IsAffine ((SmallEtale.toOver B S hS D.X.1 ⋙ BigFppfOver.toScheme B S hS).obj V))
    (φ : V ⟶ Z₀) (J : Ideal Γ(S, ⊤)) :
    letI : Module Γ(S, ⊤) (D.G.val.obj (op Z₀) : Type u) :=
      Module.compHom _ (chartToBaseRingHom B S hS D.X Z₀)
    letI : Module Γ(S, ⊤) (D.G.val.obj (op V) : Type u) :=
      Module.compHom _ (chartToBaseRingHom B S hS D.X V)
    (∀ z : D.F.val.obj (op Z₀), D.u.val.app (op Z₀) z ∈
        J • (⊤ : Submodule Γ(S, ⊤) (D.G.val.obj (op Z₀) : Type u))) →
      ∀ x : D.F.val.obj (op V), D.u.val.app (op V) x ∈
        J • (⊤ : Submodule Γ(S, ⊤) (D.G.val.obj (op V) : Type u)) :=
  val_app_mem_smul_top_of_forall_mem_smul_top B S hS D.X
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS D.X.1 D.X.2 D.F
      D.quasicoherent_F) D.u hZ₀ hV φ J

/-- **The geometric package of the finite-presentation clause of Stacks 083K.**

There is a finitely generated ideal `J` of the functions on the affine base such that

* the closed subscheme `Z = \Spec(Γ(S, ⊤)/J) ⊆ S` it cuts out is locally of finite presentation
  over `S` — and it is affine over `S`, hence quasi-compact and quasi-separated, so `Z ⟶ S` is
  of finite presentation;
* the test object `T` factors through `Z` over `S`;
* every value of `u` over the fixed affine chart `Z₀` lies in `J · 𝒢(Z₀)`, hence, by
  `AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.val_app_mem_smul_top_of_hom`, over every
  affine chart over `Z₀`.

The hypothesis is the vanishing of the base change of the map on sections over `Z₀` to the ring
of global functions on `T`. -/
theorem exists_fg_ideal_specQuotient
    (hFft : SheafOfModules.IsFiniteTypeOnSite D.F) (Z₀ : SmallEtale B S hS D.X.1)
    (hZ₀ : IsAffine ((SmallEtale.toOver B S hS D.X.1 ⋙ BigFppfOver.toScheme B S hS).obj Z₀))
    (T : BigFppfOver B S hS) :
    letI := chartBaseAlgebra B S hS D.X Z₀
    letI := testSchemeBaseAlgebra B S hS T
    letI : Module Γ(S, ⊤) (D.F.val.obj (op Z₀) : Type u) :=
      Module.compHom _ (chartToBaseRingHom B S hS D.X Z₀)
    letI : Module Γ(S, ⊤) (D.G.val.obj (op Z₀) : Type u) :=
      Module.compHom _ (chartToBaseRingHom B S hS D.X Z₀)
    haveI := isScalarTower_chartRing_sections B S hS D.X D.F Z₀
    haveI := isScalarTower_chartRing_sections B S hS D.X D.G Z₀
    LinearMap.rTensor Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)
        ((D.u.val.app (op Z₀)).hom.restrictScalars Γ(S, ⊤)) = 0 →
      ∃ J : Ideal Γ(S, ⊤), J.FG ∧
        LocallyOfFinitePresentation (specQuotientToBase S J) ∧
        Nonempty (T ⟶ specQuotientOver B S hS J) ∧
        ∀ z : D.F.val.obj (op Z₀), D.u.val.app (op Z₀) z ∈
          J • (⊤ : Submodule Γ(S, ⊤) (D.G.val.obj (op Z₀) : Type u)) := by
  let := chartBaseAlgebra B S hS D.X Z₀
  let := testSchemeBaseAlgebra B S hS T
  let : Module Γ(S, ⊤) (D.F.val.obj (op Z₀) : Type u) :=
    Module.compHom _ (chartToBaseRingHom B S hS D.X Z₀)
  let : Module Γ(S, ⊤) (D.G.val.obj (op Z₀) : Type u) :=
    Module.compHom _ (chartToBaseRingHom B S hS D.X Z₀)
  intro hzero
  obtain ⟨J, hJfg, hJle, hJ⟩ :=
    exists_fg_ideal_mem_smul_top_chart B S hS D hFft Z₀ hZ₀
      Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) hzero
  refine ⟨J, hJfg, locallyOfFinitePresentation_specQuotientToBase S hJfg,
    exists_hom_specQuotientOver B S hS J T ?_, hJ⟩
  exact hJle

/-- **The vanishing of `u_Z` over a chart of `X ×_S Z` lying above a chart of `X` over `Z₀`.**

Let `J` be an ideal of the functions on the base killing the image of `u` over an affine chart
`Z₀`, let `Z = \Spec(Γ(S, ⊤)/J)` be the closed subscheme it cuts out, and let `d` be a diagram of
affine étale charts over the projection `X ×_S Z ⟶ X` whose chart of `X` lies over `Z₀`.  Then the
base change `u_Z` vanishes on the sections over the chart of `X ×_S Z`.

The ideal is carried from `Z₀` to the chart of `X` by
`AlgebraicGeometry.Space.ModuleMapFlatTargetSituation.val_app_mem_smul_top_of_hom`, it acts by
zero on the functions of the chart of `X ×_S Z` by
`AlgebraicGeometry.Space.smul_chartRing_baseChangeSpace_eq_zero`, and
`AlgebraicGeometry.Space.modulePullback_map_val_app_eq_zero_of_forall_mem_smul_top_chart`
concludes. -/
theorem modulePullback_map_val_app_specQuotient_eq_zero (J : Ideal Γ(S, ⊤))
    {Z₀ : SmallEtale B S hS D.X.1}
    (hZ₀ : IsAffine ((SmallEtale.toOver B S hS D.X.1 ⋙ BigFppfOver.toScheme B S hS).obj Z₀))
    (d : ChartDiagram B S hS
      ((D.toModuleMapSituation B S hS).baseChangeSpace (D.specQuotientTest B S hS J)).1
      D.X.1 ((D.toModuleMapSituation B S hS).baseChangeProjection
        (D.specQuotientTest B S hS J)).hom)
    (hU : IsAffine ((SmallEtale.toOver B S hS
      ((D.toModuleMapSituation B S hS).baseChangeSpace
        (D.specQuotientTest B S hS J)).1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS D.X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V))
    (φ : d.V ⟶ Z₀) :
    letI : Module Γ(S, ⊤) (D.G.val.obj (op Z₀) : Type u) :=
      Module.compHom _ (chartToBaseRingHom B S hS D.X Z₀)
    (∀ z : D.F.val.obj (op Z₀), D.u.val.app (op Z₀) z ∈
        J • (⊤ : Submodule Γ(S, ⊤) (D.G.val.obj (op Z₀) : Type u))) →
      ((modulePullback B S hS ((D.toModuleMapSituation B S hS).baseChangeProjection
          (D.specQuotientTest B S hS J))).map D.u).val.app (op d.U) = 0 := by
  intro hJ
  exact modulePullback_map_val_app_eq_zero_of_forall_mem_smul_top_chart B S hS
    ((D.toModuleMapSituation B S hS).baseChangeProjection (D.specQuotientTest B S hS J))
    D.quasicoherent_F D.quasicoherent_G D.u d hU hV J
    (val_app_mem_smul_top_of_hom B S hS D hZ₀ hV φ J hJ)
    (smul_chartRing_baseChangeSpace_eq_zero B S hS D J d.U)

/-- **The vanishing of `u_Z` over a chart of `X ×_S Z` lying above a chart of `X` carrying no
nonzero sections of `ℱ`.**  No ideal and no flatness enters: the map on sections over the chart of
`X` is already zero, so its extension of scalars is. -/
theorem modulePullback_map_val_app_specQuotient_eq_zero_of_subsingleton (J : Ideal Γ(S, ⊤))
    (d : ChartDiagram B S hS
      ((D.toModuleMapSituation B S hS).baseChangeSpace (D.specQuotientTest B S hS J)).1
      D.X.1 ((D.toModuleMapSituation B S hS).baseChangeProjection
        (D.specQuotientTest B S hS J)).hom)
    (hU : IsAffine ((SmallEtale.toOver B S hS
      ((D.toModuleMapSituation B S hS).baseChangeSpace
        (D.specQuotientTest B S hS J)).1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hV : IsAffine ((SmallEtale.toOver B S hS D.X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V))
    (h : Subsingleton (D.F.val.obj (op d.V))) :
    ((modulePullback B S hS ((D.toModuleMapSituation B S hS).baseChangeProjection
        (D.specQuotientTest B S hS J))).map D.u).val.app (op d.U) = 0 :=
  modulePullback_map_val_app_eq_zero_of_val_app_eq_zero B S hS
    ((D.toModuleMapSituation B S hS).baseChangeProjection (D.specQuotientTest B S hS J))
    D.quasicoherent_F D.quasicoherent_G D.u d hU hV
    (val_app_eq_zero_of_subsingleton B S hS D.u d.V h)

end ModuleMapFlatTargetSituation

end AlgebraicGeometry.Space

end

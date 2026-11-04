module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineChartSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
import all StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineChartSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.Topology.Dimension.KrullSupplement

/-!
# Chart systems of size-bounded systems

Criteria for an affine chart system of a cofiltered diagram of sheaves on the big fppf site to be
size-bounded, and the limit of a size-bounded chart system in the big fppf site.

## Main results

* `AffineChartSystem.sizeBound_of_lt_cof_ord`: a chart system indexed by a category with fewer
  objects and morphisms than the cofinality of the size cutoff is size-bounded.
* `AffineChartSystem.sizeBound_of_size_le`: a chart system with charts bounded by one cardinal
  below the cutoff, indexed by a category with fewer objects than the cutoff and countable morphism
  types, is size-bounded.
* `AffineChartSystem.limitBridgeOfSizeBound`: a size-bounded chart system has a limit in the big
  fppf site, representing the base change of the limit of the diagram.
* `ChartsBounded.sizeBound`: every chart system of a system with bounded charts is size-bounded.
-/

universe u

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The limit of a chart system -/

section LimitBridge

variable {I : Type u} [Category.{u} I] {i₀ : I}
  {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀}

namespace AffineChartSystem

variable {B S hS}

/-- A chart system indexed by a slice of an index category with fewer objects than the
cofinality of the site's size cutoff, and morphism types smaller than it, is size-bounded. -/
theorem sizeBound_of_lt_cof_ord (C : AffineChartSystem B S hS i₀ D U₀ f₀)
    (hSize : #I < B.cutoff.ord.cof) (hHomSize : ∀ i j : I, #(i ⟶ j) < B.cutoff.ord.cof) :
    BigFppfOver.SizeBound C.siteDiagram :=
  .of_lt_cof_ord _ (mk_over_lt B.aleph0_lt_cutoff_cof hSize hHomSize i₀)

/-- A chart system whose charts are bounded by one cardinal below the site's size cutoff,
indexed by a slice of an index category with countable morphism types and fewer objects than
the cutoff, is size-bounded. -/
theorem sizeBound_of_size_le (C : AffineChartSystem B S hS i₀ D U₀ f₀)
    (hSize : #I < B.cutoff) (hHomSize : ∀ i j : I, #(i ⟶ j) ≤ ℵ₀)
    {mu : Cardinal.{u}} (hmu : mu < B.cutoff)
    (hC : ∀ j, ((BigFppfOver.toScheme B S hS).obj (C.siteDiagram.obj j)).size ≤ mu) :
    BigFppfOver.SizeBound C.siteDiagram :=
  .of_size_le _ (mk_over_lt_of_mk_lt B.aleph0_lt_cutoff hSize hHomSize i₀) hmu hC

/-- A size-bounded chart system has a limit in the big fppf site of `S`, whose underlying scheme
is a limit of the underlying schemes of the charts and which represents the base change of
`limit.π D i₀` along `f₀` ([Stacks, Tag 07SF]). -/
noncomputable def limitBridgeOfSizeBound [IsCofiltered I] (C : AffineChartSystem B S hS i₀ D U₀ f₀)
    (hJ : BigFppfOver.SizeBound C.siteDiagram) :
    LimitBridge C := by
  classical
  have hWaff : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (C.siteDiagram.obj j)) :=
    C.isAffine_obj
  have _ : HasLimit C.siteDiagram :=
    BigFppfOver.hasLimit_of_isAffine_of_sizeBound C.siteDiagram hWaff hJ
  have _ := BigFppfOver.preservesLimit_toScheme_of_sizeBound C.siteDiagram hWaff hJ
  have hyoneda : IsLimit (yoneda.mapCone (limit.cone C.siteDiagram)) :=
    isLimitOfPreserves yoneda (limit.isLimit C.siteDiagram)
  have hpost : IsLimit ((Cone.postcompose C.iso.hom).obj
      (yoneda.mapCone (limit.cone C.siteDiagram))) :=
    (IsLimit.postcomposeHomEquiv C.iso (yoneda.mapCone (limit.cone C.siteDiagram))).symm
      hyoneda
  have hbase : IsLimit (stageBaseChangeCone B S hS i₀ D U₀ f₀) :=
    isLimitPullbackLimitOverPost B S hS D i₀ f₀
  exact
    { cone := limit.cone C.siteDiagram
      isLimit := limit.isLimit C.siteDiagram
      schemeIsLimit :=
        isLimitOfPreserves (BigFppfOver.toScheme B S hS) (limit.isLimit C.siteDiagram)
      iso := hpost.conePointUniqueUpToIso hbase
      iso_comp_π := fun j ↦ hpost.conePointUniqueUpToIso_hom_comp hbase j }

end AffineChartSystem

namespace ChartsBounded

variable {B S hS}

/-- Every chart system of a system with bounded charts is size-bounded. -/
theorem sizeBound (h : ChartsBounded B S hS D) {i₀ : I}
    {U₀ : BigAffineFppf B S hS}
    {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀}
    (C : AffineChartSystem B S hS i₀ D U₀ f₀) : BigFppfOver.SizeBound C.siteDiagram := by
  obtain ⟨mu, hmu, hb⟩ := h.bound i₀ U₀ f₀
  exact .of_size_le _ (h.mk_over_lt i₀) hmu
    fun j => hb j.left j.hom (C.siteDiagram.obj j) (C.iso.app j)

end ChartsBounded

end LimitBridge

end AlgebraicGeometry.Space

end

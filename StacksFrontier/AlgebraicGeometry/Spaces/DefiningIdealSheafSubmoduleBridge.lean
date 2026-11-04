module

public import StacksFrontier.AlgebraicGeometry.Cohomology.InjectiveQcoh.IdealPowerQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleQuasicoherentTransfer
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRestrictModuleFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Modules.IdealSheafDataSubmodule
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSheafPreimage

/-!
# The defining ideal sheaf of a closed subspace, as a submodule of the structure sheaf of a chart

Let `S` be a scheme contained in a big fppf site `B`, let `X` be an algebraic space over `S`, let
`Z ⊆ X` be a closed subspace and let `A` be an étale scheme chart of `X`.  The defining ideal sheaf
`𝓘_Z ⊆ 𝒪_X` of Stacks 03MB induces on `A` the ideal data
`AlgebraicGeometry.Space.idealSheafDataOfChart`, which is the kernel of pullback of regular
functions along the closed immersion of schemes `Z ×_X A ⟶ A`.  This file identifies the
submodules of `𝒪_A` that these ideal data cut out,
`AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule`, and computes their sections over the
affine opens of `A`.

## Main results

* `AlgebraicGeometry.SmallEtale.preservesLimits_restrictModule`: restriction of modules from the
  small étale site to the small Zariski site of a scheme preserves limits.
* `AlgebraicGeometry.Space.unitSubmodule_idealSheafDataOfChart_obj_affine`: the sections, over an
  affine open `V` of the chart scheme, of the submodule of `𝒪_A` cut out by the chart ideal data
  of a sheaf of ideals `N` of `𝒪_X` are the sections of `N` over the étale chart cut out by `V`,
  transported along `AlgebraicGeometry.Scheme.Opens.topIso`.
* `AlgebraicGeometry.Space.unitSubmodule_ker_rep_snd`: the submodule of `𝒪_A` cut out by the
  kernel of the base change `Z ×_X A ⟶ A` is the one cut out by the chart ideal data of the
  defining ideal sheaf of `Z`.
* `AlgebraicGeometry.Space.unitSubmodule_ker_rep_snd_obj_affine`: the same, read on sections over
  an affine open, where the right-hand side is `AlgebraicGeometry.Space.definingIdealAt`.
* `AlgebraicGeometry.Space.eq_unitSubmodule_idealSheafDataOfChart_of_obj_affine`: a submodule of
  `𝒪_A` with the same sections over every affine open as the one cut out by the chart ideal data
  is that submodule.

## Implementation notes

`AlgebraicGeometry.Space.definingIdealSheaf` and the submodules of this file are submodules of
the unit modules of different sites — the small étale site of `X` and the small Zariski site of
the chart scheme — and are compared on sections, chart by chart and affine open by affine open.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 01R8](https://stacks.math.columbia.edu/tag/01R8)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

section Counit

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Restriction of modules from the small étale site to the small Zariski site of a scheme
preserves limits. -/
instance preservesLimits_restrictModule :
    Limits.PreservesLimitsOfSize.{u, u} (restrictModule B S hS) :=
  (associatedModuleAdjunction B S hS).rightAdjoint_preservesLimits

end Counit

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- For a sheaf of ideals `N ⊆ 𝒪_X` cartesian on affine charts and
an étale scheme chart `A` of `X`, the sections over an affine open `V` of the chart scheme of the
submodule `AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule` of the chart ideal data are the
sections of `N` over the étale chart `AlgebraicGeometry.Space.openChart` cut out by `V`,
transported along `AlgebraicGeometry.Scheme.Opens.topIso`. -/
theorem unitSubmodule_idealSheafDataOfChart_obj_affine
    (X : AlgebraicSpaces B S hS)
    (N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (hN : IsCartesianOnAffineCharts N.toSheafOfModules)
    (A : SmallEtale B S hS X.1) (V : (chartScheme A).affineOpens) :
    (idealSheafDataOfChart B S hS X N hN A).unitSubmodule.toSubmodule.obj (op V.1) =
      Ideal.map (openChartTopRingHom B S hS X A V.1)
        (N.obj (op (openChart B S hS X.1 A V.1))) :=
  Scheme.IdealSheafData.unitSubmodule_obj_affine _ V

/-- The submodule of `𝒪_A` cut out by the kernel of pullback of regular functions along the closed
immersion of schemes `Z ×_X A ⟶ A` is the submodule cut out by the sheaf of ideals that the
defining ideal sheaf `𝓘_Z` of Stacks 03MB induces on the chart `A`. -/
theorem unitSubmodule_ker_rep_snd
    (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1)
    (A : SmallEtale B S hS X.1) :
    (((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd A.1.hom)).ker).unitSubmodule =
      (idealSheafDataOfChart B S hS X (definingIdealSheaf B S hS X Z)
        (definingIdealSheaf_isCartesianOnAffineCharts B S hS X Z) A).unitSubmodule :=
  congrArg Scheme.IdealSheafData.unitSubmodule
    (ker_rep_snd_eq_idealSheafDataOfChart B S hS X Z A)

/-- The sections over an affine open `V` of the chart scheme of the submodule of
`𝒪_A` cut out by the kernel of the base change `Z ×_X A ⟶ A` are the defining ideal
`AlgebraicGeometry.Space.definingIdealAt` of `Z` at the étale chart cut out by `V`, transported
along `AlgebraicGeometry.Scheme.Opens.topIso`. -/
theorem unitSubmodule_ker_rep_snd_obj_affine
    (X : AlgebraicSpaces B S hS) (Z : ClosedSubspaces B S hS X.1)
    (A : SmallEtale B S hS X.1) (V : (chartScheme A).affineOpens) :
    (((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd A.1.hom)).ker).unitSubmodule.toSubmodule.obj
        (op V.1) =
      Ideal.map (openChartTopRingHom B S hS X A V.1)
        (definingIdealAt B S hS X Z (op (openChart B S hS X.1 A V.1))) := by
  rw [unitSubmodule_ker_rep_snd B S hS X Z A]
  exact unitSubmodule_idealSheafDataOfChart_obj_affine B S hS X
    (definingIdealSheaf B S hS X Z)
    (definingIdealSheaf_isCartesianOnAffineCharts B S hS X Z) A V

/-- Any submodule of the structure sheaf of the chart scheme whose sections over every
affine open `V` are the sections of `N` over the étale chart cut out by `V` is
`AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule` of the chart ideal data. -/
theorem eq_unitSubmodule_idealSheafDataOfChart_of_obj_affine
    (X : AlgebraicSpaces B S hS)
    (N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (hN : IsCartesianOnAffineCharts N.toSheafOfModules)
    (A : SmallEtale B S hS X.1)
    (P : (SheafOfModules.unit (chartScheme A).ringCatSheaf).Submodule)
    (h : ∀ V : (chartScheme A).affineOpens,
      P.toSubmodule.obj (op V.1) =
        Ideal.map (openChartTopRingHom B S hS X A V.1)
          (N.obj (op (openChart B S hS X.1 A V.1)))) :
    P = (idealSheafDataOfChart B S hS X N hN A).unitSubmodule :=
  Scheme.Modules.submodule_eq_of_obj_affineOpens_eq P _ fun V =>
    (h V).trans
      (unitSubmodule_idealSheafDataOfChart_obj_affine B S hS X N hN A V).symm

end AlgebraicGeometry.Space

end

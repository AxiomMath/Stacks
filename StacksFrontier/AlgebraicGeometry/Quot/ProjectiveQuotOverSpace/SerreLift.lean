/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.SerreQuotient
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotOverSpace.BaseReading
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.PresentationCokernelFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFromSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeModuleRelativeAmpleTransfer

/-!
# The Serre surjection of Stacks 0DPB, on `B × ℙⁿ_ℤ`

Let `F/X/B` be a Quot situation with a projective frame `X = B × ℙⁿ_ℤ`, with `B ≅ h_W` for an
affine scheme `W`, and `F` of finite type.  Read on `ℙⁿ_W`, `F` is a quasi-coherent module of
finite type `G`, so by Stacks 01Q3 (clause (7), for the ample `𝒪(1)`) it is a quotient of
`𝒪(-d)^{⊕ r}`.  Reading this surjection back on `X` (Stacks 03DX) gives a surjection onto `F`
from the module of `X` corresponding to `𝒪(-d)^{⊕ r}`: the surjection
`𝒪_X^{⊕ r} ⟶ F ⊗ L^{⊗ d}` of the proof of Stacks 0DPB, untwisted.

## Main results

* `AlgebraicGeometry.ProjectiveQuotOverSpace.isFiniteType_baseReading`: the reading on `ℙⁿ_W` of a
  quasi-coherent module of finite type is of finite type.
* `AlgebraicGeometry.ProjectiveQuotOverSpace.exists_epi_baseSpaceIso_inv_pullback`: the
  surjection onto `F`.

## References

* [Stacks Project, Tag 0DPB](https://stacks.math.columbia.edu/tag/0DPB)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.ProjectiveQuotOverSpace

open ProjectiveQuot

universe u

variable {B : BigFppfSite.{u}} {n : ℕ}

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

/-- **The Zariski reading of a quasi-coherent module of finite type on a represented algebraic
space is of finite type.** -/
theorem isFiniteType_representedZariskiModule (V : BigFppfOver B integerBase B.contains_integerBase)
    (N : Space.Modules.{u, u} B integerBase B.contains_integerBase (yoneda.obj V)
      (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase V))
    (hqc : N.IsQuasicoherentOnSite) (hft : SheafOfModules.IsFiniteTypeOnSite N) :
    (Space.representedZariskiModule B integerBase B.contains_integerBase V N).IsFiniteType :=
  Stacks.SheafOfModules.Intrinsic.isFiniteType_of_iso
    (Space.restrictToChartIsoRestrictToChartScheme B integerBase B.contains_integerBase (G := N)
        (U := Space.idEtaleChart B integerBase B.contains_integerBase V) ≪≫
      Space.restrictToChartSchemeIdEtaleChartIso B integerBase B.contains_integerBase V N)
    (Space.isFiniteType_restrictToChart B integerBase B.contains_integerBase (schemeSpace V) N
      hqc hft (Space.idEtaleChart B integerBase B.contains_integerBase V))

variable {D : Space.QuotSituation B integerBase B.contains_integerBase} (E : ProjectiveFrame B n D)
  {W : BigFppfOver B integerBase B.contains_integerBase} (φ : schemeSpace W ≅ D.Y)

/-- **The reading of a quasi-coherent module of finite type on `X` is of finite type** on
`ℙⁿ_W`. -/
theorem isFiniteType_baseReading
    (A : Space.Modules.{u, u} B integerBase B.contains_integerBase D.X.1 D.X.2)
    (hA : A.IsQuasicoherentOnSite) (hft : SheafOfModules.IsFiniteTypeOnSite A) :
    ((baseReading E φ).obj A).IsFiniteType :=
  isFiniteType_representedZariskiModule (projectiveSite B n W) _
    (Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B integerBase
      B.contains_integerBase _ A hA)
    (Space.isFiniteTypeOnSite_modulePullback B integerBase B.contains_integerBase _ A hft)

/-- **The Serre surjection of the proof of Stacks 0DPB, read on `X`.**  Over an affine `W ≅ B`, a
quasi-coherent module `F` of finite type on `X = B × ℙⁿ_ℤ` is a quotient of the module `F₀` on
`h_{ℙⁿ_W}` read on `ℙⁿ_W` as `𝒪(-d)^{⊕ r}`, transported to `X`. -/
theorem exists_epi_baseSpaceIso_inv_pullback [IsAffine ((𝒯).obj W)]
    (hft : SheafOfModules.IsFiniteTypeOnSite D.F) :
    ∃ (d r : ℕ) (_ : 1 ≤ r)
      (F₀ : Space.Modules.{u, u} B integerBase B.contains_integerBase
        (yoneda.obj (projectiveSite B n W))
        (isAlgebraicSpace_yoneda B integerBase B.contains_integerBase _))
      (_ : F₀.IsQuasicoherentOnSite)
      (_ : ((Space.representedSmallEtaleModuleEquivalence B integerBase B.contains_integerBase
          (projectiveSite B n W)).inverse ⋙
          _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((𝒯).obj (projectiveSite B n W)) (projectiveSite B n W).left.property).obj F₀ ≅
        twist (-(d : ℤ)) (freeModule n r ((𝒯).obj W)))
      (q : (Space.modulePullback B integerBase B.contains_integerBase
          ((baseSpaceIso E φ).inv : D.X ⟶
            schemeSpace (projectiveSite B n W))).obj F₀ ⟶ D.F),
      Epi q := by
  obtain ⟨d, r, hr, p, hp⟩ := exists_epi_twist_freeModule ((baseReading E φ).obj D.F)
    (isQuasicoherent_baseReading_F E φ)
    (isFiniteType_baseReading E φ D.F D.quasicoherent hft)
  let M : ((𝒯).obj (projectiveSite B n W)).Modules := twist (-(d : ℤ)) (freeModule n r ((𝒯).obj W))
  have : M.IsFinitePresentation :=
    isFinitePresentation_twist _ _ (isFinitePresentation_freeModule _)
  have hMqc : M.IsQuasicoherent := Stacks.Modules.isQuasicoherent_of_isFinitePresentation _
  have := isIso_zariskiAdjunction_unit_app (projectiveSite B n W) M hMqc
  let adj := (zariskiAdjunction B (projectiveSite B n W)).comp
    (isoReadingEquivalence (baseSpaceIso E φ)).symm.toAdjunction
  have hPE : (baseLift E φ).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (F := baseLift E φ) adj
  have hep : Epi ((baseLift E φ).map p) := @Functor.map_epi _ _ _ _ (baseLift E φ) hPE _ _ p hp
  refine ⟨d, r, hr, _, Space.isQuasicoherentOnSite_associatedModule_schemeSpace _ M hMqc,
    (asIso ((zariskiAdjunction B (projectiveSite B n W)).unit.app M)).symm,
    baseLiftMap E φ p, ?_⟩
  exact @epi_comp _ _ _ _ _ ((baseLift E φ).map p) hep
    (baseLiftReadingIso E φ D.F D.quasicoherent).hom
    (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom _))

end AlgebraicGeometry.ProjectiveQuotOverSpace

end

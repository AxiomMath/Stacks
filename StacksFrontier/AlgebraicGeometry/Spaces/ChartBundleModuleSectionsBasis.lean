module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsSchemeReading
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.VectorBundle.SymmetricAlgebraAffineSections
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.FreeModuleOfSectionsBasis

/-!
# A trivialization of a module over an affine étale chart, read on the scheme of the chart

Let `X` be an algebraic space, `ℰ` a quasi-coherent `𝒪_X`-module and `V` an affine étale chart of
`X` over which `ℰ` is free, `e : ℰ|_V ≅ 𝒪_V^{⊕ ι}` with `ι` finite. The basis of `ℰ(V)` given by
`e` (`AlgebraicGeometry.Space.SymAlgSections.sectionsBasis`) is carried by the identification
`θ : ℰ(V) ≃ Γ(V, ℰ|_V)` of the sections over the chart with the global sections of the reading of
`ℰ` on the scheme of the chart (`AlgebraicGeometry.Space.chartSectionsReadingEquiv`) to a basis
of `Γ(V, ℰ|_V)`, hence to an isomorphism `𝒪_V^{⊕ ι} ≅ ℰ|_V` of modules on the scheme of `V`.

## Main definitions

* `AlgebraicGeometry.Space.chartBundleModuleSectionsBasis`: the basis of `Γ(V, ℰ|_V)`.
* `AlgebraicGeometry.Space.chartBundleModuleFreeIso`: the isomorphism `𝒪_V^{⊕ ι} ≅ ℰ|_V`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (E : Modules.{u, u} B S hS X.1 X.2) (V : SmallEtale B S hS X.1)

/-- The identification `θ : ℰ(V) ≃ Γ(V, ℰ|_V)`, as a linear equivalence over the functions on the
chart. -/
def chartSectionsReadingLinearEquiv :
    E.val.obj (op V) ≃ₗ[Γ(chartScheme V, ⊤)] Γ(schemeReading E (chartToSpace B S hS X V), ⊤) :=
  { chartSectionsReadingEquiv E V with
    map_smul' := chartSectionsReadingEquiv_smul E V }

variable {ι : Type u} [DecidableEq ι] [Finite ι]
  (e : (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E).over V ≅
    SheafOfModules.free (R := (structureRingSheaf B S hS X).over V) ι)

/-- The coordinates of a section of `ℰ` over `V` in the trivialization, as functions on the
scheme of the chart. -/
def chartSchemeCoords (m : E.val.obj (op V)) : ι → Γ(chartScheme V, ⊤) :=
  SymAlgSections.sectionsEquivFun B S hS X
    (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E) V e m

/-- The coordinates equivalence of `ℰ(V)` provided by the trivialization `e`. -/
private abbrev sectionsEquivFun' :=
  SymAlgSections.sectionsEquivFun B S hS X
    (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E) V e

/-- The coordinates of `c • m` are `c` times the coordinates of `m`. -/
theorem chartSchemeCoords_smul (c : Γ(chartScheme V, ⊤)) (m : E.val.obj (op V)) :
    chartSchemeCoords E V e (c • m) = c • chartSchemeCoords E V e m :=
  (sectionsEquivFun' E V e).map_smul c m

/-- The section of `ℰ` over `V` with prescribed coordinates. -/
def chartSchemeOfCoords (c : ι → Γ(chartScheme V, ⊤)) : E.val.obj (op V) :=
  (SymAlgSections.sectionsEquivFun B S hS X
    (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E) V e).symm c

/-- The coordinates of the section with coordinates `c` are `c`. -/
theorem chartSchemeCoords_ofCoords (c : ι → Γ(chartScheme V, ⊤)) :
    chartSchemeCoords E V e (chartSchemeOfCoords E V e c) = c :=
  (sectionsEquivFun' E V e).apply_symm_apply c

/-- A section of `ℰ` over `V` is the section with its own coordinates. -/
theorem chartSchemeOfCoords_coords (m : E.val.obj (op V)) :
    chartSchemeOfCoords E V e (chartSchemeCoords E V e m) = m :=
  (sectionsEquivFun' E V e).symm_apply_apply m

/-- The coordinates of `ℰ(V)`, as a linear equivalence over the functions on the chart. -/
def chartSchemeCoordsEquiv :
    E.val.obj (op V) ≃ₗ[Γ(chartScheme V, ⊤)] (ι → Γ(chartScheme V, ⊤)) where
  toFun := chartSchemeCoords E V e
  invFun := chartSchemeOfCoords E V e
  map_add' m m' := (SymAlgSections.sectionsEquivFun B S hS X
    (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E) V e).map_add m m'
  map_smul' := chartSchemeCoords_smul E V e
  left_inv := chartSchemeOfCoords_coords E V e
  right_inv := chartSchemeCoords_ofCoords E V e

/-- **The basis of `Γ(V, ℰ|_V)` of a trivialization of `ℰ` over the chart `V`.** -/
def chartBundleModuleSectionsBasis :
    Module.Basis ι Γ(chartScheme V, ⊤) Γ(chartBundleModule E V, ⊤) :=
  Module.Basis.ofEquivFun ((chartSectionsReadingLinearEquiv E V).symm.trans
    (chartSchemeCoordsEquiv E V e))

/-- The `j`-th vector of the basis is the reading of the `j`-th basis section of `ℰ(V)`. -/
theorem chartBundleModuleSectionsBasis_apply (j : ι) :
    chartBundleModuleSectionsBasis E V e j =
      chartSectionsReadingEquiv E V (SymAlgSections.sectionsBasis B S hS X
        (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E) V e j) := by
  rw [chartBundleModuleSectionsBasis, Module.Basis.coe_ofEquivFun]
  refine congrArg (chartSectionsReadingEquiv E V) ?_
  rw [SymAlgSections.sectionsBasis, Module.Basis.coe_ofEquivFun]
  rfl

/-- **The trivialization of `ℰ|_V` on the scheme of an affine chart `V`** given by a
trivialization `e` of `ℰ` over `V`: its `j`-th basis vector is the reading of the `j`-th basis
section of `ℰ(V)`. -/
def chartBundleModuleFreeIso [IsAffine (chartScheme V)] (hE : E.IsQuasicoherentOnSite) :
    Stacks.RelativeProj.freeModule (T := chartScheme V) ι ≅ chartBundleModule E V :=
  haveI := Fintype.ofFinite ι
  haveI := @isQuasicoherent_chartBundleModule B S hS X E hE V
  Stacks.RelativeProj.freeIsoOfBasis _ (chartBundleModuleSectionsBasis E V e)

/-- The `j`-th basis vector of `chartBundleModuleFreeIso` sends `1` to the reading of the `j`-th
basis section of `ℰ(V)`. -/
theorem basisMap_chartBundleModuleFreeIso_app_one [IsAffine (chartScheme V)]
    (hE : E.IsQuasicoherentOnSite) (j : ι) :
    Scheme.Modules.Hom.app (Stacks.RelativeProj.UnitSplitting.basisMap
        (chartBundleModuleFreeIso E V e hE) j) ⊤ (1 : Γ(chartScheme V, ⊤)) =
      chartSectionsReadingEquiv E V (SymAlgSections.sectionsBasis B S hS X
        (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E) V e j) :=
  have := Fintype.ofFinite ι
  have := @isQuasicoherent_chartBundleModule B S hS X E hE V
  (Stacks.RelativeProj.basisMap_freeIsoOfBasis_app_one _
    (chartBundleModuleSectionsBasis E V e) j).trans
    (chartBundleModuleSectionsBasis_apply E V e j)

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFiniteTypeModuleLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedLocallyFiniteCharts
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.Basic

/-!
# The chartwise readings of quasi-coherence and of finite type, from the readings on the site

A module on an algebraic space which is quasi-coherent, respectively quasi-coherent of finite
type, on the small étale site (`SheafOfModules.IsQuasicoherentOnSite`,
`SheafOfModules.IsFiniteTypeOnSite`) is quasi-coherent, respectively of finite type, on charts
(`AlgebraicGeometry.Space.IsQuasicoherentOnCharts`,
`AlgebraicGeometry.Space.IsFiniteTypeOnCharts`): its restriction
`AlgebraicGeometry.Space.restrictToChart` to every étale scheme chart is so. For such a module,
the relative flat locus of a morphism locally of finite presentation is open.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnCharts_of_isQuasicoherentOnSite`: a module
  quasi-coherent on the small étale site is quasi-coherent on charts.
* `AlgebraicGeometry.Space.moduleFinite_sections_chartRestrictionSheaf`: the sections of the
  chart restriction of a quasi-coherent module of finite type over an affine Zariski open of the
  chart's scheme form a finite module over the functions on that open.
* `AlgebraicGeometry.Space.isFiniteType_restrictToChart` and
  `AlgebraicGeometry.Space.isFiniteTypeOnCharts_of_isFiniteTypeOnSite`: a quasi-coherent module
  of finite type on the small étale site is of finite type on charts.
* `AlgebraicGeometry.Space.isOpen_flatLocus_of_isFiniteTypeOnSite` and
  `AlgebraicGeometry.Space.isOpenSubspace_flatLocusOpenSubspace_of_isFiniteTypeOnSite`: for a
  module quasi-coherent of finite type on the small étale site, the relative flat locus is open
  and cuts out an open subspace of the source.
* `AlgebraicGeometry.Space.isOpen_flatLocus_of_isSurjectiveChart` and
  `AlgebraicGeometry.Space.isOpenSubspace_flatLocusOpenSubspace_of_isSurjectiveChart`: the same
  two, with the local finiteness of the weakly associated points of the target read on one
  surjective étale scheme chart.  This is Stacks 0DLR at its erratum: with condition (3) read on
  the point space `|Y|` the statement is false
  (`Stacks.Examples.NonOpenFlatLocusWeaklyAssociated.exists_not_isOpen_flatLocus`).

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 0DLR](https://stacks.math.columbia.edu/tag/0DLR)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- A module quasi-coherent on the small étale site is quasi-coherent on charts. -/
theorem isQuasicoherentOnCharts_of_isQuasicoherentOnSite (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) : IsQuasicoherentOnCharts B S hS X.2 M :=
  fun A => isQuasicoherent_restrictToChart B S hS X M hM A

/-- For a quasi-coherent module of finite type on the small étale site, the sections of its chart
restriction over an affine Zariski open of the chart's scheme form a finite module over the
functions on that open. -/
theorem moduleFinite_sections_chartRestrictionSheaf (M : Modules.{u, u} B S hS X.1 X.2)
    (hqc : M.IsQuasicoherentOnSite) (hft : SheafOfModules.IsFiniteTypeOnSite M)
    (A : SmallEtale B S hS X.1) (V : (chartScheme A).affineOpens) :
    Module.Finite Γ(chartScheme A, V.1) Γ(chartRestrictionSheaf B S hS X M A, V.1) := by
  let : Module (Γ(↑(V.1), ⊤) : Type u)
      (M.val.obj (Opposite.op ((chartOpens B S hS A).obj V.1)) : Type u) :=
    moduleChartSections B S hS X M ((chartOpens B S hS A).obj V.1)
  have : Module.Finite (Γ(↑(V.1), ⊤) : Type u)
      (M.val.obj (Opposite.op ((chartOpens B S hS A).obj V.1)) : Type u) :=
    module_finite_sections_of_isFiniteTypeOnSite M hqc hft
      ((chartOpens B S hS A).obj V.1) V.2
  exact Module.Finite.of_surjective
    (f := ({ toFun := fun m => ULift.up m
             map_add' := fun _ _ => rfl
             map_smul' := fun r m => congrArg ULift.up (congrArg (fun y => y • m)
               (ConcreteCategory.congr_hom V.1.topIso.hom_inv_id r).symm) } :
      (M.val.obj (Opposite.op ((chartOpens B S hS A).obj V.1)) : Type u) →ₛₗ[(V.1.topIso.hom).hom]
        (Γ(chartRestrictionSheaf B S hS X M A, V.1) : Type u))) fun y ↦ ⟨y.down, rfl⟩

/-- The restriction to an étale scheme chart of a quasi-coherent module of finite type on the small
étale site is of finite type on the chart's scheme. -/
theorem isFiniteType_restrictToChart (M : Modules.{u, u} B S hS X.1 X.2)
    (hqc : M.IsQuasicoherentOnSite) (hft : SheafOfModules.IsFiniteTypeOnSite M)
    (A : SmallEtale B S hS X.1) :
    (restrictToChart B S hS X.2 M A).IsFiniteType := by
  have : (chartRestrictionSheaf B S hS X M A).IsQuasicoherent :=
    isQuasicoherent_chartRestrictionSheaf B S hS X M hqc A
  have : (chartRestrictionSheaf B S hS X M A).IsFiniteType :=
    Stacks.AlgebraicGeometry.TopDegreeFiniteType.isFiniteType_of_forall_moduleFinite_sections
      (chartRestrictionSheaf B S hS X M A)
      (moduleFinite_sections_chartRestrictionSheaf B S hS X M hqc hft A)
  exact Stacks.SheafOfModules.isFiniteType_of_iso
    (restrictToChartIsoChartRestrictionSheaf B S hS X M A).symm

/-- A quasi-coherent module of finite type on the small étale site is of finite type on charts. -/
theorem isFiniteTypeOnCharts_of_isFiniteTypeOnSite (M : Modules.{u, u} B S hS X.1 X.2)
    (hqc : M.IsQuasicoherentOnSite) (hft : SheafOfModules.IsFiniteTypeOnSite M) :
    IsFiniteTypeOnCharts B S hS X.2 M :=
  fun A => isFiniteType_restrictToChart B S hS X M hqc hft A

/-! ### Openness of the relative flat locus -/

section FlatLocus

attribute [local instance] pointTopology

variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- For a morphism `f : X ⟶ Y` of algebraic spaces locally of finite presentation and a module
which is quasi-coherent and of finite type on the small étale site of `X`, the relative flat locus
is open in the point space of `X`, provided the weakly associated points of `Y` are locally finite
on charts. -/
theorem isOpen_flatLocus_of_isFiniteTypeOnSite (f : X.1 ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (hf : IsLocallyOfFinitePresentation B S hS f)
    (hqc : F.IsQuasicoherentOnSite) (hft : SheafOfModules.IsFiniteTypeOnSite F)
    (hwa : HasLocallyFiniteWeaklyAssociatedPointsOnCharts B S hS Y) :
    IsOpen (flatLocus B S hS X.2 f F) :=
  isOpen_flatLocus B S hS X.2 f F hf
    (isQuasicoherentOnCharts_of_isQuasicoherentOnSite B S hS X F hqc)
    (isFiniteTypeOnCharts_of_isFiniteTypeOnSite B S hS X F hqc hft) hwa

/-- For a morphism `f : X ⟶ Y` of algebraic spaces locally of finite presentation and a module
which is quasi-coherent and of finite type on the small étale site of `X`, the relative flat locus
cuts out an open subspace of `X`, provided the weakly associated points of `Y` are locally finite
on charts. -/
theorem isOpenSubspace_flatLocusOpenSubspace_of_isFiniteTypeOnSite (f : X.1 ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (hf : IsLocallyOfFinitePresentation B S hS f)
    (hqc : F.IsQuasicoherentOnSite) (hft : SheafOfModules.IsFiniteTypeOnSite F)
    (hwa : HasLocallyFiniteWeaklyAssociatedPointsOnCharts B S hS Y) :
    IsOpenSubspace B S hS (flatLocusOpenSubspace B S hS X.2 f F) :=
  isOpenSubspace_openSubspaceOfPoints B S hS X.2 _
    (isOpen_flatLocus_of_isFiniteTypeOnSite B S hS X f F hf hqc hft hwa)

/-- For a morphism `f : X ⟶ Y` of algebraic spaces locally of finite presentation and a module
which is quasi-coherent and of finite type on the small étale site of `X`, the relative flat locus
is open in the point space of `X` as soon as the weakly associated points of the scheme of one
surjective étale chart of `Y` are locally finite there.

Condition (3) of the source asks that the weakly associated points of `Y` be locally finite in
`|Y|`; the source's proof reads it as local finiteness on a surjective étale scheme chart, which can
be stronger when `Y` is not decent.  With (3) on `|Y|` the statement is false:
`Stacks.Examples.NonOpenFlatLocusWeaklyAssociated.exists_not_isOpen_flatLocus`
exhibits a target with two weakly associated points over which the flat locus is not open.  The
chart reading is therefore the correction of the statement, recorded in `errata.md`. -/
@[stacks 0DLR "openness of the locus U, at the Stacks erratum: condition (3) of the source, local \
finiteness of the weakly associated points of Y in |Y|, is replaced by local finiteness of the \
weakly associated points of the scheme of one surjective etale chart of Y, which is how the \
source's proof reads it and which implies (3). The tag as published, with (3) on |Y|, is false, \
refuted (with a target which is not decent) by the theorem \
Stacks.Examples.NonOpenFlatLocusWeaklyAssociated.exists_not_isOpen_flatLocus of \
StacksFrontier/Examples/Flatness/NonOpenFlatLocusWeaklyAssociated.lean. Conditions (1) and (2) are \
the source's: f locally of finite presentation, the module quasi-coherent of finite type on the \
small etale site"]
theorem isOpen_flatLocus_of_isSurjectiveChart (f : X.1 ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (hf : IsLocallyOfFinitePresentation B S hS f)
    (hqc : F.IsQuasicoherentOnSite) (hft : SheafOfModules.IsFiniteTypeOnSite F)
    (V₀ : SmallEtale B S hS Y) (hV₀ : IsSurjectiveChart B S hS V₀)
    (h₀ : ∀ v : etaleChartScheme B S hS V₀,
      ∃ W : (etaleChartScheme B S hS V₀).Opens, v ∈ W ∧
        (Stacks.Divisors.schemeWeaklyAssociatedPoints (etaleChartScheme B S hS V₀) ∩
          (W : Set (etaleChartScheme B S hS V₀))).Finite) :
    IsOpen (flatLocus B S hS X.2 f F) :=
  isOpen_flatLocus_of_isFiniteTypeOnSite B S hS X f F hf hqc hft
    (hasLocallyFiniteWeaklyAssociatedPointsOnCharts_of_isSurjectiveChart B S hS V₀ hV₀ h₀)

/-- For a morphism `f : X ⟶ Y` of algebraic spaces locally of finite presentation and a module
which is quasi-coherent and of finite type on the small étale site of `X`, the relative flat locus
cuts out an open subspace of `X` as soon as the weakly associated points of the scheme of one
surjective étale chart of `Y` are locally finite there.

Condition (3) of the source asks that the weakly associated points of `Y` be locally finite in
`|Y|`; the source's proof reads it as local finiteness on a surjective étale scheme chart, which can
be stronger when `Y` is not decent.  With (3) on `|Y|` the statement is false:
`Stacks.Examples.NonOpenFlatLocusWeaklyAssociated.exists_not_isOpen_flatLocus`
exhibits a target with two weakly associated points over which the flat locus is not open.  The
chart reading is therefore the correction of the statement, recorded in `errata.md`. -/
@[stacks 0DLR "the locus U cuts out an open subspace of X in the sense of Tag 03BZ, at the Stacks \
erratum: condition (3) of the source, local finiteness of the weakly associated points of Y in \
|Y|, is replaced by local finiteness of the weakly associated points of the scheme of one \
surjective etale chart of Y, which is how the source's proof reads it and which implies (3). The \
tag as published, with (3) on |Y|, is false, refuted (with a target which is not decent) by the \
theorem \
Stacks.Examples.NonOpenFlatLocusWeaklyAssociated.exists_not_isOpen_flatLocus \
of StacksFrontier/Examples/Flatness/NonOpenFlatLocusWeaklyAssociated.lean"]
theorem isOpenSubspace_flatLocusOpenSubspace_of_isSurjectiveChart (f : X.1 ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (hf : IsLocallyOfFinitePresentation B S hS f)
    (hqc : F.IsQuasicoherentOnSite) (hft : SheafOfModules.IsFiniteTypeOnSite F)
    (V₀ : SmallEtale B S hS Y) (hV₀ : IsSurjectiveChart B S hS V₀)
    (h₀ : ∀ v : etaleChartScheme B S hS V₀,
      ∃ W : (etaleChartScheme B S hS V₀).Opens, v ∈ W ∧
        (Stacks.Divisors.schemeWeaklyAssociatedPoints (etaleChartScheme B S hS V₀) ∩
          (W : Set (etaleChartScheme B S hS V₀))).Finite) :
    IsOpenSubspace B S hS (flatLocusOpenSubspace B S hS X.2 f F) :=
  isOpenSubspace_flatLocusOpenSubspace_of_isFiniteTypeOnSite B S hS X f F hf hqc hft
    (hasLocallyFiniteWeaklyAssociatedPointsOnCharts_of_isSurjectiveChart B S hS V₀ hV₀ h₀)

end FlatLocus

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.Algebra.Module.FinitePresentation.Transport
public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationFromAffine
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FinitePresentationDegreeMinusOne
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleLocusOpen

/-!
# The chartwise reading of finite presentation, from the reading on the site

Finite presentation of a module on an algebraic space is recorded in this tree twice: on the
small étale site, as `SheafOfModules.IsFinitePresentationOnSite`, the categorical form of
Stacks 03DL (7); and *chartwise*, as `AlgebraicGeometry.Space.IsFinitePresentationOnCharts`, a
property of the restriction `AlgebraicGeometry.Space.restrictToChart` of the module to every
étale scheme chart.  The chartwise form is what the scheme-level results consume, and nothing in
the tree passed from the site form to it.  This file supplies that passage, for a quasi-coherent
module and at **every** étale scheme chart.

## Main results

* `AlgebraicGeometry.Space.moduleFinitePresentation_sections_chartRestrictionSheaf`: the sections
  of the chart restriction over an affine Zariski open of the chart's scheme form a finitely
  presented module over the functions on that open.
* `AlgebraicGeometry.Space.isFinitePresentation_restrictToChart`: the restriction of a
  quasi-coherent module of finite presentation on the small étale site to an étale scheme chart
  is **of finite presentation** on the Zariski site of that chart's scheme.
* `AlgebraicGeometry.Space.isFinitePresentationOnCharts_of_isFinitePresentationOnSite`: the same,
  packaged as the chartwise predicate.

## Implementation notes

The passage is not formal: the chartwise condition is Zariski-local on the chart's scheme while
finite presentation on the site is local in the étale topology.  It is assembled from three
library statements, and it avoids any étale-to-Zariski descent of the *sheaf* condition — in
particular it does not need the half of Stacks 08HD which the implementation notes of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleFiniteType.lean` record as
open.  This is the route that
`AlgebraicGeometry.Space.isFiniteType_restrictToChart` takes for finite type:

* the chart restriction needs no sheafification
  (`AlgebraicGeometry.Space.restrictToChartIsoChartRestrictionSheaf`) and its sections over a
  Zariski open `V` of the chart's scheme are the sections of the module over the étale chart
  that `V` cuts out (`AlgebraicGeometry.Space.chartRestrictionSheaf_obj`, which holds by `rfl`),
  the scalars being carried along `AlgebraicGeometry.Scheme.Opens.topIso`;
* for `V` affine that étale chart is affine, and the sections of a quasi-coherent module of
  finite presentation over an affine étale chart form a finitely presented module over the
  functions on it, which is
  `AlgebraicGeometry.Space.module_finitePresentation_sections_of_isFinitePresentationOnSite` —
  this is where the faithfully flat descent happens, and it is the one step with content;
* a quasi-coherent module on a scheme whose sections over the members of an affine open covering
  are finitely presented is of finite presentation, which is (5) ⇒ (3) of Stacks 01XZ,
  `Stacks.AlgebraicGeometry.FinitePresentationLocal.isFinitePresentation_of_affineCover`.

**Why the change of scalars needs an isomorphism and not just a surjection.**  For finite type
the corresponding step transports `Module.Finite` across the semilinear surjection `ULift.up`,
and restriction of scalars along a surjective ring map preserves `Module.Finite`.  It does *not*
preserve `Module.FinitePresentation`, which also needs the kernel of the surjection to be
finitely generated.  What is used here instead is that the comparison
`AlgebraicGeometry.Space.chartRestrictionRingHom` is, at a Zariski open `V`, the inverse of
`AlgebraicGeometry.Scheme.Opens.topIso` on the nose, hence an *isomorphism*, so
`finitePresentation_of_ringEquiv` of
`StacksFrontier/Algebra/Module/FinitePresentation/Transport.lean` applies to the `topIso`-semilinear
additive equivalence `ULift.up`.

The covering of the chart's scheme is the family of all of its affine opens,
`AlgebraicGeometry.iSup_affineOpens_eq_top`; no quasi-compactness is needed, the criterion of
Stacks 01XZ taking an arbitrary affine open covering.

No declaration here carries a `stacks` tag.  This is the chartwise reading of a hypothesis — an
input to the tags that consume `AlgebraicGeometry.Space.restrictToChart`, among them Stacks 0CVZ,
Stacks 05WV and Stacks 0DLR — and not an assertion of any tag of its own.  In particular it is
*not* Stacks 060Q, which is about local projectivity and is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/LocallyProjectiveEtaleChart.lean`.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 05VR](https://stacks.math.columbia.edu/tag/05VR)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **The sections of the chart restriction over an affine Zariski open of the chart's scheme
form a finitely presented module.**  They are the sections of the module over the étale chart
that open cuts out, which is an affine chart, and over an affine chart the sections of a
quasi-coherent module of finite presentation form a finitely presented module over the functions
on the chart.

The scalars of the two readings differ by `AlgebraicGeometry.Scheme.Opens.topIso`, along which
`ULift.up` is a semilinear additive equivalence. -/
theorem moduleFinitePresentation_sections_chartRestrictionSheaf
    (M : Modules.{u, u} B S hS X.1 X.2) (hqc : M.IsQuasicoherentOnSite)
    (hfp : SheafOfModules.IsFinitePresentationOnSite M)
    (A : SmallEtale B S hS X.1) (V : (chartScheme A).affineOpens) :
    Module.FinitePresentation Γ(chartScheme A, V.1)
      Γ(chartRestrictionSheaf B S hS X M A, V.1) := by
  let : Module (Γ(↑(V.1), ⊤) : Type u)
      (M.val.obj (Opposite.op ((chartOpens B S hS A).obj V.1)) : Type u) :=
    moduleChartSections B S hS X M ((chartOpens B S hS A).obj V.1)
  have : Module.FinitePresentation (Γ(↑(V.1), ⊤) : Type u)
      (M.val.obj (Opposite.op ((chartOpens B S hS A).obj V.1)) : Type u) :=
    module_finitePresentation_sections_of_isFinitePresentationOnSite M hqc hfp
      ((chartOpens B S hS A).obj V.1) V.2
  refine finitePresentation_of_ringEquiv _ _ V.1.topIso.commRingCatIsoToRingEquiv _ _
    ({ toFun := fun m => ULift.up m
       invFun := fun y => y.down
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl
       map_add' := fun _ _ => rfl } :
      (M.val.obj (Opposite.op ((chartOpens B S hS A).obj V.1)) : Type u) ≃+
        (Γ(chartRestrictionSheaf B S hS X M A, V.1) : Type u))
    (fun r m => congrArg ULift.up (congrArg (fun y => y • m)
      (ConcreteCategory.congr_hom V.1.topIso.hom_inv_id r).symm)) ‹_›

/-- **The restriction to an étale scheme chart of a quasi-coherent module of finite presentation
on the small étale site is of finite presentation** on the Zariski site of the chart's scheme.

The restriction needs no sheafification, so it is
`AlgebraicGeometry.Space.chartRestrictionSheaf`, which is quasi-coherent and whose sections over
every affine open of the chart's scheme are finitely presented; (5) ⇒ (3) of Stacks 01XZ
concludes. -/
theorem isFinitePresentation_restrictToChart (M : Modules.{u, u} B S hS X.1 X.2)
    (hqc : M.IsQuasicoherentOnSite) (hfp : SheafOfModules.IsFinitePresentationOnSite M)
    (A : SmallEtale B S hS X.1) :
    (restrictToChart B S hS X.2 M A).IsFinitePresentation := by
  have : (chartRestrictionSheaf B S hS X M A).IsQuasicoherent :=
    isQuasicoherent_chartRestrictionSheaf B S hS X M hqc A
  refine SheafOfModules.IsFinitePresentation.of_iso
    (Stacks.AlgebraicGeometry.FinitePresentationLocal.isFinitePresentation_of_affineCover
      (chartRestrictionSheaf B S hS X M A) (fun V : (chartScheme A).affineOpens => V.1)
      (TopologicalSpace.IsOpenCover.mk (iSup_affineOpens_eq_top (chartScheme A)))
      (fun V => V.2)
      (fun V => moduleFinitePresentation_sections_chartRestrictionSheaf B S hS X M hqc hfp A V))
    (restrictToChartIsoChartRestrictionSheaf B S hS X M A).symm

/-- **Finite presentation on the small étale site is finite presentation on charts**, for a
quasi-coherent module.  This is the passage the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatFinitePresentationModuleLocus.lean` record as
missing. -/
theorem isFinitePresentationOnCharts_of_isFinitePresentationOnSite
    (M : Modules.{u, u} B S hS X.1 X.2) (hqc : M.IsQuasicoherentOnSite)
    (hfp : SheafOfModules.IsFinitePresentationOnSite M) :
    IsFinitePresentationOnCharts B S hS X.2 M :=
  fun A => isFinitePresentation_restrictToChart B S hS X M hqc hfp A

end AlgebraicGeometry.Space

end

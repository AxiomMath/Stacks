module

public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralSpaceLimit.CohomologyMapUniqueness

/-!
# Native sheaf cohomology as right-derived sections, and the cocones of Tag 0A37

For an abelian sheaf `F` on a topological space `X`, Mathlib's native cohomology
`Sheaf.H' F p U` is an `Ext`-group out of the free abelian sheaf on `yoneda.obj U`. This file
identifies it with the `p`-th right-derived functor of sections over `U` evaluated at `F`, and
uses that identification to construct the canonical cohomology cocones of Tag 0A37.

## Main definitions

* `cohomologyIsoRightDerivedSections` is the comparison
  `Sheaf.H' F p U ≅ ((sections X U).rightDerived p).obj F`.

## Main results

* `SpectralAbelianSheafSystem.nonempty_stageCohomologyCocone` and
  `SpectralAbelianSheafSystem.nonempty_globalCohomologyCocone`: the cohomology cocone of Tag 0A37
  has a presentation, over a quasi-compact stage open and globally.

## Implementation notes

The mathematics is the degree-wise comparison
`ModuleSheafCohomology.nonempty_extFunctorObj_iso_rightDerived`: for an additive, left exact
functor to abelian groups that is corepresented by an object `Z`, the right-derived functors
agree with the `Ext`-functors out of `Z`. Sections over `U` of abelian sheaves on the site of
opens are corepresented by the sheafification of the free abelian presheaf on `yoneda.obj U`,
which is `ModuleSheafCohomology.evaluationRepresentation`, and that sheafification is exactly
the object Mathlib's `Sheaf.cohomologyPresheafFunctor` takes `Ext` out of. So the comparison is
an instance of the general statement, with no input specific to sheaves of modules — the
`δ`-functor argument of Tag 03FD is not used here, only the identification of `Ext` in the
second variable with the right-derived functors of `preadditiveCoyoneda`.

The comparison is unnormalized: `nonempty_extFunctorObj_iso_rightDerived` asserts only that an
isomorphism exists, so `cohomologyIsoRightDerivedSections` is a choice. This is all the two
cocone statements need, because `CohomologyCocone` carries the identification with right-derived
sections as data in its `objDerivedIso` and `vertexDerivedIso` fields and constrains its arrows
only relative to that data, which is what makes `Tag0A37Uniqueness.cohomologyCocone` applicable
to an arbitrary choice.

The assertion of Tag 0A37 itself, that the comparison out of the colimit is an isomorphism, is
`SpectralAbelianSheafSystem.isIso_comparison` and
`SpectralAbelianSheafSystem.isIso_comparison_global`
(`Topology/Sheaves/Cohomology/SpectralSpaceLimit/ComparisonInEveryDegree.lean`).

## References

* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

universe u v v'

namespace Stacks.Cohomology.SpectralLimit

/-! ### Native cohomology is right-derived sections -/

/-- Sections over an open subset are left exact. The functor is evaluation of the underlying
presheaf, so this is left exactness of the inclusion of sheaves into presheaves followed by
left exactness of evaluation in a functor category. -/
instance preservesFiniteLimits_sections (X : TopCat.{u}) (U : Opens X) :
    PreservesFiniteLimits (sections.{u, u} X U) := by
  have h : PreservesFiniteLimits
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
        (evaluation ((Opens X)ᵒᵖ) AddCommGrpCat.{u}).obj (op U)) := inferInstance
  exact h

/-- The free abelian sheaf on `yoneda.obj U`: the sheafification of the free abelian presheaf
on the presheaf of sets `yoneda.obj U`. This is the object Mathlib's native cohomology over `U`
takes `Ext` out of, and the object corepresenting sections over `U`. -/
abbrev freeSheafOfOpen (X : TopCat.{u}) (U : Opens X) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (yoneda.obj U ⋙ AddCommGrpCat.free)

/-- The functor-level comparison: the `Ext`-functors out of the free abelian sheaf on
`yoneda.obj U` are the right-derived functors of sections over `U`. Sections over `U` are
corepresented by `freeSheafOfOpen X U`, so this is an instance of the general comparison
`ModuleSheafCohomology.nonempty_extFunctorObj_iso_rightDerived`. -/
theorem nonempty_extFunctorObj_iso_rightDerived_sections (X : TopCat.{u}) (U : Opens X)
    (p : ℕ) :
    Nonempty (Abelian.extFunctorObj (freeSheafOfOpen X U) p ≅
      (sections.{u, u} X U).rightDerived p) :=
  ModuleSheafCohomology.nonempty_extFunctorObj_iso_rightDerived (sections.{u, u} X U) _
    (ModuleSheafCohomology.evaluationRepresentation (Opens.grothendieckTopology X) U) p

/-- **Native sheaf cohomology is right-derived sections.** For an abelian sheaf `F` on a
topological space `X`, Mathlib's `Sheaf.H' F p U` — the `p`-th `Ext`-group from the free
abelian sheaf on `yoneda.obj U` to `F` — is identified with the `p`-th right-derived functor of
sections over `U`, evaluated at `F`.

This is the identification that `Tag0A37.IsCohomologyMap` takes as a parameter and that
`CohomologyCocone` carries as data. It is a choice: see
`nonempty_extFunctorObj_iso_rightDerived_sections`. -/
def cohomologyIsoRightDerivedSections {X : TopCat.{u}} (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ)
    (U : Opens X) :
    Sheaf.H'.{u, u, u} F p U ≅ ((sections.{u, u} X U).rightDerived p).obj F :=
  (nonempty_extFunctorObj_iso_rightDerived_sections X U p).some.app F

/-! ### The canonical cohomology cocones of Tag 0A37 -/

namespace SpectralAbelianSheafSystem

variable {K : Type v} [Category.{v'} K] [IsCofiltered K]
  (S : SpectralAbelianSheafSystem.{u, v, v'} K)

/-- Over a quasi-compact stage open, the cohomology cocone of Tag 0A37 has a presentation. The
comparison out of its colimit is an isomorphism by
`SpectralAbelianSheafSystem.isIso_comparison`. -/
theorem nonempty_stageCohomologyCocone
    (c : Cone S.E) (_hc : IsLimit c) (i : K) (U : Opens (S.E.obj i))
    (_hU : IsCompact (U : Set (S.E.obj i))) (p : ℕ) :
    let C := CohomologyCocone ((Over.forget i) ⋙ S.E) (c.whisker (Over.forget i))
      (S.stageOpenCone c i U) p
    Nonempty C :=
  ⟨cohomologyCocone _ _ _ p (fun _ => cohomologyIsoRightDerivedSections _ p _)
    (cohomologyIsoRightDerivedSections _ p _)⟩

/-- The global cohomology cocone of Tag 0A37 has a presentation.  The comparison out of its
colimit is an isomorphism by `SpectralAbelianSheafSystem.isIso_comparison_global`. -/
theorem nonempty_globalCohomologyCocone
    (c : Cone S.E) (_hc : IsLimit c) (p : ℕ) :
    let C := CohomologyCocone S.E c (S.globalOpenCone c) p
    Nonempty C :=
  ⟨cohomologyCocone _ _ _ p (fun _ => cohomologyIsoRightDerivedSections _ p _)
    (cohomologyIsoRightDerivedSections _ p _)⟩

end SpectralAbelianSheafSystem

end Stacks.Cohomology.SpectralLimit

end

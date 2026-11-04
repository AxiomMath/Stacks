module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceFromQuasicoherentIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.DefiningIdealChartFiniteGeneration
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingGeneratorOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealZeroLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroLocusClosedProperSupportUnconditional

/-!
# The closed subspace cut out by a finite type quasi-coherent sheaf of ideals

Let `X` be an algebraic space over `S` and let `ℐ ⊆ 𝒪_X` be a quasi-coherent sheaf of ideals
of finite type. There is a closed subspace `Z = V(ℐ)` of `X` whose defining ideal sheaf is `ℐ`,
whose points are the zero locus `|V(ℐ)|`, and whose inclusion `Z ⟶ X` is of finite presentation.

## Main results

All names below are in the namespace `AlgebraicGeometry.Space`.

* `isFinitePresentation_ι_of_isFiniteTypeOnSite_definingIdealSheaf`: a closed subspace whose
  defining ideal sheaf is of finite type has a finitely presented inclusion.
* `exists_closedSubspace_isFinitePresentation_ι_of_isFiniteTypeQuasicoherentIdeal`: the closed
  subspace `V(ℐ)` of a finite type quasi-coherent sheaf of ideals, with the three properties
  above.

## Implementation notes

The closed subspace comes from the correspondence of Stacks 03MB
(`AlgebraicGeometry.Space.exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite`).  Its point
set is computed by `AlgebraicGeometry.Space.range_pointsMap_ι_eq_idealZeroLocus`.  For finite
presentation: finite type of the ideal sheaf makes its sections over every affine étale chart a
finitely generated ideal
(`AlgebraicGeometry.Space.fg_chartIdeal_definingIdealSheaf_of_isFiniteTypeOnSite`).  This is
the hypothesis of the finite presentation criterion
`AlgebraicGeometry.Space.isFinitePresentation_ι_of_fg_definingIdealAt`.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 084Q](https://stacks.math.columbia.edu/tag/084Q)
* [Stacks Project, Tag 0GV1](https://stacks.math.columbia.edu/tag/0GV1)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- **A closed subspace whose defining ideal sheaf is of finite type has a finitely presented
inclusion.**  This is the implication of Stacks 084Q from finite type of the ideal sheaf to
finite presentation of the closed immersion, stated with finite type on the small étale site.

Over every affine étale chart, the sections of a finite type quasi-coherent ideal sheaf form a
finitely generated ideal.  That is the hypothesis of
`AlgebraicGeometry.Space.isFinitePresentation_ι_of_fg_definingIdealAt`. -/
theorem isFinitePresentation_ι_of_isFiniteTypeOnSite_definingIdealSheaf
    (Z : ClosedSubspaces B S hS X.1)
    (hft : SheafOfModules.IsFiniteTypeOnSite (definingIdealSheaf B S hS X Z).toSheafOfModules) :
    IsFinitePresentation B S hS Z.1.ι :=
  isFinitePresentation_ι_of_fg_definingIdealAt B S hS X Z fun W hW =>
    fg_chartIdeal_definingIdealSheaf_of_isFiniteTypeOnSite B S hS X Z hft W hW

/-- **The closed subspace `V(ℐ)` of a finite type quasi-coherent sheaf of ideals.**  Let
`ℐ ⊆ 𝒪_X` be a quasi-coherent sheaf of ideals of finite type on an algebraic space `X`.  Then
there is a closed subspace `Z` of `X` such that:

* the defining ideal sheaf of `Z` is `ℐ`;
* the point set of `Z` is the zero locus `|V(ℐ)|`;
* the inclusion `Z ⟶ X` is of finite presentation.

The closed subspace is given by the correspondence of Stacks 03MB.  Its point set is the zero
locus of its defining ideal sheaf, and finite presentation is
`AlgebraicGeometry.Space.isFinitePresentation_ι_of_isFiniteTypeOnSite_definingIdealSheaf`. -/
theorem exists_closedSubspace_isFinitePresentation_ι_of_isFiniteTypeQuasicoherentIdeal
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (hI : IsFiniteTypeQuasicoherentIdeal B S hS X I) :
    ∃ Z : ClosedSubspaces B S hS X.1, definingIdealSheaf B S hS X Z = I ∧
      Set.range (pointsMap B S hS Z.1.toFunctor Z.1.ι) = idealZeroLocus B S hS X I ∧
      IsFinitePresentation B S hS Z.1.ι := by
  obtain ⟨Z, hZ⟩ := exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite B S hS X I hI.1
  refine ⟨Z, hZ, ?_, ?_⟩
  · rw [range_pointsMap_ι_eq_idealZeroLocus B S hS X Z, hZ]
  · refine isFinitePresentation_ι_of_isFiniteTypeOnSite_definingIdealSheaf B S hS X Z ?_
    rw [hZ]
    exact hI.2

end AlgebraicGeometry.Space

end

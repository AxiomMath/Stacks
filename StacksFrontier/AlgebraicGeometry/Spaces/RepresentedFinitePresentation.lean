module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationSiteEquivalence

/-!
# Finite presentation across the comparison of the two small étale sites of a scheme

Let `U` be an object of the big fppf site over `S`.  The small étale site of the algebraic space
`yoneda.obj U` and the small étale site of the scheme underlying `U` are equivalent, by
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence`, and their structure sheaves agree, by
`AlgebraicGeometry.Space.reindexRing_representedSmallEtaleEquivalence`; a module on the second is
read on the first by `AlgebraicGeometry.Space.representedSmallEtaleModule`.

This file is the finite-presentation companion of
`AlgebraicGeometry.Space.isQuasicoherentOnSite_representedSmallEtaleModule_iff`: where that is
clause (6) of Stacks 03DL under Lemma 03DM, this is clause (7).

## Main results

* `AlgebraicGeometry.Space.isFinitePresentation_representedSmallEtaleModule_iff`: **finite
  presentation is invariant under the comparison of the two small étale sites.**

## Implementation notes

Clause (6) needs only the comparison's *inverse* to be a dense subsite inclusion, clause (7)
needs that of the functor as well; both are instances here,
`AlgebraicGeometry.Space.isDenseSubsite_representedSmallEtaleEquivalence_functor` and
`AlgebraicGeometry.Space.isDenseSubsite_representedSmallEtaleEquivalence_inverse`.  The slices of
the two sites have sheafification, but instance search does not find it at either spelling, as
elsewhere in this directory, so both are supplied by hand.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)

/-- **Finite presentation is invariant under the comparison of the two small étale sites of a
scheme.**  A module on the small étale site of the scheme underlying `U` is of finite
presentation exactly when the `𝒪`-module it becomes on the small étale site of the algebraic
space `yoneda.obj U` is.

This is `Stacks.SheafOfModules.isFinitePresentation_reindex_iff` — Modules on Sites, Lemma 03DM
for clause (7) of Stacks 03DL — at the comparison equivalence. -/
theorem isFinitePresentation_representedSmallEtaleModule_iff
    (M : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS U)) :
    M.IsFinitePresentation ↔
      (representedSmallEtaleModule B S hS U M).IsFinitePresentation := by
  let (V : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property) :
      HasSheafify ((representedSchemeSmallEtaleTopology B S hS U).over V)
        AddCommGrpCat.{u} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  let (V : SmallEtale B S hS (yoneda.obj U)) :
      HasSheafify ((SmallEtale.topology B S hS (yoneda.obj U)).over V) AddCommGrpCat.{u} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  exact Stacks.SheafOfModules.isFinitePresentation_reindex_iff
    (representedSmallEtaleEquivalence B S hS U)
    (representedSchemeStructureSheaf B S hS U) M

end AlgebraicGeometry.Space

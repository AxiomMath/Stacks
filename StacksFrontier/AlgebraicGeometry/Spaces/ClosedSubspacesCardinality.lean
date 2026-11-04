module

public import StacksFrontier.AlgebraicGeometry.Size.IdealSheafData
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ClosedSubspaceApproximation

/-!
# An algebraic space has fewer closed subspaces than the cutoff

A closed subspace of an algebraic space `Y` is pinned down by the sheaf of ideals it cuts out
on a single *surjective* étale chart of `Y`: that is
`AlgebraicGeometry.Space.le_of_etaleChartKer_le_of_chart` read in both directions. The chart is
an object of the big fppf site, so its underlying scheme has size below the cutoff, and a
scheme has fewer than cutoff-many ideal sheaves
(`AlgebraicGeometry.Scheme.mk_idealSheafData_lt_of_size_lt`). So the closed subspaces of `Y`
number fewer than the cutoff.

This is what makes a Zorn argument over closed subspaces feed a *size-bounded* limit statement.
Stacks 07SR as this library proves it —
`AlgebraicGeometry.Space.DescentSituation.exists_isRepresentable_system_obj_of_isSiteSmall` — asks
`#I < B.cutoff.ord.cof` of the index of the inverse
system, and a chain of closed subspaces supplies only `#I < B.cutoff` — the two agree exactly
when the cutoff is regular, which `AlgebraicGeometry.BigFppfSite` does not require. See
`StacksFrontier/AlgebraicGeometry/Spaces/MinimalNonSchematicClosedSubspace.lean` for where that
gap bites and for the counterexample showing it cannot be closed in general.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.etaleChartKer_injective`: a closed subspace is determined by its
  ideal sheaf on a surjective étale chart.
* `AlgebraicGeometry.Space.mk_lt_cutoff_of_injective_closedSubspaces`: a `Type u` indexing
  distinct closed subspaces of such a space is smaller than the cutoff.

## References

* [Stacks Project, Tag 0CYZ](https://stacks.math.columbia.edu/tag/0CYZ)
-/

@[expose] public section

open CategoryTheory Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A closed subspace is determined by the sheaf of ideals it cuts out on a surjective étale
chart.** Two closed subspaces with the same chart ideal are contained in one another, by
`AlgebraicGeometry.Space.le_of_etaleChartKer_le_of_chart` applied in both directions. -/
theorem etaleChartKer_injective (Y : AlgebraicSpaces B S hS) (U : SmallEtale B S hS Y.1)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) U.1.hom) :
    Function.Injective fun Z : ClosedSubspaces B S hS Y.1 => etaleChartKer B S hS Y Z U :=
  fun Z W h => Subtype.ext (le_antisymm
    (le_of_etaleChartKer_le_of_chart B S hS Y Z W U hsurj h.ge)
    (le_of_etaleChartKer_le_of_chart B S hS Y W Z U hsurj h.le))

/-- **A `Type u` indexing distinct closed subspaces of an algebraic space with a surjective
étale chart is smaller than the cutoff.** The chart's underlying scheme is an object of the
site, so its size is below the cutoff, and a scheme of size below a strong prelimit has fewer
than that many ideal sheaves.

The bound is stated against an injection rather than as `#(ClosedSubspaces …) < B.cutoff`
because `CategoryTheory.Subfunctor Y.1` lives in `Type (u + 1)`, so the latter is a
`Cardinal.{u + 1}` and cannot be compared with the cutoff at all. Every consumer has a `Type u`
index in hand anyway — a chain re-indexed along `equivShrink`, for instance. -/
theorem mk_lt_cutoff_of_injective_closedSubspaces (Y : AlgebraicSpaces B S hS)
    (U : SmallEtale B S hS Y.1)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) U.1.hom)
    {α : Type u} (f : α → ClosedSubspaces B S hS Y.1) (hf : Function.Injective f) :
    #α < B.cutoff :=
  lt_of_le_of_lt
    (Cardinal.mk_le_of_injective ((etaleChartKer_injective B S hS Y U hsurj).comp hf))
    (Scheme.mk_idealSheafData_lt_of_size_lt _ B.cutoff_isStrongPrelimit
      U.1.left.left.property)

end AlgebraicGeometry.Space

end

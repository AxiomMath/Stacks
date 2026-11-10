module

public import StacksFrontier.AlgebraicGeometry.Flatness.SubschemeLimit
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendIdealSheaf

/-!
# A closed subscheme of a quasi-compact quasi-separated scheme is the limit of its
finite-presentation enlargements

`StacksFrontier/AlgebraicGeometry/Flatness/SubschemeLimit.lean` reduces the limit half of Tag 0EV9
to the single statement that a quasi-coherent ideal sheaf on a quasi-compact and quasi-separated
scheme is the supremum of the finitely generated quasi-coherent ideal sheaves below it — the
ideal-sheaf case of Tag 01PG — and proves the converse, so that statement is *equivalent* to the
limit half and cannot be weakened. That statement is now available as
`Stacks.IdealSheaf.le_iSup_fg`, and this file feeds it in.

## Main results

* `Stacks.Flatness.le_iSup_finitePresentationSubscheme`: on a quasi-compact and quasi-separated
  scheme, quasi-coherent ideal sheaf data is the supremum of the ideal sheaves it dominates whose
  closed immersion is of finite presentation.
* `Stacks.Flatness.isLimitSubschemeCone`: the closed subscheme cut out by quasi-coherent ideal
  sheaf data on a quasi-compact and quasi-separated scheme is the limit of its
  finite-presentation closed enlargements.

## Implementation notes

The two index sets are identified by `Stacks.Flatness.finitePresentation_subschemeι_iff`: a closed
immersion cut out by ideal sheaf data is of finite presentation exactly when the data is finitely
generated on every affine open. The condition `J ≤ K` indexing the system is, by Tag 0EV8, the
condition appearing in Tag 0EV9, as recorded in
`StacksFrontier/AlgebraicGeometry/Flatness/SubschemeFiltered.lean`.

## References

* [Stacks Project, Tag 0EV9](https://stacks.math.columbia.edu/tag/0EV9)
* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Flatness

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] (K : X.IdealSheafData)

/-- On a quasi-compact and quasi-separated scheme, quasi-coherent ideal sheaf data is the supremum
of the ideal sheaves below it whose closed immersion is of finite presentation. -/
theorem le_iSup_finitePresentationSubscheme :
    K ≤ ⨆ J : FinitePresentationSubscheme K, (J : X.IdealSheafData) :=
  (Stacks.IdealSheaf.le_iSup_fg K).trans
    (iSup_le fun J ↦ le_iSup (fun J : FinitePresentationSubscheme K ↦ (J : X.IdealSheafData))
      ⟨J.1, (finitePresentation_subschemeι_iff _).mpr J.2.1, J.2.2⟩)

/-- The closed subscheme cut out by quasi-coherent ideal sheaf data on a quasi-compact and
quasi-separated scheme is the limit of the inverse system of its finite-presentation closed
enlargements. Tag 0EV9 is this statement at the ideal of sections supported on the exceptional
subscheme of an almost blowup square, see
`AlgebraicGeometry.isFiltered_and_exists_isLimit_blowUpCone`. -/
def isLimitSubschemeCone : IsLimit (subschemeCone K) :=
  isLimitSubschemeConeOfLeISup K (le_iSup_finitePresentationSubscheme K)

/-- The `Nonempty` form of
`Stacks.Flatness.isLimitSubschemeCone`. -/
theorem nonempty_isLimit_subschemeCone : Nonempty (IsLimit (subschemeCone K)) :=
  ⟨isLimitSubschemeCone K⟩

end Stacks.Flatness

end

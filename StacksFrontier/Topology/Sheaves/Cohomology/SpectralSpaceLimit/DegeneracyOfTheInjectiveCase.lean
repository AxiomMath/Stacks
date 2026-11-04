module

public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralSpaceLimit.DegreeZero

/-!
# The injective case of the colimit comparison of Tag 0A37

For a system of injective abelian sheaves both sides of the comparison of Stacks 0A37 vanish in
positive degree, and a comparison between two zero objects is an isomorphism.  This file records
that, together with the statement of the quasi-compact-open comparison as a proposition.

## Main results

* `CohomologyCocone.isIso_comparison_of_isZero`: the comparison is an isomorphism as soon as the
  cohomology diagram is pointwise zero and the cohomology on the vertex is zero.
* `SpectralAbelianSheafSystem.isIso_comparison_of_injective_of_isZero`: for a stagewise injective
  system in degree `n + 1`, the comparison is an isomorphism because both sides vanish.
* `SpectralAbelianSheafSystem.QuasiCompactOpenColimitComparison`: the quasi-compact-open
  colimit comparison of Stacks 0A37 in every degree, as a proposition, and
  `SpectralAbelianSheafSystem.quasiCompactOpenColimitComparison_iff_succ`, its reduction to
  positive degree.  It holds for every system:
  `SpectralAbelianSheafSystem.quasiCompactOpenColimitComparison`
  (`Topology/Sheaves/Cohomology/SpectralSpaceLimit/ComparisonInEveryDegree.lean`).

## References

* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u v v'

namespace Stacks.Cohomology.SpectralLimit

namespace CohomologyCocone

variable {K : Type v} [Category.{v'} K]
  {E : K ⥤ SheafedSpace.{_, _, u} AddCommGrpCat.{u}} {c : Cone E} {O : OpenCone E c} {p : ℕ}

/-- **A comparison between two zero objects is an isomorphism.**  If the cohomology diagram of a
presentation is pointwise zero and the cohomology on the vertex is zero, then
`CohomologyCocone.comparison` is invertible. No hypothesis is placed on the system `E`, the cone
`c`, the opens `O` or the degree `p`. -/
theorem isIso_comparison_of_isZero (D : CohomologyCocone E c O p)
    (hd : ∀ k : K, IsZero (D.diagram.obj (op k)))
    (hv : IsZero (Sheaf.H'.{u, u, u} c.pt.sheaf p O.pt)) :
    IsIso D.comparison :=
  isIso_comparison_of_isColimit D (isColimit_cocone_of_isZero D hd hv)

end CohomologyCocone

namespace SpectralAbelianSheafSystem

variable {J : Type u} [SmallCategory J] [IsCofiltered J]
  (S : SpectralAbelianSheafSystem.{u, u, u} J)

/-- **The positive-degree conclusion of `isIso_comparison_of_injective_of_degree` is reached from
the two vanishings alone.**  For a stagewise injective system and a degree `n + 1`, the cohomology
diagram of any presentation over a quasi-compact open of a stage is pointwise zero
(`CohomologyCocone.isZero_diagram_obj_of_injective`, since the sheaves of the restricted diagram
`(Over.forget i) ⋙ S.E` are the stage sheaves) and the cohomology on the vertex is zero
(`isZero_H'_succ_conePoint_of_injective'`).  So
`CohomologyCocone.isIso_comparison_of_isZero` already gives the conclusion. -/
alias isIso_comparison_of_injective_of_isZero := isIso_comparison_of_injective'

/-- **The quasi-compact-open colimit comparison of Stacks 0A37**, as a proposition: for a
limiting cone `c` of the system of spaces-with-sheaves, a stage `i`, a quasi-compact open `U` of
that stage and a degree `p`, every presentation of the cohomology cocone has invertible
comparison. -/
def QuasiCompactOpenColimitComparison : Prop :=
  ∀ (c : Cone S.E), IsLimit c → ∀ (i : J) (U : Opens (S.E.obj i)),
    IsCompact (U : Set (S.E.obj i)) → ∀ (p : ℕ)
      (D : CohomologyCocone ((Over.forget i) ⋙ S.E) (c.whisker (Over.forget i))
        (S.stageOpenCone c i U) p), IsIso D.comparison

/-- **The comparison is equivalent to its own restriction to positive degree**, degree zero being
`isIso_comparison_zero`. -/
theorem quasiCompactOpenColimitComparison_iff_succ :
    S.QuasiCompactOpenColimitComparison ↔
      ∀ (c : Cone S.E), IsLimit c → ∀ (i : J) (U : Opens (S.E.obj i)),
        IsCompact (U : Set (S.E.obj i)) → ∀ (n : ℕ)
          (D : CohomologyCocone ((Over.forget i) ⋙ S.E) (c.whisker (Over.forget i))
            (S.stageOpenCone c i U) (n + 1)), IsIso D.comparison := by
  refine ⟨fun h c hc i U hU n D ↦ h c hc i U hU (n + 1) D, fun h c hc i U hU p D ↦ ?_⟩
  cases p with
  | zero => exact S.isIso_comparison_zero c hc i U hU D
  | succ n => exact h c hc i U hU n D

end SpectralAbelianSheafSystem

end Stacks.Cohomology.SpectralLimit

end

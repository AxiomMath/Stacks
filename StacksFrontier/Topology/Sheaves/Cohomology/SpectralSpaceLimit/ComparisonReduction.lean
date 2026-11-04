module

public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralSpaceLimit.NativeCohomologyCocones

/-!
# The colimit-comparison clauses of Tag 0A37: chosen cocones and the reduction

This file supplies two chosen presentations of the cohomology cocone of Tag 0A37, over a
quasi-compact stage open and globally, and shows that the comparison out of the colimit is an
isomorphism exactly when the comparison cocone of the presentation is a colimit cocone.  The
colimit comparison itself is `SpectralAbelianSheafSystem.isIso_comparison` and
`SpectralAbelianSheafSystem.isIso_comparison_global`
(`Topology/Sheaves/Cohomology/SpectralSpaceLimit/ComparisonInEveryDegree.lean`).

## Main definitions

* `SpectralAbelianSheafSystem.stageCohomologyCocone` and
  `SpectralAbelianSheafSystem.globalCohomologyCocone` choose a presentation of the canonical
  cohomology cocone over a quasi-compact stage open and globally.  They are the default values
  of the `D` argument of the two colimit-comparison clauses.

## Main results

* `CohomologyCocone.isIso_comparison_iff`: the comparison out of the colimit is an isomorphism
  **exactly** when the enlarged comparison cocone is a colimit cocone.  This is an equivalence,
  with no side hypothesis.
* `CohomologyCocone.isIso_comparison_of_isColimit`: the convenient direction, with the
  hypothesis stated before the enlargement, since `AddCommGrpCat.uliftFunctor` preserves
  colimits of the index shape.
* `CohomologyCocone.isIso_comparison_iff_nonempty_isColimit`: the same equivalence before the
  enlargement, available once the index shape is `u`-small.  It shows that the hypothesis of
  `isIso_comparison_of_isColimit` holds exactly when its conclusion does.

## Implementation notes

### The universes of the two colimit-comparison clauses

The declarations of this file hold for an index `K : Type v` with `[Category.{v'} K]` and spaces
and coefficients in a universe `u`, all independent.  The two colimit-comparison clauses are
stated for `K : Type u` with `[SmallCategory K]`, i.e. `v = v' = u`: colimits of shape
`(Over i)ᵒᵖ` in `AddCommGrpCat.{u}`, and their exactness (`AB5 AddCommGrpCat.{u}`), are available
at a `u`-small index, and the systems of sheaves of the proof — the stagewise injective system
`∏_{b : k → i} f_{b,*}ℐₖ` and the sheaf `colimⱼ pⱼ⁻¹𝒜ⱼ` on the vertex — are products and
colimits of abelian sheaves indexed by `K`.

## References

* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
* [Stacks Project, Tag 0A33](https://stacks.math.columbia.edu/tag/0A33)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

universe u v v'

namespace Stacks.Cohomology.SpectralLimit

/-! ### The comparison out of the colimit, and when it is invertible -/

namespace CohomologyCocone

variable {K : Type v} [Category.{v'} K]
  {E : K ⥤ SheafedSpace.{_, _, u} AddCommGrpCat.{u}} {c : Cone E}
  {O : OpenCone E c} {p : ℕ}

/-- **The comparison of Tag 0A37 is invertible exactly when the comparison cocone is a colimit
cocone.**  `CohomologyCocone.comparison` is the map out of the colimit of the enlarged
cohomology diagram induced by the enlarged comparison cocone, so this is the general fact that
the canonical map out of a colimit induced by a cocone is an isomorphism precisely when that
cocone is itself a colimit cocone.

It carries no side hypothesis, and in particular no hypothesis on the system `E`, the cone `c`
or the opens `O`. -/
theorem isIso_comparison_iff (D : CohomologyCocone E c O p) :
    IsIso D.comparison ↔
      Nonempty (IsColimit (AddCommGrpCat.uliftFunctor.{max v v'}.mapCocone D.cocone)) := by
  constructor
  · intro h
    have : IsIso
        ((colimit.isColimit (D.diagram ⋙ AddCommGrpCat.uliftFunctor.{max v v'})).desc
          (AddCommGrpCat.uliftFunctor.{max v v'}.mapCocone D.cocone)) := h
    exact ⟨IsColimit.ofPointIso (colimit.isColimit _)⟩
  · rintro ⟨hD⟩
    exact (IsColimit.coconePointUniqueUpToIso
      (colimit.isColimit (D.diagram ⋙ AddCommGrpCat.uliftFunctor.{max v v'})) hD).isIso_hom

/-- **The comparison of Tag 0A37 is invertible as soon as the comparison cocone is a colimit
cocone**, before the coefficient universe is enlarged.  `AddCommGrpCat.uliftFunctor` preserves
colimits of the index shape, so enlarging the cohomology diagram carries a colimit cocone to a
colimit cocone, and `isIso_comparison_iff` applies. -/
theorem isIso_comparison_of_isColimit (D : CohomologyCocone E c O p)
    (hD : IsColimit D.cocone) : IsIso D.comparison :=
  (isIso_comparison_iff D).2 ⟨isColimitOfPreserves AddCommGrpCat.uliftFunctor.{max v v'} hD⟩

/-- **The comparison of Tag 0A37 is invertible exactly when the comparison cocone is a colimit
cocone**, stated before the coefficient universe is enlarged.  This needs the colimit of the
cohomology diagram to exist already in `AddCommGrpCat.{u}`, which holds as soon as the index
shape is `u`-small — in particular at the universes `v = v' = u` to which the two
colimit-comparison clauses of Tag 0A37 have to be restated.

`AddCommGrpCat.uliftFunctor` is fully faithful, hence reflects isomorphisms, hence reflects the
colimits it preserves.  Together with `isIso_comparison_of_isColimit` this shows that the
hypothesis of that lemma holds precisely when its conclusion does, so neither direction is
vacuous. -/
theorem isIso_comparison_iff_nonempty_isColimit [HasColimitsOfShape Kᵒᵖ AddCommGrpCat.{u}]
    (D : CohomologyCocone E c O p) :
    IsIso D.comparison ↔ Nonempty (IsColimit D.cocone) := by
  refine ⟨fun h => ?_, fun ⟨hD⟩ => isIso_comparison_of_isColimit D hD⟩
  have hrefl : ReflectsColimit D.diagram AddCommGrpCat.uliftFunctor.{max v v'} :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  exact ⟨isColimitOfReflects AddCommGrpCat.uliftFunctor.{max v v'}
    ((isIso_comparison_iff D).1 h).some⟩

end CohomologyCocone

/-! ### The chosen presentations -/

namespace SpectralAbelianSheafSystem

variable {K : Type v} [Category.{v'} K] [IsCofiltered K]
  (S : SpectralAbelianSheafSystem.{u, v, v'} K)

/-- A chosen presentation of the canonical cohomology cocone over a quasi-compact stage open,
supplied by Tag 0A37 without any additional diagram hypothesis.  This is the default value of
the presentation argument of the quasi-compact-open colimit-comparison clause. -/
def stageCohomologyCocone
    (c : Cone S.E) (hc : IsLimit c) (i : K) (U : Opens (S.E.obj i))
    (hU : IsCompact (U : Set (S.E.obj i))) (p : ℕ) :
    CohomologyCocone ((Over.forget i) ⋙ S.E) (c.whisker (Over.forget i))
      (S.stageOpenCone c i U) p :=
  Classical.choice (S.nonempty_stageCohomologyCocone c hc i U hU p)

/-- A chosen presentation of the canonical global cohomology cocone, supplied by Tag 0A37
without any additional diagram hypothesis.  This is the default value of the presentation
argument of the global colimit-comparison clause. -/
def globalCohomologyCocone (c : Cone S.E) (hc : IsLimit c) (p : ℕ) :
    CohomologyCocone S.E c (S.globalOpenCone c) p :=
  Classical.choice (S.nonempty_globalCohomologyCocone c hc p)

end SpectralAbelianSheafSystem

end Stacks.Cohomology.SpectralLimit

end

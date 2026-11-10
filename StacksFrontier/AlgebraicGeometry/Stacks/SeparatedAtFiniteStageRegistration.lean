module

public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedAtFiniteStageConvention
import StacksCore.Tactic.StacksAttribute

/-!
# Tag 0CPZ: separatedness of a base change descends to a finite stage

`AlgebraicGeometry.Space.DescentSituation.exists_isSeparated_stage_of_siteContainsBaseChangeLimits`
states [Stacks, Tag 0CPZ]: in Situation 0CPY, for `f₀ : 𝒳₀ ⟶ Y₀` a 1-morphism from a
quasi-compact and quasi-separated algebraic stack, if the base change `Y ×_{Y₀} 𝒳₀ ⟶ Y` to the
limit is separated, then so is `Y_i ×_{Y₀} 𝒳₀ ⟶ Y_i` for all sufficiently large `i`. The system
satisfies the chapter's standing convention of Section 70.2 (tag 07SD),
`AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`, the convention under which Stacks 0851
and Stacks 07SQ are registered as well; without it the statement fails in this bounded site
(`StacksFrontier/AlgebraicGeometry/Spaces/DescendingProperties/SiteConventionCounterexample.lean`).
This file only registers the tag.

## References

* [Stacks Project, Tag 0CPZ](https://stacks.math.columbia.edu/tag/0CPZ)
* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
-/

@[expose] public section

add_to_stacks 0CPZ "under the chapter's standing convention of Section 70.2 (tag 07SD) on the \
system, as for 0851 and 07SQ; without it the statement fails in this bounded site \
(SiteConventionCounterexample)"
  AlgebraicGeometry.Space.DescentSituation.exists_isSeparated_stage_of_siteContainsBaseChangeLimits

module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedLowerShriekFreeModuleBaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# The simplex category is its own point resolution

Stacks 08QD specialises homology on a category to `C = Δ`, and the hypothesis to check is that
the tautological cosimplicial object `U_• = 𝟭` of `Δ` is a point resolution in the sense of
Lemma 08Q9: for every `⦋m⦌` the simplicial set `Δ[m] : n ↦ Mor_Δ(⦋n⦌, ⦋m⦌)` is homotopy
equivalent to a point.

That verification is already available on this branch, as
`Stacks.ChaoticSite.isPointResolution_id_simplexCategory`, which exhibits the identity functor
of `Δ` as a cosimplicial point resolution. This file records it under the tag, so that the
assertion of the remark that `C = Δ` with `U_• = 𝟭` is an instance of Example 08PF satisfying
the hypothesis of Lemma 08Q9 is registered where it is proved.

## Main results

No new declarations are introduced; the point-resolution statement is adopted as it stands.

## References

* [Stacks Project, Tag 08QD](https://stacks.math.columbia.edu/tag/08QD)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
-/

@[expose] public section

add_to_stacks 08QD "the identity functor of `Δ` is a point resolution, which is the hypothesis \
  of Lemma 08Q9 for `C = Δ`" Stacks.ChaoticSite.isPointResolution_id_simplexCategory

end

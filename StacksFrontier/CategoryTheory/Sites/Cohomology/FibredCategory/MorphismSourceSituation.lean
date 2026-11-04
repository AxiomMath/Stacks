module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.MorphismLowerShriekAcyclic

/-!
# The source fibred category of a 1-morphism, as a situation of Stacks 08P8

Let `g : C' ⟶ C` be a 1-morphism of fibred categories `p' : C' ⥤ D` and `p : C ⥤ D` over a
ringed site `D`, as in Stacks 08PA. The target, the base together with `p`, is the situation
`Stacks.Sites.FibredCategory.MorphismSituation.totalSituation` of Stacks 08P8; this file records
the source, the base together with `p'`, in the same way, so that the results of Stacks 08P8 and
08P9 for a fibred category apply to `p'`.

## Main definitions

* `Stacks.Sites.FibredCategory.MorphismSituation.sourceSituation`: the base ringed site together
  with `p' : C' ⥤ D`, as a situation of Stacks 08P8.

## References

* [Stacks Project, Tag 08PA](https://stacks.math.columbia.edu/tag/08PA)
* [Stacks Project, Tag 08P8](https://stacks.math.columbia.edu/tag/08P8)
-/

@[expose] public noncomputable section

namespace Stacks.Sites.FibredCategory

namespace MorphismSituation

universe u₀ u₁ u₂ v₀ v₁ v₂ w

variable (S : MorphismSituation.{u₀, u₁, u₂, v₀, v₁, v₂, max w u₀ u₁ u₂ v₀ v₁ v₂})

/-- **The source fibred category, as the standing data of Stacks 08P8.** The base ringed site of
the situation, with the source fibred category and its structure functor `p'`. -/
abbrev sourceSituation : FibredCategorySituation.{u₀, v₀, u₂, v₂, max w u₀ u₁ u₂ v₀ v₁ v₂} :=
  { base := S.base, C := S.source, p := S.p', isFibered := S.p'Fibered }

end MorphismSituation

end Stacks.Sites.FibredCategory

end

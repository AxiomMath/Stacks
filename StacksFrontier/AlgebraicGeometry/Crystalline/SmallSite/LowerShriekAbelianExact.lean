module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisDirectImage
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekExactness

/-!
# Exactness of `i_!` for the small crystalline site, at abelian coefficients

Let `(S, I, γ)` be a divided power scheme over `ℤ_{(p)}` and `X` a scheme over `S₀ = V(I)` with
`p` locally nilpotent on `X`.  The inclusion `i : Cris(X/S) ⥤ CRIS(X/S)` is continuous,
cocontinuous and fully faithful, so restriction along it has a left adjoint `i_!`, and
[Stacks, Tag 07IJ] asserts that `i_!` is exact.

`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/LowerShriekExact.lean` proves that for
sheaves of **sets**, where the hard step is the final object: there `i_! *` has to be shown to be
`*`, which is the covering statement `coversTop_ι` that the source omits in general.  This file
proves the same for sheaves of **abelian groups**, where that step is not needed at all: the final
object of a category of abelian sheaves is the zero object, and `i_!` is additive, so it is
preserved for free.  What is left is the half of [Stacks, Tag 00X4] that holds in any abelian
category of coefficients satisfying `AB5`, and it is already in the library as
`Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits`: the left Kan extension along `i.op` is
a pointwise colimit over a costructured-arrow category, that category is pseudofiltered because
`Cris(X/S)` has fibre products and equalizers which `i` preserves, a pseudofiltered colimit of
abelian groups is exact, and sheafification is exact.

In particular the set-valued exactness is not the only input available: the abelian version
gives that `f_{cris, *}` preserves injective abelian sheaves.  The abelian version needs neither `coversTop_ι` nor any new
geometry, only the hypotheses of [Stacks, Tag 00X6] on `Cris(X/S)`, which instance search
supplies from the closure instance
`Crystalline.GlobalCrystallineSituation.Thickening.isClosedUnderFiniteLimits_isCrystalline`; see
`SmallSite/AlphaPCoverTriangle.lean` for the consequence.

## Main results

* `Crystalline.GlobalCrystallineSituation.CrystallineThickening.hasPullbacks_crystallineThickening`
  and `...hasEqualizers_crystallineThickening` — the two finite-limit shapes of
  [Stacks, Tag 07I9] that `Cris(X/S)` has, and `...ι_preservesPullbacks`,
  `...ι_preservesEqualizers` their preservation by the inclusion.
* `...preservesFiniteLimits_lowerShriekAb` — **`i_!` is exact on abelian sheaves**, at the
  coefficient universe `u + 1` of this chapter.

## What is and is not proved

Exactness of the abelian `i_!` is proved unconditionally, for every global crystalline situation,
with no appeal to [Stacks, Tag 07HP] and no affineness hypothesis.  Nothing here is new
mathematics: the content is [Stacks, Tag 00X4] as already formalised in
`StacksFrontier/CategoryTheory/Sites/Cocontinuous/LowerShriekExactness.lean`, and this file only
discharges its hypotheses for the inclusion of the small crystalline site.

Nothing here says anything about sheaves of modules, and nothing here supersedes
`coversTop_ι`: that statement is about sheaves of sets, where it is genuinely needed, and it is
also what makes `i_!` preserve the final *set-valued* sheaf, hence what makes the retraction
`π : (X/S)_CRIS ⟶ (X/S)_cris` a morphism of topoi.

## References

* [Stacks Project, Tag 07IJ](https://stacks.math.columbia.edu/tag/07IJ)
* [Stacks Project, Tag 07I9](https://stacks.math.columbia.edu/tag/07I9)
* [Stacks Project, Tag 00X4](https://stacks.math.columbia.edu/tag/00X4)
* [Stacks Project, Tag 00X6](https://stacks.math.columbia.edu/tag/00X6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Crystalline.GlobalCrystallineSituation

namespace CrystallineThickening

variable (S : GlobalCrystallineSituation.{u})

/-- `Cris(X/S)` has fibre products, [Stacks, Tag 07I9] for the small site: `CRIS(X/S)` has them
and the full subcategory is closed under them. -/
theorem hasPullbacks_crystallineThickening : HasPullbacks (CrystallineThickening S) :=
  inferInstance

/-- `Cris(X/S)` has equalizers, [Stacks, Tag 07I9] for the small site: `CRIS(X/S)` has them,
products of pairs and fibre products giving equalizers, and the full subcategory is closed under
them. -/
theorem hasEqualizers_crystallineThickening : HasEqualizers (CrystallineThickening S) :=
  have : HasEqualizers (Thickening S) := hasEqualizers_of_hasPullbacks_and_binary_products
  inferInstance

/-- The inclusion `Cris(X/S) ⥤ CRIS(X/S)` preserves fibre products. -/
theorem ι_preservesPullbacks : PreservesLimitsOfShape WalkingCospan (ι S) :=
  inferInstance

/-- The inclusion `Cris(X/S) ⥤ CRIS(X/S)` preserves equalizers. -/
theorem ι_preservesEqualizers : PreservesLimitsOfShape WalkingParallelPair (ι S) :=
  have : HasEqualizers (Thickening S) := hasEqualizers_of_hasPullbacks_and_binary_products
  inferInstance

/-- **Stacks Project, Tag 07IJ, clause (6), at abelian coefficients: the lower shriek `i_!` along
the inclusion `Cris(X/S) ⥤ CRIS(X/S)` is exact on sheaves of abelian groups.**

Unlike the set-valued statement `preservesFiniteLimits_lowerShriek`, this needs no covering
argument: the final object of a category of abelian sheaves is the zero object and `i_!`, being a
left adjoint between additive categories, preserves it.  What remains is
[Stacks, Tag 00X4] for the shapes of [Stacks, Tag 00X6], namely
`Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits`, whose hypotheses are that `Cris(X/S)`
have fibre products and equalizers which the inclusion preserves — the four theorems above, all
instances of [Stacks, Tag 07I9]. -/
@[stacks 07IJ "clause (6) at abelian coefficients: i_! is exact on sheaves of abelian groups, \
with no covering argument needed"]
theorem preservesFiniteLimits_lowerShriekAb :
    PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback (ι S)
      AddCommGrpCat.{u + 1} (smallTopology S) (topology S)) :=
  have := hasPullbacks_crystallineThickening S
  have := hasEqualizers_crystallineThickening S
  have := ι_preservesPullbacks S
  have := ι_preservesEqualizers S
  Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits.{u + 1} (ι S) _ _

end CrystallineThickening

end Crystalline.GlobalCrystallineSituation

end

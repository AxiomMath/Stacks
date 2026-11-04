module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingForHomsOverAMember

/-!
# The glueing condition's only witness route is degenerate at the covering hypothesis

Let `(X, 𝒪_X)` be a ringed space and `(ℬ, K_U, ρ^U_V)` a system of locally given derived objects
on it, as in Situation 0D67.  The uniqueness halves of [Stacks, Tag 0D6A] and [Stacks, Tag 0D6C],
`Stacks.DerivedGlueing.exists_unique_solutionIso_of_finite_cover` and
`Stacks.DerivedGlueing.exists_unique_solutionIso_of_covers`, are granted
`Stacks.DerivedGlueing.HasGluingForHomsOver` — the sheaf condition of [Stacks, Tag 0D66] part (2)
in the vocabulary of Situation 0D67.

Exactly one route to that hypothesis exists in this development:
`Stacks.DerivedGlueing.hasGluingForHomsOver_of_covered_mem`, which assumes that *every* open that
is the union of the members of `ℬ` contained in it is itself a member, and
`Stacks.DerivedGlueing.hasGluingForHomsOver_locallyGivenOfTop`, which is that lemma applied to the
collection of all opens.  The module documentation of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.GlueingForHomsOverAMember` observes in
prose that every inhabitant obtained that way forces `⊤ ∈ ℬ`, where
`Stacks.DerivedGlueing.exists_unique_solutionIso_of_top_mem` already proves the conclusion with
nothing granted.

This file turns that observation into theorems.  The saturation hypothesis of
`hasGluingForHomsOver_of_covered_mem` together with either tag's own covering hypothesis — finitely
many members covering `X` for 0D6A, the members covering `X` for 0D6C — forces `⊤ ∈ ℬ`, because
`⊤` is then the union of the members contained in it and saturation makes it a member.  So no
witness built from that route can certify either conditional uniqueness theorem beyond its case
`n = 1`, and a non-degenerate inhabitant of `HasGluingForHomsOver` must come from a genuinely
different argument — the general case of the sheaf condition.  The development *does* carry that
case, unconditionally, but in the vocabulary of the ringed site:
`Stacks.DerivedGlueing.existsUnique_hom_restrict_of_sSup_covered` and
`Stacks.Cohomology.UnboundedHigherDirectImage.exists_unique_restrictDerivedHom_on_isBasis`, over
[Stacks, Tag 0D66] part (2) itself,
`Stacks.Cohomology.UnboundedHigherDirectImage.isSheaf_derivedPreimageHomPresheaf`.  What is
missing is not the sheaf condition but the translation of it into Situation 0D67: the statement
that the Hom-group identification `Stacks.DerivedGlueing.homEquivSlice` intertwines
`Stacks.DerivedGlueing.restrictHomBelow` with
`AlgebraicGeometry.RingedSite.restrictDerivedHom`.  That one equation is carried open under
three names — `Stacks.DerivedGlueing.HasHomRestrictionDictionary`, the hypothesis `hcoh` of
`Stacks.DerivedGlueing.exists_unique_solutionIso_of_covers_of_coherence`, and the hypothesis
`hcan` of `Stacks.DerivedGlueing.restrictHomBelow_eq_restrictDerivedHom_of_canonical` — and
none of the three has an inhabitant.

This is the uniqueness-half counterpart of
`Stacks.DerivedGlueing.top_mem_opensLE_of_finsetSup_eq_top`, which does the same for the existence
half's granted hypothesis.  Unlike the existence half, whose hypothesis
`Stacks.DerivedGlueing.GluesAlongTwoOpens` does have a witness away from `⊤ ∈ ℬ`
(`Stacks.DerivedGlueing.nonempty_solution_opensLEPair`), no such witness is available here, and
these theorems say why no refinement of the existing route can produce one.

## Main results

* `Stacks.DerivedGlueing.top_mem_of_covered_mem_of_finsetSup_eq_top`: the saturation hypothesis of
  `Stacks.DerivedGlueing.hasGluingForHomsOver_of_covered_mem` plus a finite cover of `X` by members
  forces `⊤ ∈ ℬ`.
* `Stacks.DerivedGlueing.top_mem_of_covered_mem_of_sSup_eq_top`: the same from the covering
  hypothesis of [Stacks, Tag 0D6C].

## References

* [Stacks Project, Tag 0D6A](https://stacks.math.columbia.edu/tag/0D6A)
* [Stacks Project, Tag 0D6C](https://stacks.math.columbia.edu/tag/0D6C)
* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Stacks.DerivedGlueing

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-- **The saturation hypothesis plus a finite cover by members forces `⊤` to be a member.** When
finitely many members of the collection cover `X`, the open `⊤` is the union of the members
contained in it, by `Stacks.DerivedGlueing.top_eq_sSup_covered_of_finsetSup_eq_top`; a collection
containing every open it covers therefore contains `⊤`.

The hypothesis `hmem` is exactly the one
`Stacks.DerivedGlueing.hasGluingForHomsOver_of_covered_mem` uses to produce
`Stacks.DerivedGlueing.HasGluingForHomsOver`, and `hs` and `hcover` are the covering hypotheses of
[Stacks, Tag 0D6A].  So on every system for which that route supplies the granted hypothesis of
`Stacks.DerivedGlueing.exists_unique_solutionIso_of_finite_cover`, the conclusion is *already*
available from `Stacks.DerivedGlueing.exists_unique_solutionIso_of_top_mem`, which grants nothing.
A witness certifying the conditional theorem beyond its case `n = 1` cannot come from this
route. -/
theorem top_mem_of_covered_mem_of_finsetSup_eq_top (S : LocallyGiven X)
    (hmem : ∀ O : Opens X.carrier, O = sSup {W | W ∈ S.opens ∧ W ≤ O} → O ∈ S.opens)
    (s : Finset (Opens X.carrier)) (hs : ∀ U ∈ s, U ∈ S.opens) (hcover : s.sup id = ⊤) :
    (⊤ : Opens X.carrier) ∈ S.opens :=
  hmem ⊤ (top_eq_sSup_covered_of_finsetSup_eq_top S s hs hcover)

/-- **The same from the covering hypothesis of [Stacks, Tag 0D6C].** When the members of the
collection cover `X`, the open `⊤` is the union of the members contained in it, by
`Stacks.DerivedGlueing.top_eq_sSup_covered_of_sSup_eq_top`, so a collection containing every open
it covers contains `⊤`.

Hence `Stacks.DerivedGlueing.exists_unique_solutionIso_of_covers` is in the same position as its
0D6A counterpart: on every system for which
`Stacks.DerivedGlueing.hasGluingForHomsOver_of_covered_mem` supplies its granted hypothesis, the
unconditional `Stacks.DerivedGlueing.exists_unique_solutionIso_of_top_mem` already applies. -/
theorem top_mem_of_covered_mem_of_sSup_eq_top (S : LocallyGiven X)
    (hmem : ∀ O : Opens X.carrier, O = sSup {W | W ∈ S.opens ∧ W ≤ O} → O ∈ S.opens)
    (hcover : sSup S.opens = ⊤) :
    (⊤ : Opens X.carrier) ∈ S.opens :=
  hmem ⊤ (top_eq_sSup_covered_of_sSup_eq_top S hcover)

end Stacks.DerivedGlueing

end

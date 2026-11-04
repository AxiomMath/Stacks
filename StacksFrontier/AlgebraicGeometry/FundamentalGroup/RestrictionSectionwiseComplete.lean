module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.Chain
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionSectionwiseCriteria
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionToClosedSubscheme
import StacksCore.Tactic.StacksAttribute

/-!
# Fully faithful restriction of finite étale covers from sectionwise completeness

Let `X` be a Noetherian scheme, `Y ⊆ X` a closed subscheme and `Y_n ⊆ X` the `n`-th
infinitesimal neighbourhood of `Y` in `X`. [Stacks, Tag 0EJZ] asserts that the restriction functor
`FÉt_X ⟶ FÉt_Y` is fully faithful as soon as one of the following holds:

1. `X` is quasi-affine and `Γ(X, 𝒪_X) → lim Γ(Y_n, 𝒪_{Y_n})` is an isomorphism;
2. `X` has an ample invertible module `L` and `Γ(X, L^{⊗ m}) → lim Γ(Y_n, L^{⊗ m}|_{Y_n})` is an
   isomorphism for all `m ≫ 0`;
3. `Γ(X, ℰ) → lim Γ(Y_n, ℰ|_{Y_n})` is an isomorphism for every finite locally free `𝒪_X`-module
   `ℰ`.

This file proves the tag in all three cases, with nothing assumed beyond the tag's own
hypotheses, following the source's proof: "this lemma follows formally from Tag 0EL8 and
Tag 0EKP". The chain `(1) ⇒ (2) ⇒ (3) ⇒ (4)` of [Stacks, Tag 0EKP] is
`Stacks.Algebraization.sectionsComplete_chain`, where `(4)` is full faithfulness of the completion
functor on finite locally free coherent modules, and [Stacks, Tag 0EL8] — full faithfulness of
restriction from `(4)` — is
`Stacks.FundamentalGroup.fullyFaithful_finiteEtaleBaseChange_of_completionFullyFaithfulOnFinite`
`LocallyFree`.

## Main results

* `Stacks.FundamentalGroup.fullyFaithful_finiteEtaleBaseChange_of_sectionsComplete_of_or` —
  [Stacks, Tag 0EJZ], all three cases, the hypothesis being their disjunction.
* `Stacks.FundamentalGroup.bijective_map_finiteEtaleBaseChange_of_sectionsComplete_of_or` — the
  same conclusion restated as bijectivity of restriction on every hom set.

## Implementation notes

The three conditions are the predicates `Stacks.FundamentalGroup.SectionsCompleteQuasiAffine`,
`SectionsCompleteAmplePowers` and `SectionsCompleteFiniteLocallyFree` of
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionSectionwiseCriteria`. The isomorphism
`Γ(X, ℰ) → lim Γ(Y_n, ℰ|_{Y_n})` is expressed there by the universal property of the inverse
limit, `Stacks.Algebraization.IsInfinitesimalSectionsComplete`: every compatible family of sections
on the neighbourhoods has a unique antecedent in `Γ(X, ℰ)`. Its index `n` is the source's `n + 1`,
which changes nothing because the index set is cofinal.

The declarations here take none of the implications of Tag 0EKP, nor any auxiliary statement,
as arguments.

## References

* [Stacks Project, Tag 0EJZ](https://stacks.math.columbia.edu/tag/0EJZ)
* [Stacks Project, Tag 0EKP](https://stacks.math.columbia.edu/tag/0EKP)
* [Stacks Project, Tag 0EL8](https://stacks.math.columbia.edu/tag/0EL8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.FundamentalGroup

/-- **[Stacks, Tag 0EJZ].** Let `X` be a Noetherian scheme and `Y ⊆ X` a closed subscheme, with
infinitesimal neighbourhoods `Y_n ⊆ X`. Assume one of the following holds:

1. `X` is quasi-affine and `Γ(X, 𝒪_X) → lim Γ(Y_n, 𝒪_{Y_n})` is an isomorphism, or
2. `X` has an ample invertible module `L` and `Γ(X, L^{⊗ m}) → lim Γ(Y_n, L^{⊗ m}|_{Y_n})` is an
   isomorphism for all `m ≫ 0`, or
3. for every finite locally free `𝒪_X`-module `ℰ` the map `Γ(X, ℰ) → lim Γ(Y_n, ℰ|_{Y_n})` is an
   isomorphism.

Then the restriction functor `FÉt_X ⟶ FÉt_Y` is fully faithful.

As in the source, cases (1) and (2) are reduced to case (3) by the implications `(1) ⇒ (2) ⇒ (3)`
of [Stacks, Tag 0EKP], case (3) gives full faithfulness of completion on finite locally free
modules by `(3) ⇒ (4)` of the same tag, and [Stacks, Tag 0EL8] concludes. -/
@[stacks 0EJZ]
public theorem fullyFaithful_finiteEtaleBaseChange_of_sectionsComplete_of_or
    {X Y : Scheme.{u}} (i : Y ⟶ X) [IsNoetherian X] [IsClosedImmersion i]
    (h : SectionsCompleteQuasiAffine i ∨ SectionsCompleteAmplePowers i ∨
      SectionsCompleteFiniteLocallyFree i) :
    Nonempty (finiteEtaleBaseChange i).FullyFaithful := by
  obtain ⟨h12, h23, h34, -⟩ := Stacks.Algebraization.sectionsComplete_chain i
  have h3 : SectionsCompleteFiniteLocallyFree i := by
    rcases h with h1 | h2 | h3
    · exact h23 (h12 h1)
    · exact h23 h2
    · exact h3
  exact fullyFaithful_finiteEtaleBaseChange_of_completionFullyFaithfulOnFiniteLocallyFree i
    (h34 h3)

/-- **[Stacks, Tag 0EJZ], restated as bijectivity on hom sets.** Under any one of the three
conditions of
`Stacks.FundamentalGroup.fullyFaithful_finiteEtaleBaseChange_of_sectionsComplete_of_or`,
restriction of finite étale covers of `X` to the closed subscheme `Y` is bijective on every hom
set.

`CategoryTheory.Functor.FullyFaithful` carries the inverse map on hom sets as data, so full
faithfulness is recorded as `Nonempty _.FullyFaithful`;
`CategoryTheory.Functor.FullyFaithful.nonempty_iff_map_bijective` turns it into bijectivity on hom
sets. -/
@[stacks 0EJZ "restated as bijectivity on hom sets", sga "2 X 2.5" "special case"]
public theorem bijective_map_finiteEtaleBaseChange_of_sectionsComplete_of_or
    {X Y : Scheme.{u}} (i : Y ⟶ X) [IsNoetherian X] [IsClosedImmersion i]
    (h : SectionsCompleteQuasiAffine i ∨ SectionsCompleteAmplePowers i ∨
      SectionsCompleteFiniteLocallyFree i)
    (A B : FiniteEtaleOver X) :
    Function.Bijective (fun φ : A ⟶ B => (finiteEtaleBaseChange i).map φ) :=
  (Functor.FullyFaithful.nonempty_iff_map_bijective (finiteEtaleBaseChange i)).mp
    (fullyFaithful_finiteEtaleBaseChange_of_sectionsComplete_of_or i h) A B

end Stacks.FundamentalGroup

end

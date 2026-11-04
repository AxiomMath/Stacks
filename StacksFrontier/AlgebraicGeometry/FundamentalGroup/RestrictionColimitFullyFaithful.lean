module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.NeighbourhoodCompletionConditions
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SectionsExtendFromCompletion
public import StacksCore.Tactic.StacksAttribute

/-!
# Sectionwise criteria for full faithfulness of restriction from the neighbourhoods

Let `X` be a Noetherian scheme, `Y ⊆ X` a closed subscheme with infinitesimal neighbourhoods
`Y_n ⊆ X`, and `𝒱` the open subschemes of `X` containing `Y`, ordered by reverse inclusion.
[Stacks, Tag 0EK0] says that the restriction functor `colim_𝒱 FÉt_V ⟶ FÉt_Y` is fully faithful
as soon as one of three sectionwise conditions holds:

1. `X` is quasi-affine and `colim_𝒱 Γ(V, 𝒪_V) → lim Γ(Y_n, 𝒪_{Y_n})` is an isomorphism;
2. `X` has an ample invertible module `L` and
   `colim_𝒱 Γ(V, L^{⊗ m}) → lim Γ(Y_n, L^{⊗ m}|_{Y_n})` is an isomorphism for all `m ≫ 0`;
3. for every `V ∈ 𝒱` and every finite locally free `𝒪_V`-module `ℰ` the map
   `colim_{V' ≥ V} Γ(V', ℰ|_{V'}) → lim Γ(Y_n, ℰ|_{Y_n})` is an isomorphism.

## Main results

* `Stacks.FundamentalGroup.finiteEtaleColimitFullyFaithful_of_neighbourhoodSectionsComplete` —
  [Stacks, Tag 0EK0].

## Implementation notes

Conditions (1) and (2) are `Stacks.FundamentalGroup.NeighbourhoodSectionsCompleteQuasiAffine`
and `Stacks.FundamentalGroup.NeighbourhoodSectionsCompleteAmplePowers`. Condition (3) is
`Stacks.Algebraization.NeighbourhoodCompletion.FiniteLocallyFreeComplete` at the closed immersion
of `Y`. In it the neighbourhoods `V` are the opens of `X` containing `Y`, and the `Y_n` are the
infinitesimal neighbourhoods of `Y` in `X`, read over `V`, exactly as in the source.

The conclusion is `Stacks.FundamentalGroup.FiniteEtaleColimitFullyFaithful`. That is full
faithfulness of `colim_𝒱 FÉt_V ⟶ FÉt_Y`, written through the description of the hom sets of a
directed colimit of categories ([Stacks, Tag 04AX]): every morphism between restrictions to `Y`
comes from some neighbourhood, and two morphisms over a neighbourhood that agree on `Y` agree on a
smaller one. The conclusion of [Stacks, Tag 0ELA] in this library has the same form.

The proof is the source's: by [Stacks, Tag 0EK2], conditions (1) and (2) imply (3), and (3)
implies full faithfulness of completion on the finite locally free objects. [Stacks, Tag 0ELA]
then turns that into full faithfulness of restriction.

## References

* [Stacks Project, Tag 0EK0](https://stacks.math.columbia.edu/tag/0EK0)
* [Stacks Project, Tag 0EK2](https://stacks.math.columbia.edu/tag/0EK2)
* [Stacks Project, Tag 0ELA](https://stacks.math.columbia.edu/tag/0ELA)
* [Stacks Project, Tag 04AX](https://stacks.math.columbia.edu/tag/04AX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry

universe u

namespace Stacks.FundamentalGroup

open Stacks.Algebraization.NeighbourhoodCompletion

/-- **[Stacks, Tag 0EK0].** Let `X` be a Noetherian scheme, `Y ⊆ X` a closed subscheme with
infinitesimal neighbourhoods `Y_n ⊆ X`, and `𝒱` the open subschemes of `X` containing `Y`,
ordered by reverse inclusion. Assume one of the following holds:

1. `X` is quasi-affine and `colim_𝒱 Γ(V, 𝒪_V) → lim Γ(Y_n, 𝒪_{Y_n})` is an isomorphism;
2. `X` has an ample invertible module `L` and
   `colim_𝒱 Γ(V, L^{⊗ m}) → lim Γ(Y_n, L^{⊗ m}|_{Y_n})` is an isomorphism for all `m ≫ 0`;
3. for every `V ∈ 𝒱` and every finite locally free `𝒪_V`-module `ℰ` the map
   `colim_{V' ≥ V} Γ(V', ℰ|_{V'}) → lim Γ(Y_n, ℰ|_{Y_n})` is an isomorphism.

Then the restriction functor `colim_𝒱 FÉt_V ⟶ FÉt_Y` is fully faithful. The conclusion is in the
form `FiniteEtaleColimitFullyFaithful`, which describes the hom sets of the directed colimit.

The proof follows the source. By [Stacks, Tag 0EK2], condition (1) gives (2), (2) gives (3), and
(3) gives full faithfulness of completion on the finite locally free objects. [Stacks, Tag 0ELA]
then gives full faithfulness of restriction. -/
@[stacks 0EK0 "all three cases, under the tag's own hypotheses; full faithfulness spelled \
through the directed-colimit description of the hom sets of colim_V FEt_V"]
public theorem finiteEtaleColimitFullyFaithful_of_neighbourhoodSectionsComplete
    {X : Scheme.{u}} [IsNoetherian X] (Y : X.IdealSheafData)
    (h : NeighbourhoodSectionsCompleteQuasiAffine Y ∨
      NeighbourhoodSectionsCompleteAmplePowers Y ∨
      FiniteLocallyFreeComplete Y.subschemeι) :
    FiniteEtaleColimitFullyFaithful X Y := by
  have h3 : FiniteLocallyFreeComplete Y.subschemeι := by
    rcases h with h1 | h2 | h3
    · exact finiteLocallyFreeComplete_of_hasAmpleComplete Y.subschemeι
        (hasAmpleComplete_of_isQuasiAffineComplete Y.subschemeι
          ((isQuasiAffineComplete_iff_neighbourhoodSectionsCompleteQuasiAffine Y).2 h1))
    · exact finiteLocallyFreeComplete_of_hasAmpleComplete Y.subschemeι
        ((hasAmpleComplete_iff_neighbourhoodSectionsCompleteAmplePowers Y).2 h2)
    · exact h3
  exact finiteEtaleColimitFullyFaithful_of_completionFullyFaithfulComplete X Y
    (completionFullyFaithfulComplete_of_finiteLocallyFreeComplete Y.subschemeι h3)

end Stacks.FundamentalGroup

end

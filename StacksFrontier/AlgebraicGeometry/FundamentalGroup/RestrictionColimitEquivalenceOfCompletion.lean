module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleNeighbourhoodExtension
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SectionsExtendFromCompletion

/-!
# Restriction from the neighbourhoods of a closed subscheme is an equivalence

Let `X` be a Noetherian scheme, `Y ⊆ X` a closed subscheme with ideal sheaf `I`, and `𝒱` the open
subschemes `V ⊆ X` containing `Y`, ordered by reverse inclusion. [Stacks, Tag 0EK1]: if the
completion functor `colim_𝒱 Coh(𝒪_V) ⟶ Coh(X, I)`, `ℱ ↦ ℱ^∧`, defines an equivalence of the full
subcategories of finite locally free objects, then the restriction functor
`colim_𝒱 FÉt_V ⟶ FÉt_Y` is an equivalence.

## Main definitions

* `Stacks.FundamentalGroup.CompletionEquivalenceFiniteLocallyFree` — the hypothesis of the tag:
  the completion functor `colim_𝒱 Coh(𝒪_V) ⟶ Coh(X, I)` is an equivalence on finite locally free
  objects.

## Main results

* `Stacks.FundamentalGroup.restriction_isEquivalence_of_completionEquivalence` —
  [Stacks, Tag 0EK1].

## How the statement is written

`𝒱` is directed, so `colim_𝒱 Coh(𝒪_V)` and `colim_𝒱 FÉt_V` are the colimits of Categories,
Section 04AX. Their objects are the objects at the individual stages, and the morphisms between two
objects at a stage `V` are the colimit over `V' ≥ V` of the morphisms between their restrictions to
`V'`. A functor out of such a colimit is an equivalence exactly when it is fully faithful in that
sense and essentially surjective. Both the hypothesis and the conclusion are written this way.

* The hypothesis. Full faithfulness of completion on finite locally free objects is condition (4)
  of [Stacks, Tag 0EK2] (`NeighbourhoodCompletion.CompletionFullyFaithfulComplete`): for finite
  locally free `𝒢`, `ℱ` on `V`, `colim_{V'} Hom(𝒢|_{V'}, ℱ|_{V'}) ⟶ Hom(𝒢^∧, ℱ^∧)` is bijective.
  Essential surjectivity onto the finite locally free objects of `Coh(X, I)` says that every such
  object is the completion of a finite locally free module on some `V ∈ 𝒱`
  (`IsNeighbourhoodCompletionFiniteLocallyFree`).
* The conclusion. Full faithfulness of the restriction functor is
  `FiniteEtaleColimitFullyFaithful` ([Stacks, Tag 0ELA] proves it from the first half of the
  hypothesis). Essential surjectivity says that every finite étale cover of `Y` is, up to
  isomorphism, the restriction of a finite étale cover of some `V ∈ 𝒱`.

## The proof

Full faithfulness is [Stacks, Tag 0ELA],
`Stacks.FundamentalGroup.finiteEtaleColimitFullyFaithful_of_completionFullyFaithfulComplete`.
Essential surjectivity is the source's algebraization of the formal finite étale cover,
`Stacks.FundamentalGroup.exists_finiteEtale_neighbourhood_extension_of_completion`.

## References

* [Stacks Project, Tag 0EK1](https://stacks.math.columbia.edu/tag/0EK1)
* [Stacks Project, Tag 0ELA](https://stacks.math.columbia.edu/tag/0ELA)
* [Stacks Project, Tag 0EK2](https://stacks.math.columbia.edu/tag/0EK2)
* [Stacks Project, Tag 04AX](https://stacks.math.columbia.edu/tag/04AX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.FundamentalGroup

open Stacks.Algebraization

variable (X : Scheme.{u}) (Y : X.IdealSheafData)

/-- **The hypothesis of [Stacks, Tag 0EK1]**, exactly: the completion functor
`colim_𝒱 Coh(𝒪_V) ⟶ Coh(X, I)`, `ℱ ↦ ℱ^∧`, defines an equivalence of the full subcategories of
finite locally free objects. Since `𝒱` is directed, this is the conjunction of
* full faithfulness on finite locally free objects, condition (4) of [Stacks, Tag 0EK2]
  (`NeighbourhoodCompletion.CompletionFullyFaithfulComplete`): for finite locally free `𝒢`, `ℱ`
  on `V ∈ 𝒱`, the map `colim_{V' ⊆ V} Hom(𝒢|_{V'}, ℱ|_{V'}) ⟶ Hom_{Coh(X, I)}(𝒢^∧, ℱ^∧)` is
  bijective;
* essential surjectivity onto the finite locally free objects: every finite locally free object
  of `Coh(X, I)` is isomorphic to the completion of a finite locally free coherent module on some
  `V ∈ 𝒱` (`IsNeighbourhoodCompletionFiniteLocallyFree`).
The functor does land in the finite locally free objects
(`Stacks.Algebraization.isFiniteLocallyFreeAdic_completion`), so nothing else is asserted. -/
public def CompletionEquivalenceFiniteLocallyFree [IsLocallyNoetherian X] : Prop :=
  NeighbourhoodCompletion.CompletionFullyFaithfulComplete Y.subschemeι ∧
    ∀ F : Stacks.Coherent.CoherentAdicSystems Y, IsFiniteLocallyFreeAdic Y F →
      IsNeighbourhoodCompletionFiniteLocallyFree Y F

/-- **[Stacks, Tag 0EK1].** Let `X` be a Noetherian scheme, `Y ⊆ X` a closed subscheme with ideal
sheaf `I`, and `𝒱` the open subschemes of `X` containing `Y`, ordered by reverse inclusion. If the
completion functor `colim_𝒱 Coh(𝒪_V) ⟶ Coh(X, I)` defines an equivalence of the full
subcategories of finite locally free objects, then the restriction functor
`colim_𝒱 FÉt_V ⟶ FÉt_Y` is an equivalence: it is fully faithful in the directed-colimit sense of
`FiniteEtaleColimitFullyFaithful`, and every finite étale cover of `Y` is the restriction of a
finite étale cover of some `V ∈ 𝒱`. -/
@[stacks 0EK1 "the colimit functor is an equivalence: fully faithful, and every finite étale \
cover of Y extends to a neighbourhood"]
public theorem restriction_isEquivalence_of_completionEquivalence [IsNoetherian X]
    (h : CompletionEquivalenceFiniteLocallyFree X Y) :
    FiniteEtaleColimitFullyFaithful X Y ∧
      ∀ A : FiniteEtaleOver Y.subscheme, ∃ (W : Neighborhood X Y)
        (U : FiniteEtaleOver (Neighborhood.open X Y W).toScheme),
        Nonempty ((finiteEtaleBaseChange (Neighborhood.toSchemeHom X Y W)).obj U ≅ A) :=
  ⟨finiteEtaleColimitFullyFaithful_of_completionFullyFaithfulComplete X Y h.1,
    exists_finiteEtale_neighbourhood_extension_of_completion Y h.1 h.2⟩

end Stacks.FundamentalGroup

end

module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Kernel
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionColimitEquivalence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionEquivalenceOfCompletion

/-!
# The essential image of restriction from the neighbourhoods of a closed subscheme

Let `X` be a Noetherian scheme, let `Y ⊆ X` be a closed subscheme with ideal sheaf `I`, and let
`𝒱` be the open subschemes `V ⊆ X` containing `Y`, ordered by reverse inclusion. The
essential-image clause of [Stacks, Tag 0EK1] is the assertion that every finite étale cover of
`Y` is the restriction of a finite étale cover of some member of `𝒱`.

This file proves that clause from the completion hypothesis read at a **single** member of `𝒱`.
A member `V ∈ 𝒱` carries the closed subscheme `Y` (the chosen factorisation
`Y ⟶ V` is a closed immersion, `Stacks.FundamentalGroup.isClosedImmersion_neighborhoodToSchemeHom`)
and is itself Noetherian, so [Stacks, Tag 0EL9] applies to it: if the completion functor
`Coh(𝒪_V) ⥤ Coh(V, I|_V)` is an equivalence on the full subcategories of finite locally free
objects, then `FÉt_V ⥤ FÉt_Y` is an equivalence, and in particular essentially surjective. Its
essential surjectivity is the essential-image clause, witnessed by that one `V`.

## Main results

* `Stacks.FundamentalGroup.exists_finiteEtale_neighborhood_of_completionEquivalence` — for a
  neighbourhood `V` at which completion is an equivalence on finite locally free objects, every
  finite étale cover of `Y` is the restriction of a finite étale cover of `V`.
* `Stacks.FundamentalGroup.essentialImage_restriction_of_completionEquivalence_neighborhood` —
  the same statement in the shape the hypothesis `hessImage` of
  `Stacks.FundamentalGroup.isEquivalence_restrictionFunctor_of_fullyFaithful_of_essentialImage`
  asks for, so that hypothesis is discharged by this term.
* `isEquivalence_restrictionFunctor_of_fullyFaithful_of_completionEquivalence_neighborhood` —
  [Stacks, Tag 0EK1] with the essential-image half discharged: only full faithfulness of the
  restriction functor remains as a hypothesis.

## Relation to [Stacks, Tag 0EK1]

The hypothesis of [Stacks, Tag 0EK1] is that the completion functor out of the *colimit*,
`colim_𝒱 Coh(𝒪_V) ⟶ Coh(X, I)`, is an equivalence on the finite locally free objects. That is
weaker than the hypothesis used here, which asks for an equivalence at one fixed `V`: the colimit
hypothesis algebraises a finite locally free object of `Coh(X, I)` on a neighbourhood that
depends on the object, and identifies morphisms only after passing to a smaller neighbourhood. The
source's proof of the essential-image clause from it therefore shrinks the neighbourhood twice —
once to obtain the multiplication `𝓕 ⊗ 𝓕 ⟶ 𝓕` from the multiplications of the tower, and once
more to make it commutative and associative — and neither shrinking is needed when completion is
an equivalence at a fixed `V`, which is the hypothesis of [Stacks, Tag 0EL9].

So the clause proved here is the source's clause with the source's hypothesis replaced by the
hypothesis of [Stacks, Tag 0EL9] read at a neighbourhood rather than at `X`. **No `stacks`
attribute is attached to it**: it is not Tag 0EK1, whose hypothesis is strictly weaker, and it is
not Tag 0EL9, whose conclusion is about `X`. It generalises the essential surjectivity of Tag
0EL9, which is the case `V = X`.

## References

* [Stacks Project, Tag 0EK1](https://stacks.math.columbia.edu/tag/0EK1)
* [Stacks Project, Tag 0EL9](https://stacks.math.columbia.edu/tag/0EL9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.FundamentalGroup

variable {X : Scheme.{u}} [IsNoetherian X] (Y : X.IdealSheafData) (W : Neighborhood X Y)

/-- **A neighbourhood of a closed subscheme of a Noetherian scheme is Noetherian.** It is an open
subscheme, so this is `Stacks.Coherent.isNoetherian_of_isOpenImmersion` for its inclusion. -/
public theorem isNoetherian_neighborhood_open :
    IsNoetherian (Neighborhood.open X Y W).toScheme :=
  Stacks.Coherent.isNoetherian_of_isOpenImmersion (Neighborhood.open X Y W).ι

/-- **Restriction from a neighbourhood at which completion is an equivalence is an equivalence.**
The chosen factorisation `Y ⟶ V` of the closed immersion `Y ⟶ X` through a neighbourhood `V` is
a closed immersion, and `V` is Noetherian, so [Stacks, Tag 0EL9] applies to it. -/
public theorem isEquivalence_finiteEtaleBaseChange_neighborhood_of_completionEquivalence
    (hW : (finiteLocallyFreeCompletion (Neighborhood.open X Y W).toScheme
      (Neighborhood.toSchemeHom X Y W).ker).IsEquivalence) :
    (AlgebraicGeometry.finiteEtaleBaseChange (Neighborhood.toSchemeHom X Y W)).IsEquivalence :=
  let := isNoetherian_neighborhood_open Y W
  let := hW
  finiteEtaleBaseChange_isEquivalence_of_completionEquivalence
    (Neighborhood.toSchemeHom X Y W)

/-- **The essential-image clause of [Stacks, Tag 0EK1], at a neighbourhood at which completion is
an equivalence.** Let `X` be Noetherian, let `Y ⊆ X` be the closed subscheme cut out by `Y`, and
let `V` be an open neighbourhood of `Y` in `X`. If the completion functor
`Coh(𝒪_V) ⥤ Coh(V, I|_V)` is an equivalence on the full subcategories of finite locally free
objects, then every finite étale cover of `Y` is isomorphic to the restriction to `Y` of a finite
étale cover of `V`.

This is the essential surjectivity of the equivalence `FÉt_V ⥤ FÉt_Y` supplied by
`isEquivalence_finiteEtaleBaseChange_neighborhood_of_completionEquivalence`. -/
public theorem exists_finiteEtale_neighborhood_of_completionEquivalence
    (hW : (finiteLocallyFreeCompletion (Neighborhood.open X Y W).toScheme
      (Neighborhood.toSchemeHom X Y W).ker).IsEquivalence)
    (A : AlgebraicGeometry.FiniteEtaleOver Y.subscheme) :
    ∃ U : AlgebraicGeometry.FiniteEtaleOver (Neighborhood.open X Y W).toScheme,
      Nonempty ((AlgebraicGeometry.finiteEtaleBaseChange
        (Neighborhood.toSchemeHom X Y W)).obj U ≅ A) := by
  let := isEquivalence_finiteEtaleBaseChange_neighborhood_of_completionEquivalence Y W hW
  exact ⟨(AlgebraicGeometry.finiteEtaleBaseChange
      (Neighborhood.toSchemeHom X Y W)).objPreimage A,
    ⟨(AlgebraicGeometry.finiteEtaleBaseChange
      (Neighborhood.toSchemeHom X Y W)).objObjPreimageIso A⟩⟩

/-- **The essential-image clause of [Stacks, Tag 0EK1] in the shape its carrier consumes.** The
hypothesis `hessImage` of
`Stacks.FundamentalGroup.isEquivalence_restrictionFunctor_of_fullyFaithful_of_essentialImage`
asks, for every finite étale cover of `Y`, for *some* neighbourhood of `Y` and a cover of it
restricting to the given one. One neighbourhood at which completion is an equivalence on finite
locally free objects serves for every cover at once. -/
public theorem essentialImage_restriction_of_completionEquivalence_neighborhood
    (hW : (finiteLocallyFreeCompletion (Neighborhood.open X Y W).toScheme
      (Neighborhood.toSchemeHom X Y W).ker).IsEquivalence) :
    ∀ A : AlgebraicGeometry.FiniteEtaleOver Y.subscheme, ∃ (W' : Neighborhood X Y)
      (U : AlgebraicGeometry.FiniteEtaleOver (Neighborhood.open X Y W').toScheme),
      Nonempty ((AlgebraicGeometry.finiteEtaleBaseChange
        (Neighborhood.toSchemeHom X Y W')).obj U ≅ A) :=
  fun A => ⟨W, exists_finiteEtale_neighborhood_of_completionEquivalence Y W hW A⟩

/-- **[Stacks, Tag 0EK1] with its essential-image half discharged.** Let `X` be a Noetherian
scheme, `Y ⊆ X` a closed subscheme, and `𝒱` the open subschemes of `X` containing `Y`, ordered by
reverse inclusion. If the restriction functor `colim_𝒱 FÉt_V ⟶ FÉt_Y` is fully faithful, and if
there is one member `V` of `𝒱` at which the completion functor `Coh(𝒪_V) ⥤ Coh(V, I|_V)` is an
equivalence on the finite locally free objects, then that restriction functor is an equivalence.

Compared with
`Stacks.FundamentalGroup.isEquivalence_restrictionFunctor_of_fullyFaithful_of_essentialImage`,
the second hypothesis `hessImage` is gone: it is
`Stacks.FundamentalGroup.essentialImage_restriction_of_completionEquivalence_neighborhood`. The
first hypothesis, full faithfulness, is the conclusion of [Stacks, Tag 0ELA] and is still
assumed. -/
public theorem
    isEquivalence_restrictionFunctor_of_fullyFaithful_of_completionEquivalence_neighborhood
    (P : FiniteEtaleColimitPresentation X Y) [CategoryTheory.Limits.HasColimit P.diagram]
    (h0ELA : Nonempty P.restrictionFunctor.FullyFaithful)
    (hW : (finiteLocallyFreeCompletion (Neighborhood.open X Y W).toScheme
      (Neighborhood.toSchemeHom X Y W).ker).IsEquivalence) :
    P.restrictionFunctor.IsEquivalence :=
  isEquivalence_restrictionFunctor_of_fullyFaithful_of_essentialImage Y P h0ELA
    (essentialImage_restriction_of_completionEquivalence_neighborhood Y W hW)

end Stacks.FundamentalGroup

end

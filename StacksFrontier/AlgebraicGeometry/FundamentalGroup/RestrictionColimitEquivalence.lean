module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.Neighbourhoods
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction

/-!
# Restriction of finite étale covers from the neighbourhoods of a closed subscheme

Let `X` be a Noetherian scheme, let `Y ⊆ X` be a closed subscheme with ideal sheaf `I`, and let
`𝒱` be the open subschemes `V ⊆ X` containing `Y`, ordered by reverse inclusion. The categories
`FÉt_V` of finite étale covers of the members of `𝒱` form a filtered diagram, and restriction to
`Y` is a cocone on it; the induced functor out of the colimit is
`colim_𝒱 FÉt_V ⟶ FÉt_Y`. This file is about that functor.

[Stacks, Tag 0EK0] gives three sectionwise criteria for it to be fully faithful, and
[Stacks, Tag 0EK1] asserts that it is an equivalence as soon as the completion functor
`colim_𝒱 Coh(𝒪_V) ⟶ Coh(X, I)` is an equivalence on the finite locally free objects.

Both tags are formalized elsewhere, with full faithfulness written through the directed-colimit
description of the hom sets of `colim_𝒱 FÉt_V` ([Stacks, Tag 04AX]),
`Stacks.FundamentalGroup.FiniteEtaleColimitFullyFaithful`:
[Stacks, Tag 0EK0] is
`Stacks.FundamentalGroup.finiteEtaleColimitFullyFaithful_of_neighbourhoodSectionsComplete` and
[Stacks, Tag 0EK1] is `Stacks.FundamentalGroup.restriction_isEquivalence_of_completionEquivalence`.
Both are proved there under the source's own hypotheses. This file is about the functor
`P.restrictionFunctor` out of a colimit in `Cat` of a chosen strict presentation `P`: it proves
that this functor is essentially surjective as soon as every cover of `Y` extends to a
neighbourhood, and an equivalence when moreover it is fully faithful.

## Main definitions

* `Stacks.FundamentalGroup.FiniteEtaleColimitPresentation.restrictionFunctor` — the functor
  `colim_𝒱 FÉt_V ⟶ FÉt_Y` carried by a strict presentation of the restriction diagram.
* `Stacks.FundamentalGroup.NeighbourhoodSectionsCompleteQuasiAffine`,
  `Stacks.FundamentalGroup.NeighbourhoodSectionsCompleteAmplePowers`,
  `Stacks.FundamentalGroup.NeighbourhoodSectionsCompleteFiniteLocallyFree` — the three conditions
  of [Stacks, Tag 0EK0], spelled with the colimit-over-`𝒱` vocabulary
  `Stacks.Algebraization.IsNeighbourhoodSectionsComplete` of [Stacks, Tag 0EK2].

## Main results

* `Stacks.FundamentalGroup.isClosedImmersion_neighborhoodToSchemeHom` — a closed subscheme is a
  closed subscheme of each of its open neighbourhoods.
* `Stacks.FundamentalGroup.essSurj_restrictionFunctor_of_essentialImage` — the restriction functor
  out of the colimit is essentially surjective as soon as every finite étale cover of `Y` is the
  restriction of a cover of some neighbourhood. This is unconditional.
* `Stacks.FundamentalGroup.isEquivalence_restrictionFunctor_of_fullyFaithful_of_essentialImage` —
  `P.restrictionFunctor` is an equivalence when it is fully faithful and every finite étale cover
  of `Y` extends to a neighbourhood.

## Implementation notes

The colimit `colim_𝒱 FÉt_V` is taken through
`Stacks.FundamentalGroup.FiniteEtaleColimitPresentation`: the assignment `V ↦ FÉt_V` is only a
pseudofunctor into `Cat`, because restriction is base change and iterated base changes agree only
up to canonical isomorphism, so a strict diagram presenting it has to be chosen before a colimit
can be formed. The theorems below are stated for an arbitrary such presentation and an arbitrary
colimit of its diagram, so neither depends on the choice.

Conditions (1) and (2) of [Stacks, Tag 0EK0] are conditions (1) and (2) of [Stacks, Tag 0EK2],
and are spelled here exactly as the carrier of the implication `(1) ⇒ (2)` of that tag spells
them, so that it applies to them directly. Condition (3) quantifies over the neighbourhoods `V`,
and the comparison it asks for on `V` is the colimit over the smaller neighbourhoods `V' ≥ V`;
those are exactly the open neighbourhoods of `Y` inside `V`, so (3) is
`Stacks.Algebraization.IsNeighbourhoodSectionsComplete` for the closed immersion `Y ⟶ V`, which
is `Stacks.FundamentalGroup.isClosedImmersion_neighborhoodToSchemeHom`.

**Relation to the hom-set form.** [Stacks, Tag 0EK0] is proved unconditionally, in all three
cases and under the tag's own hypotheses, as
`Stacks.FundamentalGroup.finiteEtaleColimitFullyFaithful_of_neighbourhoodSectionsComplete`:
conditions (1) and (2) are converted to condition (3) by the implications `(1) ⇒ (2)` and
`(2) ⇒ (3)` of [Stacks, Tag 0EK2]
(`Stacks.Algebraization.NeighbourhoodCompletion.hasAmpleComplete_of_isQuasiAffineComplete`,
`Stacks.Algebraization.NeighbourhoodCompletion.finiteLocallyFreeComplete_of_hasAmpleComplete`),
condition (3) gives condition (4) by
`NeighbourhoodCompletion.completionFullyFaithfulComplete_of_finiteLocallyFreeComplete`, and
[Stacks, Tag 0ELA] is
`Stacks.FundamentalGroup.finiteEtaleColimitFullyFaithful_of_completionFullyFaithfulComplete`.
Its conclusion is the hom-set form `FiniteEtaleColimitFullyFaithful`; passing from it to full
faithfulness of `P.restrictionFunctor` for a presentation `P` needs the hom sets of a filtered
colimit in `Cat`, which are not computed in this library, so the full-faithfulness input of
`isEquivalence_restrictionFunctor_of_fullyFaithful_of_essentialImage` is a hypothesis.

Likewise, the essential-image hypothesis of
`isEquivalence_restrictionFunctor_of_fullyFaithful_of_essentialImage` is the second conjunct of
`restriction_isEquivalence_of_completionEquivalence`, proved there from the completion
equivalence by the source's algebraization of the tower `π_{n, *}𝒪_{U_n}`. The passage from it to
essential surjectivity of the functor out of the colimit is proved here, in
`essSurj_restrictionFunctor_of_essentialImage`.

## References

* [Stacks Project, Tag 0EK0](https://stacks.math.columbia.edu/tag/0EK0)
* [Stacks Project, Tag 0EK1](https://stacks.math.columbia.edu/tag/0EK1)
* [Stacks Project, Tag 0EK2](https://stacks.math.columbia.edu/tag/0EK2)
* [Stacks Project, Tag 0ELA](https://stacks.math.columbia.edu/tag/0ELA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.FundamentalGroup

/-! ### A closed subscheme inside one of its neighbourhoods -/

/-- A closed subscheme is a closed subscheme of each of its open neighbourhoods: the chosen
factorisation of the closed immersion through a neighbourhood is again a closed immersion. -/
public instance isClosedImmersion_neighborhoodToSchemeHom (X : Scheme.{u})
    (Y : X.IdealSheafData) (W : Neighborhood X Y) :
    IsClosedImmersion (Neighborhood.toSchemeHom X Y W) := by
  have : IsClosedImmersion
      (Neighborhood.toSchemeHom X Y W ≫ (Neighborhood.open X Y W).ι) := by
    rw [Neighborhood.toSchemeHom_fac]
    infer_instance
  exact IsClosedImmersion.of_comp (Neighborhood.toSchemeHom X Y W)
    (Neighborhood.open X Y W).ι

/-! ### The restriction functor out of the colimit -/

/-- **The restriction functor `colim_𝒱 FÉt_V ⟶ FÉt_Y`.** For a strict presentation of the
diagram of finite étale covers of the open neighbourhoods of a closed subscheme, the functor
induced on a colimit of that diagram by the cocone that restricts a cover to the closed
subscheme. -/
public def FiniteEtaleColimitPresentation.restrictionFunctor {X : Scheme.{u}}
    {Y : X.IdealSheafData} (P : FiniteEtaleColimitPresentation X Y) [HasColimit P.diagram] :
    (colimit P.diagram : Cat.{u, u + 1}) ⥤ FiniteEtaleOver Y.subscheme :=
  (colimit.desc P.diagram P.cocone).toFunctor ⋙ P.coconePointIso.hom.toFunctor

/-- The restriction functor out of the colimit agrees, on the image of the stage `W`, with
restriction of a cover of `W` to the closed subscheme. -/
public theorem FiniteEtaleColimitPresentation.restrictionFunctor_obj_colimit_ι
    {X : Scheme.{u}} {Y : X.IdealSheafData} (P : FiniteEtaleColimitPresentation X Y)
    [HasColimit P.diagram] (W : Neighborhood X Y) (Z : P.diagram.obj W) :
    P.restrictionFunctor.obj ((colimit.ι P.diagram W).toFunctor.obj Z) =
      ((P.cocone.ι.app W).toFunctor ⋙ P.coconePointIso.hom.toFunctor).obj Z := by
  change P.coconePointIso.hom.toFunctor.obj
    ((colimit.ι P.diagram W ≫ colimit.desc P.diagram P.cocone).toFunctor.obj Z) = _
  rw [colimit.ι_desc]
  rfl

/-- Restriction out of the colimit is essentially surjective as soon as every finite étale cover
of the closed subscheme is isomorphic to the restriction of a finite étale cover of one of its
open neighbourhoods. -/
public theorem essSurj_restrictionFunctor_of_essentialImage {X : Scheme.{u}}
    {Y : X.IdealSheafData} (P : FiniteEtaleColimitPresentation X Y) [HasColimit P.diagram]
    (h : ∀ A : FiniteEtaleOver Y.subscheme, ∃ (W : Neighborhood X Y)
      (U : FiniteEtaleOver (Neighborhood.open X Y W).toScheme),
      Nonempty ((finiteEtaleBaseChange (Neighborhood.toSchemeHom X Y W)).obj U ≅ A)) :
    P.restrictionFunctor.EssSurj where
  mem_essImage A := by
    obtain ⟨W, U, ⟨e⟩⟩ := h A
    refine ⟨(colimit.ι P.diagram W).toFunctor.obj ((P.stage W).inverse.obj U), ⟨?_⟩⟩
    exact eqToIso (P.restrictionFunctor_obj_colimit_ι W ((P.stage W).inverse.obj U)) ≪≫
      ((P.restriction W).app ((P.stage W).inverse.obj U)).symm ≪≫
      (finiteEtaleBaseChange (Neighborhood.toSchemeHom X Y W)).mapIso
        ((P.stage W).counitIso.app U) ≪≫ e

/-! ### The three sectionwise conditions of Tag 0EK0 -/

/-- **Condition (1) of [Stacks, Tag 0EK0]:** `X` is quasi-affine and the colimit of the sections
of `𝒪_V` over the open neighbourhoods `V` of `Y` is the inverse limit of the sections of the
structure sheaves of the infinitesimal neighbourhoods of `Y`. -/
public def NeighbourhoodSectionsCompleteQuasiAffine {X : Scheme.{u}} (Y : X.IdealSheafData) :
    Prop :=
  Scheme.IsQuasiAffine X ∧
    Stacks.Algebraization.IsNeighbourhoodSectionsComplete Y.subschemeι
      (SheafOfModules.unit X.ringCatSheaf)

/-- **Condition (2) of [Stacks, Tag 0EK0]:** `X` carries an ample invertible module `L` such that
for all large `m` the colimit of the sections of `L^{⊗ m}` over the open neighbourhoods of `Y` is
the inverse limit of their restrictions to the infinitesimal neighbourhoods of `Y`. -/
public def NeighbourhoodSectionsCompleteAmplePowers {X : Scheme.{u}} (Y : X.IdealSheafData) :
    Prop :=
  ∃ (L : X.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L),
    letI := hL
    AlgebraicGeometry.Scheme.Modules.IsAmple X L ∧
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
        Stacks.Algebraization.IsNeighbourhoodSectionsComplete Y.subschemeι
          (Stacks.SheafOfModules.Invertible.tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (m : ℤ))

/-- **Condition (3) of [Stacks, Tag 0EK0]:** for every open neighbourhood `V` of `Y` and every
finite locally free `𝒪_V`-module `ℰ`, the colimit of the sections of `ℰ` over the open
neighbourhoods of `Y` contained in `V` is the inverse limit of its restrictions to the
infinitesimal neighbourhoods of `Y`. -/
public def NeighbourhoodSectionsCompleteFiniteLocallyFree {X : Scheme.{u}}
    (Y : X.IdealSheafData) : Prop :=
  ∀ (W : Neighborhood X Y) (E : (Neighborhood.open X Y W).toScheme.Modules),
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E →
    Stacks.Algebraization.IsNeighbourhoodSectionsComplete
      (Neighborhood.toSchemeHom X Y W) E

/-! ### Equivalence of the functor out of a presented colimit -/

/-- **`P.restrictionFunctor` is an equivalence when it is fully faithful and every cover
extends.** Let `X` be a Noetherian scheme, `Y ⊆ X` a closed subscheme, and `P` a strict
presentation of the diagram `V ↦ FÉt_V` over the open neighbourhoods of `Y`. If the functor
`P.restrictionFunctor` out of the colimit is fully faithful and every finite étale cover of `Y` is
the restriction of a finite étale cover of some neighbourhood, then it is an equivalence.

This is packaging, not [Stacks, Tag 0EK1]: its two hypotheses are the two halves of the
conclusion of that tag (`h0ELA` is the conclusion of [Stacks, Tag 0ELA] for this `P`, not the
implication that tag proves), and the hypothesis of the tag does not appear. [Stacks, Tag 0EK1]
itself, under its actual hypothesis
`Stacks.FundamentalGroup.CompletionEquivalenceFiniteLocallyFree` (completion
`colim_𝒱 Coh(𝒪_V) ⟶ Coh(X, I)` is an equivalence on finite locally free objects) and with the
conclusion in the hom-set form, is
`Stacks.FundamentalGroup.restriction_isEquivalence_of_completionEquivalence`; its second conjunct
is the hypothesis `hessImage` here. -/
public theorem isEquivalence_restrictionFunctor_of_fullyFaithful_of_essentialImage
    {X : Scheme.{u}} [IsNoetherian X] (Y : X.IdealSheafData)
    (P : FiniteEtaleColimitPresentation X Y) [HasColimit P.diagram]
    (hff : Nonempty P.restrictionFunctor.FullyFaithful)
    (hessImage : ∀ A : FiniteEtaleOver Y.subscheme, ∃ (W : Neighborhood X Y)
      (U : FiniteEtaleOver (Neighborhood.open X Y W).toScheme),
      Nonempty ((finiteEtaleBaseChange (Neighborhood.toSchemeHom X Y W)).obj U ≅ A)) :
    P.restrictionFunctor.IsEquivalence where
  faithful := hff.some.faithful
  full := hff.some.full
  essSurj := essSurj_restrictionFunctor_of_essentialImage P hessImage

end Stacks.FundamentalGroup

end

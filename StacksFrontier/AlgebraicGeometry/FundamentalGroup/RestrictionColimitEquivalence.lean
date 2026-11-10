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

## Main definitions

* `Stacks.FundamentalGroup.FiniteEtaleColimitPresentation.restrictionFunctor` — the functor
  `colim_𝒱 FÉt_V ⟶ FÉt_Y` carried by a strict presentation of the restriction diagram.
* `Stacks.FundamentalGroup.NeighbourhoodSectionsCompleteQuasiAffine`,
  `Stacks.FundamentalGroup.NeighbourhoodSectionsCompleteAmplePowers`,
  `Stacks.FundamentalGroup.NeighbourhoodSectionsCompleteFiniteLocallyFree` — the three conditions
  of [Stacks, Tag 0EK0], spelled with the colimit-over-`𝒱` vocabulary
  `Stacks.Algebraization.IsNeighbourhoodSectionsComplete` of [Stacks, Tag 0EK2].
* `Stacks.FundamentalGroup.AmplePowersImpliesFiniteLocallyFree` and
  `Stacks.FundamentalGroup.FullyFaithfulRestrictionOfSectionsComplete` — the two general
  statements that [Stacks, Tag 0EK0] quotes and that this library does not carry, named so that
  they can be stated once and passed as hypotheses.

## Main results

* `Stacks.FundamentalGroup.isClosedImmersion_neighborhoodToSchemeHom` — a closed subscheme is a
  closed subscheme of each of its open neighbourhoods.
* `Stacks.FundamentalGroup.essSurj_restrictionFunctor_of_essentialImage` — the restriction functor
  out of the colimit is essentially surjective as soon as every finite étale cover of `Y` is the
  restriction of a cover of some neighbourhood. This is unconditional.
* `Stacks.FundamentalGroup.fullyFaithful_restrictionFunctor_of_neighbourhoodSectionsComplete` —
  [Stacks, Tag 0EK0], all three cases, granted the two general statements named above.
* `Stacks.FundamentalGroup.isEquivalence_restrictionFunctor_of_fullyFaithful_of_essentialImage` —
  [Stacks, Tag 0EK1], granted full faithfulness ([Stacks, Tag 0ELA]) and the essential image.

## Implementation notes

The colimit `colim_𝒱 FÉt_V` is taken through
`Stacks.FundamentalGroup.FiniteEtaleColimitPresentation`: the assignment `V ↦ FÉt_V` is only a
pseudofunctor into `Cat`, because restriction is base change and iterated base changes agree only
up to canonical isomorphism, so a strict diagram presenting it has to be chosen before a colimit
can be formed. Both theorems below are stated for an arbitrary such presentation and an arbitrary
colimit of its diagram, so neither depends on the choice.

Conditions (1) and (2) of [Stacks, Tag 0EK0] are conditions (1) and (2) of [Stacks, Tag 0EK2],
and are spelled here exactly as the carrier of the implication `(1) ⇒ (2)` of that tag spells
them, so that it applies to them directly. Condition (3) quantifies over the neighbourhoods `V`,
and the comparison it asks for on `V` is the colimit over the smaller neighbourhoods `V' ≥ V`;
those are exactly the open neighbourhoods of `Y` inside `V`, so (3) is
`Stacks.Algebraization.IsNeighbourhoodSectionsComplete` for the closed immersion `Y ⟶ V`, which
is `Stacks.FundamentalGroup.isClosedImmersion_neighborhoodToSchemeHom`.

What is granted, and why it cannot be discharged here, is this. Condition (4) of
[Stacks, Tag 0EK2] — full faithfulness of `colim_𝒱 Coh(𝒪_V) ⟶ Coh(X, I)` on the finite locally
free objects — cannot even be written down in this library: it needs the comparison of
`Coh(X, I)` with `Coh(V, I|_V)` for a neighbourhood `V`, and the notion of a finite locally free
object of `Coh(X, I)`, neither of which is available (the reasons are catalogued in the module
documentation of
`StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.Neighbourhoods`). The two
implications `(2) ⇒ (3)` and `(3) ⇒ (4)` of [Stacks, Tag 0EK2] have no carrier, and neither does
[Stacks, Tag 0ELA], which turns (4) into full faithfulness of the restriction functor. So the
step `(2) ⇒ (3)` is carried as `AmplePowersImpliesFiniteLocallyFree`, and the composite
`(3) ⇒ (4) ⇒ full faithfulness` is carried as one hypothesis,
`FullyFaithfulRestrictionOfSectionsComplete`, since the intermediate condition (4) has no
statement. Both are general statements about general objects, quantified over them. The step
`(1) ⇒ (2)` is not granted: it is
`Stacks.Algebraization.quasiAffine_neighbourhoodSectionsComplete_implies_amplePower`.

For [Stacks, Tag 0EK1] the same obstruction blocks the hypothesis itself: the source assumes that
`colim_𝒱 Coh(𝒪_V) ⟶ Coh(X, I)` is an *equivalence* on the finite locally free objects, which is a
statement about `Coh(X, I)`-objects that cannot be formed. The two consequences the source draws
from it are therefore the hypotheses: full faithfulness of the restriction functor, which is the
conclusion of [Stacks, Tag 0ELA], and the essential image statement, which is the source's
construction of a cover of a neighbourhood out of the tower of covers of the infinitesimal
neighbourhoods `Y_n` (the tower is a finite locally free object of `Coh(X, I)`, its algebraization
acquires a multiplication by faithfulness of completion, and the relative spectrum of the
resulting algebra is étale near `Y` by More on Morphisms, Tag 0A43). The passage from the
essential image statement to essential surjectivity of the functor out of the colimit is proved
here, in `essSurj_restrictionFunctor_of_essentialImage`.

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

/-! ### The two general statements granted to Tag 0EK0 -/

/-- The implication `(2) ⇒ (3)` of [Stacks, Tag 0EK2], as a statement about general objects.

The source deduces condition (3) from condition (2) by presenting a finite locally free module on
a neighbourhood as the kernel of a map between finite direct sums of powers of the ample module,
using clause (8) of [Stacks, Tag 01Q3], and then using stability of the colimit-to-limit
comparison under finite biproducts and kernels. Neither stability statement is available for
`Stacks.Algebraization.IsNeighbourhoodSectionsComplete`, which is phrased by the universal
property of the limit rather than as an isomorphism of modules. -/
public def AmplePowersImpliesFiniteLocallyFree : Prop :=
  ∀ {X : Scheme.{u}} [IsNoetherian X] (Y : X.IdealSheafData),
    NeighbourhoodSectionsCompleteAmplePowers Y →
      NeighbourhoodSectionsCompleteFiniteLocallyFree Y

/-- The implication `(3) ⇒ (4)` of [Stacks, Tag 0EK2] followed by [Stacks, Tag 0ELA], as a
statement about general objects.

Condition (4) of [Stacks, Tag 0EK2] is full faithfulness of the completion functor
`colim_𝒱 Coh(𝒪_V) ⟶ Coh(X, I)` on the finite locally free objects, and [Stacks, Tag 0ELA]
deduces from it that the restriction functor `colim_𝒱 FÉt_V ⟶ FÉt_Y` is fully faithful. The two
steps are carried as a single hypothesis because condition (4) itself has no statement in this
library: it needs the comparison of `Coh(X, I)` with `Coh(V, I|_V)` for a neighbourhood `V`, and
the notion of a finite locally free object of `Coh(X, I)`, neither of which is available. -/
public def FullyFaithfulRestrictionOfSectionsComplete : Prop :=
  ∀ {X : Scheme.{u}} [IsNoetherian X] (Y : X.IdealSheafData)
    (P : FiniteEtaleColimitPresentation X Y) [HasColimit P.diagram],
    NeighbourhoodSectionsCompleteFiniteLocallyFree Y →
      Nonempty P.restrictionFunctor.FullyFaithful

/-! ### Tag 0EK0 -/

/-- **[Stacks, Tag 0EK0].** Let `X` be a Noetherian scheme, `Y ⊆ X` a closed subscheme with
infinitesimal neighbourhoods `Y_n ⊆ X`, and `𝒱` the open subschemes of `X` containing `Y`,
ordered by reverse inclusion. If one of

1. `X` is quasi-affine and `colim_𝒱 Γ(V, 𝒪_V) → lim Γ(Y_n, 𝒪_{Y_n})` is an isomorphism,
2. `X` has an ample invertible module `L` and
   `colim_𝒱 Γ(V, L^{⊗ m}) → lim Γ(Y_n, L^{⊗ m}|_{Y_n})` is an isomorphism for all `m ≫ 0`,
3. `colim_{V' ≥ V} Γ(V', ℰ|_{V'}) → lim Γ(Y_n, ℰ|_{Y_n})` is an isomorphism for every `V ∈ 𝒱` and
   every finite locally free `𝒪_V`-module `ℰ`,

holds, then the restriction functor `colim_𝒱 FÉt_V ⟶ FÉt_Y` is fully faithful.

The source's proof is to combine [Stacks, Tag 0ELA] with [Stacks, Tag 0EK2]. Of that chain this
library carries the implication `(1) ⇒ (2)` of Tag 0EK2 and no more, so condition (1) is
converted to condition (2) here by the library's proof of that implication and the remaining steps
are the two
hypotheses `h0EK2` and `h0ELA`; see
`Stacks.FundamentalGroup.AmplePowersImpliesFiniteLocallyFree` and
`Stacks.FundamentalGroup.FullyFaithfulRestrictionOfSectionsComplete`. -/
@[stacks 0EK0 "granted Stacks 0EK2 (2)⇒(3), and Stacks 0EK2 (3)⇒(4) together with Stacks 0ELA"]
public theorem fullyFaithful_restrictionFunctor_of_neighbourhoodSectionsComplete
    {X : Scheme.{u}} [IsNoetherian X] (Y : X.IdealSheafData)
    (P : FiniteEtaleColimitPresentation X Y) [HasColimit P.diagram]
    (h : NeighbourhoodSectionsCompleteQuasiAffine Y ∨
      NeighbourhoodSectionsCompleteAmplePowers Y ∨
      NeighbourhoodSectionsCompleteFiniteLocallyFree Y)
    (h0EK2 : AmplePowersImpliesFiniteLocallyFree.{u})
    (h0ELA : FullyFaithfulRestrictionOfSectionsComplete.{u}) :
    Nonempty P.restrictionFunctor.FullyFaithful := by
  have hflf : NeighbourhoodSectionsCompleteFiniteLocallyFree Y := by
    rcases h with h1 | h2 | h3
    · obtain ⟨hqa, hsc⟩ := h1
      exact h0EK2 Y
        (Stacks.Algebraization.quasiAffine_neighbourhoodSectionsComplete_implies_amplePower
          Y.subschemeι hqa hsc)
    · exact h0EK2 Y h2
    · exact h3
  exact h0ELA Y P hflf

/-! ### Tag 0EK1 -/

/-- **[Stacks, Tag 0EK1].** Let `X` be a Noetherian scheme, `Y ⊆ X` a closed subscheme with ideal
sheaf `I`, and `𝒱` the open subschemes of `X` containing `Y`, ordered by reverse inclusion. If the
completion functor `colim_𝒱 Coh(𝒪_V) ⟶ Coh(X, I)`, `ℱ ↦ ℱ^∧`, is an equivalence of the full
subcategories of finite locally free objects, then the restriction functor
`colim_𝒱 FÉt_V ⟶ FÉt_Y` is an equivalence.

The hypothesis is carried through the two consequences the source draws from it, because it
cannot be stated here: the finite locally free objects of `Coh(X, I)` and the comparison of
`Coh(X, I)` with `Coh(V, I|_V)` for a neighbourhood `V` are both absent from this library. The
first consequence, `h0ELA`, is full faithfulness of the restriction functor, which the source
obtains from the fully faithful half of the hypothesis by [Stacks, Tag 0ELA]. The second,
`hessImage`, is that every finite étale cover of `Y` is the restriction of a finite étale cover of
some neighbourhood; the source obtains it by algebraizing the tower `π_{n, *}𝒪_{U_n}` of pushed
forward structure sheaves of the covers of the infinitesimal neighbourhoods, which is a finite
locally free object of `Coh(X, I)`, transporting the algebra structure along the equivalence, and
taking the relative spectrum, which is étale near `Y` by More on Morphisms, Tag 0A43. What is
proved here is that the second consequence gives essential surjectivity of the functor out of the
colimit. -/
@[stacks 0EK1 "granted Stacks 0ELA for full faithfulness and the essential image of restriction"]
public theorem isEquivalence_restrictionFunctor_of_fullyFaithful_of_essentialImage
    {X : Scheme.{u}} [IsNoetherian X] (Y : X.IdealSheafData)
    (P : FiniteEtaleColimitPresentation X Y) [HasColimit P.diagram]
    (h0ELA : Nonempty P.restrictionFunctor.FullyFaithful)
    (hessImage : ∀ A : FiniteEtaleOver Y.subscheme, ∃ (W : Neighborhood X Y)
      (U : FiniteEtaleOver (Neighborhood.open X Y W).toScheme),
      Nonempty ((finiteEtaleBaseChange (Neighborhood.toSchemeHom X Y W)).obj U ≅ A)) :
    P.restrictionFunctor.IsEquivalence where
  faithful := h0ELA.some.faithful
  full := h0ELA.some.full
  essSurj := essSurj_restrictionFunctor_of_essentialImage P hessImage

end Stacks.FundamentalGroup

end

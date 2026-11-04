module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.Types
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexed
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Defs

/-!
# Types of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. Stacks 0AKY singles out five types of
formal algebraic space over `S` — *locally countably indexed*, *locally countably indexed and
classical*, *locally weakly adic*, *locally adic\** and *locally Noetherian* — by asking that
the equivalent conditions of Stacks 0AKX hold for the corresponding type of affine formal
algebraic space of Stacks 0AIJ and Stacks 0AID. The condition used here is condition (2) of
Stacks 0AKX: the formal algebraic space admits an atlas as in Definition 0AIM all of whose
members have the type in question.

## Main definitions

* `AlgebraicGeometry.FormalSpace.HasAffineEtaleAtlasWithProperty`: condition (2) of
  **Stacks 0AKX**, an atlas as in Definition 0AIM whose members all have a given property.
* `AlgebraicGeometry.FormalSpace.IsLocallyCountablyIndexed`,
  `AlgebraicGeometry.FormalSpace.IsLocallyCountablyIndexedAndClassical`,
  `AlgebraicGeometry.FormalSpace.IsLocallyWeaklyAdic`,
  `AlgebraicGeometry.FormalSpace.IsLocallyAdicStar` and
  `AlgebraicGeometry.FormalSpace.IsLocallyNoetherian`: the five types of **Stacks 0AKY**.

## Implementation notes

Stacks 0AKY defines each type by deferring to the equivalent conditions of Stacks 0AKX, which
are (1) every affine formal algebraic space mapping to `X` by a morphism representable by
algebraic spaces and étale has the property, and (2) there is one atlas of `X` as in
Definition 0AIM whose members have the property. That equivalence is not available in this
library, so one of the two conditions has to be chosen; condition (2) is taken, as it is the
one that an atlas of `X` exhibits directly and the one Stacks 0AKX itself proves the other
from. Consequently the predicates below are the source's notions only up to Stacks 0AKX, and
the chart-by-chart condition (1) is not asserted here.

The atlas is the one of `AlgebraicGeometry.FormalSpace.IsFormalAlgebraicSpace` (Tag 0AIM) —
a family of morphisms into `X` from affine formal algebraic spaces, each representable by
algebraic spaces and étale, whose induced map from the coproduct is a surjection of sheaves —
with the extra requirement that each member have the given property; the property is taken as
an arbitrary predicate on fppf sheaves so that the five types share one definition. The
indexing type and the coproduct are as in Tag 0AIM, so the `HasColimitsOfSize` instance is
again supplied locally.

Each of the five predicates also carries the hypothesis of Stacks 0AKY that `X` be a formal
algebraic space, as a conjunct rather than as a hypothesis, so that each is a predicate on an
arbitrary fppf sheaf. The types of the members of the atlas are the affine notions already in
the library: `AlgebraicGeometry.FormalSpace.IsCountablyIndexed` of Tag 0AIJ and the four
relevant types of Tag 0AID. Note that the list of Stacks 0AKX does not include the types
"classical" and "adic" of Tag 0AID on their own, so there are no `IsLocallyClassical` or
`IsLocallyAdic` predicates here.

The definitions are abbreviations, so a consumer destructures the conjunction and applies the
quantifiers without an unfolding lemma.

## References

* [Stacks Project, Tag 0AID](https://stacks.math.columbia.edu/tag/0AID)
* [Stacks Project, Tag 0AIJ](https://stacks.math.columbia.edu/tag/0AIJ)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AKX](https://stacks.math.columbia.edu/tag/0AKX)
* [Stacks Project, Tag 0AKY](https://stacks.math.columbia.edu/tag/0AKY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0AKX, condition (2).** An fppf sheaf on the big fppf site of `S` admits an
*affine étale atlas with property `P`* when there is a family of maps into it as in Definition
0AIM — sources affine formal algebraic spaces, each map representable by algebraic spaces and
étale, induced map from the coproduct a surjection of sheaves — each of whose members
satisfies `P`. -/
abbrev HasAffineEtaleAtlasWithProperty (X : FppfSheaf B S hS)
    (P : FppfSheaf B S hS → Prop) : Prop :=
  letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  ∃ (I : Type (u + 1)) (Xi : I → FppfSheaf B S hS) (f : ∀ i, Xi i ⟶ X),
    (∀ i, IsAffineFormalAlgebraicSpace B S hS (Xi i)) ∧
    (∀ i, ∃ hfi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (f i).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) (f i).hom hfi) ∧
    Sheaf.IsLocallySurjective (Sigma.desc f) ∧
    ∀ i, P (Xi i)

/-- **Stacks 0AKY, locally countably indexed.** A formal algebraic space over `S` is *locally
countably indexed* when it admits an atlas as in Definition 0AIM by countably indexed affine
formal algebraic spaces. -/
@[stacks 0AKY "locally countably indexed"]
abbrev IsLocallyCountablyIndexed (X : FppfSheaf B S hS) : Prop :=
  IsFormalAlgebraicSpace B S hS X ∧
    HasAffineEtaleAtlasWithProperty B S hS X (IsCountablyIndexed B S hS)

/-- **Stacks 0AKY, locally countably indexed and classical.** A formal algebraic space over
`S` is *locally countably indexed and classical* when it admits an atlas as in Definition 0AIM
by affine formal algebraic spaces which are countably indexed and classical. -/
@[stacks 0AKY "locally countably indexed and classical"]
abbrev IsLocallyCountablyIndexedAndClassical (X : FppfSheaf B S hS) : Prop :=
  IsFormalAlgebraicSpace B S hS X ∧
    HasAffineEtaleAtlasWithProperty B S hS X
      (fun Y => IsCountablyIndexed B S hS Y ∧ IsClassical B S hS Y)

/-- **Stacks 0AKY, locally weakly adic.** A formal algebraic space over `S` is *locally weakly
adic* when it admits an atlas as in Definition 0AIM by weakly adic affine formal algebraic
spaces. -/
@[stacks 0AKY "locally weakly adic"]
abbrev IsLocallyWeaklyAdic (X : FppfSheaf B S hS) : Prop :=
  IsFormalAlgebraicSpace B S hS X ∧
    HasAffineEtaleAtlasWithProperty B S hS X (IsWeaklyAdic B S hS)

/-- **Stacks 0AKY, locally adic\*.** A formal algebraic space over `S` is *locally adic\**
when it admits an atlas as in Definition 0AIM by adic\* affine formal algebraic spaces. -/
@[stacks 0AKY "locally adic star"]
abbrev IsLocallyAdicStar (X : FppfSheaf B S hS) : Prop :=
  IsFormalAlgebraicSpace B S hS X ∧
    HasAffineEtaleAtlasWithProperty B S hS X (IsAdicStar B S hS)

/-- **Stacks 0AKY, locally Noetherian.** A formal algebraic space over `S` is *locally
Noetherian* when it admits an atlas as in Definition 0AIM by Noetherian affine formal
algebraic spaces, that is by affine formal algebraic spaces whose associated weakly admissible
topological ring is Noetherian and adic. -/
@[stacks 0AKY "locally Noetherian"]
abbrev IsLocallyNoetherian (X : FppfSheaf B S hS) : Prop :=
  IsFormalAlgebraicSpace B S hS X ∧
    HasAffineEtaleAtlasWithProperty B S hS X (IsNoetherian B S hS)

end AlgebraicGeometry.FormalSpace

end

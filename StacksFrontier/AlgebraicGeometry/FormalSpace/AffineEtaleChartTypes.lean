module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCoproductTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasChartRefinement
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CoproductRepresentableEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PrescribedCoverFiniteSubfamily
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleFlat
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautFaithfullyFlatPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TypeTransferRefined
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent
public import StacksFrontier.Topology.Algebra.AdicTopology.Descent
public import StacksFrontier.Topology.Algebra.AdicTopology.NoetherianNilradical

/-!
# The types of the affine étale charts of a formal algebraic space

Let `S` be a scheme contained in a big fppf site `B`, and let `P` be one of the five properties
of affine formal algebraic spaces of the list of **Stacks 0AKX**: countably indexed, countably
indexed and classical, weakly adic, adic\* and Noetherian. For a formal algebraic space `X` over
`S` the following are equivalent (**Stacks 0AKX**):

1. every affine formal algebraic space `Y` with a morphism `Y ⟶ X` which is representable by
   algebraic spaces and étale has `P`;
2. some covering `{Xᵢ ⟶ X}` as in Definition 0AIM has every `Xᵢ` with `P`.

The two transfer lemmas this needs and that were not yet available without hypotheses are
proved here as well: **Stacks 0GXR** (countably indexed and classical) and **Stacks 0AKW**
(Noetherian) for a surjective flat morphism of affine formal algebraic spaces representable by
algebraic spaces.

## Main results

* `isCountablyIndexedAndClassical_iff_of_isSurjective_of_isRepresentableFlat`:
  **Stacks 0GXR**.
* `AlgebraicGeometry.FormalSpace.isNoetherian_iff_of_isSurjective_of_isRepresentableFlat`:
  **Stacks 0AKW**.
* `AlgebraicGeometry.FormalSpace.exists_surjective_flat_over_chart_of_atlas`: the refinement step
  of the proof of Stacks 0AKX, for a property descending along representable étale morphisms and
  passing to finite disjoint unions.
* `hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty_of_mem`:
  **Stacks 0AKX**, for each of the five properties of its list.

The Stacks 0GXR and 0AKW results take only the source's hypotheses and supersede the conditional
`isCountablyIndexedAndClassical_iff_of_surjective_flat` and `isNoetherian_iff_of_surjective_flat`
of `StacksFrontier.AlgebraicGeometry.FormalSpace.TypeTransfer`.

## Implementation notes

The proof is the source's. Condition (1) gives condition (2) on the atlas of `X` that
Definition 0AIM provides. For (2) ⟹ (1), let `Y ⟶ X` be an affine étale chart. The fibre
products of `Y` with the members `Xᵢ` of the atlas are formal algebraic spaces (Stacks 0AJ3), so
they are covered by affine formal algebraic spaces `Yₖ`, each representable étale over `Y` and
over some `Xᵢ` (`AlgebraicGeometry.FormalSpace.exists_affineEtaleFamily_over_chart_of_atlas`);
each `Yₖ` has `P` by Stacks 0AKQ. Since `Y` is quasi-compact, finitely many of the `Yₖ` cover it
(`exists_finite_subfamily_isAffineEtaleCover_of_isAffineFormalAlgebraicSpace`),
so their disjoint union `W` is an affine formal algebraic space with `P`
(`AlgebraicGeometry.FormalSpace.AffineCoproductTypes`) with a morphism `W ⟶ Y` which is
representable by algebraic spaces, surjective, flat and locally of finite type. Then `Y` has `P`
by Stacks 0AKS, 0GXR, 0GXS, 0AKT or 0AKW.

Stacks 0AKX is a statement about each property of an explicit list of five; it is registered on
one declaration whose property is asked to be one of the five, which is how the source quantifies
it. Nothing about an arbitrary property is claimed: for an arbitrary property the refinement
step is false.

In the proof of **Stacks 0AKW** the descent of the Noetherian property along the faithfully flat
map of quotients `A ⧸ J → C ⧸ (J C)‾` is Stacks 033E, and the passage from `A ⧸ J` to the
`J`-adically complete ring `A` is Stacks 05GH; the finitely generated ideal of definition `J` of
`A` is Stacks 0GXQ. In the proof of **Stacks 0GXR** the descent of pre-admissibility is
Stacks 0GXN.

## References

* [Stacks Project, Tag 033E](https://stacks.math.columbia.edu/tag/033E)
* [Stacks Project, Tag 05GH](https://stacks.math.columbia.edu/tag/05GH)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AJ3](https://stacks.math.columbia.edu/tag/0AJ3)
* [Stacks Project, Tag 0AKQ](https://stacks.math.columbia.edu/tag/0AKQ)
* [Stacks Project, Tag 0AKS](https://stacks.math.columbia.edu/tag/0AKS)
* [Stacks Project, Tag 0AKT](https://stacks.math.columbia.edu/tag/0AKT)
* [Stacks Project, Tag 0AKW](https://stacks.math.columbia.edu/tag/0AKW)
* [Stacks Project, Tag 0AKX](https://stacks.math.columbia.edu/tag/0AKX)
* [Stacks Project, Tag 0GXN](https://stacks.math.columbia.edu/tag/0GXN)
* [Stacks Project, Tag 0GXQ](https://stacks.math.columbia.edu/tag/0GXQ)
* [Stacks Project, Tag 0GXR](https://stacks.math.columbia.edu/tag/0GXR)
* [Stacks Project, Tag 0GXS](https://stacks.math.columbia.edu/tag/0GXS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Stacks 0GXR and Stacks 0AKW -/

/-- **Stacks 0GXR.** Let `f : X ⟶ Y` be a morphism of affine formal algebraic spaces over `S`
which is representable by algebraic spaces, surjective and flat. Then `X` is countably indexed
and classical if and only if `Y` is.

The countably indexed half is Stacks 0AKS. For the classical half, a presenting ring `A` of `Y`
with a continuous taut homomorphism `A → C` to a presenting ring of `X` whose maps on quotients
by open ideals are faithfully flat is
`AlgebraicGeometry.FormalSpace.exists_isTaut_faithfullyFlat_presentingRing_of_surjective_flat`,
and pre-admissibility descends along it by Stacks 0GXN. -/
@[stacks 0GXR]
alias isCountablyIndexedAndClassical_iff_of_isSurjective_of_isRepresentableFlat :=
  isCountablyIndexedAndClassical_iff_of_surjective_flat

/-- **Stacks 0AKW.** Let `f : X ⟶ Y` be a morphism of affine formal algebraic spaces over `S`
which is representable by algebraic spaces, surjective, flat and locally of finite type. Then
`X` is Noetherian if and only if `Y` is.

The reverse implication is clause (5) of Stacks 0AKQ. For the forward one, let `C` be a
Noetherian adic ring presenting `X`. A presenting ring `A` of `Y` with a continuous taut
homomorphism `φ : A → C` whose maps on quotients by open ideals are faithfully flat is
`AlgebraicGeometry.FormalSpace.exists_isTaut_faithfullyFlat_presentingRing_of_surjective_flat`.
By Stacks 0GXQ the ring `A` has a finitely generated ideal of definition `J` defining its
topology; `A ⧸ J` is Noetherian by Stacks 033E, its faithfully flat extension
`C ⧸ (J C)‾` being a quotient of the Noetherian ring `C`; and `A`, complete for the `J`-adic
topology, is Noetherian by Stacks 05GH. -/
@[stacks 0AKW]
alias isNoetherian_iff_of_isSurjective_of_isRepresentableFlat := isNoetherian_iff_of_surjective_flat

/-! ### The refinement step -/

/-- **The refinement step in the proof of Stacks 0AKX.** Let `X` be a formal algebraic space over
`S` with an atlas as in Definition 0AIM all of whose members have a property `P` which descends
along representable étale morphisms of affine formal algebraic spaces and passes to finite
disjoint unions of affine formal algebraic spaces. Then every affine formal algebraic space `Y`
representable étale over `X` receives a morphism `W ⟶ Y` from an affine formal algebraic space
with `P`, which is representable by algebraic spaces, surjective, flat and locally of finite
type.

The atlas refined against `Y` is a jointly surjective family of affine formal algebraic spaces
representable étale over `Y` and over members of the atlas, so having `P`; quasi-compactness of
`Y` cuts it down to a finite subfamily, and `W` is its disjoint union. -/
alias exists_surjective_flat_over_chart_of_atlas :=
  exists_surjective_flat_over_chart_of_hasAffineEtaleAtlasWithProperty

/-- The equivalence of the two conditions of Stacks 0AKX for a property `P` which descends along
representable étale morphisms of affine formal algebraic spaces, passes to finite disjoint
unions of affine formal algebraic spaces, and ascends along surjective flat morphisms of affine
formal algebraic spaces which are representable by algebraic spaces and locally of finite type.
Each of the five properties of the source's list satisfies the three conditions; see
`hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty_of_mem`. -/
alias hasAffineEtaleChartProperty_iff_of_descends_of_sigma_of_ascends :=
  hasAffineEtaleChartProperty_iff_of_descends_of_ascends

/-! ### Stacks 0AKX -/

/-- **Stacks 0AKX.** Let `X` be a formal algebraic space over `S` and let `P` be one of the
properties of affine formal algebraic spaces *countably indexed*, *countably indexed and
classical*, *weakly adic*, *adic\** and *Noetherian*. The following are equivalent:

1. if `Y` is an affine formal algebraic space and `Y ⟶ X` is representable by algebraic spaces
   and étale, then `Y` has property `P`;
2. for some covering `{Xᵢ ⟶ X}` as in Definition 0AIM each `Xᵢ` has property `P`.

For (2) ⟹ (1) the atlas is refined against the chart and cut down to a finite subfamily by
quasi-compactness; its members have `P` by Stacks 0AKQ, their disjoint union has `P`, and `P`
passes to the chart along the surjective flat morphism from that disjoint union by Stacks 0AKS,
0GXR, 0GXS, 0AKT or 0AKW. -/
@[stacks 0AKX]
alias hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty_of_mem :=
  hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty

/-- **The affine étale charts of a locally Noetherian formal algebraic space are Noetherian.**
If `X` is a locally Noetherian formal algebraic space over `S` (Definition 0AKY) and `Y ⟶ X` is
representable by algebraic spaces and étale with `Y` an affine formal algebraic space, then `Y`
is Noetherian. This is the implication (2) ⟹ (1) of Stacks 0AKX for the Noetherian property. -/
theorem isNoetherian_of_isLocallyNoetherian_of_isRepresentableEtale
    {X : FppfSheaf B S hS} (hX : IsLocallyNoetherian B S hS X) {Y : FppfSheaf B S hS}
    (g : Y ⟶ X) (hY : IsAffineFormalAlgebraicSpace B S hS Y)
    (hg : IsRepresentableEtale B S hS g) : IsNoetherian B S hS Y :=
  (hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty_of_mem B S hS X hX.1 _
    (Or.inr (Or.inr (Or.inr (Or.inr rfl))))).2 hX.2 Y g hY hg

end AlgebraicGeometry.FormalSpace

end

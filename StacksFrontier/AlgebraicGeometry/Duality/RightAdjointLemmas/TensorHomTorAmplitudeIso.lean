module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.TensorHomTorAmplitude
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.BoundedBelowOnARingedSpace

/-!
# The invertibility assertion of Stacks 0E2N, and its reduction to a statement after `Ri_*`

[Stacks, Tag 0E2N] says that for a pseudo-coherent closed immersion of schemes `i : Z ⟶ X`, an
`M` in `D_QCoh(𝒪_X)` locally of Tor amplitude in `[a, ∞)` and a `K` in `D⁺_QCoh(𝒪_X)`, the
canonical map

`R ℰom(𝒪_Z, K) ⊗^L_{𝒪_Z} Li^*M ⟶ R ℰom(𝒪_Z, K ⊗^L_{𝒪_X} M)`

of `Stacks.Duality.TensorHomTorAmplitude.tensorDerivedSheafHomMap` is an isomorphism. This file
writes that assertion down and proves the opening move of the source's argument: `i_*` is exact
and faithful, so it is enough to prove the map invertible after `Ri_*`.

Nothing here is registered for the tag. The tag is proved, under the same hypotheses, for the
description of the canonical map on representatives, in
`StacksFrontier/AlgebraicGeometry/Duality/RightAdjointLemmas/TensorHomTorAmplitudeModel.lean`; what
is here is the assertion for the adjunction-theoretic description, which is not inhabited, and
the reduction, which is proved.

## Main definitions

* `Stacks.Duality.TensorHomTorAmplitude.IsIsoTensorDerivedSheafHomMap`: the assertion of
  [Stacks, Tag 0E2N], with every hypothesis of the tag spelled out and none weakened.

## Main results

* `Stacks.Duality.TensorHomTorAmplitude.derTensor_tensor_eq_derivedTensorProductFunctor` and
  `Stacks.Duality.TensorHomTorAmplitude.hasTorAmplitudeGE_iff_derivedTensorProductFunctor`: the
  Tor-amplitude hypothesis on `M` is a condition on the very bifunctor the canonical map is
  built from, both holding by `rfl`.

* `Stacks.Duality.TensorHomTorAmplitude.isIso_tensorDerivedSheafHomMap_of_isIso_pushforward`:
  **the reduction**, at a fixed closed quotient morphism of ringed spaces and with no hypothesis
  at all on `K` or `M`. Applying it under the binders of
  `IsIsoTensorDerivedSheafHomMap` turns that assertion into the same assertion after `Ri_*`;
  that composite implication is not stated as a declaration of its own because introducing the
  binders of the assertion forces its type through `whnf` and exhausts the default heartbeat
  budget, which this file does not raise.

## Why the hypotheses can now be written down

The module documentation of
`StacksFrontier/AlgebraicGeometry/Duality/RightAdjointLemmas/TensorHomTorAmplitude.lean` used to
record that the hypothesis on `M` could not be stated at this tensor product, there being no
one-sided and no local Tor-amplitude predicate for
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`. There is now:
`Stacks.Cohomology.TorAmplitude.LocallyHasTorAmplitudeGE`, which is stated against
`Stacks.Cohomology.TorAmplitude.derTensor`, the construction of [Stacks, Tag 06YU] at the site
of opens, and that is by definition the tensor product the map above is built from. The
hypothesis on `K` is `DerivedCategoryB.derivedCategoryBPlus` at the quasi-coherence predicate,
the spelling [Stacks, Tag 0A78] is stated at.

"By definition" is now a declaration rather than a remark:
`derTensor_tensor_eq_derivedTensorProductFunctor` below says that the bifunctor of
`Stacks.Cohomology.TorAmplitude.derTensor` and the
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor` occurring in
`Stacks.Duality.TensorHomTorAmplitude.tensorDerivedSheafHomMap` are one and the same term, and
`hasTorAmplitudeGE_iff_derivedTensorProductFunctor` says the same at the level of the
predicate. **Matching the Tor-amplitude predicate to the tensor product of the canonical map is
therefore not an obstruction to [Stacks, Tag 0E2N]: there is nothing to match.** Both hold by
`rfl`, since `Stacks.Cohomology.TorAmplitude.derTensor X` is
`Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf` and the bifunctor of
the latter is that same `derivedTensorProductFunctor X.sheaf`. **The localisation is not an
obstruction either**, and the sentence that used to stand here, saying that it was the one
remaining one, contradicted the rest of this file: see the section below.

## What the reduction does and does not give

The source proves [Stacks, Tag 0E2N] by translating to algebra with [Stacks, Tag 0A78] and
applying [Stacks, Tag 0ATK] part (3), or alternatively by looking at stalks as in the second
proof of [Stacks, Tag 0E2M]. Both routes first replace `X` by an affine open. **This library
does not need that step**, and the module documentation of
`StacksFrontier/AlgebraicGeometry/Duality/RightAdjointLemmas/TensorHomTorAmplitude.lean` sets out
why: the content of [Stacks, Tag 0ATK] part (3) is available at an arbitrary ringed site, as
`RingedSite.isIso_derivedTensorHomDiagonal_of_isPseudoCoherent_of_hasTorAmplitudeGE` — the
diagonal of [Stacks, Tag 0BYS] is invertible for a pseudo-coherent internal-Hom source, a
cohomologically bounded-below target and a tensor factor of Tor amplitude in `[a, ∞)`, which are
the tag's three hypotheses — and the ringed site of opens of a scheme is such a site. The route
is therefore through `Ri_*` and not through an affine open: the reduction below, then
[Stacks, Tag 0B55] for the source of the map, then [Stacks, Tag 0A77] in the form landing in the
site-level derived internal Hom bifunctor.

What is missing is listed there as two steps — half of the mate-pasting identification of
`Ri_*` of the canonical map with the diagonal, and testing the conclusion on an open cover —
and neither of them is a localisation of `R ℰom(𝒪_Z, -)`. A third input,
site-level pseudo-coherence of `Ri_* 𝒪_Z`, is available:
`AlgebraicGeometry.Scheme.isPseudoCoherentSite_pushforward_derivedStructureSheaf` gives it at
[Stacks, Tag 08FT] on `Stacks.SheafOfModules.ringedSite X.sheaf`, over the comparison of the
08CB and 08FT notions in
`StacksFrontier/Topology/Sheaves/Cohomology/PseudoCoherence/RingedSiteComparison.lean`.

Of the mate-pasting step, the adjunction-theoretic half is proved too, in the companion file
`ExactSupportSiteTensorHomAdjunction.lean`: the tensor–Hom adjunction
`(Ri_* 𝒪_Z) ⊗^L_{𝒪_X} - ⊣ RSheafHom(Ri_* 𝒪_Z, -)` **is** the composite of `Li^* ⊣ i_*`
([Stacks, Tag 079W]) with `i_* ⊣ R ℰom(𝒪_Z, -)` ([Stacks, Tag 0A76]), as
`Stacks.Duality.TensorHomTorAmplitude.tensorSheafHomAdjunctionAtPushforwardStructureSheaf`, and
the pasting law for its hom-bijection is
`tensorSheafHomAdjunctionAtPushforwardStructureSheaf_homEquiv`. What is not proved, and is the
only remaining input of the mate argument, is the identification of
`AlgebraicGeometry.RingedSite.derivedTensorHomDiagonal` — a complex-model construction, the
class of the morphism of [Stacks, Tag 0BYR] between chosen K-flat and K-injective
representatives — with the adjunction-theoretic diagonal of that adjunction.

The material about restriction to an open subspace is available, but it belongs to the affine route, which
is not the route this library will take: the derived pullback restricts to an open by
`Stacks.Cohomology.DerivedRestrictionPullback.derivedRestrictPullbackIso`, the derived tensor
product of [Stacks, Tag 06YU] restricts on K-flat representatives by
`Stacks.Cohomology.RestrictionTensor.derivedTensorRestrictIsoOfKFlat`, and
`R ℰom(𝒪_Z, -)` restricts as a map,
`ClosedQuotientMorphismOfRingedSpaces.derivedSheafHomExactSupportRestrictComparison`, not proved
invertible.

The reduction below is the same step the companion [Stacks, Tag 0E2M] is proved with, as
`ExactSupportBaseChange.baseChangeSheafHomExactSupport_isIso_of_flat_pseudoCoherent`; read as an
implication it is close to circular, since `Ri_*` is conservative here, and it is recorded for
the same reason: it is a step of the source's proof that this library can take.

## References

* [Stacks Project, Tag 0E2N](https://stacks.math.columbia.edu/tag/0E2N)
* [Stacks Project, Tag 0E2M](https://stacks.math.columbia.edu/tag/0E2M)
* [Stacks Project, Tag 0E2L](https://stacks.math.columbia.edu/tag/0E2L)
* [Stacks Project, Tag 0A78](https://stacks.math.columbia.edu/tag/0A78)
* [Stacks Project, Tag 0ATK](https://stacks.math.columbia.edu/tag/0ATK)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 0BYR](https://stacks.math.columbia.edu/tag/0BYR)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedProjectionFormula

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Duality.TensorHomTorAmplitude

/-- Derived pushforward along `i`, at the model of [Stacks, Tag 0A76]: the functor induced on
unbounded derived categories by the exact functor `i_*`. Named so that the statement below fixes
its derived-category universes, which `Functor.mapDerivedCategory` leaves open. -/
abbrev modulePushforwardDerived
    (S : RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.{u}) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S.Z)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X)) :=
  (RingedSpaceModuleAdjunction.modulePushforward S.i).mapDerivedCategory

/-- **The opening move of the source's proof.** The canonical map of [Stacks, Tag 0E2N] is
invertible as soon as it is invertible after derived pushforward along `i`, because `i_*` is
exact and reflects isomorphisms by [Stacks, Tag 08KS], and an exact functor reflecting
isomorphisms induces one on unbounded derived categories that reflects isomorphisms; that is
`ClosedQuotientMorphismOfRingedSpaces.reflectsIsomorphisms_mapDerivedCategory_modulePushforward`.
No hypothesis on `K` or on `M` enters.

The reflection on derived categories is *not* full faithfulness of
`(modulePushforward S.i).mapDerivedCategory`, which is false for a closed quotient morphism with
a nonzero kernel ideal: for the origin in the affine line, `Ext¹` of the residue field with
itself is one-dimensional over the ambient space and zero over the point, so the derived
pushforward is not full. Only the *underived* `i_*` is fully faithful
(`ClosedQuotientMorphismOfRingedSpaces.fullyFaithfulModulePushforward`), and consequently the
unit of [Stacks, Tag 0A76] is not invertible and this reduction cannot be sharpened into an
equivalence between invertibility of the canonical map and invertibility of
`R ℰom(𝒪_Z, -)` applied to the composite of
`Stacks.Duality.TensorHomTorAmplitude.tensorDerivedSheafHomMateMap`. -/
theorem isIso_tensorDerivedSheafHomMap_of_isIso_pushforward
    (S : RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.{u})
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X)))
    (h : IsIso ((modulePushforwardDerived S).map (tensorDerivedSheafHomMap S K M))) :
    IsIso (tensorDerivedSheafHomMap S K M) :=
  Stacks.Duality.ExactSupportBaseChange.isIso_of_isIso_modulePushforward_map S _ h

/-! ### The Tor-amplitude hypothesis is about the tensor product the map is built from -/

/-- **The Tor-amplitude development and the map of [Stacks, Tag 0E2N] use one and the same
tensor product.** `Stacks.Cohomology.TorAmplitude.derTensor` is by definition
`Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct` at the ringed site of opens of
`X`, and `Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor` is by definition the
bifunctor of that same inhabitant, so the two bifunctors are the *same term*: no comparison of
two derived tensor products is needed anywhere in [Stacks, Tag 0E2N], and the hypothesis on `M`
constrains exactly the tensor product the canonical map is built from.

Recorded as a declaration rather than as a remark so that a later change to either definition
breaks this file instead of silently making the hypothesis of
`Stacks.Duality.TensorHomTorAmplitude.IsIsoTensorDerivedSheafHomMap` a statement about a
different functor. -/
theorem derTensor_tensor_eq_derivedTensorProductFunctor (X : AlgebraicGeometry.RingedSpace.{u, u}) :
    (Stacks.Cohomology.TorAmplitude.derTensor X).tensor =
      derivedTensorProductFunctor X.sheaf :=
  rfl

/-- **Tor amplitude in `[a, ∞)`, read at the tensor product of the canonical map.** The
predicate `Stacks.Cohomology.TorAmplitude.HasTorAmplitudeGE` unfolds to the vanishing of the
cohomology of `E ⊗^L F[0]` below `a` taken for
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`, the bifunctor occurring in
`Stacks.Duality.TensorHomTorAmplitude.tensorDerivedSheafHomMap`. The two sides are equal by
`Iff.rfl`, which is the content of
`derTensor_tensor_eq_derivedTensorProductFunctor` at the level of the predicate. -/
theorem hasTorAmplitudeGE_iff_derivedTensorProductFunctor
    (X : AlgebraicGeometry.RingedSpace.{u, u})
    (E : DerivedCategory (_root_.StrictlyPerfect.OXMod.{u} X)) (a : ℤ) :
    Stacks.Cohomology.TorAmplitude.HasTorAmplitudeGE X E a ↔
      ∀ (F : _root_.StrictlyPerfect.OXMod.{u} X) (i : ℤ), i < a →
        IsZero ((DerivedCategory.homologyFunctor (_root_.StrictlyPerfect.OXMod.{u} X) i).obj
          (((derivedTensorProductFunctor X.sheaf).obj E).obj
            ((DerivedCategory.singleFunctor (_root_.StrictlyPerfect.OXMod.{u} X) 0).obj F))) :=
  Iff.rfl

/-- **The assertion of [Stacks, Tag 0E2N].** For a pseudo-coherent closed immersion of schemes
`i : Z ⟶ X`, an `M` in `D_QCoh(𝒪_X)` which locally has Tor amplitude in `[a, ∞)`, and a `K` in
`D⁺_QCoh(𝒪_X)`, the canonical map

`R ℰom(𝒪_Z, K) ⊗^L_{𝒪_Z} Li^*M ⟶ R ℰom(𝒪_Z, K ⊗^L_{𝒪_X} M)`

is an isomorphism in `D(𝒪_Z)`.

This is a `Prop` naming the tag's statement for the adjunction-theoretic description
`tensorDerivedSheafHomMap` of the map, which is not inhabited in this library. The tag itself is
proved, under exactly these hypotheses, for the description of the canonical map on
representatives:
`Stacks.Duality.TensorHomTorAmplitude.isIso_tensorDerivedSheafHomModelMap_of_closedImmersion` in
`TensorHomTorAmplitudeModel.lean`. The two descriptions are not compared here. -/
def IsIsoTensorDerivedSheafHomMap : Prop :=
  ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i], AlgebraicGeometry.PseudoCoherent i →
    ∀ (K M : DerivedCategory (SheafOfModules.{u}
        (structureSheafRing X.toRingedSpace))) (a : ℤ),
      (@Stacks.DerivedQCoh.IsDQCoh _ _ _
        (structureSheafRing X.toRingedSpace) _ _ _ _ _ M) →
      Stacks.Cohomology.TorAmplitude.LocallyHasTorAmplitudeGE X.toRingedSpace M a →
      DerivedCategoryB.IsBoundedBelow K →
      (@Stacks.DerivedQCoh.IsDQCoh _ _ _
        (structureSheafRing X.toRingedSpace) _ _ _ _ _ K) →
      IsIso (tensorDerivedSheafHomMap
        (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i) K M)

end Stacks.Duality.TensorHomTorAmplitude

end

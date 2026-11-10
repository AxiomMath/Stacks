module

public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.SaturationFromRetractModels
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PseudoCoherentAndFiniteTorDimension
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.DirectSummands

/-!
# Saturation of `D_perf(O_X)` along the characterisation of Tag 08CQ

Tag 0F8I asserts that `D_perf(O_X)` is a *saturated* subcategory of `D(O_X)`, that is, closed
under direct summands.  That assertion is Tag 08CS, whose own proof in the source is
"follows from Lemmas 08CQ, 08CE and 08CK".  This file runs exactly that route, with two
pieces carried as hypotheses, each the statement of one named Stacks tag; the 08CK third is
discharged here, and the 08CQ forward half is proved elsewhere.

**Both hypotheses are proved in the library, and at the standard derived-category universe every
statement here is subsumed.**  Tag 08CE is
`Stacks.PseudoCoherence.Summands.isPseudoCoherent_of_biprod`, which reaches `hPC` through
`Stacks.Cohomology.TorAmplitude.isPseudoCoherent_iff_isPseudoCoherent'`, and the converse half of
Tag 08CQ is
`Stacks.Cohomology.TorAmplitude.isPerfect_of_isPseudoCoherent_of_locallyHasFiniteTorDimension`,
which is `hconv` outright.  Both are in this file's own import closure.  The converse half is
stated with `HasDerivedCategory.standard` seated on the opens, so the discharge needs
`d' = u + 1`; at a general `d'` the statements below are still strictly more general than anything
else in the library.

What the discharge would produce at `d' = u + 1` already exists, which is why nothing here is
freed in place.  `isPerfect_of_biprod_of_pseudoCoherent_summands` fed its two hypotheses
reproduces, step for step, the proof of `Stacks.Cohomology.TorAmplitude.isPerfect_of_biprod`,
which is Tag 08CS unconditionally; and
`perfectDerivedProperty_isSaturated_of_pseudoCoherent_summands` so fed reproduces
`perfectDerivedProperty_isSaturated` in the sibling file, which is Tag 0F8I's saturation clause
unconditionally.  Discharging in place would add a second copy of each.  This file records the
reduction.

`Stacks.Perfect.BoundedLocallyFreeComplexes.isSaturated_isPerfect_of_biprod` in the sibling file
`SaturationFromRetractModels.lean` derives the same clause from the single hypothesis that is the
conclusion of Tag 08CS.  The reduction here is to *two* hypotheses instead of one, but both are
Stacks tags in their own right rather than a statement invented for the reduction, so each is
checkable against the source.  No statement in this file is
registered against 0F8I: each carries hypotheses that Tag 0F8I does not.

The source offers *one* route to 08CS, the three-lemma citation above; 08CQ is in the library in
both directions, as is 08CE.

## Main results

* `Stacks.Perfect.BoundedLocallyFreeComplexes.isPerfect_of_biprod_of_pseudoCoherent_summands`: Tag
  08CS, from Tag 08CE and the converse half of Tag 08CQ.  The Tag 08CK third of the source's
  proof is supplied by `Stacks.Cohomology.TorAmplitude.locallyHasFiniteTorDimension_of_biprod`
  and is not a hypothesis.
* `Stacks.Perfect.BoundedLocallyFreeComplexes.isSaturated_isPerfect_of_pseudoCoherent_summands`:
  the ringed-space saturation statement from the same two hypotheses.
* `perfectDerivedProperty_isSaturated_of_pseudoCoherent_summands`: the scheme-level form, which is
  Tag 0F8I's saturation clause with those two hypotheses added.

## Implementation notes

The two hypotheses are stated at the shape the forward half produces, so that no
translation is needed to discharge them:

* pseudo-coherence is `AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent`, the
  predicate of Tag 08CB that Tag 08CC, Tag 08CM and
  `Stacks.Cohomology.TorAmplitude.isPseudoCoherent_of_isPerfect` are all stated against — not the
  character-identical `AlgebraicGeometry.RingedSpace.IsPseudoCoherent` of
  `StacksFrontier/AlgebraicGeometry/PseudoCoherent/SheafLevel.lean`, which is the copy carrying the
  `08CB` tags but is pinned at a single module universe;
* locally finite Tor dimension is `Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension`,
  stated against the canonical derived tensor product `Stacks.Cohomology.TorAmplitude.derTensor`
  rather than against a hypothesised bifunctor; see the implementation notes of
  `StacksFrontier/Topology/Sheaves/Cohomology/TorAmplitude/DirectSummands.lean` for why that is the
  only one of the four Tor-amplitude predicates in the trees that this argument can use.

The universes of the space, its structure sheaf and its modules coincide, as they already must for
`StrictlyPerfect.OXMod` and for `Stacks.Cohomology.TorAmplitude.derTensor`; the derived category's
hom universes stay independent (`d` for `X`, `d'` for its opens), matching the file
`PseudoCoherentAndFiniteTorDimension.lean` in the directory
`StacksFrontier/Topology/Sheaves/Cohomology/PerfectComplexes/`.
The universe arguments of the scheme-level statement are written out, as in the sibling file
`Triangulated.lean`: the level of the derived-category instance is a `max` which unification will
not read off the value.

## References

* [Stacks Project, Tag 0F8I](https://stacks.math.columbia.edu/tag/0F8I)
* [Stacks Project, Tag 08CS](https://stacks.math.columbia.edu/tag/08CS)
* [Stacks Project, Tag 08CQ](https://stacks.math.columbia.edu/tag/08CQ)
* [Stacks Project, Tag 08CE](https://stacks.math.columbia.edu/tag/08CE)
* [Stacks Project, Tag 08CK](https://stacks.math.columbia.edu/tag/08CK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open Stacks.Cohomology.PerfectComplexes

universe u d d'

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

section RingedSpace

variable {X : RingedSpace.{u, u}} [HasDerivedCategory.{d} (OXMod.{u} X)]
variable [∀ U : Opens X.carrier,
  HasDerivedCategory.{d'} (OXMod.{u} (X.restrict U.isOpenEmbedding))]

attribute [local instance] Stacks.Cohomology.TorAmplitude.restrictModules_preservesFiniteLimits
  Stacks.Cohomology.TorAmplitude.restrictModules_preservesFiniteColimits

/-- **Tag 08CS, from Tag 08CE and the converse half of Tag 08CQ.**  The source's proof is
"Lemmas 08CQ, 08CE and 08CK".  The forward half of 08CQ makes a perfect biproduct pseudo-coherent
and locally of finite Tor dimension; 08CE (the hypothesis `hPC`) splits the first conclusion off
onto the summands and `Stacks.Cohomology.TorAmplitude.locallyHasFiniteTorDimension_of_biprod`,
which is 08CK, splits the second; the converse half of 08CQ (the hypothesis `hconv`) puts them
back together. -/
theorem isPerfect_of_biprod_of_pseudoCoherent_summands
    (hPC : ∀ K L : DerivedCategory (OXMod.{u} X),
      AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent (X := X) (K ⊞ L) →
        AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent (X := X) K ∧
          AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent (X := X) L)
    (hconv : ∀ E : DerivedCategory (OXMod.{u} X),
      AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent (X := X) E →
        Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension X E → IsPerfect E)
    (K L : DerivedCategory (OXMod.{u} X)) (h : IsPerfect (K ⊞ L)) :
    IsPerfect K ∧ IsPerfect L := by
  obtain ⟨hpc, hlftd⟩ :=
    Stacks.Cohomology.TorAmplitude.isPseudoCoherent_and_locallyHasFiniteTorDimension_of_isPerfect
      (K ⊞ L) h
  obtain ⟨hpcK, hpcL⟩ := hPC K L hpc
  obtain ⟨hltK, hltL⟩ :=
    Stacks.Cohomology.TorAmplitude.locallyHasFiniteTorDimension_of_biprod K L hlftd
  exact ⟨hconv K hpcK hltK, hconv L hpcL hltL⟩

/-- **Perfectness is a saturated property of objects of `D(O_X)`, from Tag 08CE and the converse
half of Tag 08CQ.**  The two hypotheses give Tag 08CS, which is what
`Stacks.Perfect.BoundedLocallyFreeComplexes.isSaturated_isPerfect_of_biprod` consumes. -/
theorem isSaturated_isPerfect_of_pseudoCoherent_summands
    (hPC : ∀ K L : DerivedCategory (OXMod.{u} X),
      AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent (X := X) (K ⊞ L) →
        AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent (X := X) K ∧
          AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent (X := X) L)
    (hconv : ∀ E : DerivedCategory (OXMod.{u} X),
      AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent (X := X) E →
        Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension X E → IsPerfect E) :
    ObjectProperty.IsSaturated
      (fun K : DerivedCategory (OXMod.{u} X) => IsPerfect K) :=
  isSaturated_isPerfect_of_biprod (isPerfect_of_biprod_of_pseudoCoherent_summands hPC hconv)

end RingedSpace

section Scheme

attribute [local instance] HasDerivedCategory.standard

/-- **`D_perf(O_X)` is a saturated subcategory of `D(O_X)`, from Tag 08CE and the converse half of
Tag 08CQ.**  This is the saturation clause of Tag 0F8I with those two hypotheses added; it is read
on the ringed space underlying `X`, at the standard derived-category universe the rest of Tag 0F8I
uses. -/
theorem perfectDerivedProperty_isSaturated_of_pseudoCoherent_summands (X : Scheme.{u})
    (hPC : ∀ K L : DerivedCategory (OXMod.{u} X.toRingedSpace),
      AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent (X := X.toRingedSpace) (K ⊞ L)
        →
        AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent (X := X.toRingedSpace) K ∧
          AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent (X := X.toRingedSpace) L)
    (hconv : ∀ E : DerivedCategory (OXMod.{u} X.toRingedSpace),
      AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherent (X := X.toRingedSpace) E →
        Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension.{u, u + 1, u + 1}
          X.toRingedSpace E →
          IsPerfect (X := X.toRingedSpace) E) :
    (show ObjectProperty (DerivedCategory X.Modules) from
      fun K => IsPerfect (X := X.toRingedSpace) K).IsSaturated :=
  @isSaturated_isPerfect_of_pseudoCoherent_summands.{u, u + 1, u + 1} X.toRingedSpace
    inferInstance inferInstance hPC hconv

end Scheme

end Stacks.Perfect.BoundedLocallyFreeComplexes

end

module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ColimitOfConstructibles
public import StacksFrontier.Topology.Sheaves.Spectral.CompactBasisColimit
public import StacksCore.Tactic.StacksAttribute

/-!
# Sheaves of sets on the small étale site as filtered colimits of finite presentations

Every sheaf of sets on the small étale site of a scheme `X` is a filtered colimit of
coequalizers of pairs of maps between finite coproducts of the sheaves `h_U^#` represented by
quasi-compact quasi-separated étale objects `U` of `X`.

The quasi-compact quasi-separated étale objects form a collection of distinguished objects of
the small étale site in the sense of Stacks 0937, satisfying conditions (1) and (2) of that
situation: every étale object is covered by those of its affine opens which lie over an affine
open of `X`, and an étale object with quasi-compact underlying scheme is a quasi-compact object
of the site. Granted those two, the site-level form of Stacks 093C (1),
`Stacks.isFilteredColimit_of_hasEnoughQuasiCompactObjects`, gives the presentation.

## Main definitions

* `AlgebraicGeometry.SmallEtale.quasiCompactObjectsSituation` — the small étale site of `X`
  with the quasi-compact quasi-separated étale objects as its distinguished collection.

## Main results

* `AlgebraicGeometry.setSheavesAreFilteredColimitsOfPresentations` — Stacks 093C (1) for the
  small étale site, in the spelling
  `AlgebraicGeometry.SetSheavesAreFilteredColimitsOfPresentations`, which is the hypothesis
  `h093C` of `AlgebraicGeometry.exists_isFilteredColimit_isConstructibleSetSheaf`
  (Stacks 03SA (1)).

## Implementation notes

Nothing is assumed about `X`. The distinguished collection covers every étale object and
consists of quasi-compact objects of the site whatever `X` is, so the conclusion needs neither
the quasi-compactness nor the quasi-separatedness of `X` that Stacks 03SA (1) carries; it is
formally stronger than the étale case of the tag, not weaker.

`AlgebraicGeometry.HasFiniteQCSRepresentableCoequalizerPresentation` and
`Stacks.HasFiniteRepresentableCoequalizerPresentation` form their finite coproducts and their
coequalizer with different `CategoryTheory.Limits.HasColimit` instances. Those are propositions,
so the two predicates are definitionally equal and the transfer between them needs no comparison
isomorphism.

## References

* [Stacks Project, Tag 093C](https://stacks.math.columbia.edu/tag/093C)
* [Stacks Project, Tag 0937](https://stacks.math.columbia.edu/tag/0937)
* [Stacks Project, Tag 03SA](https://stacks.math.columbia.edu/tag/03SA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-- The small étale site of `X` with the quasi-compact quasi-separated étale objects of `X` as
its distinguished collection of objects. This is the collection `B` of the proof of
Stacks 03SA, in the form of the standing data of Stacks 0937. -/
public def SmallEtale.quasiCompactObjectsSituation :
    Stacks.QuasiCompactObjectsSituation (SmallEtale B X.obj X.property) where
  topology := SmallEtale.topology B X.obj X.property
  objects := {U | IsQCQSEtaleObject B X U}

/-- **Condition (1) of Stacks 0937 for the small étale site.** Every étale object of `X` is
covered by quasi-compact quasi-separated ones, namely by those of its affine opens which lie
over an affine open of `X`: an affine scheme is quasi-compact and quasi-separated. -/
public theorem SmallEtale.hasEnoughObjects_quasiCompactObjectsSituation :
    (SmallEtale.quasiCompactObjectsSituation B X).HasEnoughObjects := by
  intro U
  refine ⟨SmallEtale.affineSubordinateCover B X.obj X.property U,
    SmallEtale.mem_topology_sieve₀_affineSubordinateCover B X.obj X.property U, fun i => ?_⟩
  have : _root_.AlgebraicGeometry.IsAffine ((SmallEtale.toScheme B X.obj X.property).obj
      ((SmallEtale.affineSubordinateCover B X.obj X.property U).X i)) := i.down.1.2
  exact ⟨inferInstance, inferInstance⟩

/-- **Condition (2) of Stacks 0937 for the small étale site.** An étale object of `X` whose
underlying scheme is quasi-compact is a quasi-compact object of the small étale site, by
`AlgebraicGeometry.SmallEtale.isQuasiCompactObject_of_compactSpace`. -/
public theorem SmallEtale.objectsAreQuasiCompact_quasiCompactObjectsSituation :
    (SmallEtale.quasiCompactObjectsSituation B X).ObjectsAreQuasiCompact :=
  fun U hU => SmallEtale.isQuasiCompactObject_of_compactSpace B X.obj X.property U hU.1

/-- **Stacks 093C (1) for the small étale site.** Every sheaf of sets on the small étale site of
`X` is a filtered colimit of sheaves which are coequalizers of a pair of maps between finite
coproducts of sheaves represented by quasi-compact quasi-separated étale objects of `X`.

This is the hypothesis `h093C` of
`AlgebraicGeometry.exists_isFilteredColimit_isConstructibleSetSheaf`, Stacks 03SA (1). It is the
specialisation to the collection of quasi-compact quasi-separated étale objects of
`Stacks.isFilteredColimit_of_hasEnoughQuasiCompactObjects`, which states
[Stacks Tag 093C](https://stacks.math.columbia.edu/tag/093C) part (1) for an arbitrary
situation and carries the tag. -/
@[stacks 093C "part (1), sheaves of sets, étale site"]
public theorem setSheavesAreFilteredColimitsOfPresentations :
    SetSheavesAreFilteredColimitsOfPresentations B X := by
  intro F
  obtain ⟨I, hI, hfiltered, D, ι, hcolimit, hpresentation⟩ :=
    Stacks.isFilteredColimit_of_hasEnoughQuasiCompactObjects
      (SmallEtale.quasiCompactObjectsSituation B X)
      (SmallEtale.hasEnoughObjects_quasiCompactObjectsSituation B X)
      (SmallEtale.objectsAreQuasiCompact_quasiCompactObjectsSituation B X) F
  exact ⟨I, hI, hfiltered, D, ι, ⟨hcolimit⟩, hpresentation⟩

end AlgebraicGeometry

end

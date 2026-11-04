module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.FiniteFreeRepresentation
public import StacksFrontier.Topology.Sheaves.RecoveryExtend.FiniteLocallyFreeRetract

/-!
# Perfectness on a space with local stalks

On a ringed space all of whose structure-sheaf stalks are local rings, an object of the derived
category of `𝒪_X`-modules is perfect exactly when it has a finite locally free representation:
some complex representing it receives, on an open covering, quasi-isomorphisms from bounded
complexes with finite locally free terms.

One direction is the general fact that a bounded complex with finite free terms is strictly
perfect, which is
`AlgebraicGeometry.RingedSpace.isPerfect_of_hasFiniteFreeRepresentation` applied after
`AlgebraicGeometry.RingedSpace.hasFiniteLocallyFreeRepresentation_iff_hasFiniteFreeRepresentation`.
The other needs the local-ring hypothesis: a strictly perfect complex has terms that are direct
summands of finite free modules, and over local rings a direct summand of a finite locally free
module is finite locally free, which is [Stacks, Tag 0BCI].

## Main results

* `AlgebraicGeometry.RingedSpace.isPerfect_iff_hasFiniteLocallyFreeRepresentation`:
  [Stacks, Tag 0BCJ].

The other half of [Stacks, Tag 0BCJ], the equivalence of local finite locally free and local
finite free representations, is
`AlgebraicGeometry.RingedSpace.hasFiniteLocallyFreeRepresentation_iff_hasFiniteFreeRepresentation`,
which this file records against the tag.

## Implementation notes

The hypothesis is imposed on the stalks of `X`, and [Stacks, Tag 0BCI] is applied on an open
subspace `X|_U`; the stalks there are transported from those of `X` along
`AlgebraicGeometry.PresheafedSpace.restrictStalkIso`.

## References

* [Stacks Project, Tag 0BCJ](https://stacks.math.columbia.edu/tag/0BCJ)
* [Stacks Project, Tag 0BCI](https://stacks.math.columbia.edu/tag/0BCI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

namespace AlgebraicGeometry.RingedSpace

universe u d

variable {X : RingedSpace.{u, u}}

/-- **Stacks 0BCJ.** On a ringed space whose structure-sheaf stalks are local rings, a derived
object is perfect exactly when it has local bounded finite locally free representatives. -/
@[stacks 0BCJ "perfect iff locally finite locally free"]
theorem isPerfect_iff_hasFiniteLocallyFreeRepresentation
    [∀ x : X.carrier, IsLocalRing (ToType (X.presheaf.stalk x))]
    [HasDerivedCategory.{d} (OXMod.{u, u} X)] (K : DerivedCategory (OXMod.{u, u} X)) :
    IsPerfect K ↔ HasFiniteLocallyFreeRepresentation K := by
  refine ⟨fun hK => ?_, fun hrep => isPerfect_of_hasFiniteFreeRepresentation
    ((hasFiniteLocallyFreeRepresentation_iff_hasFiniteFreeRepresentation K).mp hrep)⟩
  obtain ⟨E, hE, hEK⟩ := hK
  obtain ⟨I, U, hU, hmodels⟩ := (isPerfectComplex_iff E).mp hE
  refine ⟨E, hEK, I, U, hU, fun i => ?_⟩
  obtain ⟨P, hstrict, f, hf⟩ := hmodels i
  refine ⟨P, hstrict.bounded, fun j => ?_, f, hf⟩
  obtain ⟨n, hret⟩ :=
    (StrictlyPerfect.isDirectSummandOfFiniteFree_iff_retract (P.X j)).mp
      (hstrict.directSummand j)
  let Y := X.restrict (U i).isOpenEmbedding
  let _ : ∀ y : Y.carrier, IsLocalRing (ToType (Y.sheaf.presheaf.stalk y)) := fun y =>
    RingEquiv.isLocalRing
      ((X.restrictStalkIso (U i).isOpenEmbedding y).symm.commRingCatIsoToRingEquiv)
  exact Stacks.SheafOfModules.isFiniteLocallyFree_of_retract
    (X := Y.carrier) (O := Y.sheaf) hret (isFiniteLocallyFree_finiteFree Y n)

end AlgebraicGeometry.RingedSpace

add_to_stacks 0BCJ "finite locally free iff finite free locally"
  AlgebraicGeometry.RingedSpace.hasFiniteLocallyFreeRepresentation_iff_hasFiniteFreeRepresentation

end

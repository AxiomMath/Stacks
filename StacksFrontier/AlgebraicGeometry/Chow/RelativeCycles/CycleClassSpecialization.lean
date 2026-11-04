module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.FlatCycleClasses

/-!
# The cycle class of a Hilbert datum specializes correctly over a discrete valuation ring

Over the spectrum of a discrete valuation ring the family of cycles attached to an element of
the free abelian group on `Hilb(X/S, r)` satisfies the valuative condition for the identity
morphism of the base: the specialization of its generic member is its closed member.

## Main results

* `Stacks.Chow.specializationCycle_cycleFamily` — the identity for a single member of
  `Hilb(X/S, r)`.
* `Stacks.Chow.specializationCycle_cycleClassMap` — the identity for an element of the free abelian
  group on `Hilb(X/S, r)`.

## Implementation notes

The statement is the instance of the valuative condition defining a relative cycle at the
identity morphism of `Spec R`, which the definition of `Stacks.Chow.IsRelativeCycle` reaches only
through the base change along that morphism. Proving it directly on the generators avoids
comparing `X` with `X ×_{Spec R} Spec R`.

## References

* [Stacks Project, Tag 0H4J](https://stacks.math.columbia.edu/tag/0H4J)
* [Stacks Project, Tag 0H5A](https://stacks.math.columbia.edu/tag/0H5A)
* [Stacks Project, Tag 0H5P](https://stacks.math.columbia.edu/tag/0H5P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-- Over a discrete valuation ring the specialization of the generic member of the family of
cycles `[Z/X/S]_r` of a member of `Hilb(X/S, r)` is its closed member. -/
theorem specializationCycle_cycleFamily {r : ℕ} {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [LocallyOfFinitePresentation f] (Z : HilbertCycleDatum f r) :
    specializationCycle f r (Z.cycleFamily f (genericPoint (Spec (.of R)))) =
      Z.cycleFamily f (IsLocalRing.closedPoint R) := by
  have := Z.flat
  exact specializationCycle_familyAssociatedToModule f Z.structureModule
    (isFlatOver_pushforwardStructureSheaf Z.ideal.subschemeι f) r
    (Z.structureModule_fiberSupport_dimension_le f _)

/-- Over a discrete valuation ring the specialization of the generic member of a combination of
cycle classes of members of `Hilb(X/S, r)` is its closed member. -/
theorem specializationCycle_cycleClassMap {r : ℕ} {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [LocallyOfFinitePresentation f] (b : FreeAbelianGroup (HilbertCycleDatum f r)) :
    specializationCycle f r (cycleClassMap f r b (genericPoint (Spec (.of R)))) =
      cycleClassMap f r b (IsLocalRing.closedPoint R) := by
  have key : ((specializationCycleHom f r).comp
      ((Pi.evalAddMonoidHom (fun t ↦ FiberCycleGroup f t r) (genericPoint (Spec (.of R)))).comp
        (cycleClassMap f r))) =
      (Pi.evalAddMonoidHom (fun t ↦ FiberCycleGroup f t r) (IsLocalRing.closedPoint R)).comp
        (cycleClassMap f r) :=
    FreeAbelianGroup.lift_ext _ _ fun Z => by
      simp only [AddMonoidHom.comp_apply, cycleClassMap_of]
      exact specializationCycle_cycleFamily f Z
  exact DFunLike.congr_fun key b

end Stacks.Chow

end

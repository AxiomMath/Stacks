module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.Inseparable
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Specialization
public import StacksFrontier.RingTheory.KrullDimension.Defs
public import StacksFrontier.Topology.Dimension.Krull

/-!
# Fibre dimension along a specialization

Local dimension inside a fibre is monotone along specialization: a point specializing to another
point of the same fibre has local dimension no larger. This is purely topological. If moreover
the morphism is locally of finite type and the specialization is strict, the Krull dimension of
the fibre's local ring increases strictly.

## Main results

* `AlgebraicGeometry.topologicalKrullDimAt_fiber_le_of_specialization` compares the local
  dimensions at two points of one fibre.
* `AlgebraicGeometry.ringKrullDim_fiber_stalk_lt_of_specialization` gives the strict inequality
  of local dimensions in the fibre.

## Implementation notes

The points of the fibre are the canonical inverse images of the given points under
`Scheme.Hom.fiberHomeo`. The first proof is purely topological, so the locally finite type and
nontriviality assumptions in the source are unnecessary there. The specialization relation is
Mathlib's `Specializes`, written `⤳`.

## References

* [Stacks Project, Tag 06RU](https://stacks.math.columbia.edu/tag/06RU)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Local dimension in a fibre is monotone along a specialization of points with a common
image in the base. -/
@[stacks 06RU "fiber_dimension_monotone"]
public theorem topologicalKrullDimAt_fiber_le_of_specialization {X S : Scheme.{u}}
    (f : X ⟶ S) {x x' : X} (hxx' : x ⤳ x') {s : S}
    (hx : f x = s) (hx' : f x' = s) :
    topologicalKrullDimAt (f.fiber s) ((f.fiberHomeo s).symm ⟨x, hx⟩) ≤
      topologicalKrullDimAt (f.fiber s) ((f.fiberHomeo s).symm ⟨x', hx'⟩) := by
  apply topologicalKrullDimAt_le_of_specialization
  simpa only [(f.fiberHomeo s).symm.isInducing.specializes_iff, subtype_specializes_iff]
    using hxx'

/-- A strict specialization inside a fibre of a locally finite type morphism strictly
increases the dimension of the fibre's local ring. -/
@[stacks 06RU "fiber_local_dimension_strict"]
public theorem ringKrullDim_fiber_stalk_lt_of_specialization
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    {x x' : X} (hxx' : x ⤳ x') (hne : x ≠ x')
    {s : S} (hx : f x = s) (hx' : f x' = s) :
    ringKrullDim ((f.fiber s).presheaf.stalk ((f.fiberHomeo s).symm ⟨x, hx⟩)) <
      ringKrullDim ((f.fiber s).presheaf.stalk ((f.fiberHomeo s).symm ⟨x', hx'⟩)) := by
  subst s
  let y := f.asFiber x
  let y' := (f.fiberHomeo (f x)).symm ⟨x', hx'⟩
  have hyy' : y ⤳ y' :=
    (f.fiberHomeo (f x)).isInducing.specializes_iff.mp
      (Topology.IsInducing.subtypeVal.specializes_iff.mp (by simpa [y, y'] using hxx'))
  have hyne : y ≠ y' := fun he => hne (by simpa [y, y'] using congrArg (f.fiberι (f x)) he)
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) :=
    inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd f (S.fromSpecResidueField (f x))))
  exact krullDimOfRing_stalk_lt_of_specialization
    (S.residueField (f x)) (f.fiber (f x)) (f.fiberToSpecResidueField (f x)) hyy' hyne

end AlgebraicGeometry

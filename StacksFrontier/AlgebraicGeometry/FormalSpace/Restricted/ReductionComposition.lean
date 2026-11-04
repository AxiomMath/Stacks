module

public import Mathlib.RingTheory.FiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Rig.Reduction
public import StacksFrontier.RingTheory.Rig.ReductionLocality
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteTypeOnReductionsIsLocal

/-!
# Finite type on reductions is stable under composition

Reduction by the ideal of topologically nilpotent elements is functorial for continuous
homomorphisms of linearly topologized rings, and the reduction of a composition is the
composition of the reductions.  Finite type on reductions is therefore inherited by a
composition from its two factors.

## Main results

* `Rig.isFiniteTypeOnReductions_comp`: a composition of continuous homomorphisms of finite
  type on reductions is of finite type on reductions.
* `Rig.finiteTypeOnReductions_isStableUnderComposition`: finite type on reductions is a local
  property of morphisms of countably indexed weakly admissible rings that is stable under
  composition.

## References

* [Stacks Project, Tag 0GC2](https://stacks.math.columbia.edu/tag/0GC2)
* [Stacks Project, Tag 0GC4](https://stacks.math.columbia.edu/tag/0GC4)
-/

@[expose] public section

namespace Rig

section

universe u

/-- A composition of continuous homomorphisms of linearly topologized rings that are of finite
type on reductions is again of finite type on reductions. -/
public theorem isFiniteTypeOnReductions_comp
    {A B C : Type u} [CommRing A] [TopologicalSpace A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsLinearTopology B B]
    [CommRing C] [TopologicalSpace C] [IsLinearTopology C C]
    (f : B →+* A) (g : C →+* B) (hf : Continuous f) (hg : Continuous g)
    (hft : Rig.IsFiniteTypeOnReductions f hf)
    (hgt : Rig.IsFiniteTypeOnReductions g hg) :
    Rig.IsFiniteTypeOnReductions (f.comp g) (hf.comp hg) := by
  convert RingHom.FiniteType.comp hft hgt using 1
  ext x
  rfl

/-- Finite type on reductions is a composition-stable local property of morphisms of countably
indexed weakly admissible topological rings. -/
@[stacks 0GC4]
public theorem finiteTypeOnReductions_isStableUnderComposition :
    TopologicalRing.PropertyIsStableUnderComposition
      TopologicalRing.FiniteTypeOnReductionsProperty.{u} where
  isLocal := isFiniteTypeOnReductions_local
  comp := by
    intro A B C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f g hf hg hPf hPg
    obtain ⟨hf', hft⟩ := hPf
    obtain ⟨hg', hgt⟩ := hPg
    intro _ _
    exact ⟨hf'.comp hg', isFiniteTypeOnReductions_comp f g hf' hg' hft hgt⟩

end

end Rig

end

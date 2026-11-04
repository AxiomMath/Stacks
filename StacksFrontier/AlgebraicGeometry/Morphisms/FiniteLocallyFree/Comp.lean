module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Basic

/-!
# Composition of finite locally free morphisms

The composite of two finite locally free morphisms of schemes is finite locally free.

## Main results

* `Stacks.Morphisms.isFiniteLocallyFree_comp`: finite locally free morphisms are closed under
  composition.

## Implementation notes

The result is registered as an instance, so the property of a composite is available to
typeclass inference. It is obtained from the characterization of finite local freeness as
finiteness together with flatness and local finite presentation, each of which Mathlib already
knows to be stable under composition.

## References

* [Stacks Project, Tag 02KC](https://stacks.math.columbia.edu/tag/02KC)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Morphisms

/-- **Stacks Project, Tag 02KC.** A composition of finite locally free morphisms is finite
locally free. -/
@[stacks 02KC, instance]
theorem isFiniteLocallyFree_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFiniteLocallyFree f] [IsFiniteLocallyFree g] :
    IsFiniteLocallyFree (f ≫ g) := by
  obtain ⟨hf₁, hf₂, hf₃⟩ :=
    (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation f).mp ‹_›
  obtain ⟨hg₁, hg₂, hg₃⟩ :=
    (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation g).mp ‹_›
  refine (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation (f ≫ g)).mpr
    ⟨?_, ?_, ?_⟩
  · have := hf₁
    have := hg₁
    infer_instance
  · have := hf₂
    have := hg₂
    infer_instance
  · have := hf₃
    have := hg₃
    infer_instance

end Stacks.Morphisms

end

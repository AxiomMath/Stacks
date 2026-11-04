module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint

/-!
# Finite presentation of open immersions

An open immersion of schemes is of finite presentation exactly when it is quasi-compact: an open
immersion is always locally of finite presentation and quasi-separated, so the only condition
left in the definition of a morphism of finite presentation is quasi-compactness.

## Main results

* `AlgebraicGeometry.finitePresentation_iff_quasiCompact_of_isOpenImmersion`: an open immersion
  is of finite presentation if and only if it is quasi-compact.

## References

* [Stacks Project, Tag 01TU](https://stacks.math.columbia.edu/tag/01TU)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 01TU.** An open immersion is of finite presentation if and only if
it is quasi-compact. -/
@[stacks 01TU, ega "IV 1.6.2"]
theorem finitePresentation_iff_quasiCompact_of_isOpenImmersion
    {X S : Scheme.{u}} (f : X ⟶ S) [IsOpenImmersion f] :
    FinitePresentation f ↔ QuasiCompact f := ⟨(·.2.1), fun h => ⟨inferInstance, h, inferInstance⟩⟩

end AlgebraicGeometry

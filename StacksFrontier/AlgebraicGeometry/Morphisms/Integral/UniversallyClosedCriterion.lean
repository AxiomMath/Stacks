module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import StacksCore.Tactic.StacksAttribute

/-!
# Integral morphisms are the affine universally closed ones

A morphism of schemes is integral if and only if it is affine and universally closed. Mathlib
proves this, so the statement is recorded against the library declaration rather than restated.

## References

* [Stacks Project, Tag 01WM](https://stacks.math.columbia.edu/tag/01WM)
-/

add_to_stacks 01WM "A morphism of schemes is integral if and only if it is affine and
  universally closed." AlgebraicGeometry.IsIntegralHom.iff_universallyClosed_and_isAffineHom
add_to_ega "II 6.1.10" "more general"
  AlgebraicGeometry.IsIntegralHom.iff_universallyClosed_and_isAffineHom
add_to_ega "II 6.1.2" "forward implication"
  AlgebraicGeometry.IsIntegralHom.iff_universallyClosed_and_isAffineHom
add_to_ega "II 7.3.11" "special case"
  AlgebraicGeometry.IsIntegralHom.iff_universallyClosed_and_isAffineHom
add_to_ega "IV 18.12.8" AlgebraicGeometry.IsIntegralHom.iff_universallyClosed_and_isAffineHom
add_to_ega "IV 18.12.9" "partial"
  AlgebraicGeometry.IsIntegralHom.iff_universallyClosed_and_isAffineHom

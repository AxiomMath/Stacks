module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import StacksCore.Tactic.StacksAttribute

/-!
# Base change of an immersion of schemes over a base

Stacks Tag 01JY: for schemes `X` and `Y` over a base `S`, a morphism `f : X ⟶ Y` over `S` which is
an immersion — respectively a closed immersion, respectively an open immersion — stays one under
every base change `S' ⟶ S`.

Mathlib already has all three assertions, as the statements that each of the three properties is
stable under base change; stability under base change of a morphism property is exactly
inheritance under `CategoryTheory.Over.pullback`, by
`CategoryTheory.MorphismProperty.overPullbackMap`. This file records the Stacks tag on those
three Mathlib declarations.

## References

* [Stacks Project, Tag 01JY](https://stacks.math.columbia.edu/tag/01JY)
-/

add_to_stacks 01JY "immersion" AlgebraicGeometry.IsImmersion.isStableUnderBaseChange
add_to_sga "3 VIB 10.1" "partial" AlgebraicGeometry.IsImmersion.isStableUnderBaseChange
add_to_ega "I 4.3.1" "special case" AlgebraicGeometry.IsImmersion.isStableUnderBaseChange
add_to_ega "I 4.3.2" AlgebraicGeometry.IsImmersion.isStableUnderBaseChange
add_to_ega "I 4.5.5" "(iii), special case" AlgebraicGeometry.IsImmersion.isStableUnderBaseChange
add_to_ega "II 3.8.1" "Immersion clause" AlgebraicGeometry.IsImmersion.isStableUnderBaseChange
add_to_ega "IV 17.13.1" AlgebraicGeometry.IsImmersion.isStableUnderBaseChange
add_to_stacks 01JY "closed immersion"
  AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange
add_to_sga "1 VIII 5.5" "closed-immersion clause"
  AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange
add_to_sga "3 VIB 10.1" "partial" AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange
add_to_sga "4 XII 4.3" "Parenthetical clause"
  AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange
add_to_ega "I 10.14.5" "(ii), ordinary schemes"
  AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange
add_to_ega "I 4.3.1" "special case" AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange
add_to_ega "I 4.3.2" AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange
add_to_ega "I 4.5.5" "(iii), special case"
  AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange
add_to_ega "II 8.10.2" "j′ is a closed immersion"
  AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange
add_to_ega "IV 17.13.1" "closed immersions"
  AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange
add_to_ega "IV 2.7.1" "implication" AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange
add_to_ega "IV 8.6.2" "more general" AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange
add_to_stacks 01JY "open immersion"
  AlgebraicGeometry.isOpenImmersion_stableUnderBaseChange
add_to_sga "1 VIII 5.5" "open-immersion clause"
  AlgebraicGeometry.isOpenImmersion_stableUnderBaseChange
add_to_sga "3 VIB 10.1" "open immersions" AlgebraicGeometry.isOpenImmersion_stableUnderBaseChange
add_to_sga "6 VIII 1.6" "partial" AlgebraicGeometry.isOpenImmersion_stableUnderBaseChange
add_to_ega "I 4.3.1" "special case" AlgebraicGeometry.isOpenImmersion_stableUnderBaseChange
add_to_ega "I 4.3.2" AlgebraicGeometry.isOpenImmersion_stableUnderBaseChange
add_to_ega "I 4.5.5" "(iii), special case" AlgebraicGeometry.isOpenImmersion_stableUnderBaseChange
add_to_ega "IV 11.9.5" "Geometric clause" AlgebraicGeometry.isOpenImmersion_stableUnderBaseChange
add_to_ega "IV 2.7.1" "(x)" AlgebraicGeometry.isOpenImmersion_stableUnderBaseChange

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import StacksCore.Tactic.StacksAttribute

/-!
# An étale morphism of schemes is open

Stacks 03WT: the underlying map of topological spaces of an étale morphism of schemes is an
open map.

Mathlib already has this. An étale morphism is flat and locally of finite presentation, and
such a morphism is universally open by `AlgebraicGeometry.UniversallyOpen.of_flat` — which
Mathlib itself tags with Stacks 01UA — while a universally open morphism is open on the
underlying spaces by `AlgebraicGeometry.Scheme.Hom.isOpenMap`. Both instances are found by
typeclass inference from `Etale f` alone, so for an étale `f` the term `f.isOpenMap` *is* the
statement of this tag. This file records the tag on that pair of Mathlib declarations.

## Implementation notes

Nothing is restated here: a theorem whose proof is `f.isOpenMap` would be a name for a Mathlib
fact rather than a proof of anything, so uses call `AlgebraicGeometry.Scheme.Hom.isOpenMap`
directly. The tag is recorded by the annotations below so that a dependency census over Stacks
attributes can see the fact.

The same pair of declarations carries clause (9) of Stacks 03PC, which asserts exactly this.

## References

* [Stacks Project, Tag 03WT](https://stacks.math.columbia.edu/tag/03WT)
* [Stacks Project, Tag 01UA](https://stacks.math.columbia.edu/tag/01UA)
* [Stacks Project, Tag 03PC](https://stacks.math.columbia.edu/tag/03PC)
-/

add_to_stacks 03WT "a flat morphism locally of finite presentation is universally open"
  AlgebraicGeometry.UniversallyOpen.of_flat
add_to_sga "1 IV 6.6" "F = O_X" AlgebraicGeometry.UniversallyOpen.of_flat
add_to_sga "1 VIII 4.9" "more general" AlgebraicGeometry.UniversallyOpen.of_flat
add_to_sga "3 V 10.1.1" "more general" AlgebraicGeometry.UniversallyOpen.of_flat
add_to_sga "3 V 4.1.1" "flat and fp implies open" AlgebraicGeometry.UniversallyOpen.of_flat
add_to_sga "3 VIA 2.5.4" "Final implication" AlgebraicGeometry.UniversallyOpen.of_flat
add_to_sga "3 VIB 3.11" "more general" AlgebraicGeometry.UniversallyOpen.of_flat
add_to_sga "3 VIB 4.3" AlgebraicGeometry.UniversallyOpen.of_flat
add_to_sga "3 VIB 7.5" "f|_V is an open morphism" AlgebraicGeometry.UniversallyOpen.of_flat
add_to_sga "3 X 5.4" "partial" AlgebraicGeometry.UniversallyOpen.of_flat
add_to_sga "3 XVI 2.1" "more general" AlgebraicGeometry.UniversallyOpen.of_flat
add_to_sga "6 VIII 1.3" "more general" AlgebraicGeometry.UniversallyOpen.of_flat
add_to_ega "IV 1.10.4" "b) ⇒ a), special case" AlgebraicGeometry.UniversallyOpen.of_flat
add_to_ega "IV 11.3.1" "special case" AlgebraicGeometry.UniversallyOpen.of_flat
add_to_ega "IV 14.4.10" "special case" AlgebraicGeometry.UniversallyOpen.of_flat
add_to_ega "IV 15.2.1" AlgebraicGeometry.UniversallyOpen.of_flat
add_to_ega "IV 15.2.4" "(ii), special case" AlgebraicGeometry.UniversallyOpen.of_flat
add_to_ega "IV 18.2.7" "partial" AlgebraicGeometry.UniversallyOpen.of_flat
add_to_ega "IV 2.4.6" AlgebraicGeometry.UniversallyOpen.of_flat
add_to_ega "IV 2.4.7" "more general" AlgebraicGeometry.UniversallyOpen.of_flat
add_to_ega "IV 4.4.1" "special case" AlgebraicGeometry.UniversallyOpen.of_flat
add_to_stacks 03WT "a universally open morphism is open on the underlying spaces"
  AlgebraicGeometry.Scheme.Hom.isOpenMap

add_to_stacks 03PC "open" AlgebraicGeometry.UniversallyOpen.of_flat
add_to_stacks 03PC "open" AlgebraicGeometry.Scheme.Hom.isOpenMap

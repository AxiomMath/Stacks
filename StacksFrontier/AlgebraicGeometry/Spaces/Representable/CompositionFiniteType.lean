module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms of finite type are stable under composition

A morphism of schemes is of finite type when it is locally of finite type and
quasi-compact. Both conditions are preserved by composition, by
`AlgebraicGeometry.locallyOfFiniteType_comp` and `AlgebraicGeometry.quasiCompact_comp`, so a
composite of morphisms of finite type is again of finite type. This is the entry of the
composition list for that property.

## References

* [Stacks Project, Tag 02WG](https://stacks.math.columbia.edu/tag/02WG)
-/

@[expose] public section

add_to_stacks 02WG "finite_type" AlgebraicGeometry.locallyOfFiniteType_comp
add_to_ega "I 10.13.5" "(i), special case" AlgebraicGeometry.locallyOfFiniteType_comp
add_to_ega "I 6.3.4" "clause (ii)" AlgebraicGeometry.locallyOfFiniteType_comp
add_to_ega "I 6.6.6" AlgebraicGeometry.locallyOfFiniteType_comp
add_to_ega "IV 1.3.4" AlgebraicGeometry.locallyOfFiniteType_comp

add_to_stacks 02WG "finite_type" AlgebraicGeometry.quasiCompact_comp

end

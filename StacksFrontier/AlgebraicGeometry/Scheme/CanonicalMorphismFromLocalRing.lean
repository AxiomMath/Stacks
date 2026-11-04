module

public import Mathlib.AlgebraicGeometry.Stalk
public import StacksCore.Tactic.StacksAttribute

/-!
# The canonical morphism from the spectrum of a local ring

For a point `x` of a scheme `X`, the identity of the local ring `𝒪_{X, x}` corresponds to a
canonical morphism `Spec 𝒪_{X, x} → X`. Mathlib constructs it as
`AlgebraicGeometry.Scheme.fromSpecStalk`.

## References

* [Stacks Project, Tag 02NA](https://stacks.math.columbia.edu/tag/02NA)
-/

@[expose] public section

add_to_stacks 02NA "the canonical morphism `Spec 𝒪_{X, x} ⟶ X`"
  AlgebraicGeometry.Scheme.fromSpecStalk
add_to_ega "I 2.4.2" AlgebraicGeometry.Scheme.fromSpecStalk
add_to_ega "I 2.4.7" "zero ideal a_y = 0" AlgebraicGeometry.Scheme.fromSpecStalk
add_to_ega "IV 5.9.6" AlgebraicGeometry.Scheme.fromSpecStalk

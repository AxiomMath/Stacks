module

public import Mathlib.Geometry.RingedSpace.Basic

import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0093 — composition of morphisms of ringed spaces

A morphism of ringed spaces `(X, 𝒪_X) → (Y, 𝒪_Y)` is a pair `(f, f^♯)` of a continuous map and
an `f`-map of sheaves of rings. Tag 0093 defines the composition of two such morphisms by
`(g, g^♯) ∘ (f, f^♯) = (g ∘ f, f^♯ ∘ g^♯)` and observes that it is again a morphism of ringed
spaces.

In Mathlib this is the composition of presheafed-space morphisms,
`AlgebraicGeometry.PresheafedSpace.comp`, which the categorical composition in
`RingedSpace = SheafedSpace CommRingCat` is inherited from; `comp_base` and `comp_c` are the two
formulas the tag prescribes — on the base the composite continuous map, and on sheaves `g^♯`
followed by the pushforward of `f^♯` along `g`.
-/

@[expose] public section

add_to_stacks 0093 "the composition of two morphisms of ringed spaces"
  AlgebraicGeometry.PresheafedSpace.comp
add_to_ega "0 3.5.2" AlgebraicGeometry.PresheafedSpace.comp
add_to_ega "0 4.1.1" "composition" AlgebraicGeometry.PresheafedSpace.comp
add_to_stacks 0093 "its base map is the composite continuous map"
  AlgebraicGeometry.PresheafedSpace.comp_base
add_to_ega "0 3.5.2" "partial" AlgebraicGeometry.PresheafedSpace.comp_base
add_to_ega "0 4.1.1" "psi''=psi'o psi" AlgebraicGeometry.PresheafedSpace.comp_base
add_to_stacks 0093 "its sharp map is `g^♯` followed by the pushforward of `f^♯` along `g`"
  AlgebraicGeometry.PresheafedSpace.comp_c
add_to_ega "0 4.1.1" "theta''=psi_*(th)o th'" AlgebraicGeometry.PresheafedSpace.comp_c

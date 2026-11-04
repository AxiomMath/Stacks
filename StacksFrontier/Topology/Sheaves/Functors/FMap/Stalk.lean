module

public import Mathlib.Geometry.RingedSpace.Stalks

import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 008M — composition of f-maps on stalks

An *f-map* from a presheaf `G` on `Y` to a presheaf `F` on `X`, along a continuous map
`f : X → Y`, is a morphism `G → f_* F` of presheaves on `Y`. Such a map induces at each point
`x` of `X` a map of stalks `G_{f x} → F_x`, and Stacks 008M says that composing an f-map with a
g-map, along `g : Y → Z`, composes these: `(φ ∘ ψ)_x = φ_x ∘ ψ_{f x}`.

Mathlib packages the pair `(f, φ)` as a morphism of presheafed spaces — a
`AlgebraicGeometry.PresheafedSpace.Hom`, whose `base` field is `f` and whose `c` field is the
f-map. Its induced map of stalks is `AlgebraicGeometry.PresheafedSpace.Hom.stalkMap`, built
exactly as here from the stalk functor and the canonical map out of the stalk of a pushforward,
and the statement of the tag is `AlgebraicGeometry.PresheafedSpace.stalkMap.comp`.
-/

@[expose] public section

-- The former @[stacks 008M] theorem re-proved this Mathlib theorem for a bare f-map, over an
-- f-map vocabulary defined in this file rather than Mathlib's presheafed-space morphisms.
add_to_stacks 008M "an f-map `(f, φ)`, i.e. a morphism `G ⟶ f_* F` of presheaves on `Y` over a
  continuous `f`" AlgebraicGeometry.PresheafedSpace.Hom
add_to_ega "0 3.5.1" AlgebraicGeometry.PresheafedSpace.Hom
add_to_stacks 008M "the map of stalks `G_{f x} ⟶ F_x` induced by an f-map"
  AlgebraicGeometry.PresheafedSpace.Hom.stalkMap
add_to_ega "0 3.5.1" AlgebraicGeometry.PresheafedSpace.Hom.stalkMap
add_to_ega "0 4.4.3" "partial" AlgebraicGeometry.PresheafedSpace.Hom.stalkMap
add_to_ega "0 3.4.4" "construction of ψ_x" AlgebraicGeometry.PresheafedSpace.Hom.stalkMap
add_to_stacks 008M "the stalk map of a composition is the composition of the stalk maps"
  AlgebraicGeometry.PresheafedSpace.stalkMap.comp
add_to_ega "0 3.4.4" "ψ''_x = ψ_x ∘ ψ'_{ψ(x)}" AlgebraicGeometry.PresheafedSpace.stalkMap.comp

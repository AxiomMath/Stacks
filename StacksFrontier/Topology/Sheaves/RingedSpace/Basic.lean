module

public import Mathlib.Geometry.RingedSpace.Basic

import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0091 — Ringed spaces

A ringed space is a pair `(X, 𝒪_X)` consisting of a topological space `X` and a sheaf of
(commutative) rings `𝒪_X` on `X`. A morphism of ringed spaces `(X, 𝒪_X) ⟶ (Y, 𝒪_Y)` is a pair
consisting of a continuous map `f : X → Y` and an `f`-map of sheaves of rings
`f^♯ : 𝒪_Y → f_* 𝒪_X`.

Mathlib's `AlgebraicGeometry.RingedSpace` is `AlgebraicGeometry.SheafedSpace CommRingCat`,
whose data are exactly a `carrier : TopCat`, a `presheaf` on it and the proof `IsSheaf` that the
presheaf is a sheaf — that is, the pair of the definition. A morphism is a morphism of the
underlying presheafed spaces, `AlgebraicGeometry.PresheafedSpace.Hom`, whose two fields are the
continuous map `base` and the `f`-map `c : Y.presheaf ⟶ (pushforward base).obj X.presheaf`.
-/

@[expose] public section

-- The former @[stacks 0091] definitions were the structural bijections between these Mathlib
-- types and `Σ`-re-encodings of the same data; every direction was an η-equality.
add_to_stacks 0091 "a ringed space: a topological space together with a sheaf of commutative
  rings on it" AlgebraicGeometry.RingedSpace
add_to_sga "4 Vbis 1.3.1" "topological space case" AlgebraicGeometry.RingedSpace
add_to_sga "4 IV 11.1.1" "site of opens of a space" AlgebraicGeometry.RingedSpace
add_to_ega "0 4.1.1" "ringed space def" AlgebraicGeometry.RingedSpace
add_to_stacks 0091 "a morphism of ringed spaces: a continuous map `base` together with an
  `f`-map `c` of sheaves of rings" AlgebraicGeometry.PresheafedSpace.Hom
add_to_ega "0 4.1.1" "morphism definition" AlgebraicGeometry.PresheafedSpace.Hom
add_to_ega "0 3.5.2" "category of pairs" AlgebraicGeometry.PresheafedSpace.Hom

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Global sections on an affine scheme are additive

`AlgebraicGeometry.moduleSpecΓFunctor` is the global-sections functor
`Mod(𝒪_{Spec R}) ⥤ Mod R`. Addition of morphisms is sectionwise on both sides, so the functor is
additive by `rfl`.

## Main results

* `AlgebraicGeometry.moduleSpecΓFunctor_additive`

## Implementation notes

The one line was restated in five modules of the tree, under four names. It lives here, in a
module whose only import is the Mathlib file that declares the functor, so that every one of
those modules reaches it without gaining anything else: their import closures range from 258 to
854 modules and all of them already have `Mathlib.AlgebraicGeometry.Modules.Tilde`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Global sections of `𝒪_{Spec R}`-modules is an additive functor. -/
public instance moduleSpecΓFunctor_additive (R : CommRingCat.{u}) :
    (moduleSpecΓFunctor (R := R)).Additive where
  map_add := rfl

end AlgebraicGeometry

end

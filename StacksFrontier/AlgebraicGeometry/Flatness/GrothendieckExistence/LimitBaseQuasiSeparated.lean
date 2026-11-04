module

public import StacksFrontier.AlgebraicGeometry.Flatness.GrothendieckExistence.Basic

/-!
# Schemes quasi-separated over the inverse-limit base are quasi-separated

A scheme `X` over the spectrum `Spec (lim Aₙ)` of the inverse limit of an inverse system of rings
is quasi-separated as soon as `X ⟶ Spec (lim Aₙ)` is quasi-separated, for instance of finite
presentation, its target being affine. This is the quasi-separatedness that the situations of
Grothendieck's existence theorem (Stacks 0DIB) use.

## Main results

* `AlgebraicGeometry.GrothendieckExistence.quasiSeparatedSpace_left_of_quasiSeparated`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GrothendieckExistence

/-- A scheme quasi-separated over the inverse-limit base `Spec (lim Aₙ)` is quasi-separated, the
base being affine. A morphism of finite presentation is quasi-separated, so this applies to the
scheme of Situation 0DIB. -/
instance quasiSeparatedSpace_left_of_quasiSeparated {system : ℕᵒᵖ ⥤ CommRingCat.{u}}
    (X : Over (limitBase system)) [QuasiSeparated X.hom] : QuasiSeparatedSpace X.left :=
  quasiSeparatedSpace_of_quasiSeparated X.hom

end AlgebraicGeometry.GrothendieckExistence

end

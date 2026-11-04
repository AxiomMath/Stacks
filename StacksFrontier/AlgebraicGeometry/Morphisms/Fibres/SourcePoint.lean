module

public import Mathlib.AlgebraicGeometry.Fiber

/-!
# The point of a fibre determined by a point of the source

Mathlib's `AlgebraicGeometry.Scheme.Hom.asFiber` sends a point `x` of the source of
`f : X ⟶ Y` to a point of the fibre `f.fiber (f x)` over `f x`. In practice the fibre of
interest is presented as `f.fiber y` for some `y` with a proof that `f x = y`, so one needs the
transport of `f.asFiber x` along that proof: this is
`AlgebraicGeometry.Scheme.Hom.asFiberAt`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

/-- The point of `f.fiber y` determined by a point `x` of the source together with a proof
that `f x = y`. For `h = rfl` this is `AlgebraicGeometry.Scheme.Hom.asFiber`. -/
def asFiberAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (y : Y) (h : f x = y) :
    f.fiber y := h ▸ f.asFiber x

end Scheme.Hom

end AlgebraicGeometry

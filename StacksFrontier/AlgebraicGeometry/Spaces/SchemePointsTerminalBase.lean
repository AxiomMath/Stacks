module

public import StacksFrontier.AlgebraicGeometry.Spaces.SchemePointsAffineHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SpecGlobalFunctionsTerminalIso

/-!
# The functor of points of a scheme over a terminal base

Let `B` be a big fppf site and let `S` be a scheme contained in it which is terminal in the
category of schemes. Then every contained scheme is an object of the big fppf category over `S`,
and its functor of points is representable by that object.

## Main definitions

* `AlgebraicGeometry.Space.schemePointsObj`: a contained scheme as an object of the big fppf
  category over a terminal base.
* `AlgebraicGeometry.Space.schemePointsIsoYoneda`: the identification of the functor of points of a
  contained scheme with the presheaf represented by that object.

## References

* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A scheme contained in a big fppf site, as an object of the big fppf category over a terminal
base: its structure morphism is the unique one. -/
def schemePointsObj (hterminal : IsTerminal S) {T : Scheme.{u}} (hT : B.Contains T) :
    BigFppfOver B S hS :=
  BigFppfOver.mk B S hS hT (hterminal.from T)

/-- The underlying scheme of `schemePointsObj B S hS hterminal hT` is `T`. -/
@[simp]
theorem toScheme_obj_schemePointsObj (hterminal : IsTerminal S) {T : Scheme.{u}}
    (hT : B.Contains T) :
    (BigFppfOver.toScheme B S hS).obj (schemePointsObj B S hS hterminal hT) = T :=
  rfl

/-- **Over a terminal base the functor of points of a contained scheme is representable.** -/
def schemePointsIsoYoneda (hterminal : IsTerminal S) {T : Scheme.{u}} (hT : B.Contains T) :
    schemePoints B S hS T ≅ yoneda.obj (schemePointsObj B S hS hterminal hT) :=
  haveI := isIso_schemePointsUnit B S hS hterminal (schemePointsObj B S hS hterminal hT)
  (asIso (schemePointsUnit B S hS (schemePointsObj B S hS hterminal hT))).symm

end AlgebraicGeometry.Space

end

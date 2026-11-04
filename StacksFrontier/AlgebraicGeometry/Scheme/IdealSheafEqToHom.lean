module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Transporting the closed immersion of a subscheme along an equality of ideal sheaves

The closed subscheme cut out by an ideal sheaf is unchanged by rewriting the ideal sheaf.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Transporting the closed immersion of the subscheme cut out by an ideal sheaf along an
equality of ideal sheaves gives back that closed immersion. -/
@[reassoc]
theorem eqToHom_subscheme_comp_subschemeι {X : Scheme.{u}} (I J : X.IdealSheafData) (h : I = J) :
    eqToHom (congrArg Scheme.IdealSheafData.subscheme h) ≫ J.subschemeι = I.subschemeι := by
  cases h; simp

end AlgebraicGeometry

end

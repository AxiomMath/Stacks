module

public import Mathlib.AlgebraicGeometry.Scheme

/-!
# Taking preimages along a composite of scheme morphisms

Mathlib has `AlgebraicGeometry.Scheme.Hom.comp_base`, that the underlying continuous map of a
composite is the composite of the underlying maps. This module records the one-line consequence
for preimages of sets, which two modules had each proved privately:
`StacksFrontier/AlgebraicGeometry/Blowup/Transform/CartierProduct.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/NormalizationQuasiFiniteLocus.lean`. Their import closures
are 238 and 1360 with no cheap edge between them — pointing either at the other costs over a
thousand modules — so the shared declaration lives here instead, on Mathlib alone.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- The preimage of a set along a composite of morphisms of schemes is the iterated preimage. -/
public theorem preimage_comp_base {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (Z : Set C) :
    (f ≫ g).base ⁻¹' Z = f.base ⁻¹' (g.base ⁻¹' Z) := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]

end AlgebraicGeometry

end

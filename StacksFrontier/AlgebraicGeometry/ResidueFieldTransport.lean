module

public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Transporting a residue field along an equality of points

Two equal points of a scheme have equal stalks and equal residue fields, and the resulting
`eqToHom` identifications are compatible with the residue maps. The statement is used wherever a
construction produces a point only up to a proved equality -- a fibre of a pushforward, a
normalization fibre, a generic point obtained from a component -- and the residue field has to be
read at the other spelling of the point.

## Main results

* `AlgebraicGeometry.residueField_eqToHom_comp_residue`: the identification of residue fields at
  equal points commutes with the residue maps.

## Implementation notes

This module exists to be low in import order. The statement had been written out separately in
`AlgebraicGeometry/Morphisms/Integral/PushforwardStalkFibre.lean`,
`AlgebraicGeometry/Variety/OneDimensional/NormalizationFiber.lean` and
`AlgebraicGeometry/Chow/PrincipalDivisorPushforward/StalkTransport.lean`, none of which imports
another; the first two now take it from here, and the third still carries its own copy.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Transporting a residue field along an equality of points commutes with the residue maps. -/
theorem residueField_eqToHom_comp_residue (Z : Scheme.{u}) {a b : Z} (h : a = b) :
    (eqToHom (congrArg Z.residueField h)).hom.comp (Z.residue a).hom =
      (Z.residue b).hom.comp (eqToHom (congrArg Z.presheaf.stalk h)).hom := by
  cases h
  rfl

end AlgebraicGeometry

end

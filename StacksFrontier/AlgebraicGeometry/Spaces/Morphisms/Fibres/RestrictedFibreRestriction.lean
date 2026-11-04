module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.GeometricallyReduced
import all StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.GeometricallyReduced

/-!
# Restricting the fibre over a section of an algebraic space

Let `f : X ⟶ Y` be a morphism of presheaves on the big fppf site over `S`, let `v` be a section
of `Y` over an object `T` of the site and let `m : T' ⟶ T` be a morphism of the site. The fibre
of `f` over the restricted section `m^* v`, formed over `T'`, is isomorphic to the restriction
along `m` of the fibre of `f` over `v`, formed over `T`.

## Main results

* `AlgebraicGeometry.Space.nonempty_restrictedFibre_iso_relocalizeRestrict`: the comparison
  isomorphism of `AlgebraicGeometry.Space.restrictedFibre` with restriction along `m`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

variable (f : X ⟶ Y) {T T' : Scheme.{u}} (hT : B.Contains T) (hT' : B.Contains T')
  (g : B.obj hT ⟶ B.obj hS) (m : B.obj hT' ⟶ B.obj hT) (v : Y.obj (op (Over.mk g)))

/-- The fibre over a section restricted along `m` is isomorphic to the restriction along `m` of
the fibre: restriction preserves fibre products, and it carries the tautological section of `Y`
over `T` to the tautological section over `T'`. -/
theorem nonempty_restrictedFibre_iso_relocalizeRestrict :
    Nonempty (restrictedFibre B S hS f hT' (m ≫ g) (Y.map (Over.homMk m rfl).op v) ≅
      (OverShriek.relocalizeRestrict m).obj (restrictedFibre B S hS f hT g v)) :=
  ⟨restrictedFibreRestrictIso B S hS f hT hT' g m v⟩

end AlgebraicGeometry.Space

end

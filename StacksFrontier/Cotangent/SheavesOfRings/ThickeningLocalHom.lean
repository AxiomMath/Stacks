module

public import Mathlib.AlgebraicGeometry.Scheme
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Morphisms of ringed spaces over a thickening are local

Let `iX : X ⟶ X'` and `iY : Y ⟶ Y'` be morphisms of locally ringed spaces, let `g : X ⟶ Y` be a
morphism of locally ringed spaces and let `φ : X' ⟶ Y'` be a morphism of the underlying
sheafed spaces with `iX ≫ φ = g ≫ iY`.  If every point of `X'` is the image of a point of `X` —
as for a thickening `X ⟶ X'`, which is a homeomorphism — then `φ` is a morphism of locally
ringed spaces.

At a point `x' = iX x` the stalk maps satisfy `iX_x ∘ φ_{x'} = g_x ∘ iY_{g x}` up to the
identification of stalks along the equality of the two composites, and the right-hand side is a
local homomorphism.  A ring homomorphism whose composite with some ring homomorphism is local is
itself local (`isLocalHom_of_comp`), so `φ_{x'}` is local.  No nilpotence or surjectivity of the
stalk maps of `iX` is needed: only that `iX` hits every point.

This is the locality-on-stalks step by which a morphism of ringed spaces between first order
thickenings of schemes, compatible with a morphism of the reductions, is a morphism of schemes.

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.isLocalHom_stalkMap_of_comp_eq`: `φ` has local stalk
  maps.
* `AlgebraicGeometry.LocallyRingedSpace.homOfCompEq`: `φ` as a morphism of locally ringed
  spaces.
* `AlgebraicGeometry.Scheme.homOfCompEq`: `φ` as a morphism of schemes, when `X'` and `Y'` are
  schemes; its underlying morphism of sheafed spaces is `φ` by `rfl`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- An element of a commutative ring whose image along `eqToHom` is a unit is a unit. -/
theorem isUnit_of_isUnit_eqToHom_hom {R S : CommRingCat.{u}} (e : R = S) (a : R)
    (ha : IsUnit ((eqToHom e).hom a)) : IsUnit a := by
  subst e
  simpa using ha

namespace LocallyRingedSpace

variable {X X' Y Y' : LocallyRingedSpace.{u}} (iX : X ⟶ X') (iY : Y ⟶ Y') (g : X ⟶ Y)
  (φ : X'.toSheafedSpace ⟶ Y'.toSheafedSpace)

/-- **A morphism of sheafed spaces lying over a morphism of locally ringed spaces through a map
hitting every point is local.**  If `iX ≫ φ = g ≫ iY` as morphisms of sheafed spaces and the
underlying map of `iX` is surjective, every stalk map of `φ` is a local ring homomorphism. -/
@[sga "3 V 1.2" "more general"]
theorem isLocalHom_stalkMap_of_comp_eq
    (h : iX.toHom ≫ φ.hom = g.toHom ≫ iY.toHom)
    (hsurj : Function.Surjective iX.base) (x' : X') :
    IsLocalHom (φ.hom.stalkMap x').hom := by
  obtain ⟨x, rfl⟩ := hsurj x'
  have hcomp := PresheafedSpace.stalkMap.congr_hom _ _ h x
  rw [PresheafedSpace.stalkMap.comp, PresheafedSpace.stalkMap.comp] at hcomp
  refine ⟨fun a ha => ?_⟩
  have h1 : IsUnit ((φ.hom.stalkMap (iX.base x) ≫ iX.toHom.stalkMap x).hom a) :=
    ha.map (iX.toHom.stalkMap x).hom
  rw [hcomp] at h1
  have := iY.prop (g.base x)
  have := g.prop x
  exact isUnit_of_isUnit_eqToHom_hom _ _
    (isUnit_of_map_unit (iY.toHom.stalkMap (g.base x)).hom _
      (isUnit_of_map_unit (g.toHom.stalkMap x).hom _ h1))

/-- `φ` as a morphism of locally ringed spaces. -/
def homOfCompEq (h : iX.toHom ≫ φ.hom = g.toHom ≫ iY.toHom)
    (hsurj : Function.Surjective iX.base) : X' ⟶ Y' :=
  homMk φ (isLocalHom_stalkMap_of_comp_eq iX iY g φ h hsurj)

/-- The underlying morphism of sheafed spaces of `homOfCompEq` is `φ`. -/
@[simp]
theorem homOfCompEq_toHom (h : iX.toHom ≫ φ.hom = g.toHom ≫ iY.toHom)
    (hsurj : Function.Surjective iX.base) : (homOfCompEq iX iY g φ h hsurj).toHom = φ.hom :=
  rfl

end LocallyRingedSpace

namespace Scheme

variable {X X' Y Y' : Scheme.{u}} (iX : X ⟶ X') (iY : Y ⟶ Y') (g : X ⟶ Y)
  (φ : X'.toSheafedSpace ⟶ Y'.toSheafedSpace)

/-- **A morphism of ringed spaces between schemes, lying over a morphism of schemes through a
map hitting every point, is a morphism of schemes.**  The typical case is a morphism between first
order thickenings `X ⟶ X'`, `Y ⟶ Y'` of schemes compatible with a morphism `g` of the
reductions. -/
def homOfCompEq (h : iX.toLRSHom.toHom ≫ φ.hom = g.toLRSHom.toHom ≫ iY.toLRSHom.toHom)
    (hsurj : Function.Surjective iX.base) : X' ⟶ Y' :=
  ⟨LocallyRingedSpace.homOfCompEq iX.toLRSHom iY.toLRSHom g.toLRSHom φ h hsurj⟩

/-- The underlying morphism of sheafed spaces of `Scheme.homOfCompEq` is `φ`. -/
@[simp]
theorem homOfCompEq_toLRSHom_toHom
    (h : iX.toLRSHom.toHom ≫ φ.hom = g.toLRSHom.toHom ≫ iY.toLRSHom.toHom)
    (hsurj : Function.Surjective iX.base) :
    (homOfCompEq iX iY g φ h hsurj).toLRSHom.toHom = φ.hom :=
  rfl

end Scheme

end AlgebraicGeometry

end

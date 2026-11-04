module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AmplePullback.QuasiAffineUnitIso
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyRelativelyAmple

/-!
# The resolution property along an affine or quasi-affine morphism

This file proves Stacks 0F88: if `f : X ⟶ Y` is an affine **or** quasi-affine morphism of schemes
and `Y` is quasi-compact, quasi-separated and has the resolution property, then `X` has the
resolution property.

By Stacks 0891 a morphism is quasi-affine exactly when the structure sheaf `𝒪_X` is ample relative
to it. The statement is therefore the case `L = 𝒪_X` of Stacks 0FDD, the transport of the
resolution property along a morphism carrying a relatively ample invertible module.

## Main results

* `AlgebraicGeometry.hasResolutionProperty_of_isQuasiAffineHom`: the quasi-affine case, with the
  hypothesis on `f` as an instance.
* `AlgebraicGeometry.hasResolutionProperty_of_isAffineHom_or_isQuasiAffineHom` (Stacks 0F88): the
  statement in the form the source gives it, with the disjunction as a hypothesis.

## Implementation notes

An affine morphism is quasi-affine, so the disjunction of the source statement collapses to its
second alternative. It is retained in the statement of
`AlgebraicGeometry.hasResolutionProperty_of_isAffineHom_or_isQuasiAffineHom` because that is the
hypothesis the source offers.

## References

* [Stacks Project, Tag 0F88](https://stacks.math.columbia.edu/tag/0F88)
* [Stacks Project, Tag 0FDD](https://stacks.math.columbia.edu/tag/0FDD)
* [Stacks Project, Tag 0891](https://stacks.math.columbia.edu/tag/0891)
-/

@[expose] public section

open CategoryTheory
open Stacks.Ample (unitModule)

universe u

namespace AlgebraicGeometry

/-- **Stacks 0F88**, the quasi-affine case: the source of a quasi-affine morphism onto a
quasi-compact, quasi-separated scheme with the resolution property has the resolution property. -/
theorem hasResolutionProperty_of_isQuasiAffineHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsQuasiAffineHom f] [CompactSpace Y] [QuasiSeparatedSpace Y] [HasResolutionProperty Y] :
    HasResolutionProperty X :=
  hasResolutionProperty_of_isRelativelyAmple f (unitModule X)
    (Stacks.AmplePullback.isRelativelyAmple_of_isQuasiAffineHom_of_iso_unitModule f
      (unitModule X) (Iso.refl _))

/-- **Stacks 0F88**. Let `f : X ⟶ Y` be an affine or quasi-affine morphism of schemes with `Y`
quasi-compact and quasi-separated. If `Y` has the resolution property, so does `X`. -/
@[stacks 0F88 "affine or quasi-affine f; the whole statement"]
theorem hasResolutionProperty_of_isAffineHom_or_isQuasiAffineHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : IsAffineHom f ∨ IsQuasiAffineHom f) [CompactSpace Y] [QuasiSeparatedSpace Y]
    [HasResolutionProperty Y] : HasResolutionProperty X :=
  have : IsQuasiAffineHom f :=
    hf.elim (fun h => @Stacks.QuasiAffineSource.isQuasiAffineHom_of_isAffineHom X Y f h) id
  hasResolutionProperty_of_isQuasiAffineHom f

end AlgebraicGeometry

end

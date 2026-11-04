module

public import StacksFrontier.AlgebraicGeometry.Topologies.AffineSliceAlgebraAdjunction

/-!
# `Spec` into the slice at an affine object hits every affine object

Let `S` be a scheme, let `U` be an object of `Over S` whose total space `U.left` is affine, and
let `R = Γ(U.left, 𝒪)`. The essential image of `AlgebraicGeometry.overAffineAlgSpec U` consists
of the `V : Over U` whose underlying scheme `V.left.left` is affine, and the unit of
`AlgebraicGeometry.overAffineAlgAdjunction U` is an isomorphism at each of them.

## Main definitions

* `AlgebraicGeometry.overAffineSliceEquiv`: the equivalence of the slice of schemes at `Spec R`
  with the slice of `Over S` at `U`.
* `AlgebraicGeometry.overAffineAlgSpecΓIso`: an object of `Over U` with affine underlying scheme
  is isomorphic to the spectrum of its coordinate algebra.
* `AlgebraicGeometry.overAffineAlgSpecΓIsoMk`: the same, for an object presented as
  `CategoryTheory.Over.mk` of a morphism.

## Main results

* `Stacks.CategoryTheory.essImage_comp_equivalence_functor`: the essential image of a functor is
  unchanged, up to transport, by post-composition with an equivalence.
* `AlgebraicGeometry.isIso_unit_algΓAlgSpecAdjunction`: the unit of
  `AlgebraicGeometry.algΓAlgSpecAdjunction` is an isomorphism at every affine object.
* `AlgebraicGeometry.overAffineAlgSpec_eq_comp_overAffineSliceEquiv`:
  `AlgebraicGeometry.overAffineAlgSpec` is `AlgebraicGeometry.algSpec` followed by
  `AlgebraicGeometry.overAffineSliceEquiv`.
* `AlgebraicGeometry.essImage_overAffineAlgSpec`: an object of `Over U` is in the essential image
  of `AlgebraicGeometry.overAffineAlgSpec U` if and only if its underlying scheme is affine.
* `AlgebraicGeometry.isIso_unit_overAffineAlgAdjunction`: the unit of
  `AlgebraicGeometry.overAffineAlgAdjunction U` is an isomorphism at every object of `Over U` with
  affine underlying scheme.
* `AlgebraicGeometry.isIso_unit_overAffineAlgAdjunction_mk`: the same, for an object presented as
  `CategoryTheory.Over.mk` of a morphism.

## References

* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 01I1](https://stacks.math.columbia.edu/tag/01I1)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe v₁ v₂ v₃ u₁ u₂ u₃ u

namespace Stacks.CategoryTheory

open CategoryTheory

/-- An object `X` is in the essential image of `F ⋙ e.functor` exactly when `e.inverse.obj X` is
in the essential image of `F`. -/
theorem essImage_comp_equivalence_functor {A : Type u₁} {B : Type u₂} {C : Type u₃}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] (F : A ⥤ B) (e : B ≌ C) {X : C} :
    (F ⋙ e.functor).essImage X ↔ F.essImage (e.inverse.obj X) :=
  ⟨fun ⟨Y, ⟨i⟩⟩ => ⟨Y, ⟨e.unitIso.app (F.obj Y) ≪≫ e.inverse.mapIso i⟩⟩,
    fun ⟨Y, ⟨i⟩⟩ => ⟨Y, ⟨e.functor.mapIso i ≪≫ e.counitIso.app X⟩⟩⟩

end Stacks.CategoryTheory

namespace AlgebraicGeometry

/-- The unit of `AlgebraicGeometry.algΓAlgSpecAdjunction R` is an isomorphism at every object of
`Over (Spec R)` with affine total space. -/
instance isIso_unit_algΓAlgSpecAdjunction {R : CommRingCat.{u}} (V : Over (Spec R))
    [IsAffine V.left] : IsIso ((algΓAlgSpecAdjunction R).unit.app V) :=
  haveI : (algSpec R).Full := algSpec.instFull
  haveI : (algSpec R).Faithful := algSpec.instFaithful
  ((algΓAlgSpecAdjunction R).isIso_unit_app_iff_mem_essImage).mpr
    (essImage_algSpec.mpr ‹IsAffine V.left›)

variable {S : Scheme.{u}} (U : Over S) [IsAffine U.left]

/-- The equivalence of the slice of schemes at `Spec Γ(U.left, 𝒪)` with the slice of `Over S` at
`U`: the transport along `AlgebraicGeometry.specOverAffineBaseRingIso` followed by the
slice-of-slice equivalence. -/
def overAffineSliceEquiv : Over (Spec (overAffineBaseRing U)) ≌ Over U :=
  (Over.mapIso (specOverAffineBaseRingIso U)).trans (Over.iteratedSliceEquiv U).symm

/-- `AlgebraicGeometry.overAffineAlgSpec` is `AlgebraicGeometry.algSpec` followed by the
equivalence `AlgebraicGeometry.overAffineSliceEquiv`. -/
theorem overAffineAlgSpec_eq_comp_overAffineSliceEquiv :
    overAffineAlgSpec U =
      algSpec (overAffineBaseRing U) ⋙ (overAffineSliceEquiv U).functor := rfl

/-- An object `V` of `Over U` is the spectrum of an algebra over the coordinate ring of `U.left`,
over `U`, exactly when the scheme `V.left.left` underlying it is affine. -/
theorem essImage_overAffineAlgSpec {V : Over U} :
    (overAffineAlgSpec U).essImage V ↔ IsAffine V.left.left :=
  (Stacks.CategoryTheory.essImage_comp_equivalence_functor
    (algSpec (overAffineBaseRing U)) (overAffineSliceEquiv U)).trans essImage_algSpec

/-- For `V` an object of `Over U` whose underlying scheme is affine, the unit of
`AlgebraicGeometry.overAffineAlgAdjunction U` is an isomorphism at `V`. -/
instance isIso_unit_overAffineAlgAdjunction (V : Over U) [IsAffine V.left.left] :
    IsIso ((overAffineAlgAdjunction U).unit.app V) :=
  ((overAffineAlgAdjunction U).isIso_unit_app_iff_mem_essImage).mpr
    ((essImage_overAffineAlgSpec U).mpr ‹IsAffine V.left.left›)

/-- `AlgebraicGeometry.isIso_unit_overAffineAlgAdjunction` for an object of `Over U` presented as
`CategoryTheory.Over.mk` of a morphism `f : W ⟶ U` of `Over S` with `W.left` affine. -/
instance isIso_unit_overAffineAlgAdjunction_mk {W : Over S} (f : W ⟶ U) [IsAffine W.left] :
    IsIso ((overAffineAlgAdjunction U).unit.app (Over.mk f)) :=
  haveI : IsAffine (Over.mk f).left.left := ‹IsAffine W.left›
  isIso_unit_overAffineAlgAdjunction U (Over.mk f)

/-- An object of the slice at `U` with affine underlying scheme is isomorphic, in `Over U`, to the
spectrum of its coordinate algebra, by the inverse of the unit of
`AlgebraicGeometry.overAffineAlgAdjunction U`. -/
def overAffineAlgSpecΓIso (V : Over U) [IsAffine V.left.left] :
    (overAffineAlgSpec U).obj ((overAffineAlgΓ U).obj V) ≅ V :=
  (asIso ((overAffineAlgAdjunction U).unit.app V)).symm

/-- `AlgebraicGeometry.overAffineAlgSpecΓIso` for an object of `Over U` presented as
`CategoryTheory.Over.mk` of a morphism `f : W ⟶ U` of `Over S` with `W.left` affine. -/
def overAffineAlgSpecΓIsoMk {W : Over S} (f : W ⟶ U) [IsAffine W.left] :
    (overAffineAlgSpec U).obj ((overAffineAlgΓ U).obj (Over.mk f)) ≅ Over.mk f :=
  (asIso ((overAffineAlgAdjunction U).unit.app (Over.mk f))).symm

end AlgebraicGeometry

end

module

public import Mathlib.Topology.Sheaves.Functors
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace

/-!
# The inverse-image ringed space

Let `(X, 𝒪_X)` be a ringed space and let `i : Z ⟶ X` be a continuous map. Then `Z` carries the
inverse-image sheaf of rings `i⁻¹𝒪_X`, and `(Z, i⁻¹𝒪_X)` is a ringed space. The unit of the
inverse-image/direct-image adjunction `i⁻¹ ⊣ i_*` provides a canonical morphism of ringed spaces
`(Z, i⁻¹𝒪_X) ⟶ (X, 𝒪_X)` lying over `i`.

## Main definitions

* `AlgebraicGeometry.RingedSpace.inverseImage` is the ringed space `(Z, i⁻¹𝒪_X)`.
* `AlgebraicGeometry.RingedSpace.inverseImageProjection` is the canonical morphism of ringed
  spaces `(Z, i⁻¹𝒪_X) ⟶ (X, 𝒪_X)` over `i`.
* `AlgebraicGeometry.RingedSpace.inverseImageModulePullback` and
  `AlgebraicGeometry.RingedSpace.inverseImageModulePushforward` are the restriction and
  corestriction of sheaves of modules along that morphism, with
  `AlgebraicGeometry.RingedSpace.inverseImageModuleAdjunction` the adjunction between them.

## Main results

* `AlgebraicGeometry.RingedSpace.inverseImageProjection_base` identifies the underlying
  continuous map of the canonical morphism with `i`.
* `AlgebraicGeometry.RingedSpace.inverseImageProjection_c` identifies its structure-sheaf
  component with the unit of the sheaf-level inverse-image/direct-image adjunction.

## Implementation notes

The inverse-image sheaf is Mathlib's `TopCat.Sheaf.pullback`, the left adjoint of
`TopCat.Sheaf.pushforward`, so it is the sheafification of the presheaf-level inverse image; the
sheaf condition for `i⁻¹𝒪_X` therefore comes for free as the second component of the sheaf
object, with no sheafification argument to run here.

A morphism of ringed spaces is a morphism of the underlying presheafed spaces, and its
structure-sheaf datum has the shape `𝒪_X ⟶ i_*(i⁻¹𝒪_X)`, which is exactly the component of the
unit of `TopCat.Sheaf.pullbackPushforwardAdjunction` at `𝒪_X`. The morphism is assembled with
`CategoryTheory.InducedCategory.homMk`, since `AlgebraicGeometry.SheafedSpace` is an induced
category over `AlgebraicGeometry.PresheafedSpace`.

Everything is stated for `AlgebraicGeometry.RingedSpace.{u, u}`, a ringed space whose underlying
space and structure sheaf live in the same universe. For the ringed space and the projection this
is only so that the module-level API applies verbatim; for the module functors it is forced, see
the implementation notes of `StacksFrontier/Topology/Sheaves/Functors/Module/RingedSpace.lean`.

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 008C](https://stacks.math.columbia.edu/tag/008C)
-/

@[expose] public section

open CategoryTheory RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.RingedSpace

variable (X : RingedSpace.{u, u}) {Z : TopCat.{u}} (i : Z ⟶ X.carrier)

/-- The **inverse-image ringed space** `(Z, i⁻¹𝒪_X)` of a ringed space `(X, 𝒪_X)` along a
continuous map `i : Z ⟶ X`: the space `Z`, equipped with the inverse image of the structure
sheaf of `X`. -/
noncomputable def inverseImage : RingedSpace.{u, u} where
  carrier := Z
  presheaf := ((TopCat.Sheaf.pullback CommRingCat.{u} i).obj X.sheaf).obj
  IsSheaf := ((TopCat.Sheaf.pullback CommRingCat.{u} i).obj X.sheaf).property

/-- The underlying space of the inverse-image ringed space `(Z, i⁻¹𝒪_X)` is `Z`. -/
@[simp]
theorem inverseImage_carrier : (inverseImage X i).carrier = Z := rfl

/-- The structure presheaf of the inverse-image ringed space is the underlying presheaf of the
inverse-image sheaf `i⁻¹𝒪_X`. -/
@[simp]
theorem inverseImage_presheaf :
    (inverseImage X i).presheaf = ((TopCat.Sheaf.pullback CommRingCat.{u} i).obj X.sheaf).obj :=
  rfl

/-- The structure sheaf of the inverse-image ringed space is the inverse-image sheaf. -/
theorem inverseImage_sheaf :
    (inverseImage X i).sheaf = (TopCat.Sheaf.pullback CommRingCat.{u} i).obj X.sheaf := rfl

/-- The canonical morphism of ringed spaces `(Z, i⁻¹𝒪_X) ⟶ (X, 𝒪_X)`. Its underlying continuous
map is `i`, and its structure-sheaf datum `𝒪_X ⟶ i_*(i⁻¹𝒪_X)` is the unit of the
inverse-image/direct-image adjunction. -/
noncomputable def inverseImageProjection : inverseImage X i ⟶ X :=
  InducedCategory.homMk
    { base := i
      c := ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} i).unit.app X.sheaf).hom }

/-- The underlying continuous map of `inverseImageProjection X i` is `i`. -/
@[simp]
theorem inverseImageProjection_base : (inverseImageProjection X i).hom.base = i := rfl

/-- The structure-sheaf datum `𝒪_X ⟶ i_*(i⁻¹𝒪_X)` of `inverseImageProjection X i` is the unit of
the inverse-image/direct-image adjunction at `𝒪_X`. -/
@[simp]
theorem inverseImageProjection_c :
    (inverseImageProjection X i).hom.c =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} i).unit.app X.sheaf).hom :=
  rfl

/-- Restriction of sheaves of modules to the inverse-image ringed space: the pullback of
`𝒪_X`-modules along `inverseImageProjection X i`. Since the structure sheaf of the source is
`i⁻¹𝒪_X`, no tensoring takes place and this is ordinary restriction of sections along `i`. -/
noncomputable abbrev inverseImageModulePullback :
    SheafOfModules.{u} (structureSheafRing X) ⥤
      SheafOfModules.{u} (structureSheafRing (inverseImage X i)) :=
  modulePullback (inverseImageProjection X i)

/-- Corestriction of sheaves of modules from the inverse-image ringed space: the pushforward of
`i⁻¹𝒪_X`-modules along `inverseImageProjection X i`. -/
noncomputable abbrev inverseImageModulePushforward :
    SheafOfModules.{u} (structureSheafRing (inverseImage X i)) ⥤
      SheafOfModules.{u} (structureSheafRing X) :=
  modulePushforward (inverseImageProjection X i)

/-- Restriction of modules to the inverse-image ringed space is left adjoint to corestriction. -/
noncomputable def inverseImageModuleAdjunction :
    inverseImageModulePullback X i ⊣ inverseImageModulePushforward X i :=
  modulePullbackPushforwardAdjunction (inverseImageProjection X i)

end AlgebraicGeometry.RingedSpace

end

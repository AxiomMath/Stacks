module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackEssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiCartesianOfPresentation
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiSliceComponentModule

/-!
# The pullback to a slice of the total Zariski site

Let `X` be a simplicial scheme and `(a, W)` an object of its total Zariski site. The degree-`a`
component functor on the slice at `(a, W)`,
`AlgebraicGeometry.SimplicialScheme.sliceComponentModule`, is a restriction of sheaves of modules
along a continuous functor of sites, and the slice of the degree-`a` site at `W` is essentially
small, so it has a left adjoint. This file constructs that adjoint and proves the one thing the
colimit mechanism of Stacks 0D7M asks of it: the counit is invertible on the structure sheaf,
hence on every module on the slice admitting a presentation.

## Main definitions

* `AlgebraicGeometry.SimplicialScheme.sliceModulePullback`: the left adjoint of the degree-`a`
  component functor on the slice at `(a, W)`.
* `AlgebraicGeometry.SimplicialScheme.sliceModulePullbackAdj`: the adjunction.

## Main results

* `AlgebraicGeometry.SimplicialScheme.isIso_sliceModulePullbackObjUnit`: the pullback carries the
  structure sheaf of the slice of the degree-`a` site to the structure sheaf of the slice of the
  total site.
* `AlgebraicGeometry.SimplicialScheme.isIso_sliceCounit_unit`: the counit is invertible on the
  structure sheaf of the slice.
* `AlgebraicGeometry.SimplicialScheme.isIso_sliceCounit_of_presentation`: the counit is
  invertible on every module on the slice with a global presentation.

## Implementation notes

The left adjoint exists because the slice `Over W` of the open-set site of `X_a` is essentially
small in the universe of the schemes: that is the hypothesis of
`PresheafOfModules.isRightAdjoint_pushforward_of_essentiallySmall`, from which Mathlib's
instance for sheaves of modules follows. No universe is collapsed, which is what rules out the
route through `AlgebraicGeometry.RingedSite.Hom`, whose source and target have their objects and
their morphisms in one universe.

That the pullback carries the structure sheaf to the structure sheaf is Mathlib's
`SheafOfModules.pullbackObjUnitToUnit`, invertible because the component inclusion of a slice is
`Over.post` of a functor, hence final: the slice has a terminal object and `Over.post` preserves
it. This is the one place where the slice is essentially different from the total site itself,
where the corresponding left adjoint does *not* carry `𝒪_{X_a}` to `𝒪_X`: the inclusion of a
simplicial degree into the whole total site is not final, its comma categories having one
connected component per simplex map.

The counit on the structure sheaf is then invertible because it is a factor of
`SheafOfModules.pullbackObjUnitToUnit`: by `CategoryTheory.Adjunction.homEquiv_counit` that
comparison is the pullback of the identification of the component of `𝒪_X` with `𝒪_{X_a}`
followed by the counit, and both the comparison and that identification are invertible.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Topology.Simplicial
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.SimplicialScheme

variable (X : SimplicialObject Scheme.{u}) (a : SimplexCategoryᵒᵖ)
  (W : Opens ↥(X.obj a))

/-- **The pullback to a slice of the total Zariski site.** The left adjoint of the degree-`a`
component functor on the slice at `(a, W)`: it exists because the slice of the degree-`a` site at
`W` is essentially small. -/
public noncomputable abbrev sliceModulePullback :=
  SheafOfModules.pullback.{u} (SheafOfModules.overComparison (componentStructureHom X a) W)

/-- The pullback to the slice is left adjoint to the degree-`a` component functor on the
slice. -/
public noncomputable abbrev sliceModulePullbackAdj :
    sliceModulePullback X a W ⊣ sliceComponentModule X a W :=
  SheafOfModules.pullbackPushforwardAdjunction.{u}
    (SheafOfModules.overComparison (componentStructureHom X a) W)

/-- The pullback to the slice preserves colimits, being a left adjoint. -/
public noncomputable instance sliceModulePullback_preservesColimitsOfSize :
    PreservesColimitsOfSize.{u, u} (sliceModulePullback X a W) :=
  (sliceModulePullbackAdj X a W).leftAdjoint_preservesColimits

/-- The identification of the degree-`a` component of `𝒪_X` with the structure sheaf of `X_a`,
restricted to the slice at `(a, W)`, is an isomorphism. -/
public instance isIso_sliceComponentStructureHom :
    IsIso (SheafOfModules.overComparison (componentStructureHom X a) W) :=
  Functor.map_isIso _ _

/-- **The pullback to the slice carries the structure sheaf to the structure sheaf.** The
component inclusion of a slice is `Over.post` of a functor, hence final, which is what Mathlib's
comparison `SheafOfModules.pullbackObjUnitToUnit` needs in order to be invertible. -/
public instance isIso_sliceModulePullbackObjUnit :
    IsIso (SheafOfModules.pullbackObjUnitToUnit
      (SheafOfModules.overComparison (componentStructureHom X a) W)) :=
  inferInstance

/-- **The counit of the slice adjunction is invertible on the structure sheaf of the slice.** It
is a factor of `SheafOfModules.pullbackObjUnitToUnit`, which is invertible because the component
inclusion of a slice is final, and the other factor is the pullback of the identification of the
degree-`a` component of `𝒪_X` with `𝒪_{X_a}`, which is invertible as well. -/
public theorem isIso_sliceCounit_unit :
    IsIso ((sliceModulePullbackAdj X a W).counit.app
      (SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf (zariskiRingedTopos X).O).over
          (sliceObj X a W)))) := by
  have : IsIso (SheafOfModules.unitToPushforwardObjUnit
      (SheafOfModules.overComparison (componentStructureHom X a) W)) :=
    isIso_unitToPushforwardObjUnit' _
  have : IsIso ((sliceModulePullback X a W).map (SheafOfModules.unitToPushforwardObjUnit
      (SheafOfModules.overComparison (componentStructureHom X a) W))) :=
    Functor.map_isIso _ _
  have key : SheafOfModules.pullbackObjUnitToUnit
        (SheafOfModules.overComparison (componentStructureHom X a) W) =
      (sliceModulePullback X a W).map (SheafOfModules.unitToPushforwardObjUnit
          (SheafOfModules.overComparison (componentStructureHom X a) W)) ≫
        (sliceModulePullbackAdj X a W).counit.app
          (SheafOfModules.unit
            ((Stacks.SheafOfModules.Tensor.ringSheaf (zariskiRingedTopos X).O).over
              (sliceObj X a W))) :=
    Adjunction.homEquiv_counit (sliceModulePullbackAdj X a W) _ _ _
  exact IsIso.of_isIso_fac_left key.symm

/-- **The counit of the slice adjunction is invertible on a presented module.** It is a natural
transformation between two functors that preserve colimits — the composite of the component
functor with its left adjoint, and the identity — and it is invertible on the structure sheaf, so
it is invertible on every module exhibited as a cokernel of a map of coproducts of copies of the
structure sheaf. -/
public theorem isIso_sliceCounit_of_presentation
    (M : @SheafOfModules.{u} (Over (sliceObj X a W)) _ _
      ((Stacks.SheafOfModules.Tensor.ringSheaf (zariskiRingedTopos X).O).over (sliceObj X a W)))
    (P : M.Presentation) :
    IsIso ((sliceModulePullbackAdj X a W).counit.app M) := by
  exact Stacks.SheafOfModules.isIso_app_of_presentation_of_unit
    (sliceModulePullbackAdj X a W).counit (isIso_sliceCounit_unit X a W) P

end AlgebraicGeometry.SimplicialScheme

end

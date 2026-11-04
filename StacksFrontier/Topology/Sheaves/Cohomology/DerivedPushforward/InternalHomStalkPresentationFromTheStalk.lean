module

public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomStalkPullbackReduction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackUnit
public import StacksFrontier.Topology.Sheaves.Cohomology.GodementResolution.StalkHomotopy

/-!
# The stalk presentation of a point, built from the stalk functor

`Stacks.Cohomology.DerivedInternalHomStalk.StalkPresentation X x` presents the point `x` as a
one-point ringed space with two compatibilities, `StalkPullbackComparison` and
`InternalHomComparison` at the one-point description.  Here the identification
`D(𝒪_Y) ≌ D(𝒪_{X,x})` is the stalk functor itself, which on a one-point space is an equivalence,
and at that identification the compatibility with derived pullback is the Stacks 0098 comparison,
`pointStalkPullbackComparison`, for an arbitrary ringed space and point.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.onePointStalkEquivalence`: **on a space with a single point,
  the stalk functor on sheaves of modules is an equivalence** onto modules over the stalk of the
  sheaf of rings.
* `Stacks.RingedSpace.restrictedStalkEquivalence`: for a morphism `f : Z ⟶ W` out of a one-point
  ringed space whose germ map at the point is invertible,
  `AlgebraicGeometry.GodementResolution.restrictedStalkFunctor f q` is an equivalence
  `Mod(𝒪_Z) ≌ Mod(𝒪_{W, f q})`.
* `Stacks.Cohomology.DerivedInternalHomStalk.pointStalkModulesEquiv` and
  `Stacks.Cohomology.DerivedInternalHomStalk.pointStalkDerivedEquiv`: that equivalence at the
  one-point inclusion `Y = {x} ⟶ X`, and its derived form `D(𝒪_Y) ≌ D(𝒪_{X,x})`.
* `Stacks.Cohomology.DerivedInternalHomStalk.PointStalkInternalHomComparison`: the
  compatibility that `pointStalkDerivedEquiv` carries the derived internal hom of `Y` to `RHom`
  over `𝒪_{X,x}`.

## Main results

* `AlgebraicGeometry.SheafOfModules.isIso_stalkSkyscraperAdjunction_unit_app_of_unique`: on a
  space with a single point the unit of the stalk--skyscraper adjunction is invertible.  Its
  counit is invertible on every space.
* `Stacks.Cohomology.DerivedInternalHomStalk.pointStalkPullbackComparison`: **the first
  compatibility of the stalk presentation** -- derived pullback along
  `Y = {x} ⟶ X`, read through `pointStalkDerivedEquiv`, is the derived stalk at `x`.
* `Stacks.Cohomology.DerivedInternalHomStalk.stalkPresentationOfInternalHomComparison`: **a
  `StalkPresentation X x` from `PointStalkInternalHomComparison X x`**, for an arbitrary
  ringed space and an arbitrary point.

## References

* [Stacks Project, Tag 0GM8](https://stacks.math.columbia.edu/tag/0GM8)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 009A](https://stacks.math.columbia.edu/tag/009A)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

/-! ### On a one-point space the stalk functor is an equivalence -/

namespace AlgebraicGeometry.SheafOfModules

variable {T : TopCat.{u}}
  (O : CategoryTheory.Sheaf (Opens.grothendieckTopology T) RingCat.{u}) (p : T)

/-- **The counit of the stalk--skyscraper adjunction is `skyscraperStalkIsoObj`**, on any space:
the stalk at `p` of the skyscraper at `p` with value `N` is `N`. -/
theorem stalkSkyscraperAdjunction_counit_app
    (N : ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) O.obj p)) :
    (stalkSkyscraperAdjunction O p).counit.app N = (skyscraperStalkIsoObj O p N).hom :=
  Eq.trans
    (congrArg (fun k ↦ k ≫ (skyscraperStalkIsoObj O p N).hom)
      ((stalkFunctor O p).map_id (skyscraperObj O p N)))
    (Category.id_comp _)

/-- Each component of the counit of the stalk--skyscraper adjunction is an isomorphism. -/
instance isIso_stalkSkyscraperAdjunction_counit_app
    (N : ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) O.obj p)) :
    IsIso ((stalkSkyscraperAdjunction O p).counit.app N) :=
  (stalkSkyscraperAdjunction_counit_app O p N).symm ▸ (skyscraperStalkIsoObj O p N).isIso_hom

/-- The counit of the stalk--skyscraper adjunction is an isomorphism, on any space. -/
instance isIso_stalkSkyscraperAdjunction_counit :
    IsIso (stalkSkyscraperAdjunction O p).counit :=
  NatIso.isIso_of_isIso_app _

/-- **The stalk functor applied to the unit of the stalk--skyscraper adjunction is invertible**,
on any space. -/
theorem isIso_stalkFunctor_map_stalkSkyscraperAdjunction_unit_app
    (M : _root_.SheafOfModules.{u} O) :
    IsIso ((stalkFunctor O p).map ((stalkSkyscraperAdjunction O p).unit.app M)) :=
  IsIso.of_isIso_fac_right ((stalkSkyscraperAdjunction O p).left_triangle_components M)

/-- **On a space whose only point is `p`, the unit of the stalk--skyscraper adjunction is
invertible.** -/
theorem isIso_stalkSkyscraperAdjunction_unit_app_of_unique (hT : ∀ q : T, q = p)
    (M : _root_.SheafOfModules.{u} O) :
    IsIso ((stalkSkyscraperAdjunction O p).unit.app M) := by
  rw [isIso_iff_forall_isIso_stalkFunctor_map]
  exact fun q ↦ hT q ▸ isIso_stalkFunctor_map_stalkSkyscraperAdjunction_unit_app O p M

/-- **On a space with a single point, taking the stalk is an equivalence**
`Mod(𝒪) ≌ Mod(𝒪_p)`. -/
def onePointStalkEquivalence (hT : ∀ q : T, q = p) :
    _root_.SheafOfModules.{u} O ≌
      ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) O.obj p) :=
  haveI : ∀ M : _root_.SheafOfModules.{u} O,
      IsIso ((stalkSkyscraperAdjunction O p).unit.app M) :=
    isIso_stalkSkyscraperAdjunction_unit_app_of_unique O p hT
  haveI : IsIso (stalkSkyscraperAdjunction O p).unit := NatIso.isIso_of_isIso_app _
  (stalkSkyscraperAdjunction O p).toEquivalence

end AlgebraicGeometry.SheafOfModules

/-! ### The restricted stalk functor of a one-point inclusion is an equivalence -/

namespace Stacks.RingedSpace

open AlgebraicGeometry.GodementResolution AlgebraicGeometry.SheafOfModules
open RingedSpaceModuleAdjunction

variable {Z W : AlgebraicGeometry.RingedSpace.{u, u}} (f : Z ⟶ W) (q : Z.carrier)

/-- Restriction of scalars along an invertible germ map is an equivalence. -/
theorem isEquivalence_restrictScalars_stalkRingMap (h : IsIso (stalkRingMap f q)) :
    (ModuleCat.restrictScalars.{u, u, u} (stalkRingMap f q).hom).IsEquivalence :=
  ModuleCat.restrictScalars_isEquivalence_of_ringEquiv
    (@asIso _ _ _ _ _ h).ringCatIsoToRingEquiv

/-- **For a morphism out of a one-point ringed space with invertible germ map, the restricted
stalk functor is an equivalence** `Mod(𝒪_Z) ≌ Mod(𝒪_{W, f q})`. -/
def restrictedStalkEquivalence (hZ : ∀ r : Z.carrier, r = q) (h : IsIso (stalkRingMap f q)) :
    _root_.SheafOfModules.{u} (structureSheafRing Z) ≌
      ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := W.carrier)
        (structureSheafRing W).obj (f.hom.base q)) :=
  haveI := isEquivalence_restrictScalars_stalkRingMap f q h
  (onePointStalkEquivalence (structureSheafRing Z) q hZ).trans
    (ModuleCat.restrictScalars.{u, u, u} (stalkRingMap f q).hom).asEquivalence

/-- The functor of `restrictedStalkEquivalence f q hZ h` is `restrictedStalkFunctor f q`. -/
theorem restrictedStalkEquivalence_functor (hZ : ∀ r : Z.carrier, r = q)
    (h : IsIso (stalkRingMap f q)) :
    (restrictedStalkEquivalence f q hZ h).functor = restrictedStalkFunctor f q := rfl

/-- Pulling a sheaf of `𝒪_W`-modules back to the one-point space `Z` and reading it as a module
over `𝒪_{W, f q}` through `restrictedStalkEquivalence` is taking its stalk at `f q`. -/
def pullbackRestrictedStalkComparison (hZ : ∀ r : Z.carrier, r = q)
    (h : IsIso (stalkRingMap f q)) :
    modulePullback f ⋙ (restrictedStalkEquivalence f q hZ h).functor ≅
      stalkFunctor (structureSheafRing W) (f.hom.base q) :=
  (restrictedStalkPullbackIso f q h).symm

end Stacks.RingedSpace

/-! ### The presentation of a point of a ringed space -/

namespace Stacks.Cohomology.DerivedInternalHomStalk

open RingedSpaceModuleAdjunction
open Stacks.AssociatedSheaf
open Stacks.Cohomology.DerivedInternalHomPullback
open Stacks.Cohomology.DerivedProjectionFormula (singleUnit)

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local implicit_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable (X : RingedSpace.{u, u}) (x : X.carrier)

attribute [local instance] stalkCommRing

/-- **The germ map of the one-point inclusion is invertible**, in the `RingCat`-valued spelling
that sheaves of modules are stated at. -/
instance isIso_stalkRingMap_pointHom :
    IsIso (Stacks.RingedSpace.stalkRingMap (pointHom X x) PUnit.unit) :=
  Stacks.RingedSpace.isIso_stalkRingMap_of_isIso_stalkMap (pointHom X x) PUnit.unit inferInstance

/-- **The identification `Mod(𝒪_Y) ≌ Mod(𝒪_{X,x})` through the stalk at the one point.** -/
def pointStalkModulesEquiv :
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules (pointSpace X x) ≌
      ModuleCat.{u} (stalkRing X x) :=
  Stacks.RingedSpace.restrictedStalkEquivalence (pointHom X x) PUnit.unit
    (pointSpace_unique_pt X x) inferInstance

/-- The functor of `pointStalkModulesEquiv X x` is additive. -/
instance pointStalkModulesEquiv_functor_additive :
    (pointStalkModulesEquiv X x).functor.Additive :=
  (pointStalkModulesEquiv X x).functor.additive_of_preserves_binary_products

/-- The inverse of `pointStalkModulesEquiv X x` is additive. -/
instance pointStalkModulesEquiv_inverse_additive :
    (pointStalkModulesEquiv X x).inverse.Additive := inferInstance

/-- Pulling a sheaf of `𝒪_X`-modules back to the one-point space `Y = {x}` and reading it as an
`𝒪_{X,x}`-module through `pointStalkModulesEquiv` is taking its stalk at `x`. -/
def pointStalkPullbackComparisonAbelian :
    pointPullback X x ⋙ (pointStalkModulesEquiv X x).functor ≅
      AlgebraicGeometry.SheafOfModules.stalkFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) x :=
  Stacks.RingedSpace.pullbackRestrictedStalkComparison (pointHom X x) PUnit.unit
    (pointSpace_unique_pt X x) inferInstance

/-- **The identification `D(𝒪_Y) ≌ D(𝒪_{X,x})`**: `pointStalkModulesEquiv` carried to unbounded
derived categories. -/
def pointStalkDerivedEquiv :
    DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules
        (pointSpace X x)) ≌
      DerivedCategory (ModuleCat.{u} (stalkRing X x)) :=
  Dualizing.mapDerivedCategoryEquivalenceOfEquivalence (pointStalkModulesEquiv X x)

/-- **The first compatibility of the stalk presentation, with no hypothesis.**  Derived pullback
along the one-point inclusion `Y = {x} ⟶ X`, read through `pointStalkDerivedEquiv`, is the derived
stalk at `x`. -/
def pointStalkPullbackComparison :
    derivedPullbackFunctor (pointHom X x) ⋙ (pointStalkDerivedEquiv X x).functor ≅
      derivedStalk X x :=
  haveI : PreservesFiniteLimits
      (RingedSpaceModuleAdjunction.modulePullback (pointHom X x)) :=
    RingedSpaceModuleAdjunction.preservesFiniteLimits_modulePullback_of_isFlat _
      (isFlat_pointHom X x)
  haveI : PreservesColimits
      (RingedSpaceModuleAdjunction.modulePullback (pointHom X x)) :=
    RingedSpaceModuleAdjunction.preservesColimits_modulePullback (pointHom X x)
  haveI : PreservesFiniteLimits (pointPullback X x) :=
    RingedSpaceModuleAdjunction.preservesFiniteLimits_modulePullback_of_isFlat _
      (isFlat_pointHom X x)
  haveI : PreservesColimits (pointPullback X x) :=
    RingedSpaceModuleAdjunction.preservesColimits_modulePullback (pointHom X x)
  haveI : PreservesFiniteColimits (pointPullback X x) := inferInstance
  haveI : (pointPullback X x).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ Functor.map_zero
      (RingedSpaceModuleAdjunction.modulePullback (pointHom X x)) _ _⟩
  haveI : (pointPullback X x).Additive :=
    Functor.additive_of_preserves_binary_products _
  Functor.isoWhiskerRight
      (show derivedPullbackFunctor (pointHom X x) ≅ (pointPullback X x).mapDerivedCategory from
        Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackIsoMapDerivedCategory
          (pointHom X x) (isFlat_pointHom X x))
      (pointStalkDerivedEquiv X x).functor ≪≫
    Dualizing.mapDerivedCategoryCompNatIso (pointPullback X x)
      (pointStalkModulesEquiv X x).functor
      (AlgebraicGeometry.SheafOfModules.stalkFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) x)
      (pointStalkPullbackComparisonAbelian X x)

/-- **The internal-hom compatibility**: `pointStalkDerivedEquiv` carries the derived internal
hom of `Y = {x}` to `RHom` over `𝒪_{X,x}`. -/
abbrev PointStalkInternalHomComparison :=
  Functor.uncurry.obj (Stacks.SheafOfModules.derivedSheafHom (pointSpace X x).sheaf) ⋙
      (pointStalkDerivedEquiv X x).functor ≅
    (pointStalkDerivedEquiv X x).functor.op.prod (pointStalkDerivedEquiv X x).functor ⋙
      stalkDerivedHom X x

/-- **A presentation of the point from the internal-hom compatibility**, for an arbitrary
ringed space `X` and an arbitrary point `x`.

Every other field is constructed: the one-point ringed space is `pointSpace`, the inclusion is
`pointHom`, its flatness is `Stacks.AssociatedSheaf.isIso_stalkMap_fromCoefficientPoint`, the
identification `D(𝒪_Y) ≌ D(𝒪_{X,x})` is `pointStalkDerivedEquiv` and its compatibility with
derived pullback is `pointStalkPullbackComparison`. -/
def stalkPresentationOfInternalHomComparison (homIso : PointStalkInternalHomComparison X x) :
    StalkPresentation X x where
  space := pointSpace X x
  pt := PUnit.unit
  unique_pt := pointSpace_unique_pt X x
  hom := pointHom X x
  base_pt := pointHom_base_pt X x
  stalkMap_isIso := inferInstance
  equiv := pointStalkDerivedEquiv X x
  stalkIso := pointStalkPullbackComparison X x
  homIso := homIso

end Stacks.Cohomology.DerivedInternalHomStalk

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionBaseChangeConstruction
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.Algebra
public import StacksFrontier.CategoryTheory.Adjunction.MateIsIso

/-!
# The Zariski reading on a represented algebraic space as a right adjoint

For an object `T` of the big fppf site, the Zariski reading of an `𝒪`-module on the small étale
site of `yoneda.obj T` — its direct image along the inclusion of the Zariski opens of the scheme
of `T` (`AlgebraicGeometry.Space.selfOpensStructureMap`) — is right adjoint to the
associated-module functor of Stacks 03DU, transported to the small étale site of `yoneda.obj T`.
The unit is invertible on quasi-coherent modules on the scheme and the counit on quasi-coherent
`𝒪`-modules on the small étale site: this is Stacks 03DU, part (4), on quasi-coherent objects.

## Main definitions

* `AlgebraicGeometry.Space.zariskiReadingAdjunction`: the adjunction.

## Main results

* `AlgebraicGeometry.Space.isIso_zariskiReadingAdjunction_unit_app`: the unit is invertible at a
  quasi-coherent module.
* `AlgebraicGeometry.Space.isIso_zariskiReadingAdjunction_counit_app`: the counit is invertible at
  a quasi-coherent `𝒪`-module.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Reading a Zariski open of the scheme of `T` as an étale chart of `yoneda.obj T` is
continuous, the topology of the source spelled on the scheme of `T`. -/
instance isContinuous_selfOpensFunctor' (T : BigFppfOver B S hS) :
    (selfOpensFunctor B S hS T).IsContinuous
      (Opens.grothendieckTopology ↥((BigFppfOver.toScheme B S hS).obj T))
      (SmallEtale.topology B S hS (yoneda.obj T)) :=
  isContinuous_selfOpensFunctor B S hS T

/-- The Zariski reading, through the identification of the two small étale sites, is restriction
of modules on the small étale site of the scheme to its Zariski site. -/
def zariskiReadingIso (T : BigFppfOver B S hS) :=
  NatIso.ofComponents (F := (representedSmallEtaleModuleEquivalence B S hS T).inverse ⋙
      _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
    (selfOpensPushforwardIso B S hS T) fun _ =>
      SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun _ => rfl)

/-- **The Zariski reading is right adjoint to the associated-module functor of Stacks 03DU**, read
on the small étale site of `yoneda.obj T`. -/
def zariskiReadingAdjunction (T : BigFppfOver B S hS) :=
  ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property).comp
    (representedSmallEtaleModuleEquivalence B S hS T).toAdjunction).ofNatIsoRight
    (zariskiReadingIso T)

/-- **The unit of the Zariski reading adjunction is invertible at a quasi-coherent module.** -/
theorem isIso_zariskiReadingAdjunction_unit_app (T : BigFppfOver B S hS)
    (M : ((BigFppfOver.toScheme B S hS).obj T).Modules) (hM : SheafOfModules.IsQuasicoherent M) :
    IsIso ((zariskiReadingAdjunction T).unit.app M) := by
  have := _root_.AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj T) T.left.property ⟨M, hM⟩
  simp only [zariskiReadingAdjunction, Adjunction.ofNatIsoRight, NatTrans.comp_app,
    Adjunction.comp_unit_app]
  have : IsIso ((representedSmallEtaleModuleEquivalence B S hS T).toAdjunction.unit.app
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj M)) :=
    inferInstanceAs (IsIso ((representedSmallEtaleModuleEquivalence B S hS T).unitIso.hom.app _))
  have : IsIso (((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property ⋙
      (representedSmallEtaleModuleEquivalence B S hS T).functor).whiskerLeft
        (zariskiReadingIso T).hom).app M) :=
    inferInstanceAs (IsIso ((zariskiReadingIso T).app _).hom)
  infer_instance

/-- **The counit of the Zariski reading adjunction is invertible at a quasi-coherent
`𝒪`-module.** -/
theorem isIso_zariskiReadingAdjunction_counit_app (T : BigFppfOver B S hS)
    (N : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN : N.IsQuasicoherentOnSite) :
    IsIso ((zariskiReadingAdjunction T).counit.app N) := by
  let E := representedSmallEtaleModuleEquivalence B S hS T
  have hG : (E.inverse.obj N).IsQuasicoherentOnSite :=
    (isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS T (E.inverse.obj N)).1
      (SheafOfModules.IsQuasicoherentOnSite.of_iso (E.counitIso.app N).symm hN)
  have hR : SheafOfModules.IsQuasicoherent
      ((_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property).obj (E.inverse.obj N)) :=
    ObjectProperty.prop_of_iso
      (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf)
      (selfOpensPushforwardIso B S hS T N).symm (isQuasicoherent_zariskiReading_piece T N hN)
  have := _root_.AlgebraicGeometry.SmallEtale.isIso_counit (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj T) T.left.property (E.inverse.obj N) hG hR
  have : IsIso ((representedSmallEtaleModuleEquivalence B S hS T).toAdjunction.counit.app N) :=
    inferInstanceAs (IsIso ((representedSmallEtaleModuleEquivalence B S hS T).counitIso.app N).hom)
  have : IsIso (((_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property).comp
        (representedSmallEtaleModuleEquivalence B S hS T).toAdjunction).counit.app N) :=
    (congrArg IsIso (Adjunction.comp_counit_app
      (_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction
        (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
      (representedSmallEtaleModuleEquivalence B S hS T).toAdjunction N)).mpr inferInstance
  exact @Adjunction.isIso_ofNatIsoRight_counit_app _ _ _ _ _ _ _ _ _ N this

end AlgebraicGeometry.Space

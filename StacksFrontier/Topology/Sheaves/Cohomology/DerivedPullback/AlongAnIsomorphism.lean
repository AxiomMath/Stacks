module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnconditional
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackComp

/-!
# Derived pullback along an isomorphism of ringed spaces

For an isomorphism `e : X ≅ Y` of ringed spaces the derived pullbacks `Le.hom^*` and `Le.inv^*`
are mutually inverse equivalences of the derived categories of modules.

## Main definitions

* `Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackIdIso`: `L(𝟙 X)^* ≅ 𝟭`.
* `Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackHomInvIso` and
  `Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackInvHomIso`: the two round trips
  `Le.hom^* ⋙ Le.inv^* ≅ 𝟭` and `Le.inv^* ⋙ Le.hom^* ≅ 𝟭`.
* `Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackEquivalence`: the resulting
  equivalence `D(𝒪_Y) ≌ D(𝒪_X)`.

## Implementation notes

The identity case is the whole content: degreewise pullback along `𝟙 X` is isomorphic to the
identity functor, so after passage to the homotopy category and localization it inverts the
quasi-isomorphisms; hence the identity functor of `D(𝒪_X)`, with the resulting comparison, is a
left derived functor of it, and uniqueness of left derived functors identifies it with
`L(𝟙 X)^*`. The two compositions are then
`Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical` transported along
`e.hom ≫ e.inv = 𝟙 X` and `e.inv ≫ e.hom = 𝟙 Y`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction

namespace Stacks.Cohomology.DerivedPullbackAlongIso

noncomputable section

section HomotopyCategory

variable {ι : Type*} {V : Type*} [Category* V] [Preadditive V]
  {W : Type*} [Category* W] [Preadditive W]

/-- A natural isomorphism of additive functors induces a natural isomorphism of the induced
functors on homotopy categories. -/
def mapHomotopyCategoryIso {F G : V ⥤ W} [F.Additive] [G.Additive] (α : F ≅ G)
    (c : ComplexShape ι) : F.mapHomotopyCategory c ≅ G.mapHomotopyCategory c where
  hom := NatTrans.mapHomotopyCategory α.hom c
  inv := NatTrans.mapHomotopyCategory α.inv c
  hom_inv_id := by
    rw [← NatTrans.mapHomotopyCategory_comp, α.hom_inv_id, NatTrans.mapHomotopyCategory_id]
  inv_hom_id := by
    rw [← NatTrans.mapHomotopyCategory_comp, α.inv_hom_id, NatTrans.mapHomotopyCategory_id]

/-- The functor induced on homotopy categories by the identity functor is the identity
functor. -/
def mapHomotopyCategoryIdIso (V : Type*) [Category* V] [Preadditive V] (c : ComplexShape ι) :
    (𝟭 V).mapHomotopyCategory c ≅ 𝟭 (HomotopyCategory V c) :=
  Quotient.natIsoLift _ ((𝟭 V).mapHomotopyCategoryFactors c ≪≫
    Functor.isoWhiskerRight (Functor.mapHomologicalComplexIdIso V c)
      (HomotopyCategory.quotient V c) ≪≫
    Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm)

end HomotopyCategory

universe u

attribute [local instance] HasDerivedCategory.standard

/-- Degreewise pullback along the identity, followed by localization, is the localization
functor. -/
def pullbackOnHomotopyIdIso (X : RingedSpace.{u, u}) :
    DerivedCategory.Qh ⋙ 𝟭 (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) ≅
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackOnHomotopy (𝟙 X) :=
  Functor.rightUnitor _ ≪≫
    (Functor.isoWhiskerRight
      (mapHomotopyCategoryIso (RingedSpaceModuleAdjunction.modulePullbackId X)
          (ComplexShape.up ℤ) ≪≫
        mapHomotopyCategoryIdIso _ (ComplexShape.up ℤ)) DerivedCategory.Qh ≪≫
      Functor.leftUnitor _).symm

/-- **Derived pullback along the identity is the identity**, `L(𝟙 X)^* ≅ 𝟭`. -/
def derivedPullbackIdIso (X : RingedSpace.{u, u}) :
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback (𝟙 X) ≅
      𝟭 (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :=
  letI : (𝟭 (DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))).IsLeftDerivedFunctor
      (pullbackOnHomotopyIdIso X).hom
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ (pullbackOnHomotopyIdIso X)
  Functor.leftDerivedUnique
    (LF := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback (𝟙 X))
    (LF' := 𝟭 (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))))
    (α := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison (𝟙 X))
    (α'₂ := (pullbackOnHomotopyIdIso X).hom)
    (W := HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))

variable {X Y : RingedSpace.{u, u}}

/-- Equal morphisms of ringed spaces have equal derived pullbacks. -/
theorem derivedPullback_eq_of_eq {f g : X ⟶ Y} (h : f = g) :
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f =
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g := by
  rw [h]

/-- **The round trip `Le.hom^* ⋙ Le.inv^* ≅ 𝟭` on `D(𝒪_Y)`** for an isomorphism `e : X ≅ Y` of
ringed spaces. -/
def derivedPullbackHomInvIso (e : X ≅ Y) :
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback e.hom ⋙
        Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback e.inv ≅
      𝟭 (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :=
  Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical e.inv e.hom ≪≫
    eqToIso (derivedPullback_eq_of_eq e.inv_hom_id) ≪≫ derivedPullbackIdIso Y

/-- **The round trip `Le.inv^* ⋙ Le.hom^* ≅ 𝟭` on `D(𝒪_X)`** for an isomorphism `e : X ≅ Y` of
ringed spaces. -/
def derivedPullbackInvHomIso (e : X ≅ Y) :
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback e.inv ⋙
        Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback e.hom ≅
      𝟭 (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :=
  Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical e.hom e.inv ≪≫
    eqToIso (derivedPullback_eq_of_eq e.hom_inv_id) ≪≫ derivedPullbackIdIso X

/-- **An isomorphism of ringed spaces induces an equivalence of the derived categories of
modules**, with the derived pullbacks along the two directions as the two functors. -/
def derivedPullbackEquivalence (e : X ≅ Y) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) ≌
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) :=
  CategoryTheory.Equivalence.mk
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback e.hom)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback e.inv)
    (derivedPullbackHomInvIso e).symm (derivedPullbackInvHomIso e)

end

end Stacks.Cohomology.DerivedPullbackAlongIso

end

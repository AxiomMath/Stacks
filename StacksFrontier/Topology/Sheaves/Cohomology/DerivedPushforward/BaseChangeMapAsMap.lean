module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMap
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquare

/-!
# The derived base change map as the base change map of the derived adjunctions

The derived base change map `Lg^*Rf_*K ⟶ Rf'_*L(g')^*K` of [Stacks, Tag 08HY] for a commutative
square of ringed spaces is `Stacks.CategoryTheory.BaseChange.map` of the two derived adjunctions
and the two identifications of the composite derived pullbacks, at the standard model.

## Main results

* `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_eq_map`
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedPullback.Composition (derivedPullbackCompIsoCanonical)

universe u

namespace Stacks.Cohomology.DerivedBaseChange

attribute [local instance 10000] HasDerivedCategory.standard

/-- A mate, read as a base change map. -/
theorem _root_.Stacks.CategoryTheory.BaseChange.mateEquiv_app_eq_map {A B A' B' : Type*}
    [Category A] [Category B] [Category A'] [Category B']
    {Lf : A ⥤ B} {Rf : B ⥤ A} {Lf' : A' ⥤ B'} {Rf' : B' ⥤ A'}
    {Lg : A ⥤ A'} {Lg' : B ⥤ B'} {Lc : A ⥤ B'}
    (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc) (K : B) :
    (mateEquiv adjf adjf' (TwoSquare.mk _ _ _ _ (eg.hom ≫ ef.inv))).app K =
      Stacks.CategoryTheory.BaseChange.map adjf adjf' eg ef K := rfl

namespace Mate

variable {X' X S' S : RingedSpace.{u, u}}
  {Lf : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
  {Lg : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S'))}
  {Lf' : DerivedCategory (SheafOfModules.{u} (structureSheafRing S')) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
  {Lg' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
  {Lc : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
  {Rf : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S))}
  {Rf' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X')) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S'))}

/-- `Mate.derivedBaseChangeMap` is the mate at a component. -/
theorem derivedBaseChangeMap_eq_mateEquiv_app (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf')
    (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    derivedBaseChangeMap adjf adjf' eg ef K =
      (mateEquiv adjf adjf' (TwoSquare.mk _ _ _ _ (eg.hom ≫ ef.inv))).app K := rfl

end Mate

/-- The derived base change map of [Stacks, Tag 08HY] is the base change map of the derived
adjunctions. -/
theorem derivedBaseChangeMap_eq_map {X' X S' S : RingedSpace.{u, u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (sq : g' ≫ f = f' ≫ g)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    derivedBaseChangeMap g' f' f g sq K =
      Stacks.CategoryTheory.BaseChange.map (derivedAdjunction f) (derivedAdjunction f')
        (derivedPullbackCompIsoLeft g' f' f g sq) (derivedPullbackCompIsoCanonical g' f) K :=
  (Mate.derivedBaseChangeMap_eq_mateEquiv_app _ _ _ _ K).trans
    (Stacks.CategoryTheory.BaseChange.mateEquiv_app_eq_map _ _ _ _ K)

end Stacks.Cohomology.DerivedBaseChange

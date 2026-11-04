module

public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit
public import StacksFrontier.Homology.Injectives.Spaltenstein.RightDerivedFunctor

/-!
# Right derived functors presented on cochain complexes are triangulated

A right derived functor of an additive functor `F : A ⥤ B` out of a Grothendieck abelian
category can be presented either by a unit on `CochainComplex A ℤ`, along the localization
`DerivedCategory.Q`, or by a unit on `HomotopyCategory A (ComplexShape.up ℤ)`, along
`DerivedCategory.Qh`.  Triangulatedness is available in the second presentation only, because
only the homotopy category is pretriangulated.  This file transports a unit of the first kind
to one of the second, and so equips a derived functor presented on cochain complexes with its
shift-compatibility and triangulatedness.

## Main definitions

* `Stacks.Injectives.homotopyUnitOfComplexUnit`: the unit read on the homotopy category.
* `Stacks.Injectives.commShiftOfComplexUnit`: the shift-compatibility.

## Main results

* `Stacks.Injectives.isRightDerivedFunctor_homotopyUnitOfComplexUnit`: the transported unit
  again exhibits the functor as a right derived functor.
* `Stacks.Injectives.isTriangulated_of_complexUnit`: triangulatedness.
* `Stacks.Injectives.isRightDerivedFunctor_complexUnit`: the transport in the other direction, of
  a unit on the homotopy category to one on cochain complexes along
  `Stacks.Injectives.complexUnit`.

## Implementation notes

The two presentations have the same values on K-injective complexes, where both units are
invertible, and K-injective complexes recognise right derived functors in both presentations
(Stacks 070K): at the level of cochain complexes this is
`Stacks.Injectives.KInjectiveResolution.isIso_app_of_isKInjective`, and on the homotopy
category it is the companion statement
`Stacks.Injectives.KInjectiveResolution.isRightDerivedFunctor_of_isIso_app_quotient_isKInjective`.
Triangulatedness is then `Stacks.Injectives.rightDerivedFunctor_isTriangulated`, for the
shift-compatibility `Stacks.Injectives.commShiftOfComplexUnit`.

## References

* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w w₁ w₂ v₁ v₂ u₁ u₂

namespace Stacks.Injectives

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
  (F : A ⥤ B) [F.Additive] (RF : DerivedCategory A ⥤ DerivedCategory B)
  (α : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ RF)

/-- The comparison map of a right derived functor presented on cochain complexes, transported
to the homotopy category of cochain complexes. -/
noncomputable def quotientUnitOfComplexUnit :
    HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙
        (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⟶
      HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙ (DerivedCategory.Qh ⋙ RF) where
  app K := (DerivedCategory.quotientCompQhIso B).hom.app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫ α.app K ≫
    RF.map ((DerivedCategory.quotientCompQhIso A).inv.app K)
  naturality K L f := by
    change DerivedCategory.Qh.map ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f)) ≫
        (DerivedCategory.quotientCompQhIso B).hom.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) ≫
          α.app L ≫ RF.map ((DerivedCategory.quotientCompQhIso A).inv.app L) =
      ((DerivedCategory.quotientCompQhIso B).hom.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
          α.app K ≫ RF.map ((DerivedCategory.quotientCompQhIso A).inv.app K)) ≫
        RF.map (DerivedCategory.Qh.map
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f))
    rw [DerivedCategory.quotientCompQhIso_hom_naturality_assoc]
    simp only [Category.assoc, ← RF.map_comp]
    rw [dsimp% α.naturality_assoc f]
    simp only [← RF.map_comp]
    rw [DerivedCategory.quotientCompQhIso_inv_naturality]

/-- The comparison map of a right derived functor presented on cochain complexes, read on the
homotopy category.  This is the inverse transport of `Stacks.Injectives.complexUnit`. -/
noncomputable def homotopyUnitOfComplexUnit :
    F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF :=
  Quotient.natTransLift _ (quotientUnitOfComplexUnit F RF α)

/-- The value of the transported unit at the image of a cochain complex. -/
lemma homotopyUnitOfComplexUnit_app_quotient (K : CochainComplex A ℤ) :
    (homotopyUnitOfComplexUnit F RF α).app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) =
      (DerivedCategory.quotientCompQhIso B).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫ α.app K ≫
        RF.map ((DerivedCategory.quotientCompQhIso A).inv.app K) :=
  rfl

variable [IsGrothendieckAbelian.{w} A]
  [RF.IsRightDerivedFunctor α (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]

/-- The transported unit is invertible at every K-injective complex, the unit on cochain
complexes being invertible there. -/
lemma isIso_homotopyUnitOfComplexUnit_app_quotient (I : CochainComplex A ℤ)
    (hI : I.IsKInjective) :
    IsIso ((homotopyUnitOfComplexUnit F RF α).app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) := by
  have := KInjectiveResolution.isIso_app_of_isKInjective DerivedCategory.Q RF α
    (KInjectiveResolution.invertsQuasiIso_mapHomologicalComplex_comp_Q
      (A := B) (C := A) F) I hI
  rw [homotopyUnitOfComplexUnit_app_quotient]
  exact IsIso.comp_isIso' ((DerivedCategory.quotientCompQhIso B).app _).isIso_hom
    (IsIso.comp_isIso' this
      (RF.mapIso ((DerivedCategory.quotientCompQhIso A).app I).symm).isIso_hom)

/-- **A right derived functor presented on cochain complexes is one presented on the homotopy
category.**  Both presentations are recognised by their unit being invertible at the
K-injective complexes. -/
instance isRightDerivedFunctor_homotopyUnitOfComplexUnit :
    RF.IsRightDerivedFunctor (homotopyUnitOfComplexUnit F RF α)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  KInjectiveResolution.isRightDerivedFunctor_of_isIso_app_quotient_isKInjective
    (fun K => exists_kInjective_resolution_of_grothendieck K) _ RF _
    (isIso_homotopyUnitOfComplexUnit_app_quotient F RF α)

/-- **A right derived functor presented on cochain complexes commutes with the shift.** -/
@[instance_reducible]
noncomputable def commShiftOfComplexUnit : RF.CommShift ℤ :=
  Functor.IsRightDerivedFunctor.commShift RF (homotopyUnitOfComplexUnit F RF α)
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ℤ

/-- **A right derived functor presented on cochain complexes is triangulated.** -/
lemma isTriangulated_of_complexUnit :
    letI := commShiftOfComplexUnit F RF α
    RF.IsTriangulated :=
  rightDerivedFunctor_isTriangulated F RF (homotopyUnitOfComplexUnit F RF α)

section ComplexUnitOfHomotopyUnit

variable (β : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF)
  [RF.IsRightDerivedFunctor β (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]

/-- **A right derived functor presented on the homotopy category is one presented on cochain
complexes**, with `Stacks.Injectives.complexUnit` as its unit.  This is the transport inverse to
`Stacks.Injectives.isRightDerivedFunctor_homotopyUnitOfComplexUnit`, and as there both
presentations are recognised by the invertibility of the unit at the K-injective complexes. -/
instance isRightDerivedFunctor_complexUnit :
    RF.IsRightDerivedFunctor (complexUnit F RF β)
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) :=
  (KInjectiveResolution.isRightDerivedFunctor_iff_isIso_app_of_isKInjective DerivedCategory.Q RF
      (complexUnit F RF β)
      (KInjectiveResolution.invertsQuasiIso_mapHomologicalComplex_comp_Q (A := B) (C := A) F)).2
    fun K hK =>
      letI := hK
      isIso_complexUnit_app F RF β K

end ComplexUnitOfHomotopyUnit

end Stacks.Injectives

end

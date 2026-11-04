module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayCupPairing
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.RealizationShift
public import StacksFrontier.CategoryTheory.Triangulated.ConnectingMorphismNatTrans
public import StacksFrontier.Algebra.Homology.HomotopyCategory.InducedCommShift
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareCommShift
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomologyCompare
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.HomologySingleShiftGeneric
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped

/-!
# The Leray identification commutes with the shift

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces. The Leray identification
`Hⁿ(Y, Rf_*K) ≅ Hⁿ(X, K)` ([Stacks, Tag 0D5W]) is compatible with the identifications
`Hⁿ(-, M[s]) ≅ Hⁿ⁺ˢ(-, M)`, where `Rf_*` and the derived sections functors commute with the shift
as right derived functors.

The Leray comparison `RΓ(f⁻¹ V, -) ⟶ RΓ(V, -) ∘ Rf_*` is the descent along a right derived
functor of a transformation which commutes with the shift, so it commutes with the shift
(`Stacks.Triangulated.natTransCommShift_rightDerivedDesc`); so does the identification of derived
sections over `f⁻¹ ⊤` with derived global sections on `X` with restricted scalars.

## Main results

* `Stacks.Cohomology.LerayCupPairing.natTransCommShift_lerayRestrictIso_hom`: the Leray
  identification `RΓ(Y, Rf_* -) ≅ RΓ(X, -)` commutes with the shift.
* `Stacks.Cohomology.LerayCupPairing.lerayCohomologyIso_shift`: **the Leray identification on
  cohomology commutes with the identifications `Hⁿ(-, M[s]) ≅ Hⁿ⁺ˢ(-, M)`.**

## References

* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.GlobalKunneth Stacks.Cohomology.DerivedGlobalCupProduct
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.RealizationShift (shiftHomologyIsoU)
universe u

namespace Stacks.Cohomology.SiteCohomologyPresheaf

universe v₁ v₂ v₃ u₁ u₂ u₃ wG wD wD₁ wD₂

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{wG} A]
    [HasDerivedCategory.{wD} A]
  {B₁ : Type u₂} [Category.{v₂} B₁] [Abelian B₁] [HasDerivedCategory.{wD₁} B₁]
  {B₂ : Type u₃} [Category.{v₃} B₂] [Abelian B₂] [HasDerivedCategory.{wD₂} B₂]
  (F : A ⥤ B₁) [F.Additive]
  (G : B₁ ⥤ B₂) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- The comparison of the two sources commutes with the shift. -/
instance natTransCommShift_mapDerivedCategorySourceIso_hom :
    NatTrans.CommShift (mapDerivedCategorySourceIso F G).hom ℤ := by
  have h₁ : NatTrans.CommShift ((Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (F.mapHomotopyCategory (ComplexShape.up ℤ))
      G.mapDerivedCategoryFactorsh.hom ≫ (Functor.associator _ _ _).inv) ℤ := inferInstance
  have h₂ : NatTrans.CommShift (Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).hom
      DerivedCategory.Qh) ℤ := inferInstance
  have h₃ := NatTrans.CommShift.comp (A := ℤ)
    (τ := (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (F.mapHomotopyCategory (ComplexShape.up ℤ))
      G.mapDerivedCategoryFactorsh.hom ≫ (Functor.associator _ _ _).inv)
    (τ' := Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).hom
      DerivedCategory.Qh)
  have heq : (mapDerivedCategorySourceIso F G).hom =
      ((Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (F.mapHomotopyCategory (ComplexShape.up ℤ))
        G.mapDerivedCategoryFactorsh.hom ≫ (Functor.associator _ _ _).inv) ≫
      Functor.whiskerRight
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).hom
        DerivedCategory.Qh := by
    ext K
    simp [mapDerivedCategorySourceIso]
  rw [heq]
  exact h₃

/-- **The comparison `R(F) ⋙ G ≅ R(F ⋙ G)` commutes with the shift**, for the commutations of the
right derived functors with the shift. -/
instance natTransCommShift_totalRightDerivedMapDerivedCategoryIso_hom :
    NatTrans.CommShift (totalRightDerivedMapDerivedCategoryIso F G).hom ℤ := by
  have := isRightDerivedFunctor_totalRightDerived_comp (A := A)
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) G.mapDerivedCategory
  have : NatTrans.CommShift (totalRightDerivedCompUnit
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      G.mapDerivedCategory) ℤ := by
    dsimp only [totalRightDerivedCompUnit]
    infer_instance
  dsimp only [totalRightDerivedMapDerivedCategoryIso, Functor.rightDerivedNatIso,
    Functor.rightDerivedNatTrans]
  exact Stacks.Triangulated.natTransCommShift_rightDerivedDesc _ _
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ℤ _ _

end Stacks.Cohomology.SiteCohomologyPresheaf

open scoped Stacks.StandardDerivedModel

namespace Stacks.Cohomology.LerayCupPairing

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The unit of the Leray comparison commutes with the shift. -/
instance natTransCommShift_lerayUnit (V : Opens Y.carrier) :
    NatTrans.CommShift (lerayUnit f V) ℤ := by
  have hA : NatTrans.CommShift (Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (pushforwardPreimageSectionsIso f V)
        (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft ((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ))
        (derivedSectionsOverOpenUnit Y V)) ℤ := inferInstance
  have hB : NatTrans.CommShift ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (derivedPushforwardUnit f) (derivedSectionsOverOpen Y V) ≫
        (Functor.associator _ _ _).hom) ℤ := inferInstance
  have hC := NatTrans.CommShift.comp (A := ℤ) (τ := Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (pushforwardPreimageSectionsIso f V)
        (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft ((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ))
        (derivedSectionsOverOpenUnit Y V))
    (τ' := (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (derivedPushforwardUnit f) (derivedSectionsOverOpen Y V) ≫
        (Functor.associator _ _ _).hom)
  have heq : lerayUnit f V = (Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (pushforwardPreimageSectionsIso f V)
        (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft ((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ))
        (derivedSectionsOverOpenUnit Y V)) ≫ ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (derivedPushforwardUnit f) (derivedSectionsOverOpen Y V) ≫
        (Functor.associator _ _ _).hom) := by
    ext K
    simp [lerayUnit]
  rw [heq]
  exact hC

/-- **The Leray comparison commutes with the shift.** -/
instance natTransCommShift_lerayComparison (V : Opens Y.carrier) :
    NatTrans.CommShift (lerayComparison f V) ℤ :=
  Stacks.Triangulated.natTransCommShift_rightDerivedDesc _ _ _ ℤ _ _

/-- The identification of derived sections over `f⁻¹ ⊤` with derived global sections with
restricted scalars commutes with the shift. -/
instance natTransCommShift_preimageSectionsIso_hom :
    NatTrans.CommShift (preimageSectionsIso f).hom ℤ :=
  SiteCohomologyPresheaf.natTransCommShift_totalRightDerivedMapDerivedCategoryIso_hom
    _ _

/-- **The Leray identification `RΓ(Y, Rf_* -) ≅ RΓ(X, -)` commutes with the shift.** -/
instance natTransCommShift_lerayRestrictIso_hom :
    NatTrans.CommShift (lerayRestrictIso f).hom ℤ := by
  have := isIso_lerayComparison f ⊤
  have h₀ : NatTrans.CommShift (asIso (lerayComparison f ⊤)).hom ℤ :=
    (inferInstance : NatTrans.CommShift (lerayComparison f ⊤) ℤ)
  have h₁ : NatTrans.CommShift (lerayIso f).hom ℤ :=
    NatTrans.CommShift.of_iso_symm (asIso (lerayComparison f ⊤)) ℤ
  dsimp only [lerayRestrictIso, Iso.trans_hom]
  infer_instance

/-- **The Leray identification on cohomology commutes with the shift.** For `s + n = n'`, the
square

`Hⁿ(Y, Rf_*(K[s])) ≅ Hⁿ(Y, (Rf_*K)[s]) ≅ Hⁿ'(Y, Rf_*K) ≅ Hⁿ'(X, K)`,
`Hⁿ(Y, Rf_*(K[s])) ≅ Hⁿ(X, K[s]) ≅ Hⁿ'(X, K)`

commutes. -/
theorem lerayCohomologyIso_shift (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (s n n' : ℤ) (h : s + n = n') :
    (DerivedCategory.homologyFunctor _ n).map
        ((baseSections Y).map (((derivedPushforward f).commShiftIso s).hom.app K)) ≫
      (shiftHomologyIsoU (baseSections Y) ((derivedPushforward f).obj K) s n n' h).hom ≫
      (lerayCohomologyIso f K n').hom =
    (lerayCohomologyIso f (K⟦s⟧) n).hom ≫
      (restrictGlobal f).map (shiftHomologyIsoU (baseSections X) K s n n' h).hom := by
  have e₁ := Stacks.Cohomology.RealizationShift.shiftHomologyIsoU_comp_hom
    (derivedPushforward f) (baseSections Y) K s n n' h
  have e₂ := Stacks.Cohomology.RealizationShift.shiftHomologyIsoU_naturality_of_commShift
    (lerayRestrictIso f).hom K s n n' h
  have e₃ := Stacks.DeRham.GysinCupHodge.shiftHomologyIsoU_mapDerivedCategory
    (baseSections X) (restrictGlobal f) K s n n' h
  rw [CategoryTheory.Functor.mapDerivedCategoryHomologyIso_eq_mapDerivedCategoryHomologyFunctorIso,
    CategoryTheory.Functor.mapDerivedCategoryHomologyIso_eq_mapDerivedCategoryHomologyFunctorIso]
    at e₃
  have e₁' : (DerivedCategory.homologyFunctor _ n).map
        ((baseSections Y).map (((derivedPushforward f).commShiftIso s).hom.app K)) ≫
      (shiftHomologyIsoU (baseSections Y) ((derivedPushforward f).obj K) s n n' h).hom =
      (shiftHomologyIsoU (derivedPushforward f ⋙ baseSections Y) K s n n' h).hom :=
    e₁.symm
  dsimp only [lerayCohomologyIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ ((restrictGlobal f).mapDerivedCategoryHomologyFunctorIso n').hom.app
    ((baseSections X).obj K)) ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (DerivedCategory.homologyFunctor _ n').map ((lerayRestrictIso f).hom.app K))
        e₁').trans e₂.symm))).trans ?_
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e₃).trans (Category.assoc _ _ _).symm)

end Stacks.Cohomology.LerayCupPairing

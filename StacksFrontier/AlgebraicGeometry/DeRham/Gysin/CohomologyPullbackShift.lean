module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CohomologyPullbackComparisonCanonical
public import StacksFrontier.Algebra.Homology.HomotopyCategory.InducedCommShift
public import StacksFrontier.CategoryTheory.Triangulated.ConnectingMorphismNatTrans
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeShift
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreePullbackIdentity

/-!
# The pullback map on cohomology does not depend on the placement degree

`Stacks.DeRham.GysinCohomologyBaseChange.pullbackHgroup` computes the pullback map
`H^n(X, ℳ) ⟶ H^n(X', ℳ')` of [Stacks, Tag 01F9] along a morphism of ringed spaces `G : X' ⟶ X`
by placing both modules in a chosen degree `a` of the derived category.  For the canonical
comparisons `CohomologyPullbackComparison.canonical` this file proves that the result does not
depend on `a`: `pullbackHgroup_canonical_eq`.  It is the shift-compatibility of the two
comparisons the map is built from:

* `singleToDerivedPushforward_comm`: the map `(G_*ℳ')[-a] ⟶ RG_*(ℳ'[-a])` of [Stacks, Tag 01F8]
  commutes with the identifications of the single functors with the shift, read through
  `derivedPushforwardUnitQ`, the unit of `RG_*` on cochain complexes, which commutes with the
  shift;
* the Leray comparison `lerayComparisonAb` of [Stacks, Tag 01EZ] commutes with the shift, being
  the descent along a right derived functor of a unit that does
  (`Stacks.Triangulated.natTransCommShift_rightDerivedDesc`);
* `homologyTotalRightDerivedSingleShiftIso_comp_eq`: a family of maps between right derived
  functors on single objects compatible with the shift induces one map on the classical derived
  functors, whatever the placement degree.

## References

* [Stacks Project, Tag 01F8](https://stacks.math.columbia.edu/tag/01F8)
* [Stacks Project, Tag 01F9](https://stacks.math.columbia.edu/tag/01F9)
* [Stacks Project, Tag 01EZ](https://stacks.math.columbia.edu/tag/01EZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DeRham.CohomologicalGysin

namespace Stacks.DeRham.GysinCohomologyBaseChange

universe u

open _root_.DerivedCategory

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat
attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory

/-- Cancelling an isomorphism around an identity at the front, in term mode. -/
private theorem iso_cancel_helper' {𝒞 : Type*} [Category 𝒞] {A B C : 𝒞} (e : B ≅ A) (u : B ⟶ B)
    (f : A ⟶ C) (hu : u = 𝟙 _) : e.inv ≫ u ≫ e.hom ≫ f = f := by
  rw [hu, Category.id_comp, Iso.inv_hom_id_assoc]

/-- Bookkeeping for `homologyTotalRightDerivedSingleShiftIso_comp_eq`. -/
private theorem helper_shift {𝒞 : Type*} [Category 𝒞] {P₁ P₂ Q₁ Q₂ R₁ R₂ S₁ S₂ : 𝒞}
    (ν₁ : P₁ ≅ Q₁) (ν₂ : P₂ ≅ Q₂) (I₁ : Q₁ ≅ R₁) (I₂ : Q₂ ≅ R₂) {x : P₁ ⟶ S₁} {y : S₁ ⟶ S₂}
    {z : S₂ ⟶ P₂} {w : P₁ ⟶ P₂} {v : Q₁ ⟶ Q₂} (hk : x ≫ y ≫ z = w)
    (hn : w ≫ ν₂.hom = ν₁.hom ≫ v) :
    (ν₁ ≪≫ I₁).inv ≫ x ≫ y ≫ z ≫ (ν₂ ≪≫ I₂).hom = I₁.inv ≫ v ≫ I₂.hom := by
  simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc]
  rw [reassoc_of% hk, reassoc_of% hn, Iso.inv_hom_id_assoc]

section Generic

variable {A : Type*} [Category A] [Abelian A] [EnoughInjectives A] [HasDerivedCategory A]
  {A' : Type*} [Category A'] [Abelian A'] [EnoughInjectives A'] [HasDerivedCategory A']
  {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B]

/-- **A family of maps between right derived functors on single objects, compatible with the
shift, induces the same map on classical right derived functors in every placement degree.** -/
theorem homologyTotalRightDerivedSingleShiftIso_comp_eq (F₁ : A ⥤ B) [F₁.Additive]
    (RF₁ : DerivedCategory A ⥤ DerivedCategory B)
    (α₁ : F₁.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF₁)
    [RF₁.IsRightDerivedFunctor α₁ (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hres₁ : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (F₂ : A' ⥤ B) [F₂.Additive]
    (RF₂ : DerivedCategory A' ⥤ DerivedCategory B)
    (α₂ : F₂.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF₂)
    [RF₂.IsRightDerivedFunctor α₂ (HomotopyCategory.quasiIso A' (ComplexShape.up ℤ))]
    (hres₂ : ∀ K : CochainComplex A' ℤ, ∃ (I : CochainComplex A' ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (M : A) (M' : A') (a m : ℤ) (n : ℕ) (hn : m - a = n)
    (Ψ : RF₁.obj ((DerivedCategory.singleFunctor A a).obj M) ⟶
      RF₂.obj ((DerivedCategory.singleFunctor A' a).obj M'))
    (Ψ₀ : RF₁.obj ((DerivedCategory.singleFunctor A 0).obj M) ⟶
      RF₂.obj ((DerivedCategory.singleFunctor A' 0).obj M'))
    (hΨ : RF₁.map (((DerivedCategory.singleFunctors A).shiftIso (-a) a 0 (by omega)).inv.app M) ≫
          (Functor.commShiftIso (self := Functor.IsRightDerivedFunctor.commShift RF₁ α₁
            (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ℤ) RF₁ (-a)).hom.app
            ((DerivedCategory.singleFunctor A 0).obj M) ≫
          (shiftFunctor (DerivedCategory B) (-a)).map Ψ₀ =
        Ψ ≫ RF₂.map
            (((DerivedCategory.singleFunctors A').shiftIso (-a) a 0 (by omega)).inv.app M') ≫
          (Functor.commShiftIso (self := Functor.IsRightDerivedFunctor.commShift RF₂ α₂
            (HomotopyCategory.quasiIso A' (ComplexShape.up ℤ)) ℤ) RF₂ (-a)).hom.app
            ((DerivedCategory.singleFunctor A' 0).obj M')) :
    (Stacks.DerivedFunctor.homologyTotalRightDerivedSingleShiftIso F₁ RF₁ α₁ hres₁ M a m n hn).inv ≫
        (DerivedCategory.homologyFunctor B m).map Ψ ≫
        (Stacks.DerivedFunctor.homologyTotalRightDerivedSingleShiftIso F₂ RF₂ α₂ hres₂ M' a m n
          hn).hom =
      (Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso F₁ RF₁ α₁ hres₁ M n).inv ≫
        (DerivedCategory.homologyFunctor B n).map Ψ₀ ≫
        (Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso F₂ RF₂ α₂ hres₂ M' n).hom := by
  let := Functor.IsRightDerivedFunctor.commShift RF₁ α₁
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ℤ
  let := Functor.IsRightDerivedFunctor.commShift RF₂ α₂
    (HomotopyCategory.quasiIso A' (ComplexShape.up ℤ)) ℤ
  have hsh := ((DerivedCategory.homologyFunctor B 0).shiftIso (-a) m n (by omega)).hom.naturality Ψ₀
  simp only [Stacks.DerivedFunctor.homologyTotalRightDerivedSingleShiftIso, Iso.trans_inv,
    Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv,
    Category.assoc]
  have key : (DerivedCategory.homologyFunctor B m).map
        ((RF₁.commShiftIso (-a)).inv.app ((DerivedCategory.singleFunctor A 0).obj M) ≫
          RF₁.map (((DerivedCategory.singleFunctors A).shiftIso (-a) a 0 (by omega)).hom.app M)) ≫
      (DerivedCategory.homologyFunctor B m).map Ψ ≫
      (DerivedCategory.homologyFunctor B m).map
        (RF₂.map (((DerivedCategory.singleFunctors A').shiftIso (-a) a 0 (by omega)).inv.app M') ≫
          (RF₂.commShiftIso (-a)).hom.app ((DerivedCategory.singleFunctor A' 0).obj M')) =
      (DerivedCategory.homologyFunctor B m).map
        ((shiftFunctor (DerivedCategory B) (-a)).map Ψ₀) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    rw [Category.assoc, ← hΨ, ← Category.assoc (RF₁.map _), ← Functor.map_comp, Iso.hom_inv_id_app]
    exact iso_cancel_helper' ((RF₁.commShiftIso (-a)).app _) _ _
      (CategoryTheory.Functor.map_id RF₁ _)
  have hnat := (DerivedCategory.homologyFunctor B 0).shiftIso_hom_naturality (-a) m n (by omega) Ψ₀
  exact helper_shift _ _ _ _ key hnat

end Generic

variable {X X' : RingedSpace.{u, u}} (G : X' ⟶ X)

/-- The Leray unit commutes with the shift. -/
instance : NatTrans.CommShift (lerayUnitAb G) ℤ := by
  have hA : NatTrans.CommShift (Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
      (pushforwardSectionsIso G) (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft ((modulePushforward G).mapHomotopyCategory (ComplexShape.up ℤ))
      (derivedGlobalSectionsUnit X)) ℤ := inferInstance
  have hB : NatTrans.CommShift ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (derivedPushforwardUnit G) (derivedGlobalSections X) ≫
        (Functor.associator _ _ _).hom) ℤ := inferInstance
  have hC := NatTrans.CommShift.comp (A := ℤ) (τ := Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (pushforwardSectionsIso G) (ComplexShape.up ℤ)).inv
      DerivedCategory.Qh ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft ((modulePushforward G).mapHomotopyCategory (ComplexShape.up ℤ))
      (derivedGlobalSectionsUnit X))
    (τ' := (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (derivedPushforwardUnit G) (derivedGlobalSections X) ≫
        (Functor.associator _ _ _).hom)
  have heq : lerayUnitAb G = (Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (pushforwardSectionsIso G) (ComplexShape.up ℤ)).inv
      DerivedCategory.Qh ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft ((modulePushforward G).mapHomotopyCategory (ComplexShape.up ℤ))
      (derivedGlobalSectionsUnit X)) ≫ ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (derivedPushforwardUnit G) (derivedGlobalSections X) ≫
        (Functor.associator _ _ _).hom) := by
    simp only [lerayUnitAb, Category.assoc]
  rw [heq]
  exact hC

/-- **The Leray comparison of [Stacks, Tag 01EZ] commutes with the shift.** -/
instance : NatTrans.CommShift (lerayComparisonAb G) ℤ :=
  Stacks.Triangulated.natTransCommShift_rightDerivedDesc _ _ _ ℤ _ _

/-- If `z ≫ w = x ≫ y` and `u = 𝟙 _`, then `x ≫ y ≫ R = z ≫ w ≫ u ≫ R`. Used in term mode,
where `rw` cannot see through two spellings of one object. -/
private theorem assoc_helper {𝒞 : Type*} [Category 𝒞] {W₀ W₁ W₂ W₃ W₄ : 𝒞} (x : W₀ ⟶ W₁)
    (y : W₁ ⟶ W₂) (z : W₀ ⟶ W₃) (w : W₃ ⟶ W₂) (u : W₂ ⟶ W₂) {R : W₂ ⟶ W₄}
    (he : z ≫ w = x ≫ y) (hu : u = 𝟙 _) : x ≫ y ≫ R = z ≫ w ≫ u ≫ R := by
  rw [hu, Category.id_comp, ← Category.assoc z, he, Category.assoc]

/-- Cancelling an isomorphism around an identity, in term mode. -/
private theorem iso_cancel_helper {𝒞 : Type*} [Category 𝒞] {A B C : 𝒞} (f : A ⟶ B) (e : C ≅ B)
    (u : C ⟶ C) (hu : u = 𝟙 _) : f ≫ e.inv ≫ u ≫ e.hom = f := by
  rw [hu, Category.id_comp, Iso.inv_hom_id, Category.comp_id]

/-- The derivation unit of `RG_*`, read on cochain complexes through `Q`. -/
def derivedPushforwardUnitQ :
    (modulePushforward G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ derivedPushforward G :=
  Functor.whiskerLeft ((modulePushforward G).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso (RModules X)).inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight ((modulePushforward G).mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (HomotopyCategory.quotient (RModules X') (ComplexShape.up ℤ))
      (derivedPushforwardUnit G) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso (RModules X')).hom
      (derivedPushforward G)

/-- The unit of `RG_*` on cochain complexes commutes with the shift. -/
instance : NatTrans.CommShift (derivedPushforwardUnitQ G) ℤ := by
  have h1 : NatTrans.CommShift (Functor.whiskerLeft
      ((modulePushforward G).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso (RModules X)).inv ≫ (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight ((modulePushforward G).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).inv DerivedCategory.Qh) ℤ := inferInstance
  have h2 : NatTrans.CommShift ((Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (HomotopyCategory.quotient (RModules X') (ComplexShape.up ℤ))
        (derivedPushforwardUnit G) ≫ (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (DerivedCategory.quotientCompQhIso (RModules X')).hom
        (derivedPushforward G)) ℤ := inferInstance
  have hC := NatTrans.CommShift.comp (A := ℤ) (τ := Functor.whiskerLeft
      ((modulePushforward G).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso (RModules X)).inv ≫ (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight ((modulePushforward G).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).inv DerivedCategory.Qh)
    (τ' := (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (HomotopyCategory.quotient (RModules X') (ComplexShape.up ℤ))
        (derivedPushforwardUnit G) ≫ (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (DerivedCategory.quotientCompQhIso (RModules X')).hom
        (derivedPushforward G))
  have heq : derivedPushforwardUnitQ G = (Functor.whiskerLeft
      ((modulePushforward G).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso (RModules X)).inv ≫ (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight ((modulePushforward G).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).inv DerivedCategory.Qh) ≫ ((Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (HomotopyCategory.quotient (RModules X') (ComplexShape.up ℤ))
        (derivedPushforwardUnit G) ≫ (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (DerivedCategory.quotientCompQhIso (RModules X')).hom
        (derivedPushforward G)) := by
    simp only [derivedPushforwardUnitQ, Category.assoc]
  rw [heq]
  exact hC

/-- The comparison of the single functors into `D(C)` with the shift is the localization of the
one on complexes. -/
theorem derivedCategory_singleFunctors_shiftIso_hom_app {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (n a a' : ℤ) (h : n + a = a') (M : C) :
    ((DerivedCategory.singleFunctors C).shiftIso n a a' h).hom.app M =
      (DerivedCategory.Q.commShiftIso n).inv.app ((CochainComplex.singleFunctor C a').obj M) ≫
        DerivedCategory.Q.map
          (((CochainComplex.singleFunctors C).shiftIso n a a' h).hom.app M) := by
  simp [DerivedCategory.singleFunctors]

/-- The single map of [Stacks, Tag 01F8] through `Q`. -/
theorem singleToDerivedPushforward_app_eq (a : ℤ) (M' : RModules X') :
    (singleToDerivedPushforward G a).app M' =
      DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex (modulePushforward G)
        (ComplexShape.up ℤ) a).inv.app M') ≫
      (derivedPushforwardUnitQ G).app ((CochainComplex.singleFunctor (RModules X') a).obj M') := by
  have e1 := Stacks.DerivedIndexing.singleFunctorIsoCompQh_hom_app (C := RModules X) a
    ((modulePushforward G).obj M')
  have e1' := Stacks.DerivedIndexing.singleFunctorIsoCompQh_hom_app (C := RModules X') a M'
  have e2 : (singleFunctorIsoCompQh (RModules X') a).inv.app M' =
      (DerivedCategory.quotientCompQhIso (RModules X')).hom.app
        ((CochainComplex.singleFunctor (RModules X') a).obj M') :=
    Iso.inv_ext (f := (singleFunctorIsoCompQh (RModules X') a).app M')
      ((congrArg (· ≫ (DerivedCategory.quotientCompQhIso (RModules X')).hom.app
        ((CochainComplex.singleFunctor (RModules X') a).obj M')) e1').trans
        (Iso.inv_hom_id_app _ _))
  have e3h :=
    Stacks.AlgebraicGeometry.TopDegreeBaseChange.mapHomotopyCategorySingleFunctor_hom_app_eq
    (T := modulePushforward G) a M'
  have e3 : ((modulePushforward G).mapHomotopyCategorySingleFunctor a).inv.app M' =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex (modulePushforward G)
          (ComplexShape.up ℤ) a).inv.app M') :=
    Iso.inv_ext (f := ((modulePushforward G).mapHomotopyCategorySingleFunctor a).app M')
      ((congrArg (· ≫ (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex (modulePushforward G)
          (ComplexShape.up ℤ) a).inv.app M')) e3h).trans
            (((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map_comp _ _).symm.trans
              ((congrArg (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
                (Iso.hom_inv_id_app _ _)).trans (CategoryTheory.Functor.map_id _ _))))
  have e4 := DerivedCategory.quotientCompQhIso_inv_naturality
    ((HomologicalComplex.singleMapHomologicalComplex (modulePushforward G)
      (ComplexShape.up ℤ) a).inv.app M')
  simp only [singleToDerivedPushforward, derivedPushforwardUnitQ, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp]
  rw [e1, e2, e3]
  exact assoc_helper _ _ _ _ _ e4 (by
    simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv]
    exact CategoryTheory.Functor.map_id _ _)

/-- **The single map of [Stacks, Tag 01F8] is compatible with the shift.** -/
theorem singleToDerivedPushforward_comm (n a a' : ℤ) (h : n + a = a') (M' : RModules X') :
    ((DerivedCategory.singleFunctors (RModules X)).shiftIso n a a' h).hom.app
        ((modulePushforward G).obj M') ≫ (singleToDerivedPushforward G a).app M' =
      (shiftFunctor (DerivedCategory (RModules X)) n).map
          ((singleToDerivedPushforward G a').app M') ≫
        ((derivedPushforward G).commShiftIso n).inv.app
          ((DerivedCategory.singleFunctor (RModules X') a').obj M') ≫
        (derivedPushforward G).map
          (((DerivedCategory.singleFunctors (RModules X')).shiftIso n a a' h).hom.app M') := by
  set Y := (CochainComplex.singleFunctor (RModules X') a').obj M'
  have hs := Stacks.DerivedIndexing.singleMapHomologicalComplex_shiftIso (modulePushforward G)
    n a a' h M'
  have hu := NatTrans.app_shift (derivedPushforwardUnitQ G) n Y
  have hnat := (derivedPushforwardUnitQ G).naturality
    (((CochainComplex.singleFunctors (RModules X')).shiftIso n a a' h).hom.app M')
  have hQ := DerivedCategory.Q.commShiftIso_hom_naturality
    ((HomologicalComplex.singleMapHomologicalComplex (modulePushforward G)
      (ComplexShape.up ℤ) a').inv.app M') n
  simp only [Functor.comp_map, Functor.commShiftIso_comp_hom_app,
    Functor.commShiftIso_comp_inv_app, Functor.comp_obj] at hu hnat
  rw [derivedCategory_singleFunctors_shiftIso_hom_app,
    derivedCategory_singleFunctors_shiftIso_hom_app,
    singleToDerivedPushforward_app_eq, singleToDerivedPushforward_app_eq]
  have hs' := congrArg DerivedCategory.Q.map hs
  simp only [Functor.map_comp] at hs'
  rw [Category.assoc, ← Functor.map_comp_assoc, hs, Functor.map_comp, Functor.map_comp,
    Category.assoc, Category.assoc, hnat, hu]
  have hcancel : DerivedCategory.Q.map
        ((((modulePushforward G).mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).inv.app
          Y) ≫
      DerivedCategory.Q.map
        ((((modulePushforward G).mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).hom.app
          Y) =
      𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app]; exact CategoryTheory.Functor.map_id _ _
  have hQ' : (DerivedCategory.Q.commShiftIso n).inv.app
        ((CochainComplex.singleFunctor (RModules X) a').obj ((modulePushforward G).obj M')) ≫
      DerivedCategory.Q.map ((shiftFunctor (CochainComplex (RModules X) ℤ) n).map
        ((HomologicalComplex.singleMapHomologicalComplex (modulePushforward G)
          (ComplexShape.up ℤ) a').inv.app M')) ≫
      (DerivedCategory.Q.commShiftIso n).hom.app
        (((modulePushforward G).mapHomologicalComplex (ComplexShape.up ℤ)).obj Y) =
      (shiftFunctor (DerivedCategory (RModules X)) n).map (DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex (modulePushforward G)
          (ComplexShape.up ℤ) a').inv.app M')) := by
    rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom]; exact hQ
  simp only [Category.assoc]
  rw [reassoc_of% hcancel, reassoc_of% hQ']
  simp only [Functor.map_comp, Category.assoc]
  rfl

/-- **The derived `g`-map of [Stacks, Tag 01F8] for a module in degree `a` is the degree-`0` one
shifted by `-a`.** -/
theorem derivedPushforwardMap_canonical_shift (a : ℤ) {M : RModules X} {M' : RModules X'}
    (φ : M ⟶ (modulePushforward G).obj M') :
    derivedPushforwardMap (CohomologyPullbackComparison.canonical G) a φ ≫
        (derivedPushforward G).map
          (((DerivedCategory.singleFunctors (RModules X')).shiftIso (-a) a 0
            (by omega)).inv.app M') ≫
        ((derivedPushforward G).commShiftIso (-a)).hom.app
          ((DerivedCategory.singleFunctor (RModules X') 0).obj M') =
      ((DerivedCategory.singleFunctors (RModules X)).shiftIso (-a) a 0 (by omega)).inv.app M ≫
        (shiftFunctor (DerivedCategory (RModules X)) (-a)).map
          (derivedPushforwardMap (CohomologyPullbackComparison.canonical G) 0 φ) := by
  have h1 := singleToDerivedPushforward_comm G (-a) a 0 (by omega) M'
  have h2 :=
    ((DerivedCategory.singleFunctors (RModules X)).shiftIso (-a) a 0 (by omega)).inv.naturality φ
  simp only [Functor.comp_map] at h2
  simp only [derivedPushforwardMap, Functor.map_comp, Category.assoc]
  change _ ≫ (singleToDerivedPushforward G a).app M' ≫ _ =
    _ ≫ _ ≫ (shiftFunctor (DerivedCategory (RModules X)) (-a)).map
      ((singleToDerivedPushforward G 0).app M')
  have h1' : (singleToDerivedPushforward G a).app M' =
      ((DerivedCategory.singleFunctors (RModules X)).shiftIso (-a) a 0 (by omega)).inv.app
          ((modulePushforward G).obj M') ≫
        (shiftFunctor (DerivedCategory (RModules X)) (-a)).map
          ((singleToDerivedPushforward G 0).app M') ≫
        ((derivedPushforward G).commShiftIso (-a)).inv.app
          ((DerivedCategory.singleFunctor (RModules X') 0).obj M') ≫
        (derivedPushforward G).map
          (((DerivedCategory.singleFunctors (RModules X')).shiftIso (-a) a 0 (by omega)).hom.app
            M') := by
    rw [← h1, Iso.inv_hom_id_app_assoc]
  rw [h1']
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  rw [reassoc_of% h2]
  congr 2
  exact iso_cancel_helper _ (((derivedPushforward G).commShiftIso (-a)).app _) _
    (CategoryTheory.Functor.map_id _ _)

/-- The map of derived global sections behind `pullbackHgroup`. -/
abbrev pullbackDerivedSections (a : ℤ) {M : RModules X} {M' : RModules X'}
    (φ : M ⟶ (modulePushforward G).obj M') :
    (derivedGlobalSections X).obj ((DerivedCategory.singleFunctor (RModules X) a).obj M) ⟶
      (derivedGlobalSections X').obj ((DerivedCategory.singleFunctor (RModules X') a).obj M') :=
  (derivedGlobalSections X).map
      (derivedPushforwardMap (CohomologyPullbackComparison.canonical G) a φ) ≫
    (CohomologyPullbackComparison.canonical G).leray.hom.app
      ((DerivedCategory.singleFunctor (RModules X') a).obj M')

/-- **The map of derived global sections behind the pullback map is compatible with the shift.** -/
theorem pullbackDerivedSections_shift (a : ℤ) {M : RModules X} {M' : RModules X'}
    (φ : M ⟶ (modulePushforward G).obj M') :
    (derivedGlobalSections X).map
        (((DerivedCategory.singleFunctors (RModules X)).shiftIso (-a) a 0 (by omega)).inv.app M) ≫
      ((derivedGlobalSections X).commShiftIso (-a)).hom.app
        ((DerivedCategory.singleFunctor (RModules X) 0).obj M) ≫
      (shiftFunctor (DerivedCategory AddCommGrpCat) (-a)).map (pullbackDerivedSections G 0 φ) =
    pullbackDerivedSections G a φ ≫
      (derivedGlobalSections X').map
        (((DerivedCategory.singleFunctors (RModules X')).shiftIso (-a) a 0 (by omega)).inv.app M') ≫
      ((derivedGlobalSections X').commShiftIso (-a)).hom.app
        ((DerivedCategory.singleFunctor (RModules X') 0).obj M') := by
  have := isIso_lerayComparisonAb G
  have : NatTrans.CommShift (asIso (lerayComparisonAb G)).hom ℤ :=
    (inferInstance : NatTrans.CommShift (lerayComparisonAb G) ℤ)
  have : NatTrans.CommShift (CohomologyPullbackComparison.canonical G).leray.hom ℤ :=
    (inferInstance : NatTrans.CommShift (asIso (lerayComparisonAb G)).inv ℤ)
  have hL := NatTrans.shift_app_comm (CohomologyPullbackComparison.canonical G).leray.hom (-a)
    ((DerivedCategory.singleFunctor (RModules X') 0).obj M')
  have hLn := (CohomologyPullbackComparison.canonical G).leray.hom.naturality
    (((DerivedCategory.singleFunctors (RModules X')).shiftIso (-a) a 0 (by omega)).inv.app M')
  have hD := derivedPushforwardMap_canonical_shift G a φ
  have hN := (derivedGlobalSections X).commShiftIso_hom_naturality
    (derivedPushforwardMap (CohomologyPullbackComparison.canonical G) 0 φ) (-a)
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_map] at hL hLn
  simp only [pullbackDerivedSections, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hLn, ← hL]
  simp only [← Functor.map_comp_assoc, Category.assoc]
  rw [hD, Functor.map_comp, Category.assoc, reassoc_of% hN]

/-- **The pullback map on cohomology does not depend on the degree the module is placed in.**
`pullbackHgroup` computes `H^n(X, ℳ) ⟶ H^n(X', ℳ')` by placing both modules in an arbitrary
degree `a`; for the canonical comparisons of [Stacks, Tag 01F8] and [Stacks, Tag 01EZ] the result
is the same map for every `a`. -/
theorem pullbackHgroup_canonical_eq (a m : ℤ) (n : ℕ) (hn : m - a = n) {M : RModules X}
    {M' : RModules X'} (φ : M ⟶ (modulePushforward G).obj M') :
    pullbackHgroup (CohomologyPullbackComparison.canonical G) a m n hn φ =
      pullbackHgroup (CohomologyPullbackComparison.canonical G) 0 n n (by omega) φ := by
  have key := fun (a m : ℤ) (hn : m - a = n) => homologyTotalRightDerivedSingleShiftIso_comp_eq
    (secF (structureSheafRing X) ⊤) (derivedGlobalSections X) (derivedGlobalSectionsUnit X)
    (Stacks.Cohomology.SupportedComplexes.exists_isKInjective_quasiIso_moduleSheaves X)
    (secF (structureSheafRing X') ⊤) (derivedGlobalSections X') (derivedGlobalSectionsUnit X')
    (Stacks.Cohomology.SupportedComplexes.exists_isKInjective_quasiIso_moduleSheaves X') M M' a m n
    hn (pullbackDerivedSections G a φ) (pullbackDerivedSections G 0 φ)
    (pullbackDerivedSections_shift G a φ)
  exact (key a m hn).trans (key 0 n (by omega)).symm

end Stacks.DeRham.GysinCohomologyBaseChange

end

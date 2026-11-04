module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.HodgeCohomologyModuleBridge
public import StacksFrontier.CategoryTheory.Functor.Derived.RightDerivedDescCommShift
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.HomologySingleShiftGeneric
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.HodgeCupProduct

/-!
# The comparison of derived global sections in abelian groups and in modules commutes with shifts

`Stacks.DeRham.GysinCupHodge.derivedGlobalSectionsForget` compares derived global sections in
abelian groups with derived global sections over the base ring followed by the forgetful functor.
Both functors commute with the shift; the comparison is compatible with that commutation, being
the morphism out of a right derived functor induced by a shift-compatible unit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.DeRham.CohomologicalGysin
open Stacks.Cohomology.GlobalKunneth (baseSections baseRing)
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule)
open AlgebraicGeometry.SheafOfModules (moduleDerived baseRingedSpace)
open Stacks.Cohomology.RealizationShift (shiftHomologyIsoU)

universe u

namespace Stacks.DeRham.GysinCupHodge

/-- The algebra of `homologyForgetIso_single_shift`, at variables. -/
private lemma forget_shift_chase {V : Type*} [Category* V] {P Q R S T Q' Q'' P' : V}
    (a : P ⟶ Q) (b : Q ⟶ R) (c : R ⟶ S) (d : S ⟶ T) (x : Q ⟶ Q') (y : Q' ⟶ S) (z : Q' ⟶ Q'')
    (w : Q'' ⟶ T) (r : P ⟶ P') (v : P' ⟶ Q'') (cd : R ⟶ T) (hcd : cd = c ≫ d)
    (hnat : x ≫ y = b ≫ c) (hG₂ : z ≫ w = y ≫ d) (hG₁ : a ≫ x ≫ z = r ≫ v) :
    (a ≫ b) ≫ cd = r ≫ (v ≫ w) := by
  rw [hcd, ← reassoc_of% hG₁, hG₂, reassoc_of% hnat]
  simp only [Category.assoc]

/-- The algebra of `Q_map_singleNatShiftIso`, at variables. -/
private lemma der_chase {V : Type*} [Category* V] {P Q₁ Q₂ Q₃ Q₄ R R₂ R₃ : V} (x₁ : P ⟶ Q₁)
    (x₂ : Q₁ ⟶ Q₂) (a : P ⟶ R) (b : R ⟶ Q₂) (x₃ : Q₂ ⟶ Q₃) (s₀ : R ⟶ R₂) (b' : R₂ ⟶ Q₃)
    (x₄ : Q₃ ⟶ Q₄) (c₀ : R₂ ⟶ R₃) (b'' : R₃ ⟶ Q₄) (e : P ⟶ R₃) (h₁ : x₁ ≫ x₂ = a ≫ b)
    (h₂ : b ≫ x₃ = s₀ ≫ b') (h₃ : b' ≫ x₄ = c₀ ≫ b'') (h₄ : a ≫ s₀ ≫ c₀ = e) :
    x₁ ≫ x₂ ≫ x₃ ≫ x₄ = e ≫ b'' := by
  rw [← Category.assoc x₁, h₁, Category.assoc, reassoc_of% h₂, h₃, ← h₄]
  simp only [Category.assoc]

/-- The algebra of `singleNatShiftIso_cohomology`, at variables. -/
private lemma mod_chase {V : Type*} [Category* V] {P Q₁ Q₂ Q₃ Q₄ T R₃ T₀ : V}
    (x₁ : P ⟶ Q₁) (x₂ : Q₁ ⟶ Q₂) (x₃ : Q₂ ⟶ Q₃) (x₄ : Q₃ ⟶ Q₄) (S₁ : Q₄ ⟶ T) (sCI : Q₃ ⟶ T)
    (y : P ⟶ R₃) (w : R₃ ⟶ Q₄) (S₀ : R₃ ⟶ T₀) (z : T₀ ⟶ T) (hsCI : sCI = x₄ ≫ S₁)
    (hD : x₁ ≫ x₂ ≫ x₃ ≫ x₄ = y ≫ w) (hN : w ≫ S₁ = S₀ ≫ z) :
    x₁ ≫ x₂ ≫ (x₃ ≫ sCI) = (y ≫ S₀) ≫ z := by
  subst hsCI
  simp only [Category.assoc]
  rw [← hN, ← reassoc_of% hD]

/-- The algebra of `hgroupModuleShiftIso_shift_hom`, at variables. -/
private lemma bridge_shift_chase {V : Type*} [Category* V] {A B H FA FB FA' Z : V} (dc : A ≅ H)
    (d0 : B ≅ H) (Tc : A ⟶ B) (hc : dc.hom = Tc ≫ d0.hom) (fm : A ⟶ FA) (fq : B ⟶ FB)
    (t' : FA ⟶ FB) (g₁ : FA ⟶ FA') (g₂ : FA' ⟶ Z) (g₀ : FB ⟶ Z)
    (h3 : fm ≫ t' = Tc ≫ fq) (h4 : g₁ ≫ g₂ = t' ≫ g₀) :
    (dc.inv ≫ fm ≫ g₁) ≫ g₂ = d0.inv ≫ fq ≫ g₀ := by
  have hi : dc.inv ≫ Tc = d0.inv := by
    calc dc.inv ≫ Tc = dc.inv ≫ (Tc ≫ d0.hom) ≫ d0.inv := by simp
      _ = d0.inv := by rw [← hc, Iso.inv_hom_id_assoc]
  rw [Category.assoc, Category.assoc, h4, reassoc_of% h3, ← Category.assoc, hi]

section StandardModel

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat
attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules
  AlgebraicGeometry.SheafOfModules.hasSheafifyOpens
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijectiveOpens
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose structureSheafRing
  AlgebraicGeometry.SheafedSpace.sheaf AlgebraicGeometry.SheafOfModules.baseRingedSpace
  Stacks.SheafOfModules.Tensor.ringSheaf

/-- The unit of derived global sections over the base ring, read in abelian groups, commutes
with the shift. -/
instance forgetUnit_commShift (X : RingedSpace.{u, u}) : NatTrans.CommShift (forgetUnit X) ℤ := by
  unfold forgetUnit
  infer_instance

/-- **The comparison of the two derived global sections commutes with the shift.** -/
theorem derivedGlobalSectionsForget_commShift (X : RingedSpace.{u, u}) :
    letI := Functor.IsRightDerivedFunctor.commShift
      (Stacks.DeRham.CohomologicalGysin.derivedGlobalSections X)
      (Stacks.DeRham.CohomologicalGysin.derivedGlobalSectionsUnit X)
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) ℤ
    NatTrans.CommShift (derivedGlobalSectionsForget X) ℤ :=
  Functor.IsRightDerivedFunctor.rightDerivedDesc_commShift _ _ _ ℤ _ _

variable {X : RingedSpace.{u, u}} in
/-- **A sheaf placed in degree `c`, extended by zero, is the sheaf placed in degree `0`, extended
by zero, shifted by `-c`.** -/
def singleNatShiftIso
    (N : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf))
    (c : ℕ) :
    (singleNat N c).extend ComplexShape.embeddingUpNat ≅
      ((singleNat N 0).extend ComplexShape.embeddingUpNat)⟦-(c : ℤ)⟧ :=
  HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat N c (c : ℤ) rfl ≪≫
    ((CochainComplex.singleFunctors _).shiftIso (-(c : ℤ)) (c : ℤ) 0 (by omega)).symm.app N ≪≫
    (CategoryTheory.shiftFunctor _ (-(c : ℤ))).mapIso
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat N 0 0 rfl).symm

/-- **`cohomologyDerivedSingleIso` read through the shift**: the degree-`m` cohomology of derived
global sections of `M[-a]` is moved to degree `n` of `M[0]` by the single functors and the
shift, and then compared with `Hⁿ(X, M)` in degree zero. -/
theorem cohomologyDerivedSingleIso_hom_eq (X : RingedSpace.{u, u})
    (M : _root_.SheafOfModules.{u} (structureSheafRing X)) (a m : ℤ) (n : ℕ) (hn : m - a = n) :
    letI := Functor.IsRightDerivedFunctor.commShift (derivedGlobalSections X)
      (derivedGlobalSectionsUnit X) (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) ℤ
    (cohomologyDerivedSingleIso X M a m n hn).hom =
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).map ((derivedGlobalSections X).map
          (((DerivedCategory.singleFunctors _).shiftIso (-a) a 0 (by omega)).inv.app M)) ≫
        (shiftHomologyIsoU (derivedGlobalSections X)
          ((DerivedCategory.singleFunctor _ 0).obj M) (-a) m n (by omega)).hom) ≫
        (Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso _ (derivedGlobalSections X)
          (derivedGlobalSectionsUnit X)
          (Stacks.Cohomology.SupportedComplexes.exists_isKInjective_quasiIso_moduleSheaves X)
          M n).hom := by
  simp only [cohomologyDerivedSingleIso,
    Stacks.DerivedFunctor.homologyTotalRightDerivedSingleShiftIso,
    Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Functor.map_comp, Category.assoc,
    shiftHomologyIsoU]
  rfl

/-- **The comparison of the two derived global sections carries the shift of the single functors
in abelian groups to the one over the base ring.** -/
theorem homologyForgetIso_single_shift (X : RingedSpace.{u, u})
    (M : _root_.SheafOfModules.{u} (structureSheafRing X)) (a m n : ℤ) (ha : -a + a = 0)
    (h : -a + m = n) :
    letI := Functor.IsRightDerivedFunctor.commShift (derivedGlobalSections X)
      (derivedGlobalSectionsUnit X) (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) ℤ
    (homologyForgetIso X m ((DerivedCategory.singleFunctor _ a).obj M)).hom ≫
        (forget₂ (ModuleCat.{u} (baseRing X)) AddCommGrpCat.{u}).map
          ((DerivedCategory.homologyFunctor _ m).map ((baseSections X).map
              (((DerivedCategory.singleFunctors _).shiftIso (-a) a 0 ha).inv.app M)) ≫
            (shiftHomologyIsoU (baseSections X) ((DerivedCategory.singleFunctor _ 0).obj M)
              (-a) m n h).hom) =
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).map ((derivedGlobalSections X).map
          (((DerivedCategory.singleFunctors _).shiftIso (-a) a 0 ha).inv.app M)) ≫
        (shiftHomologyIsoU (derivedGlobalSections X)
          ((DerivedCategory.singleFunctor _ 0).obj M) (-a) m n h).hom) ≫
        (homologyForgetIso X n ((DerivedCategory.singleFunctor _ 0).obj M)).hom := by
  let _ := Functor.IsRightDerivedFunctor.commShift (derivedGlobalSections X)
    (derivedGlobalSectionsUnit X) (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) ℤ
  have := derivedGlobalSectionsForget_commShift X
  let Φ := forget₂ (ModuleCat.{u} (baseRing X)) AddCommGrpCat.{u}
  let e :=
    ((DerivedCategory.singleFunctors (_root_.SheafOfModules.{u} (structureSheafRing X))).shiftIso
      (-a) a 0 ha).inv.app M
  have hG₁ := homology_single_shift_naturality (derivedGlobalSectionsForget X) M a m n ha h
  have hG₂ := shiftHomologyIsoU_mapDerivedCategory (baseSections X) Φ
    ((DerivedCategory.singleFunctor _ 0).obj M) (-a) m n h
  have hnat := (Φ.mapDerivedCategoryHomologyIso m).hom.naturality ((baseSections X).map e)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnat
  exact forget_shift_chase _ _ _ _ _ _ _ _ _ _ _ (Φ.map_comp _ _) hnat hG₂ hG₁

open Stacks.Cohomology.DerivedGlobalCupProduct (shiftBridge shiftCohomologyIsoR) in
/-- **The extension of `M[-c]` and the shift of the extension of `M[0]`, after localization**:
`singleNatShiftIso`, read in the derived category through the two extensions, the bridge
between the two spellings of the shift and the commutation of the localization with the shift,
is the comparison of the single functors of the derived category with the shift. -/
theorem Q_map_singleNatShiftIso (X : RingedSpace.{u, u})
    (M : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf))
    (c : ℕ) :
    DerivedCategory.Q.map (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat M c
        (c : ℤ) rfl).inv ≫
      DerivedCategory.Q.map (singleNatShiftIso M c).hom ≫
      DerivedCategory.Q.map (shiftBridge (S := X)
        ((singleNat M 0).extend ComplexShape.embeddingUpNat) (-(c : ℤ))).hom ≫
      (DerivedCategory.Q.commShiftIso (-(c : ℤ))).hom.app
        ((singleNat M 0).extend ComplexShape.embeddingUpNat) =
    ((DerivedCategory.singleFunctors (_root_.SheafOfModules.{u} (structureSheafRing X))).shiftIso
        (-(c : ℤ)) (c : ℤ) 0 (by omega)).inv.app M ≫
      (DerivedCategory.Q.map (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat M 0
        0 rfl).inv)⟦-(c : ℤ)⟧' := by
  let eR := HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat M c (c : ℤ) rfl
  let e₀ := HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat M 0 0 rfl
  let A := ((CochainComplex.singleFunctors
    (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf))).shiftIso
      (-(c : ℤ)) (c : ℤ) 0 (by omega)).inv.app M
  have h₁ : DerivedCategory.Q.map eR.inv ≫ DerivedCategory.Q.map (singleNatShiftIso M c).hom =
      DerivedCategory.Q.map A ≫ DerivedCategory.Q.map ((CategoryTheory.shiftFunctor
        (CochainComplex (_root_.SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)) ℤ)
        (-(c : ℤ))).map e₀.inv) := by
    rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
    exact congrArg DerivedCategory.Q.map (Iso.inv_hom_id_assoc eR _)
  have h₂ := Stacks.Cohomology.DerivedGlobalCupProduct.Q_map_shiftBridge_naturality (S := X)
    e₀.inv (-(c : ℤ))
  have h₃ := DerivedCategory.Q.commShiftIso_hom_naturality e₀.inv (-(c : ℤ))
  have h₄ : DerivedCategory.Q.map A ≫ DerivedCategory.Q.map (shiftBridge (S := X)
        ((CochainComplex.singleFunctor _ 0).obj M) (-(c : ℤ))).hom ≫
      (DerivedCategory.Q.commShiftIso (-(c : ℤ))).hom.app
        ((CochainComplex.singleFunctor _ 0).obj M) =
      ((DerivedCategory.singleFunctors (_root_.SheafOfModules.{u} (structureSheafRing X))).shiftIso
        (-(c : ℤ)) (c : ℤ) 0 (by omega)).inv.app M := by
    have hA : A ≫ (shiftBridge (S := X) ((CochainComplex.singleFunctor _ 0).obj M) (-(c : ℤ))).hom =
        ((CochainComplex.singleFunctors
          (_root_.SheafOfModules.{u} (structureSheafRing X))).shiftIso
            (-(c : ℤ)) (c : ℤ) 0 (by omega)).inv.app M := by
      refine HomologicalComplex.Hom.ext (funext fun k => ?_)
      exact (HomologicalComplex.comp_f _ _ k).trans (Category.comp_id _)
    rw [← Category.assoc, ← DerivedCategory.Q.map_comp, hA]
    simp only [DerivedCategory.singleFunctors, SingleFunctors.postcomp, Iso.trans_inv,
      NatTrans.comp_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
      Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Iso.symm_inv,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id]
    rfl
  exact der_chase _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄

open Stacks.Cohomology.DerivedGlobalCupProduct (shiftBridge shiftCohomologyIsoR shiftCohomologyIso) in
/-- **`singleNatShiftIso` on cohomology over the base ring**: through the extensions of the
single complexes, `singleNatShiftIso` followed by the shift identification `shiftCohomologyIsoR`
is the shift of the single functors followed by the identification of
`shiftHomologyIsoU`. -/
theorem singleNatShiftIso_cohomology (X : RingedSpace.{u, u})
    (M : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf))
    (c : ℕ) (m q : ℤ) (h : -(c : ℤ) + m = q) :
    (DerivedCategory.homologyFunctor _ m).map ((baseSections X).map (DerivedCategory.Q.map
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat M c (c : ℤ) rfl).inv)) ≫
      (DerivedCategory.homologyFunctor _ m).map ((baseSections X).map (DerivedCategory.Q.map
        (singleNatShiftIso M c).hom)) ≫
      (shiftCohomologyIsoR (S := X) ((singleNat M 0).extend ComplexShape.embeddingUpNat)
        (-(c : ℤ)) m q h).hom =
    ((DerivedCategory.homologyFunctor _ m).map ((baseSections X).map
        (((DerivedCategory.singleFunctors
          (_root_.SheafOfModules.{u} (structureSheafRing X))).shiftIso
          (-(c : ℤ)) (c : ℤ) 0 (by omega)).inv.app M)) ≫
      (shiftHomologyIsoU (baseSections X)
        ((DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) 0).obj M)
        (-(c : ℤ)) m q h).hom) ≫
      (DerivedCategory.homologyFunctor _ q).map ((baseSections X).map (DerivedCategory.Q.map
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat M 0 0 rfl).inv)) := by
  let Hb := baseSections X ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) m
  have hD := (Hb.map_comp _ _).symm.trans ((congrArg Hb.map (Q_map_singleNatShiftIso X M c)).trans
    (Hb.map_comp _ _))
  simp only [Functor.map_comp] at hD
  have hsCI := (AlgebraicGeometry.SheafOfModules.shiftCohomologyIso_eq_shiftHomologyIsoU (S := X)
    ((singleNat M 0).extend ComplexShape.embeddingUpNat) (-(c : ℤ)) m q h).trans
    (Stacks.Cohomology.RealizationShift.shiftHomologyIsoU_comp_hom DerivedCategory.Q
      (baseSections X)
      ((singleNat M 0).extend ComplexShape.embeddingUpNat) (-(c : ℤ)) m q h)
  have hN := shiftHomologyIsoU_naturality (baseSections X) (DerivedCategory.Q.map
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat M 0 0 rfl).inv) (-(c : ℤ)) m q h
  exact mod_chase _ _ _ _ _ _ _ _ _ _ hsCI hD hN

variable {X : RingedSpace.{u, u}} in
open Stacks.Cohomology.DerivedGlobalCupProduct (shiftBridge shiftCohomologyIsoR) in
/-- **The bridge and the shift (N-B)**: the bridge `Hᵠ(X, M) ≅ Hᵠ⁺ᶜ(RΓ(M[-c]))`, followed by
`singleNatShiftIso` and the shift identification `Hᵠ⁺ᶜ(RΓ(M[0][-c])) ≅ Hᵠ(RΓ(M[0]))`, is the
bridge in degree `0`. -/
theorem hgroupModuleShiftIso_shift_hom
    (M : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf))
    (c q : ℕ) (m : ℤ) (h : (q : ℤ) + (c : ℤ) = m) (h' : -(c : ℤ) + m = q) :
    (hgroupModuleShiftIso M c q m h).hom ≫
        (forget₂ (ModuleCat.{u} (baseRing X)) AddCommGrpCat.{u}).map
          ((DerivedCategory.homologyFunctor _ m).map ((baseSections X).map (DerivedCategory.Q.map
              (singleNatShiftIso M c).hom)) ≫
            (shiftCohomologyIsoR (S := X) ((singleNat M 0).extend ComplexShape.embeddingUpNat)
              (-(c : ℤ)) m q h').hom) =
      (hgroupModuleShiftIso M 0 q q (by simp)).hom := by
  let _ := Functor.IsRightDerivedFunctor.commShift (derivedGlobalSections X)
    (derivedGlobalSectionsUnit X) (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) ℤ
  let Φ := forget₂ (ModuleCat.{u} (baseRing X)) AddCommGrpCat.{u}
  have h₁ := cohomologyDerivedSingleIso_hom_eq X M (c : ℤ) m q (by omega)
  have h₀ := cohomologyDerivedSingleIso_hom_eq X M ((0 : ℕ) : ℤ) (q : ℤ) q (by omega)
  have hz := homology_single_shift_zero (derivedGlobalSections X) M (-((0 : ℕ) : ℤ)) (q : ℤ)
    (by simp) (by simp) (by simp)
  have h₀' := h₀.trans ((congrArg (· ≫ _) hz).trans (Category.id_comp _))
  have h3 := homologyForgetIso_single_shift X M (c : ℤ) m q (by omega) h'
  have h4 := (Φ.map_comp _ _).symm.trans ((congrArg Φ.map
    (singleNatShiftIso_cohomology X M c m q h')).trans (Φ.map_comp _ _))
  have hc := h₁.trans (congrArg (_ ≫ ·) h₀'.symm)
  exact bridge_shift_chase _ _ _ hc _ _ _ _ _ _ h3 ((Φ.map_comp _ _).symm.trans
    ((congrArg Φ.map (Category.assoc _ _ _).symm).trans ((Φ.map_comp _ _).trans h4)))

end StandardModel

end Stacks.DeRham.GysinCupHodge

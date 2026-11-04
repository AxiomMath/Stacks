module

public import StacksFrontier.Homology.DerivedComplete.DerivedHomCompletionVanishing.DerivedLimitModel
import all StacksFrontier.Homology.DerivedComplete.DerivedHomCompletionVanishing.DerivedLimitModel

/-!
# Vanishing criteria for `RHom_A(A_f, K)`

This part relates orthogonality to `D(A_f)`, invertibility of product difference maps, vanishing
of the derived limits `T(H^p(K), f)` and the degree-zero and degree-one cohomology conditions,
and proves the seven equivalent vanishing criteria `DerivedHomAway.tfae_ext_localization_vanishing`.
-/

@[expose] public noncomputable section


open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CochainComplex CochainComplex.HomComplex
open scoped ZeroObject

attribute [local instance] HasDerivedCategory.standard

universe u w

namespace DerivedHomAway

attribute [local instance] instHasExactLimitsOfShapeDiscreteNatModuleCat_stacksFrontier
attribute [local instance] instHasProductsOfShapeNatDerivedCategoryModuleCat_stacksFrontier

private noncomputable def restricted_away_module_iso
    (A : Type u) [CommRing A] (f : A) :
    (ModuleCat.restrictScalars.{u} (algebraMap A (Localization.Away f))).obj
      (ModuleCat.of (Localization.Away f) (Localization.Away f)) ≅
      ModuleCat.of A (Localization.Away f) := by
  let F := ModuleCat.restrictScalars.{u} (algebraMap A (Localization.Away f))
  let moduleEquiv : F.obj (ModuleCat.of (Localization.Away f) (Localization.Away f))
      ≃ₗ[A] ModuleCat.of A (Localization.Away f) :=
    { toFun := fun value => value
      invFun := fun value => value
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := by intros; rfl
      map_smul' := by
        intro scalar value
        let element : Localization.Away f := value
        change (algebraMap A (Localization.Away f) scalar) * element =
          scalar • element
        exact (Algebra.smul_def scalar element).symm }
  exact moduleEquiv.toModuleIso

private noncomputable def restricted_away_single_iso
    (A : Type u) [CommRing A] (f : A) :
    (ModuleCat.restrictScalars.{u} (algebraMap A (Localization.Away f))).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.Away f)) 0).obj
        (ModuleCat.of (Localization.Away f) (Localization.Away f))) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (Localization.Away f)) := by
  let F := ModuleCat.restrictScalars.{u} (algebraMap A (Localization.Away f))
  exact (F.mapDerivedCategorySingleFunctor 0).app
      (ModuleCat.of (Localization.Away f) (Localization.Away f)) ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso
      (restricted_away_module_iso A f)

private noncomputable def restricted_away_shifted_iso
    (A : Type u) [CommRing A] (f : A) (n : ℤ) :
    (ModuleCat.restrictScalars.{u} (algebraMap A (Localization.Away f))).mapDerivedCategory.obj
      (((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.Away f)) 0).obj
        (ModuleCat.of (Localization.Away f) (Localization.Away f)))⟦-n⟧) ≅
      (((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (Localization.Away f)))⟦-n⟧) := by
  let F := ModuleCat.restrictScalars.{u} (algebraMap A (Localization.Away f))
  exact (F.mapDerivedCategory.commShiftIso (-n)).app _ ≪≫
    (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (-n)).mapIso
      (restricted_away_single_iso A f)

private theorem orthogonality_implies_ext_vanishing
    (A : Type u) [CommRing A] (f : A)
    (K : DerivedCategory (ModuleCat.{u} A))
    (hOrth : ∀ E : DerivedCategory (ModuleCat.{u} (Localization.Away f)),
      Subsingleton
        ((ModuleCat.restrictScalars.{u} (algebraMap A (Localization.Away f))).mapDerivedCategory.obj
          E ⟶ K)) :
    ∀ n : ℤ, Subsingleton
      (DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (Localization.Away f))) K n) := by
  intro n
  let D := DerivedCategory (ModuleCat.{u} A)
  let Ezero := (DerivedCategory.singleFunctor
    (ModuleCat.{u} (Localization.Away f)) 0).obj
      (ModuleCat.of (Localization.Away f) (Localization.Away f))
  let E := Ezero⟦-n⟧
  let sAf := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
    (ModuleCat.of A (Localization.Away f))
  let sourceIso := restricted_away_shifted_iso A f n
  let shiftedHomEquiv :=
    (shiftEquiv' D (-n) n (neg_add_cancel n)).toAdjunction.homEquiv sAf K
  let orthEquiv : (sAf ⟶ K⟦n⟧) ≃
      ((ModuleCat.restrictScalars.{u} (algebraMap A (Localization.Away f))).mapDerivedCategory.obj E
        ⟶ K) :=
    shiftedHomEquiv.symm.trans (sourceIso.symm.homCongr (Iso.refl K))
  let := hOrth E
  constructor
  intro first second
  exact orthEquiv.injective (Subsingleton.elim (orthEquiv first) (orthEquiv second))

local instance homologyFunctorLinear
    (A : Type u) [CommRing A] (p : ℤ) :
    Functor.Linear A
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ) p) where
  map_smul f r := by
    change ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ) p).map
        (r • f)) = _
    rw [show (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} A)
      (ComplexShape.up ℤ) p).map (r • f) = r •
        (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} A)
          (ComplexShape.up ℤ) p).map f by rfl]
    apply ShortComplex.homologyMap_smul

local instance derivedHomologyFunctorLinear
    (A : Type u) [CommRing A] (p : ℤ) :
    Functor.Linear A (DerivedCategory.homologyFunctor (ModuleCat.{u} A) p) :=
  let : Localization.Lifting
      (DerivedCategory.Q (C := ModuleCat.{u} A))
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ) p)
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) p) :=
    ⟨DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) p⟩
  (Localization.functor_linear_iff
    (DerivedCategory.Q (C := ModuleCat.{u} A))
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) A
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ) p)
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) p)).mp inferInstance

/-- A linear functor with invertible product comparison preserves invertibility of the product
difference map `(x_n) ↦ (x_n - f x_{n+1})` in both directions. -/
private theorem isIso_map_productDifference_iff
    {A : Type u} [CommRing A] (f : A) {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] [Linear A C] [Linear A D]
    [HasProductsOfShape ℕ C] [HasProductsOfShape ℕ D] (F : C ⥤ D) [F.Additive] [F.Linear A]
    (K : C) [IsIso (piComparison F (fun _ : ℕ => K))] :
    IsIso (F.map (Pi.lift fun n : ℕ =>
      Pi.π (fun _ : ℕ => K) n - f • Pi.π (fun _ : ℕ => K) (n + 1))) ↔
    IsIso (Pi.lift fun n : ℕ =>
      Pi.π (fun _ : ℕ => F.obj K) n - f • Pi.π (fun _ : ℕ => F.obj K) (n + 1)) := by
  have hcomp : F.map (Pi.lift fun n : ℕ =>
        Pi.π (fun _ : ℕ => K) n - f • Pi.π (fun _ : ℕ => K) (n + 1)) ≫
      piComparison F (fun _ : ℕ => K) =
      piComparison F (fun _ : ℕ => K) ≫ Pi.lift fun n : ℕ =>
        Pi.π (fun _ : ℕ => F.obj K) n - f • Pi.π (fun _ : ℕ => F.obj K) (n + 1) := by
    refine Pi.hom_ext _ _ fun n => ?_
    simp only [Category.assoc, piComparison_comp_π, Pi.lift_π,
      Preadditive.comp_sub, Linear.comp_smul]
    rw [← F.map_comp, Pi.lift_π, F.map_sub, F.map_smul]
  rw [← isIso_comp_right_iff _ (piComparison F (fun _ : ℕ => K)), hcomp,
    isIso_comp_left_iff]

private theorem productDifference_isIso_iff_homology
    (A : Type u) [CommRing A] (f : A)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    IsIso (Pi.lift fun n : ℕ =>
      Pi.π (fun _ : ℕ => K) n - f • Pi.π (fun _ : ℕ => K) (n + 1)) ↔
    ∀ p : ℤ,
      IsIso (Pi.lift (fun n : ℕ =>
        Pi.π (fun _ : ℕ => (DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj K) n -
          f • Pi.π (fun _ : ℕ =>
            (DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj K) (n + 1))) := by
  rw [DerivedCategory.isIso_iff]
  refine forall_congr' fun p => ?_
  have : IsIso (piComparison (DerivedCategory.homologyFunctor (ModuleCat.{u} A) p)
      (fun _ : ℕ => K)) :=
    Stacks.DerivedProducts.isIso_piComparison_homologyFunctor _ p
  exact isIso_map_productDifference_iff f _ K

private theorem preservesProducts_singleFunctor
    (A : Type u) [CommRing A] :
    PreservesLimitsOfShape (Discrete ℕ)
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0) := by
  classical
  let : PreservesLimitsOfShape (Discrete ℕ)
      (DerivedCategory.Q (C := ModuleCat.{u} A)) := by
    exact Stacks.DerivedProducts.preservesLimitsOfShape_Q
  let : PreservesLimitsOfShape (Discrete ℕ)
      (CochainComplex.singleFunctor (ModuleCat.{u} A) 0) := by
    show PreservesLimitsOfShape (Discrete ℕ)
      (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0)
    infer_instance
  show PreservesLimitsOfShape (Discrete ℕ)
    (CochainComplex.singleFunctor (ModuleCat.{u} A) 0 ⋙ DerivedCategory.Q)
  infer_instance

private theorem module_productDifference_isIso_iff_derivedSingle
    (A : Type u) [CommRing A] (f : A) (M : ModuleCat.{u} A) :
    IsIso (Pi.lift fun n : ℕ =>
      Pi.π (fun _ : ℕ => M) n - f • Pi.π (fun _ : ℕ => M) (n + 1)) ↔
    IsIso (Pi.lift fun n : ℕ =>
      Pi.π (fun _ : ℕ =>
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) n -
        f • Pi.π (fun _ : ℕ =>
          (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) (n + 1)) := by
  let F := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0
  let : PreservesLimitsOfShape (Discrete ℕ) F := preservesProducts_singleFunctor A
  have : IsIso (piComparison F (fun _ : ℕ => M)) := inferInstance
  exact (isIso_iff_of_reflects_iso _ F).symm.trans (isIso_map_productDifference_iff f F M)

private theorem derivedLimitZero_iff_forall_homologyLimitZero
    (A : Type u) [CommRing A] (f : A)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (∃ L : DerivedCategory (ModuleCat.{u} A),
      IsDerivedLimit
        (Functor.ofOpSequence (X := fun _ : ℕ => K) (fun _ => f • 𝟙 K)) L ∧
      IsZero L) ↔
    (∀ p : ℤ,
      let Hp := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj K
      let sHp := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj Hp
      let towerHp := Functor.ofOpSequence (X := fun _ : ℕ => sHp) (fun _ => f • 𝟙 sHp)
      ∃ L : DerivedCategory (ModuleCat.{u} A), IsDerivedLimit towerHp L ∧ IsZero L) := by
  constructor
  · intro h p
    dsimp
    apply (derivedLimitZero_iff_constant_difference_iso A f _).mpr
    exact (module_productDifference_isIso_iff_derivedSingle A f _).mp
      ((productDifference_isIso_iff_homology A f K).mp
        ((derivedLimitZero_iff_constant_difference_iso A f K).mp h) p)
  · intro h
    apply (derivedLimitZero_iff_constant_difference_iso A f K).mpr
    apply (productDifference_isIso_iff_homology A f K).mpr
    intro p
    exact (module_productDifference_isIso_iff_derivedSingle A f _).mpr
      ((derivedLimitZero_iff_constant_difference_iso A f _).mp (h p))

private theorem exists_smul_eq_id_of_iso {R : Type*} [CommRing R] {C : Type*} [Category C]
    [Preadditive C] [Linear R C] (f : R) {X Y : C} (i : X ≅ Y) (v : End Y)
    (hv : f • v = 𝟙 Y) : ∃ u : End X, f • u = 𝟙 X := by
  refine ⟨i.hom ≫ v ≫ i.inv, ?_⟩
  show f • (i.hom ≫ v ≫ i.inv) = 𝟙 X
  rw [← Linear.comp_smul, ← Linear.smul_comp, hv, Category.id_comp, Iso.hom_inv_id]

private theorem eq_zero_of_isIso_difference {R : Type*} [CommRing R] {C : Type*} [Category C]
    [Preadditive C] [Linear R C] (f : R) {E K : C} [HasProduct fun _ : ℕ => K]
    (u : End E) (hu : f • u = 𝟙 E) (φ : E ⟶ K)
    [IsIso (Pi.lift fun n : ℕ =>
      Pi.π (fun _ : ℕ => K) n - f • Pi.π (fun _ : ℕ => K) (n + 1))] :
    φ = 0 := by
  set d : (∏ᶜ fun _ : ℕ => K) ⟶ ∏ᶜ fun _ : ℕ => K := Pi.lift fun n : ℕ =>
    Pi.π (fun _ : ℕ => K) n - f • Pi.π (fun _ : ℕ => K) (n + 1) with hd
  have hψ : (Pi.lift fun n : ℕ => (u ^ n : End E) ≫ φ) ≫
      d = (0 : E ⟶ ∏ᶜ fun _ : ℕ => K) ≫ d := by
    rw [hd]
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, Pi.lift_π, Preadditive.comp_sub, Linear.comp_smul,
      zero_comp]
    rw [sub_eq_zero, ← Linear.smul_comp, pow_succ', End.mul_def]
    have hcomp : (f • ((u ^ n : End E) ≫ u)) = (u ^ n : End E) := by
      rw [← Linear.comp_smul, hu, Category.comp_id]
    rw [hcomp]
  have := (cancel_mono _).1 hψ
  simpa using congrArg (· ≫ Pi.π (fun _ : ℕ => K) 0) this

private theorem exists_smul_eq_id_restrictScalars_complex (A : Type u) [CommRing A] (f : A)
    (M : CochainComplex (ModuleCat.{u} (Localization.Away f)) ℤ) :
    ∃ w : End (((ModuleCat.restrictScalars.{u} (algebraMap A (Localization.Away f))
      ).mapHomologicalComplex (ComplexShape.up ℤ)).obj M), f • w = 𝟙 _ := by
  refine ⟨((ModuleCat.restrictScalars.{u} (algebraMap A (Localization.Away f))
      ).mapHomologicalComplex (ComplexShape.up ℤ)).map
    ((IsLocalization.Away.invSelf (S := Localization.Away f) f) • 𝟙 M), ?_⟩
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let : Module (Localization.Away f)
      (↑(((((ModuleCat.restrictScalars.{u} (algebraMap A (Localization.Away f))
        ).mapHomologicalComplex (ComplexShape.up ℤ)).obj M).X n))) := by
    show Module (Localization.Away f)
      ((ModuleCat.restrictScalars.{u} (algebraMap A (Localization.Away f))).obj (M.X n))
    infer_instance
  show (algebraMap A (Localization.Away f) f) •
    ((IsLocalization.Away.invSelf (S := Localization.Away f) f) • (x : M.X n)) = x
  rw [smul_smul, mul_comm, IsLocalization.Away.invSelf,
    IsLocalization.mk'_spec_mk]
  simp

private theorem exists_smul_eq_id_restrictScalars_derived (A : Type u) [CommRing A] (f : A)
    (E : DerivedCategory (ModuleCat.{u} (Localization.Away f))) :
    ∃ z : End ((ModuleCat.restrictScalars.{u} (algebraMap A (Localization.Away f))
      ).mapDerivedCategory.obj E), f • z = 𝟙 _ := by
  let F := ModuleCat.restrictScalars.{u} (algebraMap A (Localization.Away f))
  obtain ⟨w, hw⟩ := exists_smul_eq_id_restrictScalars_complex A f
    (DerivedCategory.Q.objPreimage E)
  refine exists_smul_eq_id_of_iso f
    (F.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso E).symm ≪≫
      F.mapDerivedCategoryFactors.app _) (DerivedCategory.Q.map w) ?_
  rw [← Functor.map_smul, hw]
  exact DerivedCategory.Q.map_id _

private theorem subsingleton_hom_restrictScalars_of_isIso_difference
    (A : Type u) [CommRing A] (f : A) (K : DerivedCategory (ModuleCat.{u} A))
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))]
    [IsIso (Pi.lift fun n : ℕ =>
      Pi.π (fun _ : ℕ => K) n - f • Pi.π (fun _ : ℕ => K) (n + 1))]
    (E : DerivedCategory (ModuleCat.{u} (Localization.Away f))) :
    Subsingleton (((ModuleCat.restrictScalars.{u} (algebraMap A (Localization.Away f))
      ).mapDerivedCategory.obj E) ⟶ K) := by
  obtain ⟨z, hz⟩ := exists_smul_eq_id_restrictScalars_derived A f E
  constructor
  intro φ ψ
  rw [eq_zero_of_isIso_difference f z hz φ,
    eq_zero_of_isIso_difference f z hz ψ]

private noncomputable def zExtZeroEquivHom
    (A : Type u) [CommRing A] (M N : ModuleCat.{u} A) :
    Abelian.zExt M N 0 ≃ (M ⟶ N) :=
  (Abelian.Ext.homEquiv (X := M) (Y := N) (n := 0)).symm.trans
    (Abelian.Ext.homEquiv₀ (X := M) (Y := N))

private theorem triangle_vanishes_iff_homology_zero_zero_one
    (A : Type u) [CommRing A]
    (L P : DerivedCategory (ModuleCat.{u} A))
    (ι : L ⟶ P) (d : P ⟶ P) (δ : P ⟶ L⟦1⟧)
    (hT : Triangle.mk ι d δ ∈ distTriang _)
    (hP : ∀ n : ℤ, n ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj P)) :
    IsZero L ↔
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj L) ∧
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1).obj L) := by
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  constructor
  · intro h
    exact ⟨h 0, h 1⟩
  · rintro ⟨h0, h1⟩ n
    by_cases hn0 : n = 0
    · simpa only [hn0] using h0
    by_cases hn1 : n = 1
    · simpa only [hn1] using h1
    have hprev : n - 1 ≠ 0 := by omega
    let T := Triangle.mk ι d δ
    have hexact := DerivedCategory.HomologySequence.exact₁ T hT (n - 1) n (by omega)
    apply hexact.isZero_X₂
    · exact (hP (n - 1) hprev).eq_of_src _ _
    · exact (hP n hn0).eq_of_tgt _ _

private theorem homology_single_isZero
    (A : Type u) [CommRing A] (M : ModuleCat.{u} A)
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)) := by
  let h := HomologicalComplex.isZero_single_obj_homology
    (ComplexShape.up ℤ) 0 M n hn
  exact h.of_iso ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) n).app
    ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M))

private theorem homology_product_single_isZero
    (A : Type u) [CommRing A] (M : ModuleCat.{u} A)
    (n : ℤ) (hn : n ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
      (∏ᶜ (fun _ : ℕ => (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M))) := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) n
  let sM := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M
  have hsingle : IsZero (H.obj sM) := homology_single_isZero A M n hn
  have hpi : IsZero (∏ᶜ (fun _ : ℕ => H.obj sM)) := by
    rw [IsZero.iff_id_eq_zero]
    apply Pi.hom_ext
    intro index
    exact hsingle.eq_of_tgt _ _
  have : IsIso (piComparison H (fun _ : ℕ => sM)) :=
    Stacks.DerivedProducts.isIso_piComparison_homologyFunctor _ n
  exact hpi.of_iso (asIso (piComparison H (fun _ : ℕ => sM)))

private theorem derivedLimit_single_isZero_iff_homology_zero_zero_one
    (A : Type u) [CommRing A] (f : A) (M : ModuleCat.{u} A)
    (L : DerivedCategory (ModuleCat.{u} A))
    (hL : IsDerivedLimit
      (Functor.ofOpSequence
        (X := fun _ : ℕ => (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)
        (fun _ => f • 𝟙 _)) L) :
    IsZero L ↔
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj L) ∧
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1).obj L) := by
  obtain ⟨projection, connecting, distinguished⟩ := hL
  exact triangle_vanishes_iff_homology_zero_zero_one A L
    (∏ᶜ (fun _ : ℕ => (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M))
    projection _ connecting distinguished
    (homology_product_single_isZero A M)

private theorem derivedLimit_single_isZero_iff_Hom_zExt_subsingleton
    (A : Type u) [CommRing A] (f : A) (M : ModuleCat.{u} A)
    (L : DerivedCategory (ModuleCat.{u} A))
    (hL : IsDerivedLimit
      (Functor.ofOpSequence
        (X := fun _ : ℕ => (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)
        (fun _ => f • 𝟙 _)) L)
    (e0 : ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj L : Type u) ≃+
      DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (Localization.Away f)))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) 0)
    (e1 : ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1).obj L : Type u) ≃+
      DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (Localization.Away f)))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) 1) :
    IsZero L ↔
      Subsingleton ((ModuleCat.of A (Localization.Away f)) ⟶ M) ∧
      Subsingleton (Abelian.zExt (ModuleCat.of A (Localization.Away f)) M 1) := by
  rw [derivedLimit_single_isZero_iff_homology_zero_zero_one A f M L hL]
  let AfA := ModuleCat.of A (Localization.Away f)
  have first :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj L) ↔
        Subsingleton (AfA ⟶ M) := by
    exact (ModuleCat.isZero_iff_subsingleton).trans
      ((Equiv.subsingleton_congr e0.toEquiv).trans
        (Equiv.subsingleton_congr (zExtZeroEquivHom A AfA M)))
  have second :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1).obj L) ↔
        Subsingleton (Abelian.zExt AfA M 1) := by
    exact (ModuleCat.isZero_iff_subsingleton).trans
      (Equiv.subsingleton_congr e1.toEquiv)
  exact and_congr first second

private theorem derivedLimits_vanish_together
    (A : Type u) [CommRing A]
    (F : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A))
    [HasProduct fun n : ℕ => F.obj ⟨n⟩]
    (L M : DerivedCategory (ModuleCat.{u} A))
    (hL : IsDerivedLimit F L) (hM : IsDerivedLimit F M) :
    IsZero L ↔ IsZero M := by
  obtain ⟨projectionL, connectingL, distinguishedL⟩ := hL
  obtain ⟨projectionM, connectingM, distinguishedM⟩ := hM
  exact ((Triangle.mk projectionL _ connectingL).isZero₁_iff_isIso₂ distinguishedL).trans
    ((Triangle.mk projectionM _ connectingM).isZero₁_iff_isIso₂ distinguishedM).symm

private theorem derivedLimit_single_zero_iff_Hom_zExt_subsingleton
    (A : Type u) [CommRing A] (f : A) (M : ModuleCat.{u} A)
    (hmodel : IsDerivedLimit
      (Functor.ofOpSequence
        (X := fun _ : ℕ => (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)
        (fun _ => f • 𝟙 _))
      (DerivedHomAway.derivedHomFromAway A f
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)))
    (e0 : ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
      (DerivedHomAway.derivedHomFromAway A f
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)) : Type u) ≃+
      DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (Localization.Away f)))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) 0)
    (e1 : ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 1).obj
      (DerivedHomAway.derivedHomFromAway A f
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)) : Type u) ≃+
      DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (Localization.Away f)))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) 1) :
    (∃ L : DerivedCategory (ModuleCat.{u} A),
      IsDerivedLimit
        (Functor.ofOpSequence
          (X := fun _ : ℕ => (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)
          (fun _ => f • 𝟙 _)) L ∧ IsZero L) ↔
      Subsingleton ((ModuleCat.of A (Localization.Away f)) ⟶ M) ∧
      Subsingleton (Abelian.zExt (ModuleCat.of A (Localization.Away f)) M 1) := by
  let model := DerivedHomAway.derivedHomFromAway A f
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)
  have hiff := derivedLimit_single_isZero_iff_Hom_zExt_subsingleton A f M
    model hmodel e0 e1
  constructor
  · rintro ⟨L, hL, hZero⟩
    exact hiff.mp ((derivedLimits_vanish_together A _ L model hL hmodel).mp hZero)
  · intro h
    exact ⟨model, hmodel, hiff.mpr h⟩

private theorem all_single_limits_zero_iff_hom_zExt
    (A : Type u) [CommRing A] (f : A)
    (K : DerivedCategory (ModuleCat.{u} A))
    (hmodel : ∀ p : ℤ,
      let Hp := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj K
      let sHp := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj Hp
      let towerHp := Functor.ofOpSequence (X := fun _ : ℕ => sHp) (fun _ => f • 𝟙 sHp)
      IsDerivedLimit towerHp (DerivedHomAway.derivedHomFromAway A f sHp))
    (hExt : ∀ p : ℤ,
      let Hp := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj K
      let sHp := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj Hp
      Nonempty (∀ n : ℤ,
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
          (DerivedHomAway.derivedHomFromAway A f sHp)) : Type u) ≃+
          DerivedCategory.Ext
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
              (ModuleCat.of A (Localization.Away f))) sHp n)) :
    (∀ p : ℤ,
      let Hp := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj K
      let sHp := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj Hp
      let towerHp := Functor.ofOpSequence (X := fun _ : ℕ => sHp) (fun _ => f • 𝟙 sHp)
      ∃ L : DerivedCategory (ModuleCat.{u} A), IsDerivedLimit towerHp L ∧ IsZero L) ↔
    (∀ p : ℤ,
      let Hp := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj K
      let AfA := ModuleCat.of A (Localization.Away f)
      Subsingleton (AfA ⟶ Hp) ∧ Subsingleton (Abelian.zExt AfA Hp 1)) :=
  forall_congr' fun p => derivedLimit_single_zero_iff_Hom_zExt_subsingleton
    A f ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj K)
    (hmodel p) (Classical.choice (hExt p) 0) (Classical.choice (hExt p) 1)

private theorem exact_tfae_of_edges (A : Type u) [CommRing A] (f : A)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    letI : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    let Af : Type u := Localization.Away f
    let AfA := ModuleCat.of A Af
    let sAf := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj AfA
    let tower := Functor.ofOpSequence (X := fun _ : ℕ => K) (fun _ => f • 𝟙 K)
    let P₁ := ∀ n : ℤ, Subsingleton (DerivedCategory.Ext sAf K n)
    let P₂ := ∀ E : DerivedCategory (ModuleCat.{u} Af),
      Subsingleton
        (((ModuleCat.restrictScalars.{u} (algebraMap A Af)).mapDerivedCategory.obj E) ⟶ K)
    let P₃ := ∃ L : DerivedCategory (ModuleCat.{u} A), IsDerivedLimit tower L ∧ IsZero L
    let P₄ := ∀ p : ℤ,
      let Hp := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj K
      let sHp := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj Hp
      let towerHp := Functor.ofOpSequence (X := fun _ : ℕ => sHp) (fun _ => f • 𝟙 sHp)
      ∃ L : DerivedCategory (ModuleCat.{u} A), IsDerivedLimit towerHp L ∧ IsZero L
    let P₅ := ∀ p : ℤ,
      let Hp := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj K
      Subsingleton (AfA ⟶ Hp) ∧ Subsingleton (Abelian.zExt AfA Hp 1)
    let P₆ := IsZero (DerivedHomAway.derivedHomFromAway A f K)
    let P₇ := IsIso (Pi.lift fun n : ℕ =>
      Pi.π (fun _ : ℕ => K) n - f • Pi.π (fun _ : ℕ => K) (n + 1))
    (P₁ ↔ P₃) → (P₃ ↔ P₄) → (P₄ ↔ P₅) → (P₁ ↔ P₆) →
      (P₆ ↔ P₇) → (P₂ → P₁) → (P₇ → P₂) →
      List.TFAE [P₁, P₂, P₃, P₄, P₅, P₆, P₇] := by
  intro Af AfA sAf tower P₁ P₂ P₃ P₄ P₅ P₆ P₇
    h₁₃ h₃₄ h₄₅ h₁₆ h₆₇ h₂₁ h₇₂
  apply List.tfae_of_forall (b := P₁)
  intro statement membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Iff.rfl
  · exact ⟨h₂₁, fun h => h₇₂ (h₆₇.mp (h₁₆.mp h))⟩
  · exact h₁₃.symm
  · exact h₃₄.symm.trans h₁₃.symm
  · exact (h₄₅.symm.trans h₃₄.symm).trans h₁₃.symm
  · exact h₁₆.symm
  · exact h₆₇.symm.trans h₁₆.symm

private theorem tfae_aux (A : Type u) [CommRing A] (f : A)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    letI : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    let Af : Type u := Localization.Away f
    let AfA := ModuleCat.of A Af
    let sAf := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj AfA
    let tower := Functor.ofOpSequence (X := fun _ : ℕ => K) (fun _ => f • 𝟙 K)
    IsDerivedLimit tower (derivedHomFromAway A f K) ∧
      Nonempty (∀ n : ℤ,
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
      (derivedHomFromAway A f K)) ≃+
        DerivedCategory.Ext sAf K n) ∧
      List.TFAE
        [ ∀ n : ℤ, Subsingleton (DerivedCategory.Ext sAf K n)
        , ∀ E : DerivedCategory (ModuleCat.{u} Af),
            Subsingleton
              (((ModuleCat.restrictScalars.{u} (algebraMap A Af)).mapDerivedCategory.obj E) ⟶ K)
        , ∃ L : DerivedCategory (ModuleCat.{u} A), IsDerivedLimit tower L ∧ IsZero L
        , ∀ p : ℤ,
            let Hp := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj K
            let sHp := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj Hp
            let towerHp := Functor.ofOpSequence (X := fun _ : ℕ => sHp) (fun _ => f • 𝟙 sHp)
            ∃ L : DerivedCategory (ModuleCat.{u} A), IsDerivedLimit towerHp L ∧ IsZero L
        , ∀ p : ℤ,
            let Hp := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj K
            Subsingleton (AfA ⟶ Hp) ∧ Subsingleton (Abelian.zExt AfA Hp 1)
        , IsZero (derivedHomFromAway A f K)
        , IsIso (Pi.lift fun n : ℕ =>
            Pi.π (fun _ : ℕ => K) n - f • Pi.π (fun _ : ℕ => K) (n + 1)) ] := by
  intro Af AfA sAf tower
  refine ⟨derivedHomFromAway_isDerivedLimit A f K,
    derivedHomHomologyExtAddEquiv_nonempty A f K, ?_⟩
  exact exact_tfae_of_edges A f K
    (extVanishing_iff_derivedLimitZero A f K)
    (derivedLimitZero_iff_forall_homologyLimitZero A f K)
    (all_single_limits_zero_iff_hom_zExt A f K
      (fun p => derivedHomFromAway_isDerivedLimit A f _)
      (fun p => derivedHomHomologyExtAddEquiv_nonempty A f _))
    (extVanishing_iff_isZero_derivedHom A f K)
    (rhom_zero_iff_constant_difference_iso A f K)
    (orthogonality_implies_ext_vanishing A f K)
    (fun h E => by
      let := h
      exact subsingleton_hom_restrictScalars_of_isIso_difference A f K E)

/-- The cohomology of `RHom_A(A_f, K)` is `Ext_A(A_f, K)`. Moreover, the
following are equivalent: all those Ext groups vanish; `K` is right orthogonal to every object
of `D(A_f)`; `T(K, f)` vanishes; every `T(H^p(K), f)` vanishes; both
`Hom_A(A_f, H^p(K))` and `Ext^1_A(A_f, H^p(K))` vanish for every `p`;
`RHom_A(A_f, K)` vanishes; and `(x_n) ↦ (x_n - f x_{n+1})` is an isomorphism on the product
of countably many copies of `K`. -/
@[stacks 091P]
public theorem tfae_ext_localization_vanishing (A : Type u) [CommRing A] (f : A)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    letI : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    let Af : Type u := Localization.Away f
    let AfA := ModuleCat.of A Af
    let sAf := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj AfA
    let tower := Functor.ofOpSequence (X := fun _ : ℕ => K) (fun _ => f • 𝟙 K)
    IsDerivedLimit tower (derivedHomFromAway A f K) ∧
      Nonempty (∀ n : ℤ,
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
      (derivedHomFromAway A f K)) ≃+
        DerivedCategory.Ext sAf K n) ∧
      List.TFAE
        [ ∀ n : ℤ, Subsingleton (DerivedCategory.Ext sAf K n)
        , ∀ E : DerivedCategory (ModuleCat.{u} Af),
            Subsingleton
              (((ModuleCat.restrictScalars.{u} (algebraMap A Af)).mapDerivedCategory.obj E) ⟶ K)
        , ∃ L : DerivedCategory (ModuleCat.{u} A), IsDerivedLimit tower L ∧ IsZero L
        , ∀ p : ℤ,
            let Hp := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj K
            let sHp := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj Hp
            let towerHp := Functor.ofOpSequence (X := fun _ : ℕ => sHp) (fun _ => f • 𝟙 sHp)
            ∃ L : DerivedCategory (ModuleCat.{u} A), IsDerivedLimit towerHp L ∧ IsZero L
        , ∀ p : ℤ,
            let Hp := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj K
            Subsingleton (AfA ⟶ Hp) ∧ Subsingleton (Abelian.zExt AfA Hp 1)
        , IsZero (derivedHomFromAway A f K)
        , IsIso (Pi.lift fun n : ℕ =>
            Pi.π (fun _ : ℕ => K) n - f • Pi.π (fun _ : ℕ => K) (n + 1)) ] :=
  tfae_aux A f K

/-- The two-term free resolution of `A_f` identifies `RHom_A(A_f, K)` with the derived limit of
the tower given by repeated multiplication by `f`. -/
public theorem derivedHomFromAwayIsDerivedLimit (A : Type u) [CommRing A] (f : A)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    letI : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    IsDerivedLimit
      (Functor.ofOpSequence (X := fun _ : ℕ => K) (fun _ => f • 𝟙 K))
      (derivedHomFromAway A f K) :=
  (tfae_ext_localization_vanishing A f K).1

/-- The cohomology of `RHom_A(A_f, K)` is identified with `Ext_A(A_f, K)`. -/
public noncomputable def derivedHomFromAwayHomologyIsoExt (A : Type u) [CommRing A] (f : A)
    (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    letI : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
      (derivedHomFromAway A f K)) ≃+
      DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (Localization.Away f))) K n :=
  (Classical.choice (tfae_ext_localization_vanishing A f K).2.1) n

end DerivedHomAway

end

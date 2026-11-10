module

public import StacksFrontier.Homology.DerivedComplete.DerivedHomCompletionVanishing.TelescopeHom
import all StacksFrontier.Homology.DerivedComplete.DerivedHomCompletionVanishing.TelescopeHom

/-!
# The mapping cocone of the constant product difference

This part studies the difference map `∏ I ⟶ ∏ I`, `(x_n) ↦ (x_n - f x_{n+1})`, its image in the
derived category, and the components and differentials of its mapping cocone, compared with
the transported Hom complex out of the telescope resolution.
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

noncomputable def constantProductDerivedIso
    (A : Type u) [CommRing A]
    (I : CochainComplex (ModuleCat.{u} A) ℤ) :
    DerivedCategory.Q.obj (∏ᶜ fun _ : ℕ => I) ≅
      (∏ᶜ fun _ : ℕ => DerivedCategory.Q.obj I) := by
  let h := Classical.choice (Stacks.DerivedProducts.isLimit_productFanInDerivedCategory
    (A := ModuleCat.{u} A) (I := ℕ) (fun _ : ℕ => I))
  exact h.conePointUniqueUpToIso (productIsProduct (fun _ : ℕ => DerivedCategory.Q.obj I))

theorem constantProductDerivedIso_π
    (A : Type u) [CommRing A]
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (index : ℕ) :
    (constantProductDerivedIso A I).hom ≫
      Pi.π (fun _ : ℕ => DerivedCategory.Q.obj I) index =
        DerivedCategory.Q.map (Pi.π (fun _ : ℕ => I) index) := by
  unfold constantProductDerivedIso
  simpa [Stacks.DerivedProducts.productFanInDerivedCategory] using
    (IsLimit.conePointUniqueUpToIso_hom_comp
      (Classical.choice (Stacks.DerivedProducts.isLimit_productFanInDerivedCategory
        (A := ModuleCat.{u} A) (I := ℕ) (fun _ : ℕ => I)))
      (productIsProduct (fun _ : ℕ => DerivedCategory.Q.obj I)) ⟨index⟩)

noncomputable def constantProductDifferenceComplex
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) :
    (∏ᶜ fun _ : ℕ => I) ⟶ (∏ᶜ fun _ : ℕ => I) :=
  Pi.lift (fun index : ℕ => Pi.π (fun _ : ℕ => I) index -
    f • Pi.π (fun _ : ℕ => I) (index + 1))

theorem constantProductDifferenceComplex_π
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (index : ℕ) :
    constantProductDifferenceComplex A f I ≫ Pi.π (fun _ : ℕ => I) index =
      Pi.π (fun _ : ℕ => I) index - f • Pi.π (fun _ : ℕ => I) (index + 1) := by
  simp [constantProductDifferenceComplex]

theorem constantProductDifferenceDerived_square
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) :
    (constantProductDerivedIso A I).inv ≫
      DerivedCategory.Q.map (constantProductDifferenceComplex A f I) ≫
      (constantProductDerivedIso A I).hom =
    Pi.lift (fun index : ℕ =>
      Pi.π (fun _ : ℕ => DerivedCategory.Q.obj I) index -
        f • Pi.π (fun _ : ℕ => DerivedCategory.Q.obj I) (index + 1)) := by
  apply Pi.hom_ext
  intro index
  simp only [Category.assoc, constantProductDerivedIso_π]
  rw [← Functor.map_comp, constantProductDifferenceComplex_π,
    Functor.map_sub, Functor.map_smul]
  rw [Preadditive.comp_sub, Linear.comp_smul]
  rw [← constantProductDerivedIso_π A I index,
    ← constantProductDerivedIso_π A I (index + 1)]
  simp

noncomputable def constantDifferenceCoconeXIso
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    (CochainComplex.mappingCocone (constantProductDifferenceComplex A f I)).X n ≅
      ((∏ᶜ fun _ : ℕ => I).X n ⊞ (∏ᶜ fun _ : ℕ => I).X (n - 1)) := by
  let φ := constantProductDifferenceComplex A f I
  exact (CochainComplex.mappingCone φ).shiftFunctorObjXIso (-1) n (n - 1)
      (by omega) ≪≫
    HomologicalComplex.homotopyCofiber.XIsoBiprod φ (n - 1) n
      (show (ComplexShape.up ℤ).Rel (n - 1) n by simp [ComplexShape.up_Rel])

noncomputable def constantProductXIso
    (A : Type u) [CommRing A]
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    (∏ᶜ fun _ : ℕ => I).X n ≅ ModuleCat.of A (ℕ → I.X n) := by
  let : IsIso (piComparison
      (HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) n)
        (fun _ : ℕ => I)) := Stacks.DerivedProducts.isIso_piComparison_eval (fun _ : ℕ => I) n
  exact asIso (piComparison
      (HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) n)
        (fun _ : ℕ => I)) ≪≫ ModuleCat.piIsoPi (fun _ : ℕ => I.X n)

noncomputable def constantDifferenceCoconePairIso
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    (CochainComplex.mappingCocone (constantProductDifferenceComplex A f I)).X n ≅
      ModuleCat.of A ((ℕ → I.X (n - 1)) × (ℕ → I.X n)) :=
  constantDifferenceCoconeXIso A f I n ≪≫
    biprod.mapIso (constantProductXIso A I n) (constantProductXIso A I (n - 1)) ≪≫
    ModuleCat.biprodIsoProd (ModuleCat.of A (ℕ → I.X n))
      (ModuleCat.of A (ℕ → I.X (n - 1))) ≪≫
    (LinearEquiv.prodComm A (ℕ → I.X n) (ℕ → I.X (n - 1))).toModuleIso

theorem coconeSign (n : ℤ) :
    (-1 : ℤ).negOnePow = -1 ∧
      -(n + 2).negOnePow = (n + 1).negOnePow := by
  constructor
  · simp
  · have h := Int.negOnePow_succ (n + 1)
    simpa [add_assoc] using congrArg Neg.neg h

noncomputable def signTwistPairIso
    (A : Type u) [CommRing A]
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    ModuleCat.of A ((ℕ → I.X (n - 1)) × (ℕ → I.X n)) ≅
      ModuleCat.of A ((ℕ → I.X (n - 1)) × (ℕ → I.X n)) :=
  ((LinearEquiv.smulOfUnit
    (Units.map (Int.castRingHom A) (n + 1).negOnePow) :
      (ℕ → I.X (n - 1)) ≃ₗ[A] (ℕ → I.X (n - 1))).prodCongr
        (LinearEquiv.refl A (ℕ → I.X n))).toModuleIso

theorem signTwistPairIso_fst
    (A : Type u) [CommRing A]
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (pair : (ℕ → I.X (n - 1)) × (ℕ → I.X n)) (index : ℕ) :
    ((signTwistPairIso A I n).hom pair).1 index =
      (n + 1).negOnePow • pair.1 index := by
  simp only [signTwistPairIso, LinearEquiv.toModuleIso_hom, LinearEquiv.coe_prodCongr,
    LinearEquiv.refl_toLinearMap, ConcreteCategory.hom_ofHom, LinearMap.prodMap_apply,
    LinearEquiv.coe_coe, LinearMap.id_coe, id_eq, Units.smul_def]
  change ((Units.map (Int.castRingHom A) (n + 1).negOnePow : Aˣ) : A) •
      pair.1 index = ((n + 1).negOnePow : ℤ) • pair.1 index
  rw [← Int.cast_smul_eq_zsmul (R := A) ((n + 1).negOnePow : ℤ) (pair.1 index)]
  simp

theorem signTwistPairIso_snd
    (A : Type u) [CommRing A]
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (pair : (ℕ → I.X (n - 1)) × (ℕ → I.X n)) (index : ℕ) :
    ((signTwistPairIso A I n).hom pair).2 index = pair.2 index := by
  simp [signTwistPairIso]

theorem signTwistPairIso_inv_fst
    (A : Type u) [CommRing A]
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (pair : (ℕ → I.X (n - 1)) × (ℕ → I.X n)) (index : ℕ) :
    ((signTwistPairIso A I n).inv pair).1 index =
      (n + 1).negOnePow • pair.1 index := by
  let twisted := (signTwistPairIso A I n).inv pair
  have hback : ((signTwistPairIso A I n).hom twisted).1 index = pair.1 index := by
    simp [twisted]
  have hforward := signTwistPairIso_fst A I n twisted index
  rw [hback] at hforward
  change pair.1 index = ((n + 1).negOnePow : ℤ) • twisted.1 index at hforward
  change twisted.1 index = ((n + 1).negOnePow : ℤ) • pair.1 index
  calc
    twisted.1 index = (1 : ℤ) • twisted.1 index := (one_smul ℤ _).symm
    _ = (((n + 1).negOnePow : ℤ) * (n + 1).negOnePow) • twisted.1 index := by
      simp only [← Units.val_mul, Int.units_mul_self, Units.val_one]
    _ = ((n + 1).negOnePow : ℤ) • pair.1 index := by
      rw [mul_smul, hforward]

theorem signTwistPairIso_inv_snd
    (A : Type u) [CommRing A]
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (pair : (ℕ → I.X (n - 1)) × (ℕ → I.X n)) (index : ℕ) :
    ((signTwistPairIso A I n).inv pair).2 index = pair.2 index := by
  simp [signTwistPairIso]

theorem biprodIsoProd_hom_fst
    (A : Type u) [CommRing A]
    (M N : ModuleCat.{u} A) (x : (M ⊞ N : ModuleCat.{u} A)) :
    ((ModuleCat.biprodIsoProd M N).hom x).1 =
      (biprod.fst : M ⊞ N ⟶ M).hom x := by
  have h : (ModuleCat.biprodIsoProd M N).hom ≫
      ModuleCat.ofHom (LinearMap.fst A M N) =
      (biprod.fst : M ⊞ N ⟶ M) := by
    calc
      _ = (ModuleCat.biprodIsoProd M N).hom ≫
          ((ModuleCat.biprodIsoProd M N).inv ≫ biprod.fst) := by
            rw [ModuleCat.biprodIsoProd_inv_comp_fst]
      _ = biprod.fst := by rw [← Category.assoc]; simp
  have hx := congrArg (fun g : M ⊞ N ⟶ M => g.hom x) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_ofHom, LinearMap.fst_apply] using hx

theorem biprodIsoProd_hom_snd
    (A : Type u) [CommRing A]
    (M N : ModuleCat.{u} A) (x : (M ⊞ N : ModuleCat.{u} A)) :
    ((ModuleCat.biprodIsoProd M N).hom x).2 =
      (biprod.snd : M ⊞ N ⟶ N).hom x := by
  have h : (ModuleCat.biprodIsoProd M N).hom ≫
      ModuleCat.ofHom (LinearMap.snd A M N) =
      (biprod.snd : M ⊞ N ⟶ N) := by
    calc
      _ = (ModuleCat.biprodIsoProd M N).hom ≫
          ((ModuleCat.biprodIsoProd M N).inv ≫ biprod.snd) := by
            rw [ModuleCat.biprodIsoProd_inv_comp_snd]
      _ = biprod.snd := by rw [← Category.assoc]; simp
  have hx := congrArg (fun g : M ⊞ N ⟶ N => g.hom x) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_ofHom, LinearMap.snd_apply] using hx

theorem constantDifferenceCoconePairIso_fst
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (x : (CochainComplex.mappingCocone (constantProductDifferenceComplex A f I)).X n) :
    ((constantDifferenceCoconePairIso A f I n).hom x).1 =
      (constantProductXIso A I (n - 1)).hom
        ((biprod.snd :
          ((∏ᶜ fun _ : ℕ => I).X n ⊞ (∏ᶜ fun _ : ℕ => I).X (n - 1)) ⟶
            (∏ᶜ fun _ : ℕ => I).X (n - 1)).hom
          ((constantDifferenceCoconeXIso A f I n).hom x)) := by
  simp only [constantDifferenceCoconePairIso, Iso.trans_hom, biprod.mapIso_hom,
    LinearEquiv.toModuleIso_hom, ModuleCat.hom_comp, ConcreteCategory.hom_ofHom, LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.prodComm_apply, Prod.fst_swap]
  rw [biprodIsoProd_hom_snd]
  change (biprod.map (constantProductXIso A I n).hom
      (constantProductXIso A I (n - 1)).hom ≫ biprod.snd).hom
        ((constantDifferenceCoconeXIso A f I n).hom x) =
      (biprod.snd ≫ (constantProductXIso A I (n - 1)).hom).hom
        ((constantDifferenceCoconeXIso A f I n).hom x)
  rw [biprod.map_snd]

theorem constantDifferenceCoconePairIso_snd
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (x : (CochainComplex.mappingCocone (constantProductDifferenceComplex A f I)).X n) :
    ((constantDifferenceCoconePairIso A f I n).hom x).2 =
      (constantProductXIso A I n).hom
        ((biprod.fst :
          ((∏ᶜ fun _ : ℕ => I).X n ⊞ (∏ᶜ fun _ : ℕ => I).X (n - 1)) ⟶
            (∏ᶜ fun _ : ℕ => I).X n).hom
          ((constantDifferenceCoconeXIso A f I n).hom x)) := by
  simp only [constantDifferenceCoconePairIso, Iso.trans_hom, biprod.mapIso_hom,
    LinearEquiv.toModuleIso_hom, ModuleCat.hom_comp, ConcreteCategory.hom_ofHom, LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.prodComm_apply, Prod.snd_swap]
  rw [biprodIsoProd_hom_fst]
  change (biprod.map (constantProductXIso A I n).hom
      (constantProductXIso A I (n - 1)).hom ≫ biprod.fst).hom
        ((constantDifferenceCoconeXIso A f I n).hom x) =
      (biprod.fst ≫ (constantProductXIso A I n).hom).hom
        ((constantDifferenceCoconeXIso A f I n).hom x)
  rw [biprod.map_fst]

private noncomputable def coconeToHomPairComponentIso
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    (CochainComplex.mappingCocone (constantProductDifferenceComplex A f I)).X n ≅
      (telescopeHom_transport_complex A f I).X n :=
  constantDifferenceCoconePairIso A f I n ≪≫ signTwistPairIso A I n

private theorem coconeToHomPairComponentIso_fst
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (x : (CochainComplex.mappingCocone (constantProductDifferenceComplex A f I)).X n)
    (index : ℕ) :
    ((coconeToHomPairComponentIso A f I n).hom x).1 index =
      (n + 1).negOnePow •
        ((constantProductXIso A I (n - 1)).hom
          ((biprod.snd :
            ((∏ᶜ fun _ : ℕ => I).X n ⊞ (∏ᶜ fun _ : ℕ => I).X (n - 1)) ⟶
              (∏ᶜ fun _ : ℕ => I).X (n - 1)).hom
            ((constantDifferenceCoconeXIso A f I n).hom x))) index := by
  change (((constantDifferenceCoconePairIso A f I n).hom ≫
    (signTwistPairIso A I n).hom).hom x).1 index = _
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [signTwistPairIso_fst, constantDifferenceCoconePairIso_fst]

private theorem coconeToHomPairComponentIso_snd
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (x : (CochainComplex.mappingCocone (constantProductDifferenceComplex A f I)).X n)
    (index : ℕ) :
    ((coconeToHomPairComponentIso A f I n).hom x).2 index =
      ((constantProductXIso A I n).hom
        ((biprod.fst :
          ((∏ᶜ fun _ : ℕ => I).X n ⊞ (∏ᶜ fun _ : ℕ => I).X (n - 1)) ⟶
            (∏ᶜ fun _ : ℕ => I).X n).hom
          ((constantDifferenceCoconeXIso A f I n).hom x))) index := by
  change (((constantDifferenceCoconePairIso A f I n).hom ≫
    (signTwistPairIso A I n).hom).hom x).2 index = _
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [signTwistPairIso_snd, constantDifferenceCoconePairIso_snd]

theorem constantDifferenceCoconeXIso_comp_fst
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    let φ := constantProductDifferenceComplex A f I
    (constantDifferenceCoconeXIso A f I n).hom ≫
      (biprod.fst :
        ((∏ᶜ fun _ : ℕ => I).X n ⊞ (∏ᶜ fun _ : ℕ => I).X (n - 1)) ⟶
          (∏ᶜ fun _ : ℕ => I).X n) =
      ((CochainComplex.mappingCone φ).shiftFunctorObjXIso (-1) n (n - 1)
        (by omega)).hom ≫
        HomologicalComplex.homotopyCofiber.fstX φ (n - 1) n
          (by simp [ComplexShape.up_Rel]) := by
  dsimp only
  change (((CochainComplex.mappingCone (constantProductDifferenceComplex A f I)).shiftFunctorObjXIso
      (-1) n (n - 1) (by omega)).hom ≫
    (HomologicalComplex.homotopyCofiber.XIsoBiprod
      (constantProductDifferenceComplex A f I) (n - 1) n
      (by simp [ComplexShape.up_Rel])).hom) ≫ biprod.fst = _
  exact Category.assoc _ _ _

theorem constantDifferenceCoconeXIso_comp_snd
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    let φ := constantProductDifferenceComplex A f I
    (constantDifferenceCoconeXIso A f I n).hom ≫
      (biprod.snd :
        ((∏ᶜ fun _ : ℕ => I).X n ⊞ (∏ᶜ fun _ : ℕ => I).X (n - 1)) ⟶
          (∏ᶜ fun _ : ℕ => I).X (n - 1)) =
      ((CochainComplex.mappingCone φ).shiftFunctorObjXIso (-1) n (n - 1)
        (by omega)).hom ≫
        HomologicalComplex.homotopyCofiber.sndX φ (n - 1) := by
  dsimp only
  change (((CochainComplex.mappingCone (constantProductDifferenceComplex A f I)).shiftFunctorObjXIso
      (-1) n (n - 1) (by omega)).hom ≫
    (HomologicalComplex.homotopyCofiber.XIsoBiprod
      (constantProductDifferenceComplex A f I) (n - 1) n
      (by simp [ComplexShape.up_Rel])).hom) ≫ biprod.snd = _
  calc
    _ = (((CochainComplex.mappingCone (constantProductDifferenceComplex A f I)).shiftFunctorObjXIso
        (-1) n (n - 1) (by omega)).hom ≫
        ((HomologicalComplex.homotopyCofiber.XIsoBiprod
          (constantProductDifferenceComplex A f I) (n - 1) n
          (by simp [ComplexShape.up_Rel])).hom ≫ biprod.snd)) :=
      Category.assoc _ _ _
    _ = _ := by
      congr 1
      have hnext : (ComplexShape.up ℤ).next (n - 1) = n :=
        (ComplexShape.up ℤ).next_eq' (by simp [ComplexShape.up_Rel])
      simp only [HomologicalComplex.homotopyCofiber.sndX,
        dite_eq_left (show (ComplexShape.up ℤ).Rel (n - 1)
          ((ComplexShape.up ℤ).next (n - 1)) from by
            rw [hnext]
            simp [ComplexShape.up_Rel])]
      let leftIndex : { j : ℤ // (ComplexShape.up ℤ).Rel (n - 1) j } :=
        ⟨n, by simp [ComplexShape.up_Rel]⟩
      let rightIndex : { j : ℤ // (ComplexShape.up ℤ).Rel (n - 1) j } :=
        ⟨(ComplexShape.up ℤ).next (n - 1), by
          rw [hnext]
          simp [ComplexShape.up_Rel]⟩
      have hindex : leftIndex = rightIndex := Subsingleton.elim _ _
      exact congrArg (fun index : { j : ℤ // (ComplexShape.up ℤ).Rel (n - 1) j } =>
        (HomologicalComplex.homotopyCofiber.XIsoBiprod
          (constantProductDifferenceComplex A f I) (n - 1) index.1 index.2).hom ≫
            biprod.snd) hindex

theorem shiftedCone_first_projection_cast
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    let φ := constantProductDifferenceComplex A f I
    ((CochainComplex.mappingCone φ).shiftFunctorObjXIso (-1) (n + 1)
      (n + 1 - 1) (by omega)).hom ≫
      HomologicalComplex.homotopyCofiber.fstX φ (n + 1 - 1) (n + 1)
        (by simp [ComplexShape.up_Rel]) =
    ((CochainComplex.mappingCone φ).shiftFunctorObjXIso (-1) (n + 1) n
      (by omega)).hom ≫
      HomologicalComplex.homotopyCofiber.fstX φ n (n + 1)
        (by simp [ComplexShape.up_Rel]) := by
  dsimp only
  let leftIndex : { i : ℤ // (ComplexShape.up ℤ).Rel i (n + 1) } :=
    ⟨n + 1 - 1, by simp [ComplexShape.up_Rel]⟩
  let rightIndex : { i : ℤ // (ComplexShape.up ℤ).Rel i (n + 1) } :=
    ⟨n, by simp [ComplexShape.up_Rel]⟩
  have : Subsingleton { i : ℤ // (ComplexShape.up ℤ).Rel i (n + 1) } :=
    Subtype.subsingleton_iff.mpr (fun _ _ ha hb => (ComplexShape.up ℤ).prev_eq ha hb)
  have hindex : leftIndex = rightIndex := Subsingleton.elim _ _
  exact congrArg (fun index : { i : ℤ // (ComplexShape.up ℤ).Rel i (n + 1) } =>
    ((CochainComplex.mappingCone (constantProductDifferenceComplex A f I)).shiftFunctorObjXIso
      (-1) (n + 1) index.1 (by
        have hi := index.2
        simp only [ComplexShape.up_Rel] at hi
        omega)).hom ≫
      HomologicalComplex.homotopyCofiber.fstX
        (constantProductDifferenceComplex A f I) index.1 (n + 1) index.2) hindex

set_option backward.isDefEq.respectTransparency false in
theorem shiftedCone_second_projection_cast
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    let φ := constantProductDifferenceComplex A f I
    ((CochainComplex.mappingCone φ).shiftFunctorObjXIso (-1) (n + 1)
      (n + 1 - 1) (by omega)).hom ≫
      HomologicalComplex.homotopyCofiber.sndX φ (n + 1 - 1) ≫
        eqToHom (congrArg (∏ᶜ fun _ : ℕ => I).X (show n + 1 - 1 = n by omega)) =
    ((CochainComplex.mappingCone φ).shiftFunctorObjXIso (-1) (n + 1) n
      (by omega)).hom ≫
      HomologicalComplex.homotopyCofiber.sndX φ n := by
  dsimp only
  let productComplex := ∏ᶜ fun _ : ℕ => I
  let leftIndex : { i : ℤ // (ComplexShape.up ℤ).Rel i (n + 1) } :=
    ⟨n + 1 - 1, by simp [ComplexShape.up_Rel]⟩
  let rightIndex : { i : ℤ // (ComplexShape.up ℤ).Rel i (n + 1) } :=
    ⟨n, by simp [ComplexShape.up_Rel]⟩
  have : Subsingleton { i : ℤ // (ComplexShape.up ℤ).Rel i (n + 1) } :=
    Subtype.subsingleton_iff.mpr (fun _ _ ha hb => (ComplexShape.up ℤ).prev_eq ha hb)
  have hindex : leftIndex = rightIndex := Subsingleton.elim _ _
  have h := congrArg (fun index : { i : ℤ // (ComplexShape.up ℤ).Rel i (n + 1) } =>
    (((CochainComplex.mappingCone (constantProductDifferenceComplex A f I)).shiftFunctorObjXIso
      (-1) (n + 1) index.1 (by
        have hi := index.2
        simp only [ComplexShape.up_Rel] at hi
        omega)).hom ≫
      HomologicalComplex.homotopyCofiber.sndX
        (constantProductDifferenceComplex A f I) index.1) ≫
        eqToHom (congrArg productComplex.X
          ((ComplexShape.up ℤ).prev_eq index.2 rightIndex.2))) hindex
  have hleftShift :
      ((CochainComplex.mappingCone (constantProductDifferenceComplex A f I)).shiftFunctorObjXIso
        (-1) (n + 1) (n + 1 - 1) (by omega)).hom =
      (𝟙 ((CochainComplex.mappingCone (constantProductDifferenceComplex A f I)).X
        (n + 1 + -1))) := by
    rfl
  rw [hleftShift]
  simpa [leftIndex, rightIndex, productComplex] using h

theorem mappingCocone_first_differential
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    let φ := constantProductDifferenceComplex A f I
    (CochainComplex.mappingCocone φ).d n (n + 1) ≫
      ((CochainComplex.mappingCone φ).shiftFunctorObjXIso (-1) (n + 1) n
        (by omega)).hom ≫
      HomologicalComplex.homotopyCofiber.fstX φ n (n + 1)
        (by simp [ComplexShape.up_Rel]) =
    ((CochainComplex.mappingCone φ).shiftFunctorObjXIso (-1) n (n - 1)
        (by omega)).hom ≫
      HomologicalComplex.homotopyCofiber.fstX φ (n - 1) n
        (by simp [ComplexShape.up_Rel]) ≫
      (∏ᶜ fun _ : ℕ => I).d n (n + 1) := by
  dsimp only
  simp only [CochainComplex.mappingCocone, CochainComplex.shiftFunctor_obj_d',
    CochainComplex.mappingCone, CochainComplex.shiftFunctorObjXIso]
  simp only [(coconeSign n).1, Units.smul_def, Units.val_neg, Units.val_one,
    neg_smul, one_smul]
  rw [Preadditive.neg_comp]
  rw [← Category.assoc, HomologicalComplex.d_comp_XIsoOfEq_hom]
  simp [HomologicalComplex.homotopyCofiber.d_fstX]
  rfl

theorem mappingCoconeXIso_d_fst
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    (CochainComplex.mappingCocone (constantProductDifferenceComplex A f I)).d n (n + 1) ≫
      (constantDifferenceCoconeXIso A f I (n + 1)).hom ≫
      (biprod.fst :
        ((∏ᶜ fun _ : ℕ => I).X (n + 1) ⊞ (∏ᶜ fun _ : ℕ => I).X (n + 1 - 1)) ⟶
          (∏ᶜ fun _ : ℕ => I).X (n + 1)) =
    (constantDifferenceCoconeXIso A f I n).hom ≫
      (biprod.fst :
        ((∏ᶜ fun _ : ℕ => I).X n ⊞ (∏ᶜ fun _ : ℕ => I).X (n - 1)) ⟶
          (∏ᶜ fun _ : ℕ => I).X n) ≫
      (∏ᶜ fun _ : ℕ => I).d n (n + 1) := by
  conv_rhs =>
    rw [← Category.assoc]
    rw [constantDifferenceCoconeXIso_comp_fst A f I n]
  conv_lhs =>
    rw [constantDifferenceCoconeXIso_comp_fst A f I (n + 1)]
  rw [shiftedCone_first_projection_cast A f I n]
  exact mappingCocone_first_differential A f I n

theorem mappingCocone_second_differential
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    let φ := constantProductDifferenceComplex A f I
    (CochainComplex.mappingCocone φ).d n (n + 1) ≫
      ((CochainComplex.mappingCone φ).shiftFunctorObjXIso (-1) (n + 1) n
        (by omega)).hom ≫
      HomologicalComplex.homotopyCofiber.sndX φ n =
    -(((CochainComplex.mappingCone φ).shiftFunctorObjXIso (-1) n (n - 1)
        (by omega)).hom ≫
      HomologicalComplex.homotopyCofiber.fstX φ (n - 1) n
        (by simp [ComplexShape.up_Rel]) ≫ φ.f n +
      ((CochainComplex.mappingCone φ).shiftFunctorObjXIso (-1) n (n - 1)
        (by omega)).hom ≫
      HomologicalComplex.homotopyCofiber.sndX φ (n - 1) ≫
      (∏ᶜ fun _ : ℕ => I).d (n - 1) n) := by
  dsimp only
  simp only [CochainComplex.mappingCocone, CochainComplex.shiftFunctor_obj_d',
    CochainComplex.mappingCone, CochainComplex.shiftFunctorObjXIso]
  simp only [(coconeSign n).1, Units.smul_def, Units.val_neg, Units.val_one,
    neg_smul, one_smul]
  rw [Preadditive.neg_comp]
  rw [← Category.assoc, HomologicalComplex.d_comp_XIsoOfEq_hom]
  simp only [Int.reduceNeg, shiftFunctor_obj_X', HomologicalComplex.homotopyCofiber_X,
    HomologicalComplex.homotopyCofiber_d, ComplexShape.up_Rel, neg_add_cancel_right,
    HomologicalComplex.homotopyCofiber.d_sndX, neg_add_rev, shiftFunctor_obj_X,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp]
  change -HomologicalComplex.homotopyCofiber.sndX
      (constantProductDifferenceComplex A f I) (n - 1) ≫
        (∏ᶜ fun _ : ℕ => I).d (n - 1) n +
      -HomologicalComplex.homotopyCofiber.fstX
        (constantProductDifferenceComplex A f I) (n - 1) n
          (by simp [ComplexShape.up_Rel]) ≫
        (constantProductDifferenceComplex A f I).f n =
      -(HomologicalComplex.homotopyCofiber.fstX
        (constantProductDifferenceComplex A f I) (n - 1) n
          (by simp [ComplexShape.up_Rel]) ≫
        (constantProductDifferenceComplex A f I).f n +
        HomologicalComplex.homotopyCofiber.sndX
          (constantProductDifferenceComplex A f I) (n - 1) ≫
        (∏ᶜ fun _ : ℕ => I).d (n - 1) n)
  simp only [neg_add]
  exact add_comm _ _

set_option backward.isDefEq.respectTransparency false in
theorem mappingCoconeXIso_d_snd_cast
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    let φ := constantProductDifferenceComplex A f I
    (((CochainComplex.mappingCocone φ).d n (n + 1) ≫
      (constantDifferenceCoconeXIso A f I (n + 1)).hom) ≫
      (biprod.snd :
        ((∏ᶜ fun _ : ℕ => I).X (n + 1) ⊞ (∏ᶜ fun _ : ℕ => I).X (n + 1 - 1)) ⟶
          (∏ᶜ fun _ : ℕ => I).X (n + 1 - 1))) ≫
      eqToHom (congrArg (∏ᶜ fun _ : ℕ => I).X (show n + 1 - 1 = n by omega)) =
    (CochainComplex.mappingCocone φ).d n (n + 1) ≫
      (((CochainComplex.mappingCone φ).shiftFunctorObjXIso (-1) (n + 1) n
        (by omega)).hom ≫ HomologicalComplex.homotopyCofiber.sndX φ n) := by
  dsimp only
  have hprefix :
      (((CochainComplex.mappingCocone (constantProductDifferenceComplex A f I)).d
          n (n + 1) ≫ (constantDifferenceCoconeXIso A f I (n + 1)).hom) ≫
        (biprod.snd :
          ((∏ᶜ fun _ : ℕ => I).X (n + 1) ⊞ (∏ᶜ fun _ : ℕ => I).X (n + 1 - 1)) ⟶
            (∏ᶜ fun _ : ℕ => I).X (n + 1 - 1))) =
      (CochainComplex.mappingCocone (constantProductDifferenceComplex A f I)).d n (n + 1) ≫
        (((CochainComplex.mappingCone (constantProductDifferenceComplex A f I)).shiftFunctorObjXIso
          (-1) (n + 1) (n + 1 - 1) (by omega)).hom ≫
          HomologicalComplex.homotopyCofiber.sndX
            (constantProductDifferenceComplex A f I) (n + 1 - 1)) := by
    calc
      _ = (CochainComplex.mappingCocone (constantProductDifferenceComplex A f I)).d
          n (n + 1) ≫
            ((constantDifferenceCoconeXIso A f I (n + 1)).hom ≫ biprod.snd) :=
        Category.assoc _ _ _
      _ = _ := by rw [constantDifferenceCoconeXIso_comp_snd A f I (n + 1)]
  rw [hprefix]
  calc
    _ = (CochainComplex.mappingCocone (constantProductDifferenceComplex A f I)).d n (n + 1) ≫
        ((((CochainComplex.mappingCone (constantProductDifferenceComplex A f I)).shiftFunctorObjXIso
          (-1) (n + 1) (n + 1 - 1) (by omega)).hom ≫
          HomologicalComplex.homotopyCofiber.sndX
            (constantProductDifferenceComplex A f I) (n + 1 - 1)) ≫
          eqToHom (congrArg (∏ᶜ fun _ : ℕ => I).X
            (show n + 1 - 1 = n by omega))) := Category.assoc _ _ _
    _ = _ := congrArg
      (fun ψ => (CochainComplex.mappingCocone (constantProductDifferenceComplex A f I)).d
        n (n + 1) ≫ ψ)
      (shiftedCone_second_projection_cast A f I n)

set_option backward.isDefEq.respectTransparency false in
theorem mappingCoconeXIso_d_snd
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    let φ := constantProductDifferenceComplex A f I
    (((CochainComplex.mappingCocone φ).d n (n + 1) ≫
      (constantDifferenceCoconeXIso A f I (n + 1)).hom) ≫
      (biprod.snd :
        ((∏ᶜ fun _ : ℕ => I).X (n + 1) ⊞ (∏ᶜ fun _ : ℕ => I).X (n + 1 - 1)) ⟶
          (∏ᶜ fun _ : ℕ => I).X (n + 1 - 1))) ≫
      eqToHom (congrArg (∏ᶜ fun _ : ℕ => I).X (show n + 1 - 1 = n by omega)) =
    -(((constantDifferenceCoconeXIso A f I n).hom ≫
        (biprod.fst :
          ((∏ᶜ fun _ : ℕ => I).X n ⊞ (∏ᶜ fun _ : ℕ => I).X (n - 1)) ⟶
            (∏ᶜ fun _ : ℕ => I).X n)) ≫ φ.f n +
      ((constantDifferenceCoconeXIso A f I n).hom ≫
        (biprod.snd :
          ((∏ᶜ fun _ : ℕ => I).X n ⊞ (∏ᶜ fun _ : ℕ => I).X (n - 1)) ⟶
            (∏ᶜ fun _ : ℕ => I).X (n - 1))) ≫
        (∏ᶜ fun _ : ℕ => I).d (n - 1) n) := by
  dsimp only
  have hfst := congrArg (fun ψ :
      (CochainComplex.mappingCocone (constantProductDifferenceComplex A f I)).X n ⟶
        (∏ᶜ fun _ : ℕ => I).X n =>
      ψ ≫ (constantProductDifferenceComplex A f I).f n)
    (constantDifferenceCoconeXIso_comp_fst A f I n)
  have hsnd := congrArg (fun ψ :
      (CochainComplex.mappingCocone (constantProductDifferenceComplex A f I)).X n ⟶
        (∏ᶜ fun _ : ℕ => I).X (n - 1) =>
      ψ ≫ (∏ᶜ fun _ : ℕ => I).d (n - 1) n)
    (constantDifferenceCoconeXIso_comp_snd A f I n)
  rw [hfst, hsnd]
  exact (mappingCoconeXIso_d_snd_cast A f I n).trans
    (by simpa only [Category.assoc] using mappingCocone_second_differential A f I n)

private theorem transportHom_d_comp_component_iso
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (z : (HomComplexR A (telescopeResolution A f) I).X n) :
    ((telescopeHom_transport_complex A f I).d n (n + 1)).hom
        ((telescopeHom_component_iso A f I n).hom z) =
      (telescopeHom_component_iso A f I (n + 1)).hom
        (((HomComplexR A (telescopeResolution A f) I).d n (n + 1)).hom z) := by
  simp only [telescopeHom_transport_complex, CochainComplex.of_d,
    telescopeHom_component_iso]
  change (telescopeHom_product_equiv A f I (n + 1))
    (((HomComplexR A (telescopeResolution A f) I).d n (n + 1)).hom
      ((telescopeHom_product_equiv A f I n).symm
        ((telescopeHom_product_equiv A f I n) z))) = _
  simp

private theorem transportHom_first_differential
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (z : (HomComplexR A (telescopeResolution A f) I).X n) (index : ℕ) :
    ((telescopeHom_next_index_iso A I n).hom
      (((telescopeHom_transport_complex A f I).d n (n + 1)).hom
        ((telescopeHom_component_iso A f I n).hom z))).1 index =
    (I.d (n - 1) n).hom ((telescopeHom_product_equiv A f I n z).1 index) +
      (n + 1).negOnePow •
        ((telescopeHom_product_equiv A f I n z).2 index -
          f • (telescopeHom_product_equiv A f I n z).2 (index + 1)) := by
  rw [transportHom_d_comp_component_iso A f I n z]
  exact telescopeHom_pair_first_differential_normalized A f I n z index

private theorem transportHom_second_differential
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (z : (HomComplexR A (telescopeResolution A f) I).X n) (index : ℕ) :
    (((telescopeHom_transport_complex A f I).d n (n + 1)).hom
      ((telescopeHom_component_iso A f I n).hom z)).2 index =
    (I.d n (n + 1)).hom ((telescopeHom_product_equiv A f I n z).2 index) := by
  rw [transportHom_d_comp_component_iso A f I n z]
  exact telescopeHom_pair_second_differential A f I n z index

theorem constantProductXIso_projection
    (A : Type u) [CommRing A]
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) (index : ℕ) :
    (constantProductXIso A I n).hom ≫
      ModuleCat.ofHom (LinearMap.proj index :
        (ℕ → I.X n) →ₗ[A] I.X n) =
      (Pi.π (fun _ : ℕ => I) index).f n := by
  simp only [constantProductXIso, Iso.trans_hom, Category.assoc,
    ModuleCat.piIsoPi_hom_ker_subtype, asIso_hom]
  exact piComparison_comp_π
    (HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) n)
    (fun _ : ℕ => I) index

/-- The `k`-th coordinate of `constantProductXIso` is the degree-`n` part of the projection. -/
theorem constantProductXIso_hom_apply
    (A : Type u) [CommRing A]
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) (z : (∏ᶜ fun _ : ℕ => I).X n) (k : ℕ) :
    ((constantProductXIso A I n).hom z) k = ((Pi.π (fun _ : ℕ => I) k).f n).hom z := by
  have hk := congrArg
    (fun φ : (∏ᶜ fun _ : ℕ => I).X n ⟶ I.X n => φ.hom z)
    (constantProductXIso_projection A I n k)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_ofHom, LinearMap.proj_apply] using hk

theorem constantProductXIso_d
    (A : Type u) [CommRing A]
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (x : (∏ᶜ fun _ : ℕ => I).X n) (index : ℕ) :
    ((constantProductXIso A I (n + 1)).hom
      (((∏ᶜ fun _ : ℕ => I).d n (n + 1)).hom x)) index =
    (I.d n (n + 1)).hom (((constantProductXIso A I n).hom x) index) := by
  rw [constantProductXIso_hom_apply, constantProductXIso_hom_apply]
  exact (congrArg (fun φ : (∏ᶜ fun _ : ℕ => I).X n ⟶ I.X (n + 1) => φ.hom x)
    ((Pi.π (fun _ : ℕ => I) index).comm n (n + 1))).symm

theorem constantProductXIso_cast
    (A : Type u) [CommRing A]
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n m : ℤ)
    (h : n = m) (x : (∏ᶜ fun _ : ℕ => I).X n) (index : ℕ) :
    cast (congrArg (fun degree : ℤ => (I.X degree : Type u)) h)
      (((constantProductXIso A I n).hom x) index) =
    ((constantProductXIso A I m).hom
      ((eqToHom (congrArg (∏ᶜ fun _ : ℕ => I).X h)).hom x)) index := by
  cases h
  simp

theorem constantProductXIso_d_at
    (A : Type u) [CommRing A]
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (j k : ℤ)
    (h : j + 1 = k) (x : (∏ᶜ fun _ : ℕ => I).X j) (index : ℕ) :
    ((constantProductXIso A I k).hom
      (((∏ᶜ fun _ : ℕ => I).d j k).hom x)) index =
    (I.d j k).hom (((constantProductXIso A I j).hom x) index) := by
  cases h
  exact constantProductXIso_d A I j x index

private theorem coconeToHom_second_differential
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (x : (CochainComplex.mappingCocone (constantProductDifferenceComplex A f I)).X n)
    (index : ℕ) :
    ((coconeToHomPairComponentIso A f I (n + 1)).hom
      (((CochainComplex.mappingCocone (constantProductDifferenceComplex A f I)).d
        n (n + 1)).hom x)).2 index =
    (I.d n (n + 1)).hom
      (((coconeToHomPairComponentIso A f I n).hom x).2 index) := by
  have hproj := congrArg
    (fun ψ : (CochainComplex.mappingCocone
      (constantProductDifferenceComplex A f I)).X n ⟶
        (∏ᶜ fun _ : ℕ => I).X (n + 1) =>
      ((constantProductXIso A I (n + 1)).hom (ψ.hom x)) index)
    (mappingCoconeXIso_d_fst A f I n)
  rw [coconeToHomPairComponentIso_snd,
    coconeToHomPairComponentIso_snd]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hproj
  rw [hproj]
  exact constantProductXIso_d A I n
    ((biprod.fst :
      ((∏ᶜ fun _ : ℕ => I).X n ⊞ (∏ᶜ fun _ : ℕ => I).X (n - 1)) ⟶
        (∏ᶜ fun _ : ℕ => I).X n).hom
      ((constantDifferenceCoconeXIso A f I n).hom x)) index

theorem constantProductDifferenceComplex_point
    (A : Type u) [CommRing A] (f : A)
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (x : (∏ᶜ fun _ : ℕ => I).X n) (index : ℕ) :
    ((constantProductXIso A I n).hom
      (((constantProductDifferenceComplex A f I).f n).hom x)) index =
    ((constantProductXIso A I n).hom x) index -
      f • ((constantProductXIso A I n).hom x) (index + 1) := by
  have h := congrArg
    (fun φ : (∏ᶜ fun _ : ℕ => I) ⟶ I => (φ.f n).hom x)
    (constantProductDifferenceComplex_π A f I index)
  rw [constantProductXIso_hom_apply, constantProductXIso_hom_apply,
    constantProductXIso_hom_apply]
  change (((constantProductDifferenceComplex A f I).f n ≫
      (Pi.π (fun _ : ℕ => I) index).f n).hom x) =
    (((Pi.π (fun _ : ℕ => I) index).f n -
      f • (Pi.π (fun _ : ℕ => I) (index + 1)).f n).hom x) at h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_sub, ModuleCat.hom_smul,
    LinearMap.sub_apply, LinearMap.smul_apply] using h

end DerivedHomAway

end

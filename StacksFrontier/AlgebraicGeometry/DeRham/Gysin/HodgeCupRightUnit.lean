module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.HodgeCupUnitSection
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinEdgeNaturality
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.CanonicalPairingLaws

/-!
# The class of a global section is a right unit for the cup product, up to multiplication

For a multiplication `μ : F ⊗ G ⟶ H` of sheaves of modules and a global section `u` of `G`, the
cup product of Section 0FKU along `μ`, of a class `x ∈ Hⁱ(RΓ(F[0]))` with the image of the class
of `1 ∈ H⁰(RΓ(𝒪[0]))` under the chain map `𝒪[0] ⟶ G[0]` of `u`, is the image of `x` under right
multiplication by `u` (`canonicalPairingModule_unitComplexSectionMap`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open Stacks.SheafOfModules.Tensor (sheafTensor ringSheaf)
open AlgebraicGeometry.SheafOfModules (multiplicationInt baseRingedSpace)

universe u

namespace Stacks.DeRham.GysinCupHodge

section Coherence

/-- If `b ≫ r.hom = l.hom`, then `l.inv ≫ b = r.inv`. -/
private lemma inv_comp_eq_inv_of_comp_hom {C : Type*} [Category* C] {A B D : C} (l : A ≅ B)
    (b : A ⟶ D) (r : D ≅ B) (h : b ≫ r.hom = l.hom) : l.inv ≫ b = r.inv := by
  rw [Iso.inv_comp_eq, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable {S : RingedSpace.{u, u}}

/-- **The inverse left unitor of complexes followed by the symmetry is the inverse right
unitor**. -/
theorem unitTensorLeftIso_inv_tensorBraiding
    (K : CochainComplex (_root_.SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) :
    letI := Stacks.Cohomology.MonoidalComplexesOfModules.cochainComplexMonoidalCategory S.sheaf
    (Stacks.Cohomology.DerivedGlobalCupProduct.unitTensorLeftIso K).inv ≫
        Stacks.Cohomology.DerivedGlobalCupProduct.tensorBraiding
          (Stacks.Cohomology.DerivedGlobalCupProduct.unitComplexR S) K =
      (ρ_ K).inv := by
  let := Stacks.Cohomology.MonoidalComplexesOfModules.cochainComplexMonoidalCategory S.sheaf
  let := Stacks.Cohomology.MonoidalComplexesOfModules.cochainComplexSymmetricCategory S.sheaf
  have h := braiding_rightUnitor K
  exact inv_comp_eq_inv_of_comp_hom _ _ _ h

end Coherence

/-- In a monoidal category, `ρK ≫ T ≫ M = Rhs`, pasted from the identities `hρ`, `h1`, `h2`, `h3`,
`hū`, `hi₀`, `hm`, `hsU`, `hy`, `hj` and `hR`. -/
private lemma rightUnitor_whisker_chase {C : Type*} [Category* C] [MonoidalCategory C]
    {K0 F₁ F U₀ G₀ G₁ G T₁ T₂ T₃ W₁ W₂ : C}
    (eF : K0 ⟶ F₁) (sF : F₁ ⟶ F) (sU : U₀ ⟶ 𝟙_ C) (sUi : 𝟙_ C ⟶ U₀) (x : 𝟙_ C ⟶ G)
    (y : G ⟶ G₀) (eG : G₀ ⟶ G₁) (sG : G₁ ⟶ G) (ū0 : U₀ ⟶ G₀) (i₀ : K0 ⊗ U₀ ⟶ K0 ⊗ U₀)
    (m : F ⊗ G ⟶ F ⊗ G) (j : F ⟶ F ⊗ G) (zs : F ⊗ G ⟶ W₁) (zE : W₁ ⟶ W₂)
    (ι₁ : K0 ⊗ U₀ ⟶ T₁) (T : T₁ ⟶ T₂) (ι₂ : K0 ⊗ G₀ ⟶ T₂) (M : T₂ ⟶ W₂)
    (ι₃ : F₁ ⊗ G₁ ⟶ T₃) (S : T₃ ⟶ W₁) (ρK : K0 ⟶ T₁) (Rhs : K0 ⟶ W₂)
    (hρ : ρK = (ρ_ K0).inv ≫ K0 ◁ sUi ≫ ι₁)
    (h1 : ι₁ ≫ T = i₀ ≫ (K0 ◁ ū0) ≫ ι₂)
    (h2 : ι₂ ≫ M = (eF ▷ G₀) ≫ (F₁ ◁ eG) ≫ ι₃ ≫ S ≫ zE)
    (h3 : ι₃ ≫ S = (F₁ ◁ sG) ≫ (sF ▷ G) ≫ m ≫ zs)
    (hū : ū0 = sU ≫ x ≫ y) (hi₀ : i₀ = 𝟙 _) (hm : m = 𝟙 _) (hsU : sUi ≫ sU = 𝟙 _)
    (hy : y ≫ eG ≫ sG = 𝟙 G) (hj : (ρ_ F).inv ≫ F ◁ x = j)
    (hR : Rhs = eF ≫ (sF ≫ j ≫ zs) ≫ zE) :
    ρK ≫ T ≫ M = Rhs := by
  subst hρ hR hū hi₀ hm hj
  simp only [Category.assoc]
  rw [reassoc_of% h1, h2, reassoc_of% h3]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, ← Category.assoc sUi, hsU, Category.id_comp,
    MonoidalCategory.whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, Category.assoc, Category.assoc, hy,
    Category.comp_id, MonoidalCategory.whisker_exchange_assoc,
    ← MonoidalCategory.rightUnitor_inv_naturality_assoc,
    ← MonoidalCategory.rightUnitor_inv_naturality_assoc]

section SheafLevel

variable {X : RingedSpace.{u, u}}

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose structureSheafRing
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

/-- **Right multiplication by a global section, as a morphism into the tensor product**: the
inverse right unitor followed by the morphism `𝒪 ⟶ G` of the section, tensored on the left. -/
theorem rightUnitor_inv_whiskerLeft_unitHom
    (F G : _root_.SheafOfModules.{u} (ringSheaf.{u, u, u} X.sheaf)) (u : G.val.sections) :
    letI := _root_.SheafOfModules.monoidalCategorySheafTensor X.sheaf
    (ρ_ F).inv ≫ F ◁ (G.unitHomEquiv.symm u) = rightMulTensor (𝟙 _) u := by
  let := _root_.SheafOfModules.monoidalCategorySheafTensor X.sheaf
  rw [Iso.inv_comp_eq]
  refine PresheafOfModules.tensorSheaf_hom_ext (Osharp := X.sheaf) fun U a r => ?_
  have h₁ := Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit X.sheaf
    (F := F) (G := _root_.SheafOfModules.unit _) (F' := F) (G' := G)
    (𝟙 F) (G.unitHomEquiv.symm u) U a r
  rw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at h₁
  have h₂ := Stacks.RingedSpace.tensorSheafUnitRightIso_hom_tensorSheafUnit_tmul X F U a r
  have h₃ := Stacks.RingedSpace.rightUnitor_sheafTensor_eq X F
  have hu : (G.unitHomEquiv.symm u).val.app U r =
      (show (ringSheaf.{u, u, u} X.sheaf).obj.obj U from r) • (show G.val.obj U from u.val U) := by
    have e := ((G.unitHomEquiv.symm u).val.app U).hom.map_smul
      (show (ringSheaf.{u, u, u} X.sheaf).obj.obj U from r)
      (show ((_root_.SheafOfModules.unit (ringSheaf.{u, u, u} X.sheaf)).val.obj U) from
        (1 : (ringSheaf.{u, u, u} X.sheaf).obj.obj U))
    have e' := _root_.SheafOfModules.unitHomEquiv_apply_coe G (G.unitHomEquiv.symm u) U
    rw [Equiv.apply_symm_apply] at e'
    refine Eq.trans ?_ (e.trans (congrArg _ e'.symm))
    exact congrArg (fun t => ((G.unitHomEquiv.symm u).val.app U).hom t)
      (mul_one (show (ringSheaf.{u, u, u} X.sheaf).obj.obj U from r)).symm
  rw [SheafOfModules.comp_val_app_apply, h₃]
  refine h₁.trans ?_
  refine Eq.trans ?_ (congrArg (fun t => ((rightMulTensor (𝟙 _) u).val.app U).hom t) h₂.symm)
  change (PresheafOfModules.tensorSheafUnit F G).app U (a ⊗ₜ _) =
    (PresheafOfModules.tensorSheafUnit F G).app U (_ ⊗ₜ _)
  rw [hu]
  exact congrArg _ (TensorProduct.smul_tmul
    (show ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj U) from r) a
    (show G.val.obj U from u.val U)).symm

/-- Left whiskering of the monoidal structure on sheaves of modules is the tensor product functor
applied to a morphism. -/
lemma sheafTensor_obj_map_eq_whiskerLeft
    (A : _root_.SheafOfModules.{u} (ringSheaf.{u, u, u} X.sheaf))
    {B B' : _root_.SheafOfModules.{u} (ringSheaf.{u, u, u} X.sheaf)} (f : B ⟶ B') :
    letI := _root_.SheafOfModules.monoidalCategorySheafTensor X.sheaf
    ((sheafTensor.{u, u, u, u, u} X.sheaf).obj A).map f = A ◁ f :=
  rfl

/-- Right whiskering of the monoidal structure on sheaves of modules is the tensor product functor
applied to a morphism. -/
lemma sheafTensor_map_app_eq_whiskerRight
    {A A' : _root_.SheafOfModules.{u} (ringSheaf.{u, u, u} X.sheaf)} (f : A ⟶ A')
    (B : _root_.SheafOfModules.{u} (ringSheaf.{u, u, u} X.sheaf)) :
    letI := _root_.SheafOfModules.monoidalCategorySheafTensor X.sheaf
    ((sheafTensor.{u, u, u, u, u} X.sheaf).map f).app B = f ▷ B :=
  rfl

/-- `rightUnitor_whisker_chase` with the whiskerings spelled through the tensor product functor
of sheaves of modules. -/
private lemma rightUnitor_whisker_chase_sheafTensor
    {K0 F₁ F U₀ G₀ G₁ G W₁ W₂ : _root_.SheafOfModules.{u} (ringSheaf.{u, u, u} X.sheaf)}
    {T₁ T₂ T₃ : _root_.SheafOfModules.{u} (ringSheaf.{u, u, u} X.sheaf)}
    (eF : K0 ⟶ F₁) (sF : F₁ ⟶ F)
    (sU : U₀ ⟶ _root_.SheafOfModules.unit (ringSheaf.{u, u, u} X.sheaf))
    (sUi : _root_.SheafOfModules.unit (ringSheaf.{u, u, u} X.sheaf) ⟶ U₀)
    (x : _root_.SheafOfModules.unit (ringSheaf.{u, u, u} X.sheaf) ⟶ G)
    (y : G ⟶ G₀) (eG : G₀ ⟶ G₁) (sG : G₁ ⟶ G) (ū0 : U₀ ⟶ G₀)
    (i₀ : ((sheafTensor.{u, u, u, u, u} X.sheaf).obj K0).obj U₀ ⟶
      ((sheafTensor.{u, u, u, u, u} X.sheaf).obj K0).obj U₀)
    (m : ((sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj G ⟶
      ((sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj G)
    (j : F ⟶ ((sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj G)
    (zs : ((sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj G ⟶ W₁) (zE : W₁ ⟶ W₂)
    (ι₁ : ((sheafTensor.{u, u, u, u, u} X.sheaf).obj K0).obj U₀ ⟶ T₁) (T : T₁ ⟶ T₂)
    (ι₂ : ((sheafTensor.{u, u, u, u, u} X.sheaf).obj K0).obj G₀ ⟶ T₂) (M : T₂ ⟶ W₂)
    (ι₃ : ((sheafTensor.{u, u, u, u, u} X.sheaf).obj F₁).obj G₁ ⟶ T₃) (S : T₃ ⟶ W₁)
    (ρK : K0 ⟶ T₁) (Rhs : K0 ⟶ W₂)
    (hρ : letI := _root_.SheafOfModules.monoidalCategorySheafTensor X.sheaf
      ρK = (ρ_ K0).inv ≫ K0 ◁ sUi ≫ ι₁)
    (h1 : ι₁ ≫ T = i₀ ≫ ((sheafTensor.{u, u, u, u, u} X.sheaf).obj K0).map ū0 ≫ ι₂)
    (h2 : ι₂ ≫ M = ((sheafTensor.{u, u, u, u, u} X.sheaf).map eF).app G₀ ≫
      ((sheafTensor.{u, u, u, u, u} X.sheaf).obj F₁).map eG ≫ ι₃ ≫ S ≫ zE)
    (h3 : ι₃ ≫ S = ((sheafTensor.{u, u, u, u, u} X.sheaf).obj F₁).map sG ≫
      ((sheafTensor.{u, u, u, u, u} X.sheaf).map sF).app G ≫ m ≫ zs)
    (hū : ū0 = sU ≫ x ≫ y) (hi₀ : i₀ = 𝟙 _) (hm : m = 𝟙 _) (hsU : sUi ≫ sU = 𝟙 _)
    (hy : y ≫ eG ≫ sG = 𝟙 G)
    (hj : letI := _root_.SheafOfModules.monoidalCategorySheafTensor X.sheaf
      (ρ_ F).inv ≫ F ◁ x = j)
    (hR : Rhs = eF ≫ (sF ≫ j ≫ zs) ≫ zE) :
    ρK ≫ T ≫ M = Rhs := by
  let := _root_.SheafOfModules.monoidalCategorySheafTensor X.sheaf
  rw [sheafTensor_obj_map_eq_whiskerLeft] at h1
  rw [sheafTensor_map_app_eq_whiskerRight, sheafTensor_obj_map_eq_whiskerLeft] at h2
  rw [sheafTensor_map_app_eq_whiskerRight, sheafTensor_obj_map_eq_whiskerLeft] at h3
  exact rightUnitor_whisker_chase eF sF sU sUi x y eG sG ū0 i₀ m j zs zE ι₁ T ι₂ M ι₃ S ρK Rhs
    hρ h1 h2 h3 hū hi₀ hm hsU hy hj hR

attribute [local instance] _root_.SheafOfModules.monoidalCategorySheafTensor
  _root_.SheafOfModules.symmetricCategorySheafTensor
  _root_.SheafOfModules.monoidalPreadditiveSheafTensor
  _root_.SheafOfModules.monoidalClosedSheafTensor in
/-- **Right multiplication by a global section through the unit complex, on complexes**: the
right unitor of complexes inverted, the section in the second factor, and the multiplication of
`F[0]` and `G[0]` along the identity of `F ⊗ G`, is the extension of right multiplication. -/
theorem rightUnitor_inv_unitComplexSectionMap_multiplicationInt
    (F G : _root_.SheafOfModules.{u} (ringSheaf.{u, u, u} X.sheaf)) (u : G.val.sections) :
    letI := Stacks.Cohomology.MonoidalComplexesOfModules.cochainComplexMonoidalCategory X.sheaf
    (ρ_ ((singleNat F 0).extend ComplexShape.embeddingUpNat)).inv ≫
        HomologicalComplex.mapBifunctorMap (𝟙 ((singleNat F 0).extend ComplexShape.embeddingUpNat))
          (unitComplexSectionMap G u) (sheafTensor.{u, u, u, u, u} X.sheaf) (ComplexShape.up ℤ) ≫
        multiplicationInt
          (singleTensorMult (𝟙 (((sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj G)) 0 0 0 rfl) =
      HomologicalComplex.extendMap ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map
        (rightMulTensor (𝟙 _) u)) ComplexShape.embeddingUpNat := by
  let := Stacks.Cohomology.MonoidalComplexesOfModules.cochainComplexMonoidalCategory X.sheaf
  ext d : 1
  by_cases hd : d = ((0 : ℕ) : ℤ)
  swap
  · exact (isZero_singleNat_extend_X F 0 d hd).eq_of_src _ _
  subst hd
  simp only [HomologicalComplex.comp_f]
  have hρ := HomologicalComplex.rightUnitor'_inv
    ((singleNat F 0).extend ComplexShape.embeddingUpNat) ((0 : ℕ) : ℤ)
  have h1 := HomologicalComplex.ι_mapBifunctorMap
    (𝟙 ((singleNat F 0).extend ComplexShape.embeddingUpNat)) (unitComplexSectionMap G u)
    (sheafTensor.{u, u, u, u, u} X.sheaf) (ComplexShape.up ℤ) ((0 : ℕ) : ℤ) 0 ((0 : ℕ) : ℤ)
    (by simp)
  have h2 := AlgebraicGeometry.SheafOfModules.ι_multiplicationInt_f
    (singleTensorMult (𝟙 (((sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj G)) 0 0 0 rfl) 0 0 0
    (by simp)
  have h3 := ι_singleTensorMult_f (𝟙 (((sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj G)) 0 0 0
    rfl (by simp)
  have hū : (unitComplexSectionMap G u).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).hom ≫ G.unitHomEquiv.symm u ≫
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).inv ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).hom ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 G).inv ≫
          ((singleNat G 0).extendXIso ComplexShape.embeddingUpNat (rfl : _ = (0 : ℤ))).inv) := by
    simp only [unitComplexSectionMap, HomologicalComplex.comp_f,
      HomologicalComplex.single_map_f_self, Category.assoc]
    exact congrArg (fun t => _ ≫ _ ≫ _ ≫ t)
      (HomologicalComplex.extendSingleIso_inv_f ComplexShape.embeddingUpNat G 0 0 rfl)
  have hR := HomologicalComplex.extendMap_f ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map
    (rightMulTensor (𝟙 (((sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj G)) u))
    ComplexShape.embeddingUpNat (i := 0) (i' := ((0 : ℕ) : ℤ)) rfl
  rw [HomologicalComplex.single_map_f_self] at hR
  refine rightUnitor_whisker_chase_sheafTensor _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hρ h1 h2
    h3 hū ?_ rfl (Iso.inv_hom_id _) ?_ (rightUnitor_inv_whiskerLeft_unitHom F G u) hR
  · rw [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app]
    rfl
  · simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
    exact Iso.inv_hom_id _

end SheafLevel

section Complexes

variable {X : RingedSpace.{u, u}}

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose structureSheafRing
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

/-- If `l ≫ b = r`, then `l ≫ b ≫ t ≫ m ≫ e = (r ≫ t ≫ m) ≫ e`. -/
private lemma unitor_braiding_chase {C : Type*} [Category* C] {P Q R S T W : C} (l : P ⟶ Q)
    (b : Q ⟶ R) (r : P ⟶ R) (t : R ⟶ S) (m : S ⟶ T) (e : T ⟶ W) (h : l ≫ b = r) :
    l ≫ b ≫ t ≫ m ≫ e = (r ≫ t ≫ m) ≫ e := by
  rw [← h]; simp only [Category.assoc]

/-- Right multiplication along a multiplication is right multiplication into the tensor product
followed by the multiplication. -/
lemma rightMulTensor_id_comp
    {F G H : _root_.SheafOfModules.{u} (ringSheaf.{u, u, u} X.sheaf)}
    (μ : ((sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj G ⟶ H) (u : G.val.sections) :
    rightMulTensor (𝟙 _) u ≫ μ = rightMulTensor μ u := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro V
  ext a
  rfl

/-- **The multiplication of `F[0]` and `G[0]` against the class of a global section, on
complexes**: the left unitor of complexes inverted, the symmetry, the section in the second factor
and the multiplication along `μ` is the extension of right multiplication by the section. -/
theorem unitTensorLeftIso_inv_tensorBraiding_multiplicationInt
    {F G H : _root_.SheafOfModules.{u} (ringSheaf.{u, u, u} X.sheaf)}
    (μ : ((sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj G ⟶ H) (u : G.val.sections) :
    (Stacks.Cohomology.DerivedGlobalCupProduct.unitTensorLeftIso (S := baseRingedSpace X.sheaf)
        ((singleNat F 0).extend ComplexShape.embeddingUpNat)).inv ≫
        Stacks.Cohomology.DerivedGlobalCupProduct.tensorBraiding (S := baseRingedSpace X.sheaf)
          (Stacks.Cohomology.DerivedGlobalCupProduct.unitComplexR (baseRingedSpace X.sheaf))
          ((singleNat F 0).extend ComplexShape.embeddingUpNat) ≫
        HomologicalComplex.mapBifunctorMap (𝟙 ((singleNat F 0).extend ComplexShape.embeddingUpNat))
          (unitComplexSectionMap G u) (sheafTensor.{u, u, u, u, u} X.sheaf) (ComplexShape.up ℤ) ≫
        multiplicationInt (singleTensorMult μ 0 0 0 rfl) =
      HomologicalComplex.extendMap ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map
        (rightMulTensor μ u)) ComplexShape.embeddingUpNat := by
  have hc := unitTensorLeftIso_inv_tensorBraiding (S := baseRingedSpace X.sheaf)
    ((singleNat F 0).extend ComplexShape.embeddingUpNat)
  have hr := rightUnitor_inv_unitComplexSectionMap_multiplicationInt F G u
  have hμ : multiplicationInt (singleTensorMult μ 0 0 0 rfl) =
      multiplicationInt (singleTensorMult (𝟙 (((sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj G))
        0 0 0 rfl) ≫ HomologicalComplex.extendMap
          ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map μ)
            ComplexShape.embeddingUpNat := by
    rw [← Category.id_comp μ, singleTensorMult_comp]
    simp only [Category.id_comp]
    unfold multiplicationInt
    rw [HomologicalComplex.extendMap_comp]
    exact (Category.assoc _ _ _).symm
  rw [← rightMulTensor_id_comp μ u, CategoryTheory.Functor.map_comp,
    HomologicalComplex.extendMap_comp, ← hr, hμ]
  exact unitor_braiding_chase _ _ _ _ _ _ hc

end Complexes

section Cohomology

open Stacks.Cohomology.GlobalKunneth (baseRing)
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule cohomologyMap cohomologyCast
  globalCycleClass unitCycleHom cupClass)
open AlgebraicGeometry.SheafOfModules (moduleDerived canonicalPairingModule)

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose structureSheafRing
  AlgebraicGeometry.SheafedSpace.sheaf AlgebraicGeometry.SheafOfModules.baseRingedSpace
  Stacks.SheafOfModules.Tensor.ringSheaf

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat
attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules
  AlgebraicGeometry.SheafOfModules.hasSheafifyOpens
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijectiveOpens

variable {X : RingedSpace.{u, u}}

/-- A composite out of the free module of rank one, through the left unitor and a tensor product
of morphisms, evaluated at `1`. -/
private lemma moduleCat_leftUnitor_inv_tensorHom_comp_apply_one {R : CommRingCat.{u}}
    {P Q T : ModuleCat.{u} R} (f : ModuleCat.of R R ⟶ P) (g : ModuleCat.of R R ⟶ Q)
    (h : P ⊗ Q ⟶ T) :
    ((λ_ (ModuleCat.of R R)).inv ≫ (f ⊗ₘ g) ≫ h).hom (1 : R) =
      h.hom (f.hom (1 : R) ⊗ₜ g.hom 1) := by
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.leftUnitor_inv_apply, ModuleCat.MonoidalCategory.tensorHom_tmul]

/-- Two degree casts compose. -/
private lemma cohomologyCast_cohomologyCast_apply {S : RingedSpace.{u, u}}
    (K : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing S))) {a b c : ℤ}
    (h₁ : a = b) (h₂ : b = c) (x : cohomologyModule K a) :
    (cohomologyCast K h₂).hom ((cohomologyCast K h₁).hom x) =
      (cohomologyCast K (h₁.trans h₂)).hom x := by
  subst h₁ h₂
  rfl

/-- `lhs = cast₄ (R x)`, from the chain of equalities of function values `hA`, `hB`, `hC`, `hF`,
`hE`, `hG`, `hH`, `hM` and `hI`. -/
private lemma ru_assembly {A₁ A₂ A₃ A₄ A₅ A₆ A₇ A₈ B : Type*} (lhs : B) (Mi : A₁ → B)
    (T : A₂ → A₁) (Bt : A₃ → A₂) (c₂ : A₄ → A₃) (Li : A₅ → A₄) (Li' : A₆ → A₃)
    (c₂' : A₅ → A₆) (c₁ : A₇ → A₅) (c₃ : A₇ → A₆) (R' : A₆ → B) (cast₄ : A₈ → B)
    (R : A₇ → A₈) (x : A₇) (y₁ : A₁) (y₂ : A₂) (y₃ : A₃) (y₄ : A₄)
    (hA : lhs = Mi y₁) (hB : T y₂ = y₁) (hC : Bt y₃ = y₂) (hF : c₂ y₄ = y₃)
    (hE : y₄ = Li (c₁ x)) (hG : c₂ (Li (c₁ x)) = Li' (c₂' (c₁ x))) (hH : c₂' (c₁ x) = c₃ x)
    (hM : ∀ y, Mi (T (Bt (Li' y))) = R' y) (hI : R' (c₃ x) = cast₄ (R x)) :
    lhs = cast₄ (R x) := by
  rw [hA, ← hB, ← hC, ← hF, hE, hG, hH, hM, hI]

/-- An isomorphism of complexes and its inverse, on cohomology, elementwise. -/
private lemma cohomologyMap_inv_hom_apply {S : RingedSpace.{u, u}}
    {K K' : CochainComplex (_root_.SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ}
    (e : K ≅ K') (n : ℤ) (y : cohomologyModule (DerivedCategory.Q.obj K) n) :
    (cohomologyMap e.inv n).hom ((cohomologyMap e.hom n).hom y) = y := by
  rw [Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyMap_comp_apply, e.hom_inv_id,
    Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyMap_id_apply]

/-- **The class of `1` is a left unit for the cup product, on elements**: the cup product
`1 ∪ x` is the image of `x` under the inverse of the left unitor. -/
theorem unitCycleHom_left_apply {S : RingedSpace.{u, u}}
    (K : CochainComplex (_root_.SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ) (i : ℤ)
    (x : cohomologyModule (DerivedCategory.Q.obj K) i) :
    cupClass (Stacks.Cohomology.DerivedGlobalCupProduct.unitComplexR S) K rfl
        ((globalCycleClass (unitCycleHom S)).hom 1) x =
      (cohomologyMap (Stacks.Cohomology.DerivedGlobalCupProduct.unitTensorLeftIso K).inv
        (0 + i)).hom ((cohomologyCast (DerivedCategory.Q.obj K) (zero_add i).symm).hom x) := by
  have hD := ConcreteCategory.congr_hom
    (Stacks.Cohomology.DerivedGlobalCupProduct.totalCupPairing_unit_left K i
      (ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ x))) 1
  have hD' : (cohomologyMap (Stacks.Cohomology.DerivedGlobalCupProduct.unitTensorLeftIso K).hom
        (0 + i)).hom (cupClass (Stacks.Cohomology.DerivedGlobalCupProduct.unitComplexR S) K rfl
          ((globalCycleClass (unitCycleHom S)).hom 1) x) =
      (cohomologyCast (DerivedCategory.Q.obj K) (zero_add i).symm).hom x := by
    refine Eq.trans ?_ ((moduleCat_leftUnitor_inv_tensorHom_comp_apply_one _ _ _).symm.trans
      (hD.trans ?_))
    · simp only [ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul,
        ModuleCat.comp_apply]
      rfl
    · change (cohomologyCast (DerivedCategory.Q.obj K) (zero_add i).symm).hom
          ((ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ x)).hom 1) = _
      rw [ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul]
  exact (cohomologyMap_inv_hom_apply _ (0 + i) _).symm.trans (congrArg _ hD')

section UnitRight

variable {S : RingedSpace.{u, u}}

/-- **The class of `1` is a right unit for the cup product**, read through the left unitor and
the symmetry of complexes: for a bounded below complex `K` and `x ∈ Hⁱ(S, K)`, the cup product
`x ∪ 1 ∈ Hⁱ⁺⁰(S, Tot(K ⊗ 𝒪_S[0]))` is the image of `x` under the inverse of the left unitor
followed by the symmetry. -/
theorem cupClass_unitCycleHom_right
    (K : CochainComplex (_root_.SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ)
    (hK : ∃ n : ℤ, CochainComplex.IsStrictlyGE K n) (i : ℤ)
    (x : cohomologyModule (DerivedCategory.Q.obj K) i) :
    cupClass K (Stacks.Cohomology.DerivedGlobalCupProduct.unitComplexR S) rfl x
        ((globalCycleClass (unitCycleHom S)).hom 1) =
      (cohomologyMap ((Stacks.Cohomology.DerivedGlobalCupProduct.unitTensorLeftIso K).inv ≫
          Stacks.Cohomology.DerivedGlobalCupProduct.tensorBraiding
            (Stacks.Cohomology.DerivedGlobalCupProduct.unitComplexR S) K) (i + 0)).hom
        ((cohomologyCast (DerivedCategory.Q.obj K) (add_zero i).symm).hom x) := by
  have hU : ∃ n : ℤ, CochainComplex.IsStrictlyGE
      (Stacks.Cohomology.DerivedGlobalCupProduct.unitComplexR S) n := ⟨0, inferInstance⟩
  have hC := Stacks.Cohomology.DerivedGlobalCupProduct.cupClass_comm
    (Stacks.Cohomology.DerivedGlobalCupProduct.unitComplexR S) K hU hK
    (show 0 + i = i + 0 by omega) rfl ((globalCycleClass (unitCycleHom S)).hom 1) x
  have hsign : (((0 : ℤ) * i).negOnePow : ℤ) = 1 := by simp
  rw [hsign, one_smul] at hC
  have hA := (Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyCast_cupClass
    (Stacks.Cohomology.DerivedGlobalCupProduct.unitComplexR S) K (rfl : 0 + i = 0 + i)
    (show 0 + i = i + 0 by omega) ((globalCycleClass (unitCycleHom S)).hom 1) x).symm
  have hB := congrArg (cohomologyCast _ (show 0 + i = i + 0 by omega)).hom
    (unitCycleHom_left_apply K i x)
  have hG := Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyCast_cohomologyMap_apply
    (Stacks.Cohomology.DerivedGlobalCupProduct.unitTensorLeftIso K).inv
    (show 0 + i = i + 0 by omega)
    ((cohomologyCast (DerivedCategory.Q.obj K) (zero_add i).symm).hom x)
  have hH := congrArg (cohomologyMap
    (Stacks.Cohomology.DerivedGlobalCupProduct.unitTensorLeftIso K).inv (i + 0)).hom
    (cohomologyCast_cohomologyCast_apply (DerivedCategory.Q.obj K) (zero_add i).symm
      (show 0 + i = i + 0 by omega) x)
  exact hC.symm.trans ((congrArg (cohomologyMap
    (Stacks.Cohomology.DerivedGlobalCupProduct.tensorBraiding
      (Stacks.Cohomology.DerivedGlobalCupProduct.unitComplexR S) K) (i + 0)).hom
        (hA.trans (hB.trans (hG.trans hH)))).trans
    (Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyMap_comp_apply _ _ _ _))

end UnitRight

/-- **The cup product with the class of a global section is right multiplication by it.** -/
theorem canonicalPairingModule_unitComplexSectionMap
    {F G H : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)}
    (μ : ((sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj G ⟶ H) (u : G.val.sections) (i : ℤ)
    (x : cohomologyModule (moduleDerived (A := X.sheaf) (singleNat F 0)) i) :
    (canonicalPairingModule (singleTensorMult μ 0 0 0 rfl) i 0).hom
        (x ⊗ₜ (cohomologyMap (S := baseRingedSpace X.sheaf) (unitComplexSectionMap G u) 0).hom
          ((globalCycleClass (S := baseRingedSpace X.sheaf)
            (unitCycleHom (baseRingedSpace X.sheaf))).hom 1)) =
      (cohomologyCast (moduleDerived (A := X.sheaf) (singleNat H 0)) (add_zero i).symm).hom
        ((cohomologyMap (S := baseRingedSpace X.sheaf) (HomologicalComplex.extendMap
          ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map (rightMulTensor μ u))
          ComplexShape.embeddingUpNat) i).hom x) := by
  have hA := AlgebraicGeometry.SheafOfModules.canonicalPairingModule_apply (A := X.sheaf)
    (singleTensorMult μ 0 0 0 rfl) i 0 x
    ((cohomologyMap (S := baseRingedSpace X.sheaf) (unitComplexSectionMap G u) 0).hom
      ((globalCycleClass (S := baseRingedSpace X.sheaf)
        (unitCycleHom (baseRingedSpace X.sheaf))).hom 1))
  have hB := Stacks.Cohomology.DerivedGlobalCupProduct.cupClass_naturality
    (S := baseRingedSpace X.sheaf) (𝟙 ((singleNat F 0).extend ComplexShape.embeddingUpNat))
    (unitComplexSectionMap G u) (rfl : i + 0 = i + 0) x
    ((globalCycleClass (S := baseRingedSpace X.sheaf)
      (unitCycleHom (baseRingedSpace X.sheaf))).hom 1)
  have hB' := hB.trans (congrArg (fun z => cupClass (S := baseRingedSpace X.sheaf)
      ((singleNat F 0).extend ComplexShape.embeddingUpNat)
      ((singleNat G 0).extend ComplexShape.embeddingUpNat) rfl z
        ((cohomologyMap (S := baseRingedSpace X.sheaf) (unitComplexSectionMap G u) 0).hom
          ((globalCycleClass (S := baseRingedSpace X.sheaf)
            (unitCycleHom (baseRingedSpace X.sheaf))).hom 1)))
      (Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyMap_id_apply
        ((singleNat F 0).extend ComplexShape.embeddingUpNat) i x))
  have hR := cupClass_unitCycleHom_right (S := baseRingedSpace X.sheaf)
    ((singleNat F 0).extend ComplexShape.embeddingUpNat) ⟨0, inferInstance⟩ i x
  have hCL := (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans
    (unitTensorLeftIso_inv_tensorBraiding_multiplicationInt μ u))
  have hI := Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyCast_cohomologyMap_apply
    (S := baseRingedSpace X.sheaf) (HomologicalComplex.extendMap
      ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map (rightMulTensor μ u))
      ComplexShape.embeddingUpNat) (add_zero i).symm x
  refine hA.trans (Eq.trans ?_ hI.symm)
  refine (congrArg (cohomologyMap (S := baseRingedSpace X.sheaf)
    (multiplicationInt (singleTensorMult μ 0 0 0 rfl)) (i + 0)).hom
      (hB'.symm.trans (congrArg (cohomologyMap (S := baseRingedSpace X.sheaf)
        (HomologicalComplex.mapBifunctorMap (𝟙 ((singleNat F 0).extend ComplexShape.embeddingUpNat))
          (unitComplexSectionMap G u) (sheafTensor.{u, u, u, u, u} X.sheaf) (ComplexShape.up ℤ))
        (i + 0)).hom hR))).trans ?_
  refine ((congrArg (cohomologyMap (S := baseRingedSpace X.sheaf)
    (multiplicationInt (singleTensorMult μ 0 0 0 rfl)) (i + 0)).hom
      (Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyMap_comp_apply _ _ _ _)).trans
    (Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyMap_comp_apply _ _ _ _)).trans ?_
  exact congrArg (fun f => (cohomologyMap (S := baseRingedSpace X.sheaf) f (i + 0)).hom
    ((cohomologyCast _ (add_zero i).symm).hom x)) hCL
end Cohomology

end Stacks.DeRham.GysinCupHodge


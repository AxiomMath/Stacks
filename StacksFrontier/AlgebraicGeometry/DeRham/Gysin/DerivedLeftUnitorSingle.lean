module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.SupportedTensorPushNaturality
public import StacksFrontier.Homology.TensorComplex.BifunctorSingleLeftComplex
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafWorldBridge
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.HodgeCupProduct

/-!
# The left unit constraint of `⊗^L` on the structure sheaf placed in degree zero

For a ringed space `X`, the structure sheaf `𝒪_X`, placed in degree `0` of an `ℕ`-indexed
complex and extended by zero, is a left unit of the derived tensor product: the canonical map
`𝒪_X[0] ⊗^L K ⟶ Tot(𝒪_X[0] ⊗ K)` followed by the left unitor of the total tensor complex is a
natural transformation on `D(𝒪_X)`, `derivedLeftUnitor`. On a sheaf placed in a single degree
`n` its chain-level part is the multiplication `singleTensorMult` along the left unitor of the
tensor product of sheaves, `multiplicationInt_leftUnitor`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.SheafOfModules.Tensor (sheafTensor)
open AlgebraicGeometry.SheafOfModules (moduleDerived multiplicationInt)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose structureSheafRing
  AlgebraicGeometry.SheafedSpace.sheaf AlgebraicGeometry.SheafOfModules.baseRingedSpace
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.DeRham.GysinCupHodge

section StandardModel

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat
attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules
  AlgebraicGeometry.SheafOfModules.hasSheafifyOpens
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijectiveOpens

variable {X : RingedSpace.{u, u}}

/-- The structure sheaf of `X`, as a sheaf of modules over the ring sheaf of the tensor
product. -/
abbrev unitModule (X : RingedSpace.{u, u}) :
    _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf) :=
  _root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)

/-- **The left unitor of the tensor product of sheaves of modules**, `𝒪_X ⊗ N ≅ N`: the left
unitor of the monoidal structure of Tag 01CA, whose tensor product is `sheafTensor`. -/
def sheafLeftUnitor
    (N : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)) :
    ((sheafTensor.{u, u, u, u, u} X.sheaf).obj (unitModule X)).obj N ≅ N :=
  @MonoidalCategoryStruct.leftUnitor _ _
    (Stacks.TensorSheafWorld.monoidalCategory X.sheaf).toMonoidalCategoryStruct N

/-- **The left unitor on a local pure tensor**: `r ⊗ x ↦ r • x`. -/
theorem sheafLeftUnitor_hom_apply
    (N : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf))
    (U : (TopologicalSpace.Opens X.carrier)ᵒᵖ) (r : (unitModule X).val.obj U) (x : N.val.obj U) :
    (sheafLeftUnitor N).hom.val.app U
        ((PresheafOfModules.tensorSheafUnit (unitModule X) N).app U (r ⊗ₜ x)) =
      (show (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf).obj.obj U from r) • x :=
  Stacks.TensorSheafWorld.leftUnitor_hom_val_app_tensorSheafUnit X.sheaf
    (structureSheafRing X).property N U r x

/-- The left unitor of the tensor product of sheaves is natural. -/
theorem sheafLeftUnitor_naturality
    {N N' : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)}
    (f : N ⟶ N') :
    ((sheafTensor.{u, u, u, u, u} X.sheaf).obj (unitModule X)).map f ≫ (sheafLeftUnitor N').hom =
      (sheafLeftUnitor N).hom ≫ f := by
  refine PresheafOfModules.tensorSheaf_hom_ext (Osharp := X.sheaf) (F := unitModule X) (G := N)
    (Q := N') fun U r x => ?_
  have h₁ := Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit X.sheaf
    (F := unitModule X) (G := N) (F' := unitModule X) (G' := N') (𝟙 (unitModule X)) f U r x
  rw [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at h₁
  rw [SheafOfModules.comp_val_app_apply, SheafOfModules.comp_val_app_apply, h₁,
    sheafLeftUnitor_hom_apply, sheafLeftUnitor_hom_apply]
  exact (map_smul (f.val.app U).hom _ x).symm

/-- The left unitor of the tensor product of sheaves, as a natural isomorphism. -/
def sheafLeftUnitorNatIso (X : RingedSpace.{u, u}) :
    (sheafTensor.{u, u, u, u, u} X.sheaf).obj (unitModule X) ≅ 𝟭 _ :=
  NatIso.ofComponents sheafLeftUnitor fun f => sheafLeftUnitor_naturality f

/-- `𝒪_X` placed in degree `0` of an `ℕ`-indexed complex, extended by zero, is `𝒪_X` placed in
degree `0` of a `ℤ`-indexed complex. -/
def unitExtendIso (X : RingedSpace.{u, u}) :
    (singleNat (X := X) (unitModule X) 0).extend ComplexShape.embeddingUpNat ≅
      (CochainComplex.singleFunctor _ 0).obj (unitModule X) :=
  HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat (unitModule X) 0 0 rfl

/-- **The left unitor of the total tensor complex** with `𝒪_X[0]` (extended by zero) on the left:
`Tot(𝒪_X[0] ⊗ K) ⟶ K`. -/
def complexLeftUnitor
    (K : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)) ℤ) :
    HomologicalComplex.mapBifunctor
        ((singleNat (X := X) (unitModule X) 0).extend ComplexShape.embeddingUpNat) K
        (sheafTensor.{u, u, u, u, u} X.sheaf) (ComplexShape.up ℤ) ⟶ K :=
  HomologicalComplex.mapBifunctorMap (unitExtendIso X).hom (𝟙 K)
      (sheafTensor.{u, u, u, u, u} X.sheaf) (ComplexShape.up ℤ) ≫
    (HomologicalComplex.mapBifunctorSingleLeftIso (sheafTensor.{u, u, u, u, u} X.sheaf)
      (unitModule X) K).hom ≫
    (NatIso.mapHomologicalComplex (sheafLeftUnitorNatIso X) (ComplexShape.up ℤ)).hom.app K ≫
    (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).hom.app K

/-- The left unitor of the total tensor complex is an isomorphism. -/
instance isIso_complexLeftUnitor
    (K : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)) ℤ) :
    IsIso (complexLeftUnitor K) := by
  have : IsIso (HomologicalComplex.mapBifunctorMap (unitExtendIso X).hom (𝟙 K)
      (sheafTensor.{u, u, u, u, u} X.sheaf) (ComplexShape.up ℤ)) :=
    ⟨HomologicalComplex.mapBifunctorMap (unitExtendIso X).inv (𝟙 K)
      (sheafTensor.{u, u, u, u, u} X.sheaf) (ComplexShape.up ℤ), by
        rw [HomologicalComplex.mapBifunctorMap_comp, Iso.hom_inv_id, Category.id_comp,
          HomologicalComplex.mapBifunctorMap_id], by
        rw [HomologicalComplex.mapBifunctorMap_comp, Iso.inv_hom_id, Category.id_comp,
          HomologicalComplex.mapBifunctorMap_id]⟩
  unfold complexLeftUnitor
  infer_instance

/-- The left unitor of the total tensor complex on the summand of bidegree `(0, i)`. -/
theorem ι_complexLeftUnitor_f
    (K : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)) ℤ) (i : ℤ) :
    HomologicalComplex.ιMapBifunctor
        ((singleNat (X := X) (unitModule X) 0).extend ComplexShape.embeddingUpNat) K
        (sheafTensor.{u, u, u, u, u} X.sheaf) (ComplexShape.up ℤ) 0 i i (zero_add i) ≫
        (complexLeftUnitor K).f i =
      ((sheafTensor.{u, u, u, u, u} X.sheaf).map
          ((unitExtendIso X).hom.f 0 ≫
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (unitModule X)).hom)).app
          (K.X i) ≫
        (sheafLeftUnitor (K.X i)).hom := by
  have h₁ := HomologicalComplex.ι_mapBifunctorMap (unitExtendIso X).hom (𝟙 K)
    (sheafTensor.{u, u, u, u, u} X.sheaf) (ComplexShape.up ℤ) 0 i i (zero_add i)
  have h₂ : HomologicalComplex.ιMapBifunctor
        ((CochainComplex.singleFunctor _ 0).obj (unitModule X)) K
        (sheafTensor.{u, u, u, u, u} X.sheaf) (ComplexShape.up ℤ) 0 i i (zero_add i) ≫
        (HomologicalComplex.mapBifunctorSingleLeftIso (sheafTensor.{u, u, u, u, u} X.sheaf)
          (unitModule X) K).hom.f i =
      ((sheafTensor.{u, u, u, u, u} X.sheaf).map
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (unitModule X)).hom).app
        (K.X i) := by
    change HomologicalComplex.singleLeftι _ _ _ i ≫
      (HomologicalComplex.singleLeftπ _ _ _ i ≫ _) = _
    rw [← Category.assoc, HomologicalComplex.singleLeftι_π, Category.id_comp]
    rfl
  simp only [complexLeftUnitor, HomologicalComplex.comp_f]
  rw [reassoc_of% h₁, HomologicalComplex.id_f, CategoryTheory.Functor.map_id, Category.id_comp,
    reassoc_of% h₂]
  simp [sheafLeftUnitorNatIso, Functor.mapHomologicalComplexIdIso]

end StandardModel

end Stacks.DeRham.GysinCupHodge

namespace Stacks.DeRham.GysinCupHodge

/-- The algebra of `complexLeftUnitor_naturality`, at variables. -/
private lemma naturality_chase {C : Type*} [Category* C] {S S' T T' Q Q' K K' : C}
    (ι : S ⟶ T) (ι' : S' ⟶ T') (M : T ⟶ T') (Cl : T ⟶ K) (Cl' : T' ⟶ K') (b : S ⟶ S')
    (E : S ⟶ Q) (E' : S' ⟶ Q') (b'' : Q ⟶ Q') (l : Q ⟶ K) (l' : Q' ⟶ K') (φ : K ⟶ K')
    (e₁ : ι ≫ M = b ≫ ι') (e₂ : ι' ≫ Cl' = E' ≫ l') (e₃ : ι ≫ Cl = E ≫ l)
    (e₄ : b ≫ E' = E ≫ b'') (e₅ : b'' ≫ l' = l ≫ φ) :
    ι ≫ M ≫ Cl' = ι ≫ Cl ≫ φ := by
  rw [reassoc_of% e₁, e₂, reassoc_of% e₄, e₅, reassoc_of% e₃]

/-- The algebra of the naturality of `derivedLeftUnitorComparison`, at variables. -/
private lemma unitor_chase {C D : Type*} [Category* C] [Category* D] (Qf : C ⥤ D)
    {P P' : D} {S S' K K' : C} (A : P ⟶ P') (t' : P' ⟶ Qf.obj S') (t : P ⟶ Qf.obj S)
    (m : S ⟶ S') (ℓ' : S' ⟶ K') (ℓ : S ⟶ K) (φ : K ⟶ K') (h : A ≫ t' = t ≫ Qf.map m)
    (hℓ : m ≫ ℓ' = ℓ ≫ φ) : A ≫ t' ≫ Qf.map ℓ' = (t ≫ Qf.map ℓ) ≫ Qf.map φ := by
  rw [reassoc_of% h, ← Qf.map_comp, hℓ, Qf.map_comp, Category.assoc]

/-- The algebra of `multiplicationInt_singleTensorMult_leftUnitor`, at variables. -/
private lemma unit_chase {C : Type*} [Category* C] (T : C ⥤ C ⥤ C) {E O₀ U NX M₁ N₀ : C}
    (eA : E ⟶ O₀) (sO : O₀ ⟶ U) (eN : NX ≅ M₁) (sN : M₁ ≅ N₀)
    (lam : ∀ P, (T.obj U).obj P ⟶ P)
    (hl : ∀ {P Q : C} (f : P ⟶ Q), (T.obj U).map f ≫ lam Q = lam P ≫ f) :
    (T.map eA).app NX ≫ (T.obj O₀).map eN.hom ≫ (T.obj O₀).map sN.hom ≫ (T.map sO).app N₀ ≫
        lam N₀ ≫ sN.inv ≫ eN.inv =
      (T.map (eA ≫ sO)).app NX ≫ lam NX := by
  have h₁ := (T.map sO).naturality (eN.hom ≫ sN.hom)
  have h₂ := hl (eN.hom ≫ sN.hom)
  rw [T.map_comp, NatTrans.comp_app, Category.assoc, ← Functor.map_comp_assoc, reassoc_of% h₁,
    reassoc_of% h₂]
  simp

section StandardModel

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat
attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules
  AlgebraicGeometry.SheafOfModules.hasSheafifyOpens
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijectiveOpens

variable {X : RingedSpace.{u, u}}

/-- `𝒪_X[0]`, extended by zero, is K-flat. -/
theorem isKFlat_unitExtend (X : RingedSpace.{u, u}) :
    Stacks.SheafOfModules.IsKFlat X.sheaf
      ((singleNat (X := X) (unitModule X) 0).extend ComplexShape.embeddingUpNat) := by
  intro F hF
  have h := Stacks.SheafOfModules.isKFlat_single_unit X.sheaf F hF
  exact fun n => (h n).of_iso
    (((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).obj F).mapIso (unitExtendIso X)).symm


/-- A sheaf placed in degree `n`, extended by zero, vanishes away from degree `n`. -/
private theorem isZero_extend_singleNat_X
    {N : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)}
    (n : ℕ) (d : ℤ) (hd : d ≠ n) :
    IsZero (((singleNat N n).extend ComplexShape.embeddingUpNat).X d) :=
  (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (n : ℤ) N d hd).of_iso
    ((HomologicalComplex.eval _ _ d).mapIso
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat N n (n : ℤ) rfl))

/-- `𝒪_X[0]`, extended by zero, vanishes away from degree `0`. -/
theorem isZero_unitExtend_X (p : ℤ) (hp : p ≠ 0) :
    IsZero (((singleNat (X := X) (unitModule X) 0).extend ComplexShape.embeddingUpNat).X p) :=
  isZero_extend_singleNat_X 0 p hp

/-- The tensor summand of `𝒪_X[0]`, extended by zero, in a degree `p ≠ 0` vanishes. -/
private theorem isZero_tensor_unitExtend_X
    (K : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)) ℤ) (p q : ℤ) (hp : p ≠ 0) :
    IsZero (((sheafTensor.{u, u, u, u, u} X.sheaf).obj
      (((singleNat (X := X) (unitModule X) 0).extend ComplexShape.embeddingUpNat).X p)).obj
        (K.X q)) :=
  ((sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj (K.X q)).map_isZero (isZero_unitExtend_X p hp)

/-- **The left unitor of the total tensor complex is natural.** -/
theorem complexLeftUnitor_naturality
    {K K' : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)) ℤ} (φ : K ⟶ K') :
    HomologicalComplex.mapBifunctorMap
        (𝟙 ((singleNat (X := X) (unitModule X) 0).extend ComplexShape.embeddingUpNat)) φ
        (sheafTensor.{u, u, u, u, u} X.sheaf) (ComplexShape.up ℤ) ≫ complexLeftUnitor K' =
      complexLeftUnitor K ≫ φ := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  refine HomologicalComplex.mapBifunctor.hom_ext fun (p q : ℤ) hpq => ?_
  by_cases hp : p = 0
  · subst hp
    obtain rfl : q = i := by simpa using hpq
    have e₁ := HomologicalComplex.ι_mapBifunctorMap
      (𝟙 ((singleNat (X := X) (unitModule X) 0).extend ComplexShape.embeddingUpNat)) φ
      (sheafTensor.{u, u, u, u, u} X.sheaf) (ComplexShape.up ℤ) 0 q q hpq
    rw [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp] at e₁
    have e₂ := ι_complexLeftUnitor_f K' q
    have e₃ := ι_complexLeftUnitor_f K q
    have e₄ := ((sheafTensor.{u, u, u, u, u} X.sheaf).map ((unitExtendIso X).hom.f 0 ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (unitModule X)).hom)).naturality
        (φ.f q)
    have e₅ := sheafLeftUnitor_naturality (φ.f q)
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
    exact naturality_chase (b'' := ((sheafTensor.{u, u, u, u, u} X.sheaf).obj (unitModule X)).map
      (φ.f q)) (l' := (sheafLeftUnitor (K'.X q)).hom) (e₁ := e₁) (e₂ := e₂) (e₃ := e₃) (e₄ := e₄)
      (e₅ := e₅)
  · exact (isZero_tensor_unitExtend_X K p q hp).eq_of_src _ _

/-- **The left unitor on the images of complexes**: `𝒪_X[0] ⊗^L Q K ⟶ Tot(𝒪_X[0] ⊗ K) ⟶ K`,
natural in `K`. -/
def derivedLeftUnitorComparison (X : RingedSpace.{u, u}) :
    DerivedCategory.Q ⋙ (derivedTensorProductFunctor X.sheaf).obj
        (moduleDerived (A := X.sheaf) (singleNat (X := X) (unitModule X) 0)) ⟶
      DerivedCategory.Q where
  app K := (canonicalDerivedTensorProduct X.sheaf).toTensor
      ((singleNat (X := X) (unitModule X) 0).extend ComplexShape.embeddingUpNat) K ≫
    DerivedCategory.Q.map (complexLeftUnitor K)
  naturality {K K'} φ := by
    have h := (canonicalDerivedTensorProduct X.sheaf).toTensor_naturality
      (𝟙 ((singleNat (X := X) (unitModule X) 0).extend ComplexShape.embeddingUpNat)) φ
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp] at h
    exact unitor_chase DerivedCategory.Q _ _ _ _ _ _ φ h (complexLeftUnitor_naturality φ)

/-- **The left unit constraint of `⊗^L` at `𝒪_X[0]`**, as a natural transformation on
`D(𝒪_X)`: the lift of `derivedLeftUnitorComparison` along the localization. -/
def derivedLeftUnitor (X : RingedSpace.{u, u}) :
    (derivedTensorProductFunctor X.sheaf).obj
        (moduleDerived (A := X.sheaf) (singleNat (X := X) (unitModule X) 0)) ⟶ 𝟭 _ :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ (derivedTensorProductFunctor X.sheaf).obj
      (moduleDerived (A := X.sheaf) (singleNat (X := X) (unitModule X) 0)))
    DerivedCategory.Q _ (𝟭 _) (derivedLeftUnitorComparison X)

/-- The left unit constraint at the image of a complex. -/
theorem derivedLeftUnitor_app_Q
    (K : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)) ℤ) :
    (derivedLeftUnitor X).app (DerivedCategory.Q.obj K) =
      (canonicalDerivedTensorProduct X.sheaf).toTensor
          ((singleNat (X := X) (unitModule X) 0).extend ComplexShape.embeddingUpNat) K ≫
        DerivedCategory.Q.map (complexLeftUnitor K) := by
  refine (Localization.liftNatTrans_app _ _ _ _ _ _ _ K).trans ?_
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- `singleTensorMult` on its only nonzero summand. -/
@[reassoc]
theorem ι_singleTensorMult_f
    {F G H : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)}
    (μ : ((sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj G ⟶ H) (a b n : ℕ) (hn : a + b = n)
    (h : (ComplexShape.up ℕ).π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (a, b) = n) :
    HomologicalComplex.ιMapBifunctor (singleNat F a) (singleNat G b)
        (sheafTensor.{u, u, u, u, u} X.sheaf) (ComplexShape.up ℕ) a b n h ≫
        (singleTensorMult μ a b n hn).f n =
      ((sheafTensor.{u, u, u, u, u} X.sheaf).obj ((singleNat F a).X a)).map
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) b G).hom ≫
        ((sheafTensor.{u, u, u, u, u} X.sheaf).map
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) a F).hom).app G ≫ μ ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) n H).inv := by
  have e := HomologicalComplex.mkHomToSingle_f
    (K := HomologicalComplex.mapBifunctor (singleNat F a) (singleNat G b)
      (sheafTensor.{u, u, u, u, u} X.sheaf) (ComplexShape.up ℕ))
    (HomologicalComplex.mapBifunctorDesc fun a' b' _ => singleTensorMultSummand μ a b a' b')
    (fun i hi => by
      have hi' : i + 1 = n := hi
      exact (isZero_singleNatTensor_X F G a b i (by omega)).eq_of_src _ _)
  refine (congrArg (_ ≫ ·) e).trans ?_
  rw [HomologicalComplex.ι_mapBifunctorDesc_assoc, singleTensorMultSummand,
    dite_eq_left (And.intro rfl rfl)]
  simp only [Category.assoc]
  rfl

/-- **The multiplication `singleTensorMult` along the left unitor is the left unitor of the
total tensor complex.** -/
theorem multiplicationInt_singleTensorMult_leftUnitor
    (N : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf))
    (n : ℕ) :
    multiplicationInt (singleTensorMult (sheafLeftUnitor N).hom 0 n n (zero_add n)) =
      complexLeftUnitor ((singleNat N n).extend ComplexShape.embeddingUpNat) := by
  refine HomologicalComplex.hom_ext _ _ fun d => ?_
  by_cases hd : d = (n : ℤ)
  · subst hd
    refine HomologicalComplex.mapBifunctor.hom_ext fun (p q : ℤ) hpq => ?_
    by_cases hp : p = 0
    · subst hp
      obtain rfl : q = (n : ℤ) := by simpa using hpq
      rw [ι_complexLeftUnitor_f]
      have h₁ := AlgebraicGeometry.SheafOfModules.ι_multiplicationInt_f (A := X.sheaf)
        (singleTensorMult (sheafLeftUnitor N).hom 0 n n (zero_add n)) n 0 n (by simp)
      refine h₁.trans ((congrArg (fun t => _ ≫ _ ≫ t) (ι_singleTensorMult_f_assoc
        (sheafLeftUnitor N).hom 0 n n (zero_add n) (by simp) _)).trans ?_)
      have e₀ : (unitExtendIso X).hom.f 0 ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (unitModule X)).hom =
          (HomologicalComplex.extendXIso (singleNat (X := X) (unitModule X) 0)
            ComplexShape.embeddingUpNat (i' := ((0 : ℕ) : ℤ)) (i := 0) (by simp)).hom ≫
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (unitModule X)).hom := by
        have e := HomologicalComplex.extendSingleIso_hom_f ComplexShape.embeddingUpNat
          (unitModule X) 0 (0 : ℤ) rfl
        refine (congrArg (· ≫ _) e).trans ?_
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [e₀]
      exact unit_chase (sheafTensor.{u, u, u, u, u} X.sheaf) _ _
        (HomologicalComplex.extendXIso (singleNat N n) ComplexShape.embeddingUpNat
          (i' := (n : ℤ)) (i := n) (by simp))
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) n N)
        (fun P => (sheafLeftUnitor P).hom) (fun f => sheafLeftUnitor_naturality f)
    · exact (isZero_tensor_unitExtend_X _ p q hp).eq_of_src _ _
  · exact (isZero_extend_singleNat_X n d hd).eq_of_tgt _ _

end StandardModel

end Stacks.DeRham.GysinCupHodge

module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinEdgeUnitLaw

/-!
# Naturality of the edge map of Tag 0G75 in the left factor and in the target

`edgeMatchingLeft` is natural in the left factor `A` and in the target of the multiplication
`w : A ⊗ L ⟶ M`: `edgeMatchingLeft_naturality_left` and `edgeMatchingLeft_comp`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.SupportedComplexes RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.Tensor (sheafTensor)
open AlgebraicGeometry.SheafOfModules (moduleDerived multiplicationInt tensorBifunctorNat)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)
open Stacks.Perfect.SupportedQuasicoherent (derivedSupportedPushforward)
open DerivedCategory

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose structureSheafRing
  AlgebraicGeometry.SheafedSpace.sheaf AlgebraicGeometry.SheafOfModules.baseRingedSpace
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.DeRham.GysinCupHodge

private lemma bif_chase {C : Type*} [Category* C] (T : C ⥤ C ⥤ C) {a a' A A' b B H Hn : C}
    (sA : a ≅ A) (sA' : a' ≅ A') (f : A ⟶ A') (sG : b ≅ B) (w : (T.obj A').obj B ⟶ H)
    (k : H ⟶ Hn) :
    (T.obj a).map sG.hom ≫ (T.map sA.hom).app B ≫ ((T.map f).app B ≫ w) ≫ k =
      (T.map (sA.hom ≫ f ≫ sA'.inv)).app b ≫ (T.obj a').map sG.hom ≫ (T.map sA'.hom).app B ≫
        w ≫ k := by
  rw [← Category.assoc ((T.map _).app b), ← (T.map (sA.hom ≫ f ≫ sA'.inv)).naturality sG.hom]
  simp only [Category.assoc, ← NatTrans.comp_app_assoc, ← T.map_comp, Iso.inv_hom_id,
    Category.comp_id]

private lemma comp_chase {C D : Type*} [Category* C] [Category* D] (Qf : C ⥤ D) (R : D ⥤ D)
    {P P' B Y₁ : D} {S S' S'' M M' : C} (u₁ : P ⟶ P') (u₂ : P' ⟶ R.obj B) (x : B ⟶ Y₁)
    (y : Y₁ ⟶ Qf.obj S) (m : S ⟶ S') (eg : S' ⟶ S'') (eM : S' ⟶ M) (eM' : S'' ⟶ M')
    (g : M ⟶ M') (h : eg ≫ eM' = eM ≫ g) :
    u₁ ≫ u₂ ≫ R.map (x ≫ y ≫ Qf.map (m ≫ eg) ≫ Qf.map eM') =
      (u₁ ≫ u₂ ≫ R.map (x ≫ y ≫ Qf.map m ≫ Qf.map eM)) ≫ R.map (Qf.map g) := by
  simp only [Category.assoc, ← R.map_comp, ← Qf.map_comp, h]

private lemma left_chase {D : Type*} [Category* D] {T T' : D ⥤ D} (α : T ⟶ T') (R : D ⥤ D)
    {P B L₀ L₁ W W' N M₀ : D} (a : P ⟶ B) (S : T.obj B ⟶ R.obj (T.obj L₀))
    (S' : T'.obj B ⟶ R.obj (T'.obj L₀)) (mi : L₀ ⟶ L₁) (t : T.obj L₁ ⟶ W) (q : W ⟶ N)
    (t' : T'.obj L₁ ⟶ W') (q' : W' ⟶ N) (mM : N ⟶ M₀)
    (n₂ : α.app B ≫ S' = S ≫ R.map (α.app L₀)) (n₄ : α.app L₁ ≫ t' ≫ q' = t ≫ q) :
    α.app P ≫ T'.map a ≫ S' ≫ R.map (T'.map mi ≫ t' ≫ q' ≫ mM) =
      T.map a ≫ S ≫ R.map (T.map mi ≫ t ≫ q ≫ mM) := by
  rw [← reassoc_of% (α.naturality a), reassoc_of% n₂, ← R.map_comp,
    ← reassoc_of% (α.naturality mi), reassoc_of% n₄]

section StandardModel

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat
attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules
  AlgebraicGeometry.SheafOfModules.hasSheafifyOpens
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijectiveOpens

variable {X : RingedSpace.{u, u}}

/-- Away from the bidegree `(a, b)` the summands of the total tensor complex of two sheaves
placed in degrees `a` and `b` vanish. -/
theorem isZero_singleNat_tensor_summand
    (F G : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf))
    (a b a' b' : ℕ) (h : ¬ (a' = a ∧ b' = b)) :
    IsZero (((sheafTensor.{u, u, u, u, u} X.sheaf).obj ((singleNat F a).X a')).obj
      ((singleNat G b).X b')) := by
  by_cases ha : a' = a
  · exact AlgebraicGeometry.SheafOfModules.isZero_tensorFunctor_obj_obj_of_right _
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) b _ b' fun hb ↦ h ⟨ha, hb⟩)
  · exact AlgebraicGeometry.SheafOfModules.isZero_tensorFunctor_obj_obj_of_left
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) a _ a' ha) _

/-- `singleTensorMult` followed by a morphism of the target. -/
theorem singleTensorMult_comp
    {F G H H' : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)}
    (μ : ((sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj G ⟶ H) (g : H ⟶ H')
    (a b n : ℕ) (hn : a + b = n) :
    singleTensorMult (μ ≫ g) a b n hn =
      singleTensorMult μ a b n hn ≫ (HomologicalComplex.single _ (ComplexShape.up ℕ) n).map g := by
  refine HomologicalComplex.to_single_hom_ext ?_
  refine HomologicalComplex.mapBifunctor.hom_ext fun (a' b' : ℕ) h ↦ ?_
  by_cases hab : a' = a ∧ b' = b
  · obtain ⟨rfl, rfl⟩ := hab
    refine (ι_singleTensorMult_f (μ ≫ g) a' b' n hn h).trans ?_
    refine Eq.trans ?_ ((Category.assoc _ _ _).symm.trans (congrArg
      (· ≫ ((HomologicalComplex.single _ (ComplexShape.up ℕ) n).map g).f n)
      (ι_singleTensorMult_f μ a' b' n hn h))).symm
    rw [HomologicalComplex.single_map_f_self]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  · exact (isZero_singleNat_tensor_summand F G a b a' b' hab).eq_of_src _ _

/-- `singleTensorMult` precomposed with a morphism of the left factor. -/
theorem singleTensorMult_whiskerRight
    {A A' G H : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)}
    (f : A ⟶ A') (w : ((sheafTensor.{u, u, u, u, u} X.sheaf).obj A').obj G ⟶ H)
    (a b n : ℕ) (hn : a + b = n) :
    singleTensorMult (((sheafTensor.{u, u, u, u, u} X.sheaf).map f).app G ≫ w) a b n hn =
      ((tensorBifunctorNat (A := X.sheaf)).map
          ((HomologicalComplex.single _ (ComplexShape.up ℕ) a).map f)).app (singleNat G b) ≫
        singleTensorMult w a b n hn := by
  refine HomologicalComplex.to_single_hom_ext ?_
  refine HomologicalComplex.mapBifunctor.hom_ext fun (a' b' : ℕ) h ↦ ?_
  by_cases hab : a' = a ∧ b' = b
  · obtain ⟨rfl, rfl⟩ := hab
    refine (ι_singleTensorMult_f _ a' b' n hn h).trans ?_
    have e := HomologicalComplex.ι_mapBifunctorMap
      ((HomologicalComplex.single _ (ComplexShape.up ℕ) a').map f) (𝟙 (singleNat G b'))
      (sheafTensor.{u, u, u, u, u} X.sheaf) (ComplexShape.up ℕ) a' b' n h
    refine Eq.trans ?_ ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
        (congrArg (_ ≫ ·) (ι_singleTensorMult_f w a' b' n hn h)))))))).symm
    rw [HomologicalComplex.single_map_f_self, HomologicalComplex.id_f,
      CategoryTheory.Functor.map_id, Category.id_comp]
    exact bif_chase _ _ _ f _ w _
  · exact (isZero_singleNat_tensor_summand A G a b a' b' hab).eq_of_src _ _

/-- The extension by zero of a sheaf placed in degree `n` is natural in the sheaf. -/
theorem extendMap_single_comp_extendSingleIso
    {M M' : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)}
    (g : M ⟶ M') (n : ℕ) :
    HomologicalComplex.extendMap ((HomologicalComplex.single _ (ComplexShape.up ℕ) n).map g)
        ComplexShape.embeddingUpNat ≫
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat M' n (n : ℤ) rfl).hom =
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat M n (n : ℤ) rfl).hom ≫
        (HomologicalComplex.single _ (ComplexShape.up ℤ) (n : ℤ)).map g := by
  refine HomologicalComplex.to_single_hom_ext ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ)) rfl,
    HomologicalComplex.extendSingleIso_hom_f ComplexShape.embeddingUpNat M' n (n : ℤ) rfl,
    HomologicalComplex.extendSingleIso_hom_f ComplexShape.embeddingUpNat M n (n : ℤ) rfl,
    HomologicalComplex.single_map_f_self, HomologicalComplex.single_map_f_self]
  simp

variable (Z : Set X.carrier) (hZ : IsClosed Z)

/-- **The edge map of Tag 0G75 is natural in the target of the multiplication.** -/
theorem edgeMatchingLeft_comp (c : ℕ)
    {F L M M' G : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)}
    (w : ((sheafTensor.{u, u, u, u, u} X.sheaf).obj F).obj L ⟶ M) (g : M ⟶ M')
    (sL : (singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) (c : ℤ)).obj G ⟶
      (derivedSupportedPushforward X Z hZ).obj
        ((singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) ((0 : ℕ) : ℤ)).obj L)) :
    edgeMatchingLeft Z hZ c (w ≫ g) sL =
      edgeMatchingLeft Z hZ c w sL ≫ (derivedSupportedPushforward X Z hZ).map
        ((singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) ((0 : ℕ) : ℤ)).map
          g) := by
  dsimp only [edgeMatchingLeft, moduleDerivedSingleIso, Functor.mapIso_hom]
  have hm : multiplicationInt (singleTensorMult (w ≫ g) 0 0 0 rfl) =
      multiplicationInt (singleTensorMult w 0 0 0 rfl) ≫
        HomologicalComplex.extendMap ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map g)
          ComplexShape.embeddingUpNat := by
    rw [singleTensorMult_comp, multiplicationInt, multiplicationInt,
      HomologicalComplex.extendMap_comp]
    exact (Category.assoc _ _ _).symm
  rw [hm]
  exact comp_chase DerivedCategory.Q (derivedSupportedPushforward X Z hZ) _ _ _ _ _ _ _ _ _
    (extendMap_single_comp_extendSingleIso g 0)

/-- **The edge map of Tag 0G75 is natural in the left factor.** -/
theorem edgeMatchingLeft_naturality_left (c : ℕ)
    {A A' L M G : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)}
    (f : A ⟶ A') (w : ((sheafTensor.{u, u, u, u, u} X.sheaf).obj A').obj L ⟶ M)
    (sL : (singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) (c : ℤ)).obj G ⟶
      (derivedSupportedPushforward X Z hZ).obj
        ((singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing X)) ((0 : ℕ) : ℤ)).obj L)) :
    ((derivedTensorProductFunctor X.sheaf).map (DerivedCategory.Q.map
        (HomologicalComplex.extendMap ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map f)
          ComplexShape.embeddingUpNat))).app (moduleDerived (A := X.sheaf) (singleNat G c)) ≫
        edgeMatchingLeft Z hZ c w sL =
      edgeMatchingLeft Z hZ c (((sheafTensor.{u, u, u, u, u} X.sheaf).map f).app L ≫ w) sL := by
  have hm : singleTensorMult (((sheafTensor.{u, u, u, u, u} X.sheaf).map f).app L ≫ w) 0 0 0 rfl ≫
      𝟙 _ = ((tensorBifunctorNat (A := X.sheaf)).obj (singleNat A 0)).map (𝟙 (singleNat L 0)) ≫
        ((tensorBifunctorNat (A := X.sheaf)).map
          ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map f)).app (singleNat L 0) ≫
        singleTensorMult w 0 0 0 rfl := by
    rw [Category.comp_id, CategoryTheory.Functor.map_id, Category.id_comp,
      singleTensorMult_whiskerRight]
  have n₄ := AlgebraicGeometry.SheafOfModules.toTensor_multiplicationInt_naturality
    ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map f) (𝟙 (singleNat L 0)) _ _ _ hm
  rw [HomologicalComplex.extendMap_id, HomologicalComplex.extendMap_id, DerivedCategory.Q.map_id,
    DerivedCategory.Q.map_id, Category.comp_id, Functor.uncurry_obj_map,
    CategoryTheory.Functor.map_id, Category.comp_id] at n₄
  dsimp only [edgeMatchingLeft]
  exact left_chase _ _ _ _ _ _ _ _ _ _ _
    (supportedTensorPushMap_naturality_left X Z hZ _ _) n₄

end StandardModel

end Stacks.DeRham.GysinCupHodge

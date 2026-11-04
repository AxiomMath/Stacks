module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinEdgeReadOff

/-!
# The degree-`c` read-off of the maps out of `A[0] ⊗^L G[c]`

`edgeReadOff A G c : H^c(A[0] ⊗^L G[c]) ≅ A ⊗ G` is the degree-`c` cohomology of the canonical
map to the total tensor complex followed by the multiplication `singleTensorMult` along the
identity of `A ⊗ G`. A multiplication `μ : A ⊗ G ⟶ H` placed in degree `c` reads off, through it,
as `μ` itself: `homologyMap_toTensor_singleTensorMult`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.SheafOfModules.Tensor (sheafTensor)
open AlgebraicGeometry.SheafOfModules (moduleDerived multiplicationInt tensorBifunctorNat)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose structureSheafRing
  AlgebraicGeometry.SheafedSpace.sheaf AlgebraicGeometry.SheafOfModules.baseRingedSpace
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.DeRham.GysinCupHodge

/-- The algebra of `homologyMap_toTensor_singleTensorMult`, at variables. -/
private lemma readOff_chase {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (Qf : C ⥤ D) (H : D ⥤ E) {P : D} {T₀ S₁ S₂ M₁ M₂ : C} {N₁ N₂ : E}
    (t : P ⟶ Qf.obj T₀) (m : T₀ ⟶ S₁) (x : S₁ ⟶ S₂) (e₁ : S₁ ⟶ M₁) (e₂ : S₂ ⟶ M₂)
    (y : M₁ ⟶ M₂) (s₁ : H.obj (Qf.obj M₁) ⟶ N₁) (s₂ : H.obj (Qf.obj M₂) ⟶ N₂) (μ : N₁ ⟶ N₂)
    (h₁ : x ≫ e₂ = e₁ ≫ y) (h₂ : H.map (Qf.map y) ≫ s₂ = s₁ ≫ μ) :
    H.map (t ≫ Qf.map (m ≫ x)) ≫ H.map (Qf.map e₂) ≫ s₂ =
      (H.map (t ≫ Qf.map m) ≫ H.map (Qf.map e₁) ≫ s₁) ≫ μ := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc H (Qf.map x), ← Qf.map_comp, h₁, Qf.map_comp, H.map_comp_assoc,
    h₂]

/-- The algebra of `edgeReadOff_naturality`, at variables. -/
private lemma readOff_nat_chase {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (Qf : C ⥤ D) (H : D ⥤ E) {P P' : D} {T₀ T₀' S₁ S₂ M₁ M₂ : C} {N₁ N₂ : E}
    (a : P ⟶ P') (t' : P' ⟶ Qf.obj T₀') (t : P ⟶ Qf.obj T₀) (m' : T₀' ⟶ S₂)
    (m : T₀ ⟶ S₁) (x : S₁ ⟶ S₂) (e₁ : S₁ ⟶ M₁) (e₂ : S₂ ⟶ M₂) (y : M₁ ⟶ M₂)
    (s₁ : H.obj (Qf.obj M₁) ⟶ N₁) (s₂ : H.obj (Qf.obj M₂) ⟶ N₂) (μ : N₁ ⟶ N₂)
    (h₀ : a ≫ t' ≫ Qf.map m' = (t ≫ Qf.map m) ≫ Qf.map x)
    (h₁ : x ≫ e₂ = e₁ ≫ y) (h₂ : H.map (Qf.map y) ≫ s₂ = s₁ ≫ μ) :
    H.map a ≫ H.map (t' ≫ Qf.map m') ≫ H.map (Qf.map e₂) ≫ s₂ =
      (H.map (t ≫ Qf.map m) ≫ H.map (Qf.map e₁) ≫ s₁) ≫ μ := by
  rw [← H.map_comp_assoc, h₀, Category.assoc, ← Qf.map_comp]
  exact readOff_chase Qf H _ _ _ _ _ _ _ _ _ h₁ h₂

section StandardModel

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules
  AlgebraicGeometry.SheafOfModules.hasSheafifyOpens
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijectiveOpens

variable {X : RingedSpace.{u, u}}

/-- **A total complex with a single nonzero summand in some degree is that summand there.** -/
theorem isIso_ιMapBifunctor_of_isZero {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂]
    [Category* D] [Preadditive C₁] [Preadditive C₂] [Preadditive D] (F : C₁ ⥤ C₂ ⥤ D)
    [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
    (K : CochainComplex C₁ ℤ) (L : CochainComplex C₂ ℤ)
    [HomologicalComplex.HasMapBifunctor K L F (ComplexShape.up ℤ)] (a b n : ℤ)
    (hn : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, b) = n)
    (h₀ : ∀ i j : ℤ, i + j = n → ¬ (i = a ∧ j = b) → IsZero ((F.obj (K.X i)).obj (L.X j))) :
    IsIso (HomologicalComplex.ιMapBifunctor K L F (ComplexShape.up ℤ) a b n hn) := by
  refine ⟨HomologicalComplex.mapBifunctorDesc fun i j hij => if h : i = a ∧ j = b then
    eqToHom (by rw [h.1, h.2]) else 0, ?_, ?_⟩
  · simp
  · refine HomologicalComplex.mapBifunctor.hom_ext fun i j hij => ?_
    by_cases h : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · exact (h₀ i j hij h).eq_of_src _ _

/-- The identification of the extension by zero of a sheaf placed in degree `n` with the sheaf
placed in degree `n`. -/
abbrev extendSingleIsoNat
    (N : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf))
    (n : ℕ) :
    (singleNat N n).extend ComplexShape.embeddingUpNat ≅
      (HomologicalComplex.single _ (ComplexShape.up ℤ) (n : ℤ)).obj N :=
  HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat N n (n : ℤ) rfl

/-- The tensor product of the degree-`i` and degree-`j` terms of `A[0]` and `G[c]`, extended by
zero, vanishes away from `(i, j) = (0, c)`. -/
private theorem isZero_tensor_singleNat_extend_X
    (A G : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf))
    (c : ℕ) (i j : ℤ) (h : ¬ (i = ((0 : ℕ) : ℤ) ∧ j = (c : ℤ))) :
    IsZero (((sheafTensor.{u, u, u, u, u} X.sheaf).obj
      (((singleNat A 0).extend ComplexShape.embeddingUpNat).X i)).obj
        (((singleNat G c).extend ComplexShape.embeddingUpNat).X j)) := by
  by_cases hi : i = ((0 : ℕ) : ℤ)
  · exact ((sheafTensor.{u, u, u, u, u} X.sheaf).obj _).map_isZero
      ((HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (c : ℤ) G j
        fun hj => h ⟨hi, hj⟩).of_iso
        ((HomologicalComplex.eval _ _ j).mapIso (extendSingleIsoNat G c)))
  · exact ((sheafTensor.{u, u, u, u, u} X.sheaf).flip.obj _).map_isZero
      ((HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) ((0 : ℕ) : ℤ) A i hi).of_iso
        ((HomologicalComplex.eval _ _ i).mapIso (extendSingleIsoNat A 0)))

/-- The multiplication of two sheaves placed in degrees `0` and `c` along the identity, on the
summand `(0, c)`. -/
theorem isIso_multiplicationInt_singleTensorMult_id_f
    (A G : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf))
    (c : ℕ) :
    IsIso ((multiplicationInt (singleTensorMult
      (𝟙 (((sheafTensor.{u, u, u, u, u} X.sheaf).obj A).obj G)) 0 c c (zero_add c))).f
        (c : ℤ)) := by
  have hh : ((0 : ℕ) : ℤ) + (c : ℤ) = (c : ℤ) := by simp
  have hι := isIso_ιMapBifunctor_of_isZero (sheafTensor.{u, u, u, u, u} X.sheaf)
    ((singleNat A 0).extend ComplexShape.embeddingUpNat)
    ((singleNat G c).extend ComplexShape.embeddingUpNat) ((0 : ℕ) : ℤ) (c : ℤ) (c : ℤ) hh
    fun i j _ h => isZero_tensor_singleNat_extend_X A G c i j h
  have hE := (AlgebraicGeometry.SheafOfModules.ι_multiplicationInt_f (A := X.sheaf)
    (singleTensorMult (𝟙 (((sheafTensor.{u, u, u, u, u} X.sheaf).obj A).obj G)) 0 c c (zero_add c))
    c 0 c hh).trans (congrArg (fun t => _ ≫ _ ≫ t) (ι_singleTensorMult_f_assoc
      (𝟙 (((sheafTensor.{u, u, u, u, u} X.sheaf).obj A).obj G)) 0 c c (zero_add c) (by simp) _))
  rw [(IsIso.eq_inv_comp _).2 hE]
  infer_instance

/-- The total tensor complex of two sheaves placed in degrees `0` and `c`, extended by zero,
vanishes outside degree `c`. -/
theorem isZero_mapBifunctor_singleNat_extend_X
    (A G : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf))
    (c : ℕ) (d : ℤ) (hd : d ≠ (c : ℤ)) :
    IsZero ((HomologicalComplex.mapBifunctor ((singleNat A 0).extend ComplexShape.embeddingUpNat)
      ((singleNat G c).extend ComplexShape.embeddingUpNat) (sheafTensor.{u, u, u, u, u} X.sheaf)
      (ComplexShape.up ℤ)).X d) := by
  refine HomologicalComplex₂.isZero_total_X_of_isZero _ _ d fun i j hij => ?_
  have hij' : i + j = d := hij
  exact isZero_tensor_singleNat_extend_X A G c i j fun h => hd (by omega)

/-- **The multiplication along the identity is an isomorphism of complexes.** -/
instance isIso_multiplicationInt_singleTensorMult_id
    (A G : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf))
    (c : ℕ) :
    IsIso (multiplicationInt (singleTensorMult
      (𝟙 (((sheafTensor.{u, u, u, u, u} X.sheaf).obj A).obj G)) 0 c c (zero_add c))) := by
  refine @HomologicalComplex.Hom.isIso_of_components _ _ _ _ _ _ _ _ fun d => ?_
  by_cases hd : d = (c : ℤ)
  · subst hd
    exact isIso_multiplicationInt_singleTensorMult_id_f A G c
  · exact isIso_of_source_target_iso_zero _
      ((isZero_mapBifunctor_singleNat_extend_X A G c d hd).isoZero)
      (((HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (c : ℤ) _ d hd).of_iso
        ((HomologicalComplex.eval _ _ d).mapIso (extendSingleIsoNat _ c))).isoZero)

/-- **A sheaf placed in degree `c`, extended by zero, has the sheaf as its degree-`c`
cohomology.** -/
def singleNatHomologyIso
    (N : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf))
    (c : ℕ) :
    (DerivedCategory.homologyFunctor _ (c : ℤ)).obj (moduleDerived (A := X.sheaf) (singleNat N c)) ≅
      N :=
  (DerivedCategory.homologyFunctor _ (c : ℤ)).mapIso (moduleDerivedSingleIso N c) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso _ (c : ℤ)).app N

/-- **The degree-`c` read-off** `H^c(A[0] ⊗^L G[c]) ⟶ A ⊗ G`: the canonical map to the total
tensor complex, the multiplication along the identity, and the degree-`c` cohomology of a sheaf
placed in degree `c`. -/
def edgeReadOff
    (A G : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf))
    (c : ℕ) :
    (DerivedCategory.homologyFunctor _ (c : ℤ)).obj
        (((derivedTensorProductFunctor X.sheaf).obj
            (moduleDerived (A := X.sheaf) (singleNat A 0))).obj
          (moduleDerived (A := X.sheaf) (singleNat G c))) ⟶
      ((sheafTensor.{u, u, u, u, u} X.sheaf).obj A).obj G :=
  (DerivedCategory.homologyFunctor _ (c : ℤ)).map
      ((canonicalDerivedTensorProduct X.sheaf).toTensor
          ((singleNat A 0).extend ComplexShape.embeddingUpNat)
          ((singleNat G c).extend ComplexShape.embeddingUpNat) ≫
        DerivedCategory.Q.map (multiplicationInt (singleTensorMult
          (𝟙 (((sheafTensor.{u, u, u, u, u} X.sheaf).obj A).obj G)) 0 c c (zero_add c)))) ≫
    (singleNatHomologyIso _ c).hom

/-- **The degree-`c` read-off is an isomorphism**, with no hypothesis on `A` or `G`. -/
instance isIso_edgeReadOff
    (A G : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf))
    (c : ℕ) : IsIso (edgeReadOff A G c) := by
  have h₁ := isIso_homologyMap_toTensor_of_iso X.sheaf (canonicalDerivedTensorProduct X.sheaf)
    A G (c : ℤ) (extendSingleIsoNat A 0) (extendSingleIsoNat G c)
  have h₂ : IsIso ((DerivedCategory.homologyFunctor _ (c : ℤ)).map
      (DerivedCategory.Q.map (multiplicationInt (singleTensorMult
        (𝟙 (((sheafTensor.{u, u, u, u, u} X.sheaf).obj A).obj G)) 0 c c (zero_add c))))) :=
    Functor.map_isIso _ _
  unfold edgeReadOff
  rw [Functor.map_comp]
  exact IsIso.comp_isIso' (IsIso.comp_isIso' h₁ h₂) inferInstance

/-- **A multiplication placed in degree `c` reads off as itself.** -/
theorem homologyMap_toTensor_singleTensorMult
    {A G H : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)}
    (μ : ((sheafTensor.{u, u, u, u, u} X.sheaf).obj A).obj G ⟶ H) (c : ℕ) :
    (DerivedCategory.homologyFunctor _ (c : ℤ)).map
        ((canonicalDerivedTensorProduct X.sheaf).toTensor
            ((singleNat A 0).extend ComplexShape.embeddingUpNat)
            ((singleNat G c).extend ComplexShape.embeddingUpNat) ≫
          DerivedCategory.Q.map (multiplicationInt (singleTensorMult μ 0 c c (zero_add c)))) ≫
        (singleNatHomologyIso H c).hom =
      edgeReadOff A G c ≫ μ := by
  have hm : multiplicationInt (singleTensorMult μ 0 c c (zero_add c)) =
      multiplicationInt (singleTensorMult
        (𝟙 (((sheafTensor.{u, u, u, u, u} X.sheaf).obj A).obj G)) 0 c c (zero_add c)) ≫
        HomologicalComplex.extendMap ((HomologicalComplex.single _ (ComplexShape.up ℕ) c).map μ)
          ComplexShape.embeddingUpNat := by
    have e := singleTensorMult_comp (𝟙 (((sheafTensor.{u, u, u, u, u} X.sheaf).obj A).obj G)) μ
      0 c c (zero_add c)
    rw [Category.id_comp] at e
    rw [e, multiplicationInt, multiplicationInt, HomologicalComplex.extendMap_comp]
    exact (Category.assoc _ _ _).symm
  rw [hm]
  have h₂ := (DerivedCategory.singleFunctorCompHomologyFunctorIso _ (c : ℤ)).hom.naturality μ
  exact readOff_chase DerivedCategory.Q (DerivedCategory.homologyFunctor _ (c : ℤ)) _ _ _ _ _
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) (c : ℤ)).map μ) _ _ μ
    (extendMap_single_comp_extendSingleIso μ c) h₂

/-- **The degree-`c` read-off is natural in the left factor.** -/
theorem edgeReadOff_naturality
    {A A' G : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)} (f : A ⟶ A') (c : ℕ) :
    (DerivedCategory.homologyFunctor _ (c : ℤ)).map
        (((derivedTensorProductFunctor X.sheaf).map (DerivedCategory.Q.map
          (HomologicalComplex.extendMap ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map f)
            ComplexShape.embeddingUpNat))).app (moduleDerived (A := X.sheaf) (singleNat G c))) ≫
        edgeReadOff A' G c =
      edgeReadOff A G c ≫ ((sheafTensor.{u, u, u, u, u} X.sheaf).map f).app G := by
  have hm : singleTensorMult (𝟙 (((sheafTensor.{u, u, u, u, u} X.sheaf).obj A).obj G)) 0 c c
        (zero_add c) ≫
      (HomologicalComplex.single _ (ComplexShape.up ℕ) c).map
        (((sheafTensor.{u, u, u, u, u} X.sheaf).map f).app G) =
      ((tensorBifunctorNat (A := X.sheaf)).obj (singleNat A 0)).map (𝟙 (singleNat G c)) ≫
        ((tensorBifunctorNat (A := X.sheaf)).map
          ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map f)).app (singleNat G c) ≫
        singleTensorMult (𝟙 (((sheafTensor.{u, u, u, u, u} X.sheaf).obj A').obj G)) 0 c c
          (zero_add c) := by
    rw [← singleTensorMult_comp, ← singleTensorMult_whiskerRight, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.id_comp, Category.comp_id]
  have h₀ := AlgebraicGeometry.SheafOfModules.toTensor_multiplicationInt_naturality
    ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).map f) (𝟙 (singleNat G c)) _ _ _ hm
  rw [HomologicalComplex.extendMap_id, DerivedCategory.Q.map_id, Functor.uncurry_obj_map,
    CategoryTheory.Functor.map_id, Category.comp_id] at h₀
  have h₂ := (DerivedCategory.singleFunctorCompHomologyFunctorIso _ (c : ℤ)).hom.naturality
    (((sheafTensor.{u, u, u, u, u} X.sheaf).map f).app G)
  exact readOff_nat_chase DerivedCategory.Q (DerivedCategory.homologyFunctor _ (c : ℤ)) _ _ _ _ _
    _ _ _ _ _ _ _ h₀ (extendMap_single_comp_extendSingleIso _ c) h₂

/-- A sheaf placed in degree `n`, extended by zero, has no cohomology above degree `n`. -/
theorem isLE_moduleDerived_singleNat
    (N : _root_.SheafOfModules.{u} (structureSheafRing X)) (n : ℕ) :
    (moduleDerived (A := X.sheaf) (singleNat N n)).IsLE (n : ℤ) :=
  DerivedCategory.TStructure.t.isLE_of_iso (moduleDerivedSingleIso N n).symm (n : ℤ)

end StandardModel

end Stacks.DeRham.GysinCupHodge



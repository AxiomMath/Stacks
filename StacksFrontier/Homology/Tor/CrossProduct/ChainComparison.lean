module

public import StacksFrontier.Homology.Tor.CrossProduct.System

/-!
# Tor cross products: chain comparisons and the cycle product

Chain maps out of a complex of projectives lift against quasi-isomorphisms. Consequently a
normalized comparison `Tot(P ⊗ Q) → T` lifting the identity of `M ⊗ N` exists and is unique
up to chain homotopy. This file also constructs the homology cross product of two chain
complexes induced by tensoring cycles.
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory CochainComplex.DerivedTensor
open scoped TensorProduct

universe uR uA v w x

noncomputable section

open HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private theorem chain_exists_lift_of_quasiIso
    {C : Type*} [Category* C] [Abelian C]
    {P K L : ChainComplex C ℕ} [∀ n, Projective (P.X n)]
    (α : L ⟶ K) [QuasiIso α] (γ : P ⟶ K) :
    ∃ β : P ⟶ L, Nonempty (Homotopy (β ≫ α) γ) := by
  let E := ComplexShape.embeddingDownNat.extendFunctor C
  have : CochainComplex.IsKProjective (E.obj P) :=
    inferInstanceAs (CochainComplex.IsKProjective (P.extend ComplexShape.embeddingDownNat))
  have : QuasiIso (E.map α) :=
    inferInstanceAs (QuasiIso (extendMap α ComplexShape.embeddingDownNat))
  obtain ⟨β, ⟨hβ⟩⟩ :=
    (CochainComplex.IsKProjective.exists_lift_of_quasiIso (E.map α) (E.map γ)).1
  obtain ⟨β, rfl⟩ := E.map_surjective β
  refine ⟨β, ⟨Homotopy.ofExtend (e := ComplexShape.embeddingDownNat) ?_⟩⟩
  simpa only [E, ComplexShape.Embedding.extendFunctor, extendMap_comp] using hβ

private theorem chain_nonempty_homotopy_of_comp_quasiIso
    {C : Type*} [Category* C] [Abelian C]
    {P K L : ChainComplex C ℕ} [∀ n, Projective (P.X n)]
    (α : L ⟶ K) [QuasiIso α] {β₁ β₂ : P ⟶ L}
    (h : Homotopy (β₁ ≫ α) (β₂ ≫ α)) : Nonempty (Homotopy β₁ β₂) := by
  let E := ComplexShape.embeddingDownNat.extendFunctor C
  have : CochainComplex.IsKProjective (E.obj P) :=
    inferInstanceAs (CochainComplex.IsKProjective (P.extend ComplexShape.embeddingDownNat))
  have : QuasiIso (E.map α) :=
    inferInstanceAs (QuasiIso (extendMap α ComplexShape.embeddingDownNat))
  have h' : Homotopy (E.map β₁ ≫ E.map α) (E.map β₂ ≫ E.map α) := by
    simpa only [E, ComplexShape.Embedding.extendFunctor, extendMap_comp] using
      h.extend ComplexShape.embeddingDownNat
  obtain ⟨hβ⟩ := CochainComplex.IsKProjective.nonempty_homotopy_of_comp_quasiIso (E.map α) h'
  exact ⟨hβ.ofExtend⟩



private lemma homotopy_to_single_eq
    {C : Type*} [Category* C] [Abelian C]
    {P : ChainComplex C ℕ} {X : C}
    {f g : P ⟶ (ChainComplex.single₀ C).obj X} (h : Homotopy f g) : f = g := by
  apply to_single_hom_ext
  simpa only [dNext_eq_zero (c := ComplexShape.down ℕ) _ 0 (by decide),
    prevD_eq _ (show (ComplexShape.down ℕ).Rel 1 0 by simp),
    single_obj_d, comp_zero, zero_add] using h.comm 0

private lemma chain_exists_lift_resolution
    {C : Type*} [Category* C] [Abelian C]
    (P : ChainComplex C ℕ) [∀ n, Projective (P.X n)]
    {X : C} (T : ProjectiveResolution X) (γ : P ⟶ (ChainComplex.single₀ C).obj X) :
    ∃ μ : P ⟶ T.complex, μ ≫ T.π = γ := by
  obtain ⟨μ, ⟨hμ⟩⟩ := chain_exists_lift_of_quasiIso T.π γ
  exact ⟨μ, homotopy_to_single_eq hμ⟩

namespace TorCrossProduct

private lemma projective_chainTensor
    {S : Type uA} [CommRing S]
    (K L : ChainComplex (ModuleCat.{max uR uA v} S) ℕ)
    [∀ n, Projective (K.X n)] [∀ n, Projective (L.X n)] (n : ℕ) :
    Projective ((chainTensor.{uR, uA, v} K L).X n) := by
  have (p q : ℕ) : Projective
      (((ModuleCat.moduleTensorLarge.{uA, max uR v} S).obj (K.X p)).obj (L.X q)) := by
    show Projective (ModuleCat.of S (K.X p ⊗[S] L.X q))
    infer_instance
  refine ⟨fun f e _ ↦ ⟨mapBifunctorDesc (fun p q h ↦
    Projective.factorThru (ιMapBifunctor K L _ _ p q n h ≫ f) e), ?_⟩⟩
  apply mapBifunctor.hom_ext
  intro p q h
  simp

private lemma zeroBaseChange_tmul
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A]
    (f : R →+* A) (M N : ModuleCat.{max uR uA v} R)
    (a b : A) (x : M) (y : N) :
    let := f.toAlgebra
    zeroBaseChange R A f M N ((a ⊗ₜ[R] x) ⊗ₜ[A] (b ⊗ₜ[R] y)) =
      (a * b) ⊗ₜ[R] (x ⊗ₜ[R] y) := by
  let := f.toAlgebra
  exact TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul R A x y a b

private lemma zeroBaseChange_unit
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A]
    (f : R →+* A) (M N : ModuleCat.{max uR uA v} R)
    (x : M) (y : N) :
    let := f.toAlgebra
    zeroBaseChange R A f M N (((1 : A) ⊗ₜ[R] x) ⊗ₜ[A] ((1 : A) ⊗ₜ[R] y)) =
      (1 : A) ⊗ₜ[R] (x ⊗ₜ[R] y) := by
  let := f.toAlgebra
  simpa only [one_mul] using zeroBaseChange_tmul f M N 1 1 x y

private def chainTensorZeroIso
    {S : Type uA} [CommRing S]
    (K L : ChainComplex (ModuleCat.{max uR uA v} S) ℕ) :
    (chainTensor.{uR, uA, v} K L).X 0 ≅
      ((ModuleCat.moduleTensorLarge.{uA, max uR v} S).obj (K.X 0)).obj (L.X 0) where
  hom := mapBifunctorDesc fun p q h ↦ by
    have hp : p = 0 := by change p + q = 0 at h; omega
    have hq : q = 0 := by change p + q = 0 at h; omega
    subst p q
    exact 𝟙 _
  inv := ιMapBifunctor K L _ _ 0 0 0 rfl
  hom_inv_id := by
    apply mapBifunctor.hom_ext
    intro p q h
    have hp : p = 0 := by change p + q = 0 at h; omega
    have hq : q = 0 := by change p + q = 0 at h; omega
    subst p q
    simp
  inv_hom_id := by simp

private lemma chainTensorZeroIso_inv
    {S : Type uA} [CommRing S]
    (K L : ChainComplex (ModuleCat.{max uR uA v} S) ℕ) :
    (chainTensorZeroIso.{uR, uA, v} K L).inv = ιMapBifunctor K L
      (ModuleCat.moduleTensorLarge.{uA, max uR v} S) (ComplexShape.down ℕ) 0 0 0 rfl := rfl

private lemma moduleTensorMap_eq_tensorHom
    {S : Type uA} [CommRing S]
    {M M' N N' : ModuleCat.{max uR uA v} S} (f : M ⟶ M') (g : N ⟶ N') :
    let := ModuleCat.liftedModuleMonoidal.{uA, max uR v} (R := S)
    moduleTensorMap.{uR, uA, v} f g = f ⊗ₘ g := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext x y
  rfl

private lemma chainTensor_augmentation_zero
    {R : Type uR} [CommRing R]
    {M N : ModuleCat.{max uR uA v} R}
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) :
    (chainTensor.{uA, uR, v} P.complex Q.complex).d 1 0 ≫
      (chainTensorZeroIso.{uA, uR, v} P.complex Q.complex).hom ≫
      moduleTensorMap.{uA, uR, v} (P.π.f 0) (Q.π.f 0) = 0 := by
  let := ModuleCat.liftedModuleMonoidal.{uR, max uA v} (R := R)
  let := ModuleCat.liftedModuleMonoidalPreadditive.{uR, max uA v} (R := R)
  apply mapBifunctor.hom_ext
  intro p q h
  change p + q = 1 at h
  rw [mapBifunctor.d_eq]
  simp only [Preadditive.add_comp, Preadditive.comp_add, mapBifunctor.ι_D₁_assoc,
    mapBifunctor.ι_D₂_assoc]
  rcases Nat.add_eq_one_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [mapBifunctor.d₁_eq_zero P.complex Q.complex _ (ComplexShape.down ℕ) 0 1 0
        (by decide),
      mapBifunctor.d₂_eq P.complex Q.complex _ (ComplexShape.down ℕ) 0
        (show (ComplexShape.down ℕ).Rel 1 0 by simp) 0 rfl]
    rw [show ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (0, 1) = 1 from rfl]
    simp only [one_smul, zero_comp, comp_zero, zero_add, Category.assoc,
      ← (chainTensorZeroIso_inv.{uA, uR, v} P.complex Q.complex), Iso.inv_hom_id_assoc,
      moduleTensorMap_eq_tensorHom]
    show (P.complex.X 0 ◁ Q.complex.d 1 0) ≫ (P.π.f 0 ⊗ₘ Q.π.f 0) = 0
    simp [MonoidalCategory.tensorHom_def', ← MonoidalCategory.whiskerLeft_comp_assoc]
  · rw [mapBifunctor.d₁_eq P.complex Q.complex _ (ComplexShape.down ℕ)
        (show (ComplexShape.down ℕ).Rel 1 0 by simp) 0 0 rfl,
      mapBifunctor.d₂_eq_zero P.complex Q.complex _ (ComplexShape.down ℕ) 1 0 0
        (by decide)]
    rw [show ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (1, 0) = 1 from rfl]
    simp only [one_smul, zero_comp, comp_zero, add_zero, Category.assoc,
      ← (chainTensorZeroIso_inv.{uA, uR, v} P.complex Q.complex), Iso.inv_hom_id_assoc,
      moduleTensorMap_eq_tensorHom]
    show (P.complex.d 1 0 ▷ Q.complex.X 0) ≫ (P.π.f 0 ⊗ₘ Q.π.f 0) = 0
    simp [MonoidalCategory.tensorHom_def, ← MonoidalCategory.comp_whiskerRight_assoc]

private def chainTensorAugmentation
    {R : Type uR} [CommRing R]
    {M N : ModuleCat.{max uR uA v} R}
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) :
    chainTensor.{uA, uR, v} P.complex Q.complex ⟶
      (ChainComplex.single₀ _).obj (((ModuleCat.moduleTensorLarge.{uR, max uA v} R).obj M).obj N) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨(chainTensorZeroIso.{uA, uR, v} P.complex Q.complex).hom ≫
      moduleTensorMap.{uA, uR, v} (P.π.f 0) (Q.π.f 0),
      chainTensor_augmentation_zero.{uR, uA, v} P Q⟩

public section

lemma exists_normalized_comparison
    {R : Type uR} [CommRing R]
    {M N : ModuleCat.{max uR uA v} R}
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
    (T : ProjectiveResolution
      (((ModuleCat.moduleTensorLarge.{uR, max uA v} R).obj M).obj N)) :
    ∃ μ : chainTensor.{uA, uR, v} P.complex Q.complex ⟶ T.complex,
      ιMapBifunctor P.complex Q.complex (ModuleCat.moduleTensorLarge.{uR, max uA v} R)
        (ComplexShape.down ℕ) 0 0 0 rfl ≫ μ.f 0 ≫ T.π.f 0 =
          moduleTensorMap.{uA, uR, v} (P.π.f 0) (Q.π.f 0) ∧
      ∀ ν : chainTensor.{uA, uR, v} P.complex Q.complex ⟶ T.complex,
        (ιMapBifunctor P.complex Q.complex (ModuleCat.moduleTensorLarge.{uR, max uA v} R)
          (ComplexShape.down ℕ) 0 0 0 rfl ≫ ν.f 0 ≫ T.π.f 0 =
            moduleTensorMap.{uA, uR, v} (P.π.f 0) (Q.π.f 0)) → Nonempty (Homotopy μ ν) := by
  have (n : ℕ) : Projective ((chainTensor.{uA, uR, v} P.complex Q.complex).X n) :=
    projective_chainTensor.{uA, uR, v} P.complex Q.complex n
  let γ := chainTensorAugmentation.{uR, uA, v} P Q
  obtain ⟨μ, hμ⟩ := chain_exists_lift_resolution _ T γ
  have hγ : γ.f 0 = (chainTensorZeroIso.{uA, uR, v} P.complex Q.complex).hom ≫
      moduleTensorMap.{uA, uR, v} (P.π.f 0) (Q.π.f 0) :=
    ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _
  have hμ₀ := congr_hom hμ 0
  change μ.f 0 ≫ T.π.f 0 = γ.f 0 at hμ₀
  refine ⟨μ, ?_, fun ν hν ↦ ?_⟩
  · rw [hμ₀, hγ, ← (chainTensorZeroIso_inv.{uA, uR, v} P.complex Q.complex), Iso.inv_hom_id_assoc]
  · have hν' : ν ≫ T.π = γ := by
      apply to_single_hom_ext
      show ν.f 0 ≫ T.π.f 0 = γ.f 0
      rw [hγ, ← cancel_epi (chainTensorZeroIso.{uA, uR, v} P.complex Q.complex).inv,
        Iso.inv_hom_id_assoc, (chainTensorZeroIso_inv.{uA, uR, v} P.complex Q.complex)]
      exact hν
    exact chain_nonempty_homotopy_of_comp_quasiIso T.π (Homotopy.ofEq (hμ.trans hν'.symm))

lemma moduleTensorMap_comp
    {S : Type uA} [CommRing S]
    {M M' M'' N N' N'' : ModuleCat.{max uR uA v} S}
    (f : M ⟶ M') (f' : M' ⟶ M'') (g : N ⟶ N') (g' : N' ⟶ N'') :
    moduleTensorMap.{uR, uA, v} f g ≫ moduleTensorMap.{uR, uA, v} f' g' =
      moduleTensorMap.{uR, uA, v} (f ≫ f') (g ≫ g') := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext x y
  rfl

lemma comparison_homotopy
    {R : Type uR} [CommRing R]
    {M M' N N' : ModuleCat.{max uR uA v} R} (g : M ⟶ M') (h : N ⟶ N')
    {P : ProjectiveResolution M} {P' : ProjectiveResolution M'}
    {Q : ProjectiveResolution N} {Q' : ProjectiveResolution N'}
    {T : ProjectiveResolution (((ModuleCat.moduleTensorLarge.{uR, max uA v} R).obj M).obj N)}
    {T' : ProjectiveResolution (((ModuleCat.moduleTensorLarge.{uR, max uA v} R).obj M').obj N')}
    (φ : P.complex ⟶ P'.complex) (hφ : φ.f 0 ≫ P'.π.f 0 = P.π.f 0 ≫ g)
    (ψ : Q.complex ⟶ Q'.complex) (hψ : ψ.f 0 ≫ Q'.π.f 0 = Q.π.f 0 ≫ h)
    (χ : T.complex ⟶ T'.complex)
    (hχ : χ.f 0 ≫ T'.π.f 0 = T.π.f 0 ≫ moduleTensorMap.{uA, uR, v} g h)
    (μ : chainTensor.{uA, uR, v} P.complex Q.complex ⟶ T.complex)
    (hμ : ιMapBifunctor P.complex Q.complex (ModuleCat.moduleTensorLarge.{uR, max uA v} R)
        (ComplexShape.down ℕ) 0 0 0 rfl ≫ μ.f 0 ≫ T.π.f 0 =
      moduleTensorMap.{uA, uR, v} (P.π.f 0) (Q.π.f 0))
    (μ' : chainTensor.{uA, uR, v} P'.complex Q'.complex ⟶ T'.complex)
    (hμ' : ιMapBifunctor P'.complex Q'.complex (ModuleCat.moduleTensorLarge.{uR, max uA v} R)
        (ComplexShape.down ℕ) 0 0 0 rfl ≫ μ'.f 0 ≫ T'.π.f 0 =
      moduleTensorMap.{uA, uR, v} (P'.π.f 0) (Q'.π.f 0)) :
    Nonempty (Homotopy (μ ≫ χ)
      (mapBifunctorMap φ ψ (ModuleCat.moduleTensorLarge.{uR, max uA v} R)
        (ComplexShape.down ℕ) ≫ μ')) := by
  have (n : ℕ) : Projective ((chainTensor.{uA, uR, v} P.complex Q.complex).X n) :=
    projective_chainTensor.{uA, uR, v} P.complex Q.complex n
  refine chain_nonempty_homotopy_of_comp_quasiIso T'.π (Homotopy.ofEq ?_)
  apply to_single_hom_ext
  simp only [HomologicalComplex.comp_f, Category.assoc]
  apply mapBifunctor.hom_ext
  intro p q hpq
  obtain ⟨rfl, rfl⟩ := Nat.add_eq_zero_iff.mp hpq
  rw [hχ, reassoc_of% hμ, ι_mapBifunctorMap_assoc]
  show moduleTensorMap.{uA, uR, v} _ _ ≫ _ = moduleTensorMap.{uA, uR, v} (φ.f 0) (ψ.f 0) ≫
    ιMapBifunctor P'.complex Q'.complex _ _ 0 0 0 rfl ≫ μ'.f 0 ≫ T'.π.f 0
  rw [hμ', moduleTensorMap_comp, moduleTensorMap_comp, hφ, hψ]

end

section CycleProduct

variable {A : Type uA} [CommRing A]

section Generic

variable (K L : ChainComplex (ModuleCat.{max uA w} A) ℕ)

/-- Tensoring with a map killed by `d` on the left kills the first differential component. -/
private lemma tensorHom_comp_d₁_eq_zero {X Y : ModuleCat.{max uA w} A} (n m j : ℕ)
    (a : X ⟶ K.X n) (b : Y ⟶ L.X m) (ha : a ≫ K.d n ((ComplexShape.down ℕ).next n) = 0) :
    (a ⊗ₘ b) ≫ mapBifunctor.d₁ K L (curriedTensor _) (ComplexShape.down ℕ) n m j = 0 := by
  by_cases hn : (ComplexShape.down ℕ).Rel n ((ComplexShape.down ℕ).next n)
  · rw [mapBifunctor.d₁_eq' _ _ _ _ hn, Linear.comp_units_smul, curriedTensor_map_app,
      MonoidalCategory.tensorHom_def', Category.assoc, ← comp_whiskerRight_assoc, ha]
    simp
  · rw [mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ hn, comp_zero]

/-- Tensoring with a map killed by `d` on the right kills the second differential component. -/
private lemma tensorHom_comp_d₂_eq_zero {X Y : ModuleCat.{max uA w} A} (n m j : ℕ)
    (a : X ⟶ K.X n) (b : Y ⟶ L.X m) (hb : b ≫ L.d m ((ComplexShape.down ℕ).next m) = 0) :
    (a ⊗ₘ b) ≫ mapBifunctor.d₂ K L (curriedTensor _) (ComplexShape.down ℕ) n m j = 0 := by
  by_cases hm : (ComplexShape.down ℕ).Rel m ((ComplexShape.down ℕ).next m)
  · rw [mapBifunctor.d₂_eq' _ _ _ _ _ hm, Linear.comp_units_smul, curriedTensor_obj_map,
      MonoidalCategory.tensorHom_def, Category.assoc, ← whiskerLeft_comp_assoc, hb]
    simp
  · rw [mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _ hm, comp_zero]

private lemma chainTensor_cycles_comp_d (n m j : ℕ) :
    ((K.iCycles n ⊗ₘ L.iCycles m) ≫
        ιMapBifunctor K L (curriedTensor _) (ComplexShape.down ℕ) n m (n + m) rfl) ≫
      (mapBifunctor K L (curriedTensor _) (ComplexShape.down ℕ)).d (n + m) j = 0 := by
  rw [mapBifunctor.d_eq, Preadditive.comp_add]
  simp only [Category.assoc, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂]
  rw [tensorHom_comp_d₁_eq_zero K L n m j _ _ (by simp),
    tensorHom_comp_d₂_eq_zero K L n m j _ _ (by simp), add_zero]

private noncomputable def chainTensorCycles (n m : ℕ) :
    K.cycles n ⊗ L.cycles m ⟶
      (mapBifunctor K L (curriedTensor _) (ComplexShape.down ℕ)).cycles (n + m) :=
  (mapBifunctor K L (curriedTensor _) (ComplexShape.down ℕ)).liftCycles
    ((K.iCycles n ⊗ₘ L.iCycles m) ≫
      ιMapBifunctor K L (curriedTensor _) (ComplexShape.down ℕ) n m (n + m) rfl)
    _ rfl (chainTensor_cycles_comp_d K L n m _)

private lemma chainTensorCycles_i (n m : ℕ) :
    chainTensorCycles K L n m ≫
      (mapBifunctor K L (curriedTensor _) (ComplexShape.down ℕ)).iCycles (n + m) =
      (K.iCycles n ⊗ₘ L.iCycles m) ≫
        ιMapBifunctor K L (curriedTensor _) (ComplexShape.down ℕ) n m (n + m) rfl :=
  liftCycles_i _ _ _ _ _

private lemma chainTensorCycles_left_boundary (n m : ℕ) :
    (K.toCycles (n + 1) n ⊗ₘ 𝟙 (L.cycles m)) ≫ chainTensorCycles K L n m ≫
      (mapBifunctor K L (curriedTensor _) (ComplexShape.down ℕ)).homologyπ (n + m) = 0 := by
  let x : K.X (n + 1) ⊗ L.cycles m ⟶
      (mapBifunctor K L (curriedTensor _) (ComplexShape.down ℕ)).X (n + m + 1) :=
    (𝟙 _ ⊗ₘ L.iCycles m) ≫
      ιMapBifunctor K L (curriedTensor _) (ComplexShape.down ℕ) (n + 1) m (n + m + 1)
        (by change n + 1 + m = n + m + 1; omega)
  have h : (K.toCycles (n + 1) n ⊗ₘ 𝟙 (L.cycles m)) ≫ chainTensorCycles K L n m =
      x ≫ (mapBifunctor K L (curriedTensor _) (ComplexShape.down ℕ)).toCycles
        (n + m + 1) (n + m) := by
    rw [← cancel_mono ((mapBifunctor K L (curriedTensor _) (ComplexShape.down ℕ)).iCycles
      (n + m))]
    simp only [Category.assoc, chainTensorCycles_i, toCycles_i, x]
    rw [mapBifunctor.d_eq, Preadditive.comp_add, Preadditive.comp_add]
    simp only [mapBifunctor.ι_D₁, mapBifunctor.ι_D₂]
    rw [tensorHom_comp_d₂_eq_zero K L (n + 1) m (n + m) _ _ (by simp), add_zero,
      mapBifunctor.d₁_eq K L (curriedTensor _) _
        (show (ComplexShape.down ℕ).Rel (n + 1) n by simp) m (n + m) rfl]
    rw [show ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (n + 1, m) = 1 from rfl, one_smul, curriedTensor_map_app]
    simp only [MonoidalCategory.tensorHom_def, ← comp_whiskerRight_assoc, toCycles_i,
      id_whiskerRight, Category.id_comp, Category.assoc, whisker_exchange_assoc,
      MonoidalCategory.whiskerLeft_id]
  rw [← Category.assoc, h, Category.assoc, toCycles_comp_homologyπ, comp_zero]

private lemma chainTensorCycles_right_boundary (n m : ℕ) :
    (𝟙 (K.cycles n) ⊗ₘ L.toCycles (m + 1) m) ≫ chainTensorCycles K L n m ≫
      (mapBifunctor K L (curriedTensor _) (ComplexShape.down ℕ)).homologyπ (n + m) = 0 := by
  let ε : ℤˣ := ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
    (ComplexShape.down ℕ) ⟨n, m + 1⟩
  let x : K.cycles n ⊗ L.X (m + 1) ⟶
      (mapBifunctor K L (curriedTensor _) (ComplexShape.down ℕ)).X (n + m + 1) :=
    ε • ((K.iCycles n ⊗ₘ 𝟙 _) ≫
      ιMapBifunctor K L (curriedTensor _) (ComplexShape.down ℕ) n (m + 1) (n + m + 1)
        (by change n + (m + 1) = n + m + 1; omega))
  have h : (𝟙 (K.cycles n) ⊗ₘ L.toCycles (m + 1) m) ≫ chainTensorCycles K L n m =
      x ≫ (mapBifunctor K L (curriedTensor _) (ComplexShape.down ℕ)).toCycles
        (n + m + 1) (n + m) := by
    rw [← cancel_mono ((mapBifunctor K L (curriedTensor _) (ComplexShape.down ℕ)).iCycles
      (n + m))]
    simp only [Category.assoc, chainTensorCycles_i, toCycles_i, x, Linear.units_smul_comp]
    rw [mapBifunctor.d_eq, Preadditive.comp_add, Preadditive.comp_add]
    simp only [mapBifunctor.ι_D₁, mapBifunctor.ι_D₂]
    rw [tensorHom_comp_d₁_eq_zero K L n (m + 1) (n + m) _ _ (by simp), zero_add,
      mapBifunctor.d₂_eq K L (curriedTensor _) _ n
        (show (ComplexShape.down ℕ).Rel (m + 1) m by simp) (n + m) rfl,
      Linear.comp_units_smul, smul_smul, Int.units_mul_self, one_smul, curriedTensor_obj_map]
    simp only [MonoidalCategory.tensorHom_def', ← whiskerLeft_comp_assoc, toCycles_i,
      MonoidalCategory.whiskerLeft_id, Category.id_comp, Category.assoc, whisker_exchange_assoc,
      id_whiskerRight]
  rw [← Category.assoc, h, Category.assoc, toCycles_comp_homologyπ, comp_zero]

private noncomputable def tensorRightIsoTensorLeft (M : ModuleCat.{max uA w} A) :
    tensorRight M ≅ tensorLeft M :=
  NatIso.ofComponents (fun N ↦ (TensorProduct.comm A N M).toModuleIso) fun f ↦ by
    ext : 1
    apply TensorProduct.ext'
    intro x y
    rfl

private lemma preservesColimit_tensorRight (M : ModuleCat.{max uA w} A)
    {X Y : ModuleCat.{max uA w} A} (g : X ⟶ Y) :
    PreservesColimit (parallelPair g 0) (tensorRight M) :=
  preservesColimit_of_natIso _ (tensorRightIsoTensorLeft M).symm

private noncomputable def chainTensorHomology (n m : ℕ) :
    K.homology n ⊗ L.homology m ⟶
      (mapBifunctor K L (curriedTensor _) (ComplexShape.down ℕ)).homology (n + m) := by
  let k := chainTensorCycles K L n m ≫
    (mapBifunctor K L (curriedTensor _) (ComplexShape.down ℕ)).homologyπ (n + m)
  have hk : coprod.desc (K.toCycles (n + 1) n ▷ L.cycles m)
      (K.cycles n ◁ L.toCycles (m + 1) m) ≫ k = 0 := by
    apply coprod.hom_ext
    · simpa [k, ← tensorHom_id] using chainTensorCycles_left_boundary K L n m
    · simpa [k, ← id_tensorHom] using chainTensorCycles_right_boundary K L n m
  have := preservesColimit_tensorRight (L.cycles m) (K.toCycles (n + 1) n)
  have := preservesColimit_tensorRight (L.X (m + 1)) (K.toCycles (n + 1) n)
  exact (CokernelCofork.isColimitTensor
    (K.homologyIsCokernel (n + 1) n (by simp))
    (L.homologyIsCokernel (m + 1) m (by simp))).desc (CokernelCofork.ofπ k hk)

private lemma homologyπ_chainTensorHomology (n m : ℕ) :
    (K.homologyπ n ⊗ₘ L.homologyπ m) ≫ chainTensorHomology K L n m =
      chainTensorCycles K L n m ≫
        (mapBifunctor K L (curriedTensor _) (ComplexShape.down ℕ)).homologyπ (n + m) := by
  have := preservesColimit_tensorRight (L.cycles m) (K.toCycles (n + 1) n)
  have := preservesColimit_tensorRight (L.X (m + 1)) (K.toCycles (n + 1) n)
  exact Cofork.IsColimit.π_desc (hs := CokernelCofork.isColimitTensor
    (K.homologyIsCokernel (n + 1) n (by simp))
    (L.homologyIsCokernel (m + 1) m (by simp))) (t := CokernelCofork.ofπ _ _)

variable {K L} in
private lemma chainTensorCycles_naturality {K' L' : ChainComplex (ModuleCat.{max uA w} A) ℕ}
    (φ : K ⟶ K') (ψ : L ⟶ L') (n m : ℕ) :
    (cyclesMap φ n ⊗ₘ cyclesMap ψ m) ≫ chainTensorCycles K' L' n m =
      chainTensorCycles K L n m ≫
        cyclesMap (mapBifunctorMap φ ψ (curriedTensor _) (ComplexShape.down ℕ)) (n + m) := by
  rw [← cancel_mono (iCycles _ _), Category.assoc, chainTensorCycles_i, Category.assoc,
    cyclesMap_i, reassoc_of% chainTensorCycles_i, ι_mapBifunctorMap,
    curriedTensor_map_app, curriedTensor_obj_map, ← tensorHom_def_assoc,
    tensorHom_comp_tensorHom_assoc, cyclesMap_i, cyclesMap_i, tensorHom_comp_tensorHom_assoc]

variable {K L} in
private lemma chainTensorHomology_naturality {K' L' : ChainComplex (ModuleCat.{max uA w} A) ℕ}
    (φ : K ⟶ K') (ψ : L ⟶ L') (n m : ℕ) :
    (homologyMap φ n ⊗ₘ homologyMap ψ m) ≫ chainTensorHomology K' L' n m =
      chainTensorHomology K L n m ≫
        homologyMap (mapBifunctorMap φ ψ (curriedTensor _) (ComplexShape.down ℕ)) (n + m) := by
  have := preservesColimit_tensorRight (L.cycles m) (K.toCycles (n + 1) n)
  have := preservesColimit_tensorRight (L.X (m + 1)) (K.toCycles (n + 1) n)
  apply Cofork.IsColimit.hom_ext (CokernelCofork.isColimitTensor
    (K.homologyIsCokernel (n + 1) n (by simp))
    (L.homologyIsCokernel (m + 1) m (by simp)))
  show (K.homologyπ n ⊗ₘ L.homologyπ m) ≫ _ = (K.homologyπ n ⊗ₘ L.homologyπ m) ≫ _
  rw [tensorHom_comp_tensorHom_assoc, homologyπ_naturality, homologyπ_naturality,
    ← tensorHom_comp_tensorHom_assoc, homologyπ_chainTensorHomology,
    ← Category.assoc, chainTensorCycles_naturality, Category.assoc, ← homologyπ_naturality,
    ← Category.assoc, ← homologyπ_chainTensorHomology, Category.assoc]

end Generic

public section

/-- The homology cross product of two chain complexes, induced by tensoring cycles. -/
noncomputable def chainHomologyProductOfCycles
    (K L : ChainComplex (ModuleCat.{max uR uA v} A) ℕ) (n m : ℕ) :
    TorCrossProduct.ChainHomologyProduct.{uR, uA, v} A K L n m where
  map := chainTensorHomology.{uA, max uR v} K L n m
  maps_cycles := ⟨chainTensorCycles.{uA, max uR v} K L n m, by
    rw [moduleTensorMap_eq_tensorHom.{uR, uA, v}]
    exact chainTensorCycles_i.{uA, max uR v} K L n m, by
    rw [moduleTensorMap_eq_tensorHom.{uR, uA, v}]
    exact homologyπ_chainTensorHomology.{uA, max uR v} K L n m⟩

lemma chainHomologyProductOfCycles_naturality
    {K K' L L' : ChainComplex (ModuleCat.{max uR uA v} A) ℕ}
    (φ : K ⟶ K') (ψ : L ⟶ L') (n m : ℕ) :
    moduleTensorMap.{uR, uA, v} (homologyMap φ n) (homologyMap ψ m) ≫
        (chainHomologyProductOfCycles.{uR, uA, v} K' L' n m).map =
      (chainHomologyProductOfCycles.{uR, uA, v} K L n m).map ≫
        homologyMap (mapBifunctorMap φ ψ (ModuleCat.moduleTensorLarge.{uA, max uR v} A)
          (ComplexShape.down ℕ)) (n + m) := by
  rw [moduleTensorMap_eq_tensorHom.{uR, uA, v}]
  exact chainTensorHomology_naturality.{uA, max uR v} φ ψ n m

end

end CycleProduct

end TorCrossProduct

end

module

public import StacksFrontier.Homology.DerivedCategory.InverseSystem.DerivedLimitEventualFactorisation
public import StacksFrontier.Homology.DerivedComplete.DerivedHomCompletionTorSequence
public import StacksFrontier.Homology.DerivedComplete.MilnorEpiTower
public import StacksFrontier.Homology.DerivedComplete.NoetherianCompleteIdealPowers
public import StacksFrontier.Homology.TensorComplex.SingleTensor
public import StacksFrontier.Homology.Tor.DerivedTensorFlatBaseChange

/-!
# Maps from the adic completion of a flat module into a derived complete module

Let `Λ` be a Noetherian ring, `I ⊆ Λ` an ideal, `A` a flat `Λ`-module and `M` a derived complete
`Λ`-module. Every `Λ`-linear map `A → M` extends uniquely along the completion map `A → Â` to a
`Λ`-linear map `Â → M`: the `I`-adic completion `Â` is the derived completion of `A`.

The proof computes the derived completion by Stacks 0922: the reflection of `A[0]` is the
derived limit of the tower `A ⊗_Λ^L Λ/Iⁿ⁺¹`. As `A` is flat these are the modules `A/Iⁿ⁺¹A` in
degree zero, a tower with surjective transition maps, whose derived limit is its limit placed in
degree zero. Comparing the two derived limits identifies the reflection of `A[0]` with
`Â[0]`, and the unit with the completion map up to an automorphism of `A`.

## Main results

* `NoetherianAdicCompletion.bijective_comp_of_flat_of_isLimit`: maps from the completion of a
  flat module into a derived complete module are the maps from the module.
* `NoetherianAdicCompletion.exists_iso_reflection_single_of_flat`: the derived completion of a
  flat module placed in degree zero is its adic completion.
* `NoetherianAdicCompletion.IsDerivedLimitWithProjections.exists_iso`: two derived limits of
  the same tower, with projections, are isomorphic compatibly with the projections.
* `NoetherianAdicCompletion.isDerivedLimitWithProjections_single_of_isLimit`: the limit of a
  tower of modules with surjective transition maps is its derived limit.
* `NoetherianAdicCompletion.singleFunctorCompTensorObjSingleIso`: the derived tensor product
  with a flat module is the ordinary one.

## Implementation notes

Stacks 0922 computes the derived tensor products over `ULift Λ`; the module universe is that of
`Λ`, so that this change of rings is an equivalence of module categories and of derived
categories, through which the comparison is transported back to `Λ`. The completion is
represented by an arbitrary limit cone of the tower `n ↦ A/Iⁿ⁺¹A`.

## References

* [Stacks Project, Tag 0922](https://stacks.math.columbia.edu/tag/0922)
* [Stacks Project, Tag 0EEU](https://stacks.math.columbia.edu/tag/0EEU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u v

namespace NoetherianAdicCompletion

section Triangulated

variable {D : Type*} [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **Derived limits with projections are unique up to a compatible isomorphism.** -/
theorem IsDerivedLimitWithProjections.exists_iso {F : ℕᵒᵖ ⥤ D}
    [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩] {K K' : D} {p : ∀ n : ℕ, K ⟶ F.obj ⟨n⟩}
    {p' : ∀ n : ℕ, K' ⟶ F.obj ⟨n⟩} (h : IsDerivedLimitWithProjections F K p)
    (h' : IsDerivedLimitWithProjections F K' p') :
    ∃ e : K ≅ K', ∀ n, e.hom ≫ p' n = p n := by
  obtain ⟨δ, hδ⟩ := h
  obtain ⟨δ', hδ'⟩ := h'
  obtain ⟨a, ha₁, ha₃⟩ := complete_distinguished_triangle_morphism₁ _ _ hδ hδ' (𝟙 _) (𝟙 _)
    (by simp)
  let φ : Triangle.mk (Pi.lift p) _ δ ⟶ Triangle.mk (Pi.lift p') _ δ' :=
    { hom₁ := a, hom₂ := 𝟙 _, hom₃ := 𝟙 _, comm₁ := ha₁, comm₂ := by simp
      comm₃ := ha₃ }
  have : IsIso a := isIso₁_of_isIso₂₃ φ hδ hδ' (by dsimp [φ]; infer_instance)
    (by dsimp [φ]; infer_instance)
  refine ⟨asIso a, fun n => ?_⟩
  simpa using congrArg (· ≫ Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n) ha₁.symm

end Triangulated

section Modules

variable {R : Type u} [Ring R]

attribute [local instance] HasDerivedCategory.standard

/-- Countable products are exact in the category of `R`-modules. -/
local instance : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{v} R) :=
  moduleCat_hasExactLimitsOfShape_discrete.{v} R ℕ

/-- The derived category of `R`-modules has countable products. -/
local instance : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} R)) :=
  Stacks.DerivedProducts.hasProductsOfShape_derivedCategory

/-- **The limit of a tower of complexes of modules with epimorphic transition maps is its
derived limit**, with the images of the legs of a limit cone as projections. -/
theorem isDerivedLimitWithProjections_Q_of_isLimit
    {F : ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} R) ℤ}
    [∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)] (s : Cone F) (hs : IsLimit s) :
    IsDerivedLimitWithProjections (F ⋙ DerivedCategory.Q) (DerivedCategory.Q.obj s.pt)
      (fun n => DerivedCategory.Q.map (s.π.app ⟨n⟩)) := by
  have hS := CountableMilnorTower.shortExact_ofCone s hs
  have hT := DerivedCategory.triangleOfSES_distinguished hS
  have : PreservesLimitsOfShape (Discrete ℕ) (DerivedCategory.Q (C := ModuleCat.{v} R)) :=
    Stacks.DerivedProducts.preservesLimitsOfShape_Q
  let e := PreservesProduct.iso DerivedCategory.Q (fun n : ℕ ↦ F.obj ⟨n⟩)
  let T₂ : Triangle (DerivedCategory (ModuleCat.{v} R)) :=
    Triangle.mk (Pi.lift fun n ↦ DerivedCategory.Q.map (s.π.app (op n)))
      (Pi.lift fun n ↦ Pi.π (fun n ↦ DerivedCategory.Q.obj (F.obj (op n))) n -
        Pi.π (fun n ↦ DerivedCategory.Q.obj (F.obj (op n))) (n + 1) ≫
          DerivedCategory.Q.map (F.map (homOfLE (Nat.le_succ n)).op))
      (e.inv ≫ (DerivedCategory.triangleOfSES hS).mor₃)
  refine ⟨e.inv ≫ (DerivedCategory.triangleOfSES hS).mor₃,
    isomorphic_distinguished _ hT T₂
      (Triangle.isoMk (DerivedCategory.triangleOfSES hS) T₂ (Iso.refl _) e e
      ?_ ?_ ?_).symm⟩
  · apply Pi.hom_ext
    intro n
    simp only [Category.assoc, piComparison_comp_π, T₂, Triangle.mk_mor₁,
      DerivedCategory.triangleOfSES, Triangle.mk_obj₁, e, PreservesProduct.iso_hom,
      Iso.refl_hom]
    rw [← Functor.map_comp]
    simp [CountableMilnorTower.TowerAugmentation.productLift]
    rfl
  · apply Pi.hom_ext
    intro n
    simp only [Category.assoc, piComparison_comp_π, T₂, Triangle.mk_mor₂, Pi.lift_π,
      DerivedCategory.triangleOfSES, Preadditive.comp_sub, e,
      PreservesProduct.iso_hom]
    simp only [piComparison_comp_π_assoc]
    rw [← Functor.map_comp, CountableMilnorTower.oneMinusShift_π, Functor.map_sub,
      Functor.map_comp]
  · show _ ≫ (shiftFunctor _ (1 : ℤ)).map (𝟙 _) = e.hom ≫ e.inv ≫ _
    simp only [CategoryTheory.Functor.map_id]
    exact (Category.comp_id _).trans (e.hom_inv_id_assoc _).symm

end Modules

section FlatTensor

open MonoidalCategory

variable {R : Type u} [CommRing R]

attribute [local instance] HasDerivedCategory.standard

/-- **The derived tensor product with a flat module is the ordinary one**, naturally in the
second module: for a flat `R`-module `P`, `P ⊗_R^L N ≅ (P ⊗_R N)[0]` for every `R`-module `N`. -/
def singleFunctorCompTensorObjSingleIso
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct R) (P : ModuleCat.{u} R)
    [Module.Flat R P] :
    DerivedCategory.singleFunctor (ModuleCat.{u} R) 0 ⋙
        T.tensor.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj P) ≅
      tensorLeft P ⋙ DerivedCategory.singleFunctor (ModuleCat.{u} R) 0 :=
  let K := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj P
  let hK : K.KFlat := CochainComplex.DerivedTensor.kFlat_single_of_flat P
  let eS := DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0
  Functor.isoWhiskerRight eS _ ≪≫
    Functor.isoWhiskerLeft _ (T.tensor.mapIso (eS.app P) ≪≫
      AdicCompletionTor.tensorKFlatIso T K hK) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Localization.fac _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (NatIso.ofComponents
      (fun N => TotalTensorComplex.SingleTensor.singleTensorIso P
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N))
      (fun f => by
        have h := TotalTensorComplex.SingleTensor.singleTensorIso_naturality P
          ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map f)
        rw [← cancel_epi (TotalTensorComplex.SingleTensor.singleTensorIso P _).inv,
          Iso.inv_hom_id_assoc]
        exact ((reassoc_of% h) _).trans (by rw [Iso.inv_hom_id, Category.comp_id]; rfl))) _ ≪≫
    Functor.isoWhiskerRight (HomologicalComplex.singleMapHomologicalComplex (tensorLeft P)
      (ComplexShape.up ℤ) 0) _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ eS.symm

end FlatTensor

section QuotientTower

variable {R : Type u} [CommRing R]

attribute [local instance] HasDerivedCategory.standard

/-- The isomorphism between a module in degree zero extended from `ℕ` and the module in degree
zero is natural. -/
theorem extendSingleIso_embeddingDownNat_hom_naturality {C : Type*} [Category C] [Abelian C]
    {M N : C} (f : M ⟶ N) :
    HomologicalComplex.extendMap ((ChainComplex.single₀ C).map f) ComplexShape.embeddingDownNat ≫
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat N 0 0 (by simp)).hom =
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat M 0 0 (by simp)).hom ≫
      (CochainComplex.singleFunctor C 0).map f := by
  apply HomologicalComplex.to_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    HomologicalComplex.extendMap_f _ _ (show ComplexShape.embeddingDownNat.f 0 = 0 by simp),
    HomologicalComplex.extendSingleIso_hom_f, HomologicalComplex.extendSingleIso_hom_f,
    HomologicalComplex.single_map_f_self]
  simp only [CochainComplex.singleFunctor, CochainComplex.singleFunctors,
    HomologicalComplex.single_map_f_self, Category.assoc, Iso.inv_hom_id_assoc]

/-- The comparison of the tower `n ↦ (R/Jⁿ⁺¹)[0]` of `D(R)` with the tower of modules
`n ↦ R/Jⁿ⁺¹` placed in degree zero. -/
def idealPowerQuotientSystemHom (J : Ideal R) :
    idealPowerQuotientSystem J ⟶
      AdicCompletionTor.idealPowerQuotientModuleSystem J ⋙
        DerivedCategory.singleFunctor (ModuleCat.{u} R) 0 :=
  NatTrans.ofOpSequence
      (fun n => DerivedCategory.Q.map (HomologicalComplex.extendSingleIso
        ComplexShape.embeddingDownNat (ModuleCat.of R (R ⧸ J ^ (n + 1))) 0 0 (by simp)).hom ≫
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app _).inv)
      (fun n => by
        let t := idealPowerQuotientTransition J (n + 1) n (Nat.le_succ n)
        let e₁ := HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
          (ModuleCat.of R (R ⧸ J ^ (n + 1 + 1))) 0 0 (by simp)
        let e₀ := HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
          (ModuleCat.of R (R ⧸ J ^ (n + 1))) 0 0 (by simp)
        let s := DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0
        unfold idealPowerQuotientSystem AdicCompletionTor.idealPowerQuotientModuleSystem
        rw [Functor.comp_map, Functor.ofOpSequence_map_homOfLE_succ,
          Functor.ofOpSequence_map_homOfLE_succ]
        change DerivedCategory.Q.map (HomologicalComplex.extendMap
            ((ChainComplex.single₀ (ModuleCat R)).map t) ComplexShape.embeddingDownNat) ≫
            (DerivedCategory.Q.map e₀.hom ≫ (s.app _).inv) =
          (DerivedCategory.Q.map e₁.hom ≫ (s.app _).inv) ≫
            (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map t
        rw [← Category.assoc, ← Functor.map_comp, extendSingleIso_embeddingDownNat_hom_naturality,
          Functor.map_comp, Category.assoc, Category.assoc]
        rw [Iso.app_inv, Iso.app_inv, ← s.inv.naturality t]
        rfl)

/-- The comparison `idealPowerQuotientSystemHom J` is an isomorphism. -/
instance (J : Ideal R) : IsIso (idealPowerQuotientSystemHom J) :=
  have (n : ℕᵒᵖ) : IsIso ((idealPowerQuotientSystemHom J).app n) := by
    obtain ⟨k⟩ := n
    rw [idealPowerQuotientSystemHom, NatTrans.ofOpSequence_app]
    exact IsIso.comp_isIso' (Iso.isIso_hom (DerivedCategory.Q.mapIso
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
        (ModuleCat.of R (R ⧸ J ^ (k + 1))) 0 0 (by simp)))) (Iso.isIso_inv _)
  NatIso.isIso_of_isIso_app _

/-- The tower `n ↦ (R/Jⁿ⁺¹)[0]` of `D(R)` is the tower of modules `n ↦ R/Jⁿ⁺¹` placed in degree
zero. -/
def idealPowerQuotientSystemIso (J : Ideal R) :
    idealPowerQuotientSystem J ≅
      AdicCompletionTor.idealPowerQuotientModuleSystem J ⋙
        DerivedCategory.singleFunctor (ModuleCat.{u} R) 0 :=
  asIso (idealPowerQuotientSystemHom J)

/-- The quotient map `R[0] ⟶ (R/Jⁿ⁺¹)[0]` of `D(R)`, read in the tower of modules placed in
degree zero, is the quotient map of modules placed in degree zero. -/
theorem idealPowerQuotientMap_comp_idealPowerQuotientSystemIso_hom (J : Ideal R) (n : ℕ) :
    idealPowerQuotientMap J n ≫ (idealPowerQuotientSystemIso J).hom.app ⟨n⟩ =
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
        (ModuleCat.ofHom (J ^ (n + 1)).mkQ) := by
  rw [idealPowerQuotientSystemIso, asIso_hom, idealPowerQuotientSystemHom,
    NatTrans.ofOpSequence_app, idealPowerQuotientMap]
  simp [DerivedCategory.singleFunctorIsoCompQ]

end QuotientTower

section UniverseLift

variable {Λ : Type u} [CommRing Λ]

/-- Lifting `Λ`-modules to the same universe is essentially surjective. -/
instance : (ModuleCat.uliftFunctor.{u, u} Λ).EssSurj :=
  ⟨fun N => ⟨N, ⟨(ULift.moduleEquiv : ULift.{u} N ≃ₗ[Λ] N).toModuleIso⟩⟩⟩

/-- Lifting `Λ`-modules to the same universe is an equivalence. -/
instance : (ModuleCat.uliftFunctor.{u, u} Λ).IsEquivalence where

/-- The passage from `Λ`-modules to `ULift Λ`-modules is an equivalence. -/
instance : (AdicKoszul.moduleUniverseLift.{u, u} Λ).IsEquivalence := by
  have := ModuleCat.restrictScalars_isEquivalence_of_ringEquiv
    (ULift.ringEquiv : ULift.{u} Λ ≃+* Λ)
  unfold AdicKoszul.moduleUniverseLift
  infer_instance

attribute [local instance] HasDerivedCategory.standard

/-- The functor `D(Λ) ⥤ D(ULift Λ)` induced by the change of rings is an equivalence. -/
instance : (AdicKoszul.derivedUniverseLift.{u, u} Λ).IsEquivalence :=
  Stacks.Injectives.mapDerivedCategory_isEquivalence _

/-- The ideal of `ULift Λ` corresponding to an ideal of `Λ`. -/
abbrev uliftIdeal (I : Ideal Λ) : Ideal (ULift.{u} Λ) :=
  I.comap (ULift.ringEquiv : ULift.{u} Λ ≃+* Λ).toRingHom

/-- An element of `ULift Λ` lies in `(uliftIdeal I) ^ n` if and only if its underlying element
lies in `I ^ n`. -/
theorem mem_uliftIdeal_pow_iff (I : Ideal Λ) (n : ℕ) (r : ULift.{u} Λ) :
    r ∈ uliftIdeal I ^ n ↔ r.down ∈ I ^ n := by
  have h : uliftIdeal I ^ n = (I ^ n).comap (ULift.ringEquiv : ULift.{u} Λ ≃+* Λ).toRingHom := by
    have e (K : Ideal Λ) : K.comap (ULift.ringEquiv : ULift.{u} Λ ≃+* Λ).toRingHom =
        K.map (ULift.ringEquiv : ULift.{u} Λ ≃+* Λ).symm.toRingHom :=
      Ideal.comap_symm (I := K) (ULift.ringEquiv : ULift.{u} Λ ≃+* Λ).symm
    rw [uliftIdeal, e, e, Ideal.map_pow]
  rw [h, Ideal.mem_comap]
  rfl

/-- An element of the lift of `A` to `ULift Λ` lies in `(uliftIdeal I) ^ n • ⊤` if and only if
its underlying element lies in `I ^ n • ⊤`. -/
theorem down_mem_smul_top_iff (I : Ideal Λ) (n : ℕ) (A : ModuleCat.{u} Λ)
    (x : (AdicKoszul.moduleUniverseLift.{u, u} Λ).obj A) :
    x ∈ (uliftIdeal I ^ n • ⊤ : Submodule (ULift.{u} Λ) _) ↔
      x.down ∈ (I ^ n • ⊤ : Submodule Λ A) := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun r hr y _ => ?_) (fun y z hy hz => ?_)
    · show r.down • y.down ∈ _
      exact Submodule.smul_mem_smul ((mem_uliftIdeal_pow_iff I n r).1 hr) trivial
    · exact add_mem hy hz
  · intro hx
    obtain ⟨a, rfl⟩ : ∃ a, x = ULift.up a := ⟨x.down, rfl⟩
    refine Submodule.smul_induction_on
      (p := fun a => (ULift.up a : (AdicKoszul.moduleUniverseLift.{u, u} Λ).obj A) ∈
        (uliftIdeal I ^ n • ⊤ : Submodule (ULift.{u} Λ) _)) hx
      (fun r hr y _ => ?_) (fun y z hy hz => ?_)
    · show (ULift.up r : ULift.{u} Λ) •
          (ULift.up y : (AdicKoszul.moduleUniverseLift.{u, u} Λ).obj A) ∈ _
      exact Submodule.smul_mem_smul ((mem_uliftIdeal_pow_iff I n _).2 hr) trivial
    · exact add_mem hy hz

/-- The comparison `P / J^(n+1) P ≅ ULift (A / I^(n+1) A)` for the lift `P` of `A` to
`ULift Λ`, where `J = uliftIdeal I`. -/
def adicQuotientUliftEquiv (I : Ideal Λ) (A : ModuleCat.{u} Λ) (n : ℕ) :
    ((AdicKoszul.moduleUniverseLift.{u, u} Λ).obj A ⧸
        (uliftIdeal I ^ n • ⊤ :
          Submodule (ULift.{u} Λ) ((AdicKoszul.moduleUniverseLift.{u, u} Λ).obj A))) ≃ₗ[ULift.{u} Λ]
      (AdicKoszul.moduleUniverseLift.{u, u} Λ).obj
        (ModuleCat.of Λ (A ⧸ (I ^ n • ⊤ : Submodule Λ A))) :=
  let g : (AdicKoszul.moduleUniverseLift.{u, u} Λ).obj A →ₗ[ULift.{u} Λ]
      (AdicKoszul.moduleUniverseLift.{u, u} Λ).obj
        (ModuleCat.of Λ (A ⧸ (I ^ n • ⊤ : Submodule Λ A))) :=
    { toFun := fun x => ULift.up (Submodule.Quotient.mk x.down)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hker : LinearMap.ker g = (uliftIdeal I ^ n • ⊤ :
      Submodule (ULift.{u} Λ) ((AdicKoszul.moduleUniverseLift.{u, u} Λ).obj A)) := by
    ext x
    rw [LinearMap.mem_ker, down_mem_smul_top_iff]
    change ULift.up (Submodule.Quotient.mk x.down) = ULift.up 0 ↔ _
    rw [ULift.up_inj, Submodule.Quotient.mk_eq_zero]
  have hsurj : Function.Surjective g := fun y => by
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ y.down
    exact ⟨ULift.up a, by
      change ULift.up (Submodule.Quotient.mk a) = y
      rw [ha]
      rfl⟩
  (Submodule.quotEquivOfEq _ _ hker.symm).trans (g.quotKerEquivOfSurjective hsurj)

/-- `adicQuotientUliftEquiv` sends the class of `x` to the lift of the class of `x.down`. -/
@[simp]
theorem adicQuotientUliftEquiv_mk (I : Ideal Λ) (A : ModuleCat.{u} Λ) (n : ℕ)
    (x : (AdicKoszul.moduleUniverseLift.{u, u} Λ).obj A) :
    adicQuotientUliftEquiv I A n (Submodule.Quotient.mk x) =
      ULift.up (Submodule.Quotient.mk x.down) := rfl

/-- The tower of adic quotients of the lift of `A` to `ULift Λ` is the lift of the tower of adic
quotients of `A`. -/
def adicQuotientSystemUliftIso (I : Ideal Λ) (A : ModuleCat.{u} Λ) :
    AdicCompletionTor.adicQuotientSystem (uliftIdeal I)
        ((AdicKoszul.moduleUniverseLift.{u, u} Λ).obj A) ≅
      AdicCompletionTor.adicQuotientSystem I A ⋙ AdicKoszul.moduleUniverseLift.{u, u} Λ :=
  NatIso.ofComponents (fun n => (adicQuotientUliftEquiv I A (n.unop + 1)).toModuleIso)
    (fun f => by
      ext x
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rfl)

/-- Under `adicQuotientSystemUliftIso`, the quotient map of the lift of `A` by
`(uliftIdeal I) ^ (n + 1)` is the lift of the quotient map of `A` by `I ^ (n + 1)`. -/
theorem mkQ_comp_adicQuotientSystemUliftIso_hom (I : Ideal Λ) (A : ModuleCat.{u} Λ) (n : ℕ) :
    ModuleCat.ofHom (uliftIdeal I ^ (n + 1) • ⊤ :
        Submodule (ULift.{u} Λ) ((AdicKoszul.moduleUniverseLift.{u, u} Λ).obj A)).mkQ ≫
      (adicQuotientSystemUliftIso I A).hom.app ⟨n⟩ =
    (AdicKoszul.moduleUniverseLift.{u, u} Λ).map
      (ModuleCat.ofHom (I ^ (n + 1) • ⊤ : Submodule Λ A).mkQ) := by
  ext x
  rfl

/-- If `φ : A ⟶ c.pt` is compatible with the quotient maps of `A`, then its lift to `ULift Λ`,
composed with the transported cone, is the quotient map of the lift of `A`. -/
private theorem mkQ_eq_map_comp_postcompose_π (I : Ideal Λ) (A : ModuleCat.{u} Λ)
    (c : Cone (AdicCompletionTor.adicQuotientSystem I A)) (φ : A ⟶ c.pt)
    (hφ : ∀ n : ℕ, φ ≫ c.π.app ⟨n⟩ = ModuleCat.ofHom (I ^ (n + 1) • ⊤ : Submodule Λ A).mkQ)
    (n : ℕ) :
    ModuleCat.ofHom (uliftIdeal I ^ (n + 1) • ⊤ :
        Submodule (ULift.{u} Λ) ((AdicKoszul.moduleUniverseLift.{u, u} Λ).obj A)).mkQ =
      (AdicKoszul.moduleUniverseLift.{u, u} Λ).map φ ≫
        ((Cones.postcompose (adicQuotientSystemUliftIso I A).inv).obj
          ((AdicKoszul.moduleUniverseLift.{u, u} Λ).mapCone c)).π.app ⟨n⟩ := by
  ext x
  let a : A := ULift.down (x : ULift.{u} A)
  have h₁ : (c.π.app ⟨n⟩).hom (φ.hom a) = Submodule.Quotient.mk a :=
    congrArg (fun f => f.hom a) (hφ n)
  show Submodule.Quotient.mk x = (adicQuotientUliftEquiv I A (n + 1)).symm
    (ULift.up ((c.π.app ⟨n⟩).hom (φ.hom a)))
  rw [h₁]
  exact ((adicQuotientUliftEquiv I A (n + 1)).eq_symm_apply).2 rfl

end UniverseLift

section SingleLimit

variable {C : Type*} [Category C] [Abelian C]

/-- A module placed in degree zero preserves limit cones. -/
def isLimitMapConeSingle {J : Type*} [Category J] {F : J ⥤ C} {c : Cone F} (hc : IsLimit c) :
    IsLimit ((CochainComplex.singleFunctor C 0).mapCone c) :=
  HomologicalComplex.isLimitOfEval _ _ fun i => by
    by_cases hi : i = 0
    · subst hi
      exact (IsLimit.mapConeEquiv (HomologicalComplex.singleCompEvalIsoSelf C
        (ComplexShape.up ℤ) 0).symm (isLimitOfPreserves (𝟭 C) hc))
    · have hz : ∀ X : C, IsZero (((CochainComplex.singleFunctor C 0).obj X).X i) :=
        fun X => HomologicalComplex.isZero_single_obj_X _ _ _ _ hi
      exact
        { lift := fun s => 0
          fac := fun s j => (hz (F.obj j)).eq_of_tgt _ _
          uniq := fun s m _ => (hz c.pt).eq_of_tgt _ _ }

end SingleLimit

section Main

open MonoidalCategory

attribute [local instance] HasDerivedCategory.standard

/-- Countable products are exact in the category of `R`-modules. -/
local instance (R : Type u) [Ring R] : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{u} R) :=
  moduleCat_hasExactLimitsOfShape_discrete.{u} R ℕ

/-- The derived category of `R`-modules has countable products. -/
local instance (R : Type u) [Ring R] : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} R)) :=
  Stacks.DerivedProducts.hasProductsOfShape_derivedCategory

/-- **The limit of a tower of modules with surjective transition maps is its derived limit**,
the projections being the legs of a limit cone placed in degree zero. -/
theorem isDerivedLimitWithProjections_single_of_isLimit {R : Type u} [Ring R]
    {F : ℕᵒᵖ ⥤ ModuleCat.{u} R}
    (hF : ∀ n : ℕ, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op))
    (c : Cone F) (hc : IsLimit c) :
    IsDerivedLimitWithProjections (F ⋙ DerivedCategory.singleFunctor _ 0)
      ((DerivedCategory.singleFunctor _ 0).obj c.pt)
      (fun n => (DerivedCategory.singleFunctor _ 0).map (c.π.app ⟨n⟩)) := by
  have (n : ℕ) : Epi ((F ⋙ CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map
      (homOfLE (Nat.le_succ n)).op) := by
    have : Epi (F.map (homOfLE (Nat.le_succ n)).op) := (ModuleCat.epi_iff_surjective _).2 (hF n)
    have : PreservesFiniteColimits (CochainComplex.singleFunctor (ModuleCat.{u} R) 0) :=
      inferInstanceAs (PreservesFiniteColimits (HomologicalComplex.single _ (.up ℤ) 0))
    exact (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map_epi _
  have h := isDerivedLimitWithProjections_Q_of_isLimit
    (F := F ⋙ CochainComplex.singleFunctor (ModuleCat.{u} R) 0) _ (isLimitMapConeSingle hc)
  let e : (F ⋙ CochainComplex.singleFunctor (ModuleCat.{u} R) 0) ⋙ DerivedCategory.Q ≅
      F ⋙ DerivedCategory.singleFunctor _ 0 :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft F (DerivedCategory.singleFunctorIsoCompQ _ 0).symm
  have h' := h.comp_of_hasEventualInverses e.hom (hasEventualInverses_of_isIso _)
  convert h' using 2
  · rfl
  simp only [e, DerivedCategory.singleFunctorIsoCompQ, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Iso.refl_inv, NatTrans.id_app, Category.id_comp]
  exact (Category.comp_id _).symm

/-- Under `M ⊗ R/Jⁿ⁺¹ ≅ M/Jⁿ⁺¹M`, tensoring `M` with the quotient map `R → R/Jⁿ⁺¹` is the
quotient map `M → M/Jⁿ⁺¹M`. -/
private theorem whiskerLeft_mkQ_comp_adicQuotientSystemTensorIso_inv {R : Type u} [CommRing R]
    (J : Ideal R) (M : ModuleCat.{u} R) (n : ℕ) :
    M ◁ ModuleCat.ofHom (J ^ (n + 1)).mkQ ≫
        (AdicCompletionTor.adicQuotientSystemTensorIso J M).inv.app ⟨n⟩ =
      (ρ_ M).hom ≫ ModuleCat.ofHom (J ^ (n + 1) • ⊤ : Submodule R M).mkQ := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x r
  show TensorProduct.tensorQuotEquivQuotSMul M (J ^ (n + 1))
      (x ⊗ₜ Ideal.Quotient.mk _ r) = Submodule.Quotient.mk (r • x)
  rw [TensorProduct.tensorQuotEquivQuotSMul_tmul_mk]

variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] (I : Ideal Λ)

/-- **The adic completion of a flat module is its derived completion.** Let `Λ` be a Noetherian
ring, `I ⊆ Λ` an ideal and `A` a flat `Λ`-module, and let `c` be a limit cone of the tower
`n ↦ A/Iⁿ⁺¹A`, with `φ : A ⟶ c.pt` the map induced by the quotient maps. Then there are a
reflection `L` of `D(Λ)` onto the derived complete objects, an isomorphism `θ` from the
reflection of `A[0]` to `c.pt[0]` and an automorphism `β` of `A` such that the unit of the
reflection at `A[0]`, followed by `θ`, is `(β ≫ φ)[0]`. -/
theorem exists_iso_reflection_single_of_flat (A : ModuleCat.{u} Λ) [Module.Flat Λ A]
    (c : Cone (AdicCompletionTor.adicQuotientSystem I A)) (hc : IsLimit c) (φ : A ⟶ c.pt)
    (hφ : ∀ n : ℕ, φ ≫ c.π.app ⟨n⟩ = ModuleCat.ofHom (I ^ (n + 1) • ⊤ : Submodule Λ A).mkQ) :
    let P : ObjectProperty (DerivedCategory (ModuleCat.{u} Λ)) := fun K ↦ IsDerivedComplete I K
    ∃ (L : DerivedCategory (ModuleCat.{u} Λ) ⥤ P.FullSubcategory) (adj : L ⊣ P.ι)
      (θ : (L ⋙ P.ι).obj ((DerivedCategory.singleFunctor _ 0).obj A) ≅
        (DerivedCategory.singleFunctor _ 0).obj c.pt) (β : A ≅ A),
      adj.unit.app ((DerivedCategory.singleFunctor _ 0).obj A) ≫ θ.hom =
        (DerivedCategory.singleFunctor _ 0).map (β.hom ≫ φ) := by
  intro P
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct (ULift.{u} Λ)
  obtain ⟨L, adj, π, hlim, hunit⟩ := idealPowerDerivedLimit_isLeftAdjoint.{u, u} Λ I T
  let U := AdicKoszul.derivedUniverseLift.{u, u} Λ
  let V := AdicKoszul.moduleUniverseLift.{u, u} Λ
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} Λ) 0
  let S' := DerivedCategory.singleFunctor (ModuleCat.{u} (ULift.{u} Λ)) 0
  let J := uliftIdeal I
  let K := S.obj A
  let Pm := V.obj A
  have : Module.Flat (ULift.{u} Λ) Pm :=
    (Module.Flat.ulift_left_iff (M := (ModuleCat.uliftFunctor.{u, u} Λ).obj A)).mpr
      (Module.Flat.ulift (R := Λ) (M := A))
  let eS := V.mapDerivedCategorySingleFunctor 0
  let eK : U.obj K ≅ S'.obj Pm := eS.app A
  let σ := singleFunctorCompTensorObjSingleIso T Pm
  let τ : idealPowerQuotientSystem J ⋙ T.tensor.obj (U.obj K) ≅
      AdicCompletionTor.adicQuotientSystem J Pm ⋙ S' :=
    Functor.isoWhiskerRight (idealPowerQuotientSystemIso J) _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft S' (T.tensor.mapIso eK) ≪≫ σ) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (AdicCompletionTor.adicQuotientSystemTensorIso J Pm).symm S'
  have h₁ := (hlim K).comp_of_hasEventualInverses τ.hom (hasEventualInverses_of_isIso _)
  let ν := adicQuotientSystemUliftIso I A
  let c' : Cone (AdicCompletionTor.adicQuotientSystem J Pm) :=
    (Cones.postcompose ν.inv).obj (V.mapCone c)
  have hc' : IsLimit c' := (IsLimit.postcomposeInvEquiv ν _).symm (isLimitOfPreserves V hc)
  have h₂ := isDerivedLimitWithProjections_single_of_isLimit
    (AdicCompletionTor.surjective_adicQuotientSystem_map_succ J Pm) c' hc'
  obtain ⟨e, he⟩ := h₁.exists_iso h₂
  let R₁ := ModuleCat.of (ULift.{u} Λ) (ULift.{u} Λ)
  let bI : U.obj K ≅ S'.obj (Pm ⊗ R₁) := (T.rightUnitor.app (U.obj K)).symm ≪≫
    (T.tensor.mapIso eK).app (S'.obj R₁) ≪≫ σ.app R₁
  let b : U.obj K ⟶ S'.obj (Pm ⊗ R₁) := bI.hom
  have hmod (n : ℕ) : Pm ◁ ModuleCat.ofHom (J ^ (n + 1)).mkQ ≫
      (AdicCompletionTor.adicQuotientSystemTensorIso J Pm).inv.app ⟨n⟩ =
        (ρ_ Pm).hom ≫ ModuleCat.ofHom (J ^ (n + 1) • ⊤ : Submodule (ULift.{u} Λ) Pm).mkQ :=
    whiskerLeft_mkQ_comp_adicQuotientSystemTensorIso_inv J Pm n
  have hred (n : ℕ) : (derivedReductionMap J T n).app (U.obj K) ≫ τ.hom.app ⟨n⟩ =
      b ≫ S'.map ((ρ_ Pm).hom ≫ ModuleCat.ofHom
        (J ^ (n + 1) • ⊤ : Submodule (ULift.{u} Λ) Pm).mkQ) := by
    rw [← hmod n]
    have h₁ := idealPowerQuotientMap_comp_idealPowerQuotientSystemIso_hom J n
    let Yn := (AdicCompletionTor.idealPowerQuotientModuleSystem J).obj ⟨n⟩
    let g : R₁ ⟶ Yn := ModuleCat.ofHom (J ^ (n + 1)).mkQ
    have h₂ : (T.tensor.obj (U.obj K)).map (S'.map g) ≫ (T.tensor.map eK.hom).app (S'.obj Yn) =
        (T.tensor.map eK.hom).app (S'.obj R₁) ≫ (T.tensor.obj (S'.obj Pm)).map (S'.map g) :=
      (T.tensor.map eK.hom).naturality (S'.map g)
    have h₃ : (T.tensor.obj (S'.obj Pm)).map (S'.map g) ≫ σ.hom.app Yn =
        σ.hom.app R₁ ≫ S'.map (Pm ◁ g) := σ.hom.naturality g
    simp only [derivedReductionMap, NatTrans.comp_app, Functor.flip_map_app, τ, b, Iso.trans_hom,
      NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Functor.mapIso_hom, Iso.symm_hom, Category.id_comp,
      Category.assoc, Functor.comp_obj]
    let q : Pm ⊗ Yn ⟶ (AdicCompletionTor.adicQuotientSystem J Pm).obj ⟨n⟩ :=
      (AdicCompletionTor.adicQuotientSystemTensorIso J Pm).inv.app ⟨n⟩
    have key : (T.tensor.obj (U.obj K)).map (S'.map g) ≫ (T.tensor.map eK.hom).app (S'.obj Yn) ≫
        σ.hom.app Yn ≫ S'.map q = (T.tensor.map eK.hom).app (S'.obj R₁) ≫ σ.hom.app R₁ ≫
          S'.map (Pm ◁ g ≫ q) := by
      rw [reassoc_of% h₂, reassoc_of% h₃, Functor.map_comp]
    rw [← Functor.map_comp_assoc, h₁]
    refine (congrArg (T.rightUnitor.inv.app (U.obj K) ≫ ·) key).trans ?_
    simp only [bI, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom, Functor.mapIso_hom,
      Category.assoc]
    rfl
  let hS' := Functor.FullyFaithful.ofFullyFaithful S'
  let hV := Functor.FullyFaithful.ofFullyFaithful V
  let hU := Functor.FullyFaithful.ofFullyFaithful U
  let β' : Pm ≅ Pm := hS'.preimageIso (eK.symm ≪≫ bI ≪≫ S'.mapIso (ρ_ Pm))
  have hβ' : S'.map β'.hom = eK.inv ≫ b ≫ S'.map (ρ_ Pm).hom := hS'.map_preimage _
  let β₀ : A ≅ A := hV.preimageIso β'
  have hβ₀ : V.map β₀.hom = β'.hom := hV.map_preimage _
  have hunit' : U.map (adj.unit.app K) ≫ e.hom = eK.hom ≫ S'.map (β'.hom ≫ V.map φ) := by
    obtain ⟨g₀, hg₀⟩ : ∃ g₀, S'.map g₀ = eK.inv ≫ U.map (adj.unit.app K) ≫ e.hom :=
      ⟨hS'.preimage _, hS'.map_preimage _⟩
    have hg : g₀ = β'.hom ≫ V.map φ := by
      apply hc'.hom_ext
      rintro ⟨n⟩
      apply hS'.map_injective
      let mk' := ModuleCat.ofHom (J ^ (n + 1) • ⊤ : Submodule (ULift.{u} Λ) Pm).mkQ
      refine Eq.trans (b := eK.inv ≫ b ≫ S'.map ((ρ_ Pm).hom ≫ mk')) ?_ ?_
      · rw [Functor.map_comp, hg₀, Category.assoc, Category.assoc, he n,
          ← Category.assoc (U.map _), hunit K n, hred n]
        rfl
      · symm
        refine (congrArg S'.map (show (β'.hom ≫ V.map φ) ≫ c'.π.app ⟨n⟩ = β'.hom ≫ mk' from
          (Category.assoc _ _ _).trans
            (congrArg _ (mkQ_eq_map_comp_postcompose_π I A c φ hφ n).symm))).trans ?_
        refine (S'.map_comp β'.hom mk').trans ?_
        rw [hβ']
        simp only [Category.assoc, Functor.map_comp]
    rw [← hg]
    exact (Iso.hom_inv_id_assoc eK _).symm.trans (congrArg (eK.hom ≫ ·) hg₀.symm)
  refine ⟨L, adj, hU.preimageIso (e ≪≫ (eS.app c.pt).symm), β₀, ?_⟩
  apply hU.map_injective
  have h1 : U.map (hU.preimageIso (e ≪≫ (eS.app c.pt).symm)).hom =
      e.hom ≫ (eS.app c.pt).inv := hU.map_preimage _
  have step : (U.map (adj.unit.app K) ≫ e.hom) ≫ (eS.app c.pt).inv =
      U.map (S.map (β₀.hom ≫ φ)) := by
    rw [hunit', ← hβ₀, ← Functor.map_comp]
    exact (Iso.comp_inv_eq _).2 (eS.hom.naturality (β₀.hom ≫ φ)).symm
  rw [Functor.map_comp, h1]
  exact (Category.assoc _ _ _).symm.trans step

/-- **Maps from the completion of a flat module into a derived complete module.** Let `Λ` be a
Noetherian ring, `I ⊆ Λ` an ideal, `A` a flat `Λ`-module and `M` a derived complete
`Λ`-module. For a limit cone `c` of the tower `n ↦ A/Iⁿ⁺¹A` and the map `φ : A ⟶ c.pt` induced
by the quotient maps, every map `A ⟶ M` extends uniquely along `φ` to a map `c.pt ⟶ M`. -/
theorem bijective_comp_of_flat_of_isLimit (A : ModuleCat.{u} Λ) [Module.Flat Λ A]
    (c : Cone (AdicCompletionTor.adicQuotientSystem I A)) (hc : IsLimit c) (φ : A ⟶ c.pt)
    (hφ : ∀ n : ℕ, φ ≫ c.π.app ⟨n⟩ = ModuleCat.ofHom (I ^ (n + 1) • ⊤ : Submodule Λ A).mkQ)
    (M : ModuleCat.{u} Λ) (hM : IsDerivedCompleteModule I M) :
    Function.Bijective (fun g : c.pt ⟶ M => φ ≫ g) := by
  obtain ⟨L, adj, θ, β, h⟩ := exists_iso_reflection_single_of_flat I A c hc φ hφ
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} Λ) 0
  let P : ObjectProperty (DerivedCategory (ModuleCat.{u} Λ)) := fun K ↦ IsDerivedComplete I K
  let hS := Functor.FullyFaithful.ofFullyFaithful S
  let Y : P.FullSubcategory := ⟨S.obj M, hM⟩
  let E : (c.pt ⟶ M) ≃ (A ⟶ M) :=
    hS.homEquiv.trans ((θ.homCongr (Iso.refl _)).symm.trans
      ((P.fullyFaithfulι.homEquiv (Y := Y)).symm.trans
        ((adj.homEquiv _ Y).trans hS.homEquiv.symm)))
  have hE (g : c.pt ⟶ M) : E g = β.hom ≫ φ ≫ g := by
    apply hS.map_injective
    simp only [E, Equiv.trans_apply, Functor.FullyFaithful.homEquiv_apply,
      Functor.FullyFaithful.homEquiv_symm_apply, Functor.FullyFaithful.map_preimage,
      Adjunction.homEquiv_unit, Iso.homCongr_symm, Iso.homCongr_apply,
      Iso.refl_inv, Category.comp_id, Iso.symm_inv, Iso.symm_hom, Functor.map_comp,
      ObjectProperty.ι_map, ObjectProperty.homMk_hom]
    rw [← Category.assoc, h, Functor.map_comp, Category.assoc]
  have : (fun g : c.pt ⟶ M => φ ≫ g) = β.homCongr (Iso.refl M) ∘ E := by
    funext g
    simp [hE, Iso.homCongr_apply]
  rw [this]
  exact (β.homCongr (Iso.refl M)).bijective.comp E.bijective

end Main

end NoetherianAdicCompletion

end

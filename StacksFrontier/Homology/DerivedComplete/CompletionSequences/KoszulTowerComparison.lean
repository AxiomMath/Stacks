module

public import StacksFrontier.Homology.DerivedComplete.CompletionSequences.SequenceData

/-!
# Principal completion sequences: the Koszul tower comparison

Universal properties of a reflection onto derived-complete objects and their compatibility
with shifts, the identification of the principal Koszul tower with the mapping-cone stages,
and the resulting comparison of an arbitrary completion with the derived limit.
-/

section

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Preadditive CategoryTheory.Linear DerivedCategory PrincipalTorsionTower

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CompletionSequences

section Reflector
variable {C : Type*} [Category C] {P : ObjectProperty C}
  {L : C ⥤ P.FullSubcategory} (adj : L ⊣ P.ι)

/-- **Composition with the unit of a reflection is bijective** onto maps into an object of the
reflective subcategory. -/
private lemma unit_comp_bijective (X Y : C) (hY : P Y) :
    Function.Bijective (fun g : (L ⋙ P.ι).obj X ⟶ Y ↦ adj.unit.app X ≫ g) := by
  have h : (fun g : (L ⋙ P.ι).obj X ⟶ Y ↦ adj.unit.app X ≫ g) =
      (adj.homEquiv X ⟨Y, hY⟩) ∘ (P.fullyFaithfulι.homEquiv (X := L.obj X) (Y := ⟨Y, hY⟩)).symm :=
        by
    funext g
    simp only [Function.comp_apply, Adjunction.homEquiv_unit]
    rfl
  rw [h]
  exact (adj.homEquiv X ⟨Y, hY⟩).bijective.comp (Equiv.bijective _)


private noncomputable def universalHom {X Z : C} (u : X ⟶ Z) {Y : C}
    (hu : Function.Bijective (fun g : Z ⟶ Y ↦ u ≫ g)) (v : X ⟶ Y) : Z ⟶ Y :=
  (hu.2 v).choose

@[reassoc]
private lemma comp_universalHom {X Z : C} (u : X ⟶ Z) {Y : C}
    (hu : Function.Bijective (fun g : Z ⟶ Y ↦ u ≫ g)) (v : X ⟶ Y) :
    u ≫ universalHom u hu v = v :=
  (hu.2 v).choose_spec

/-- Two maps between objects with a common universal arrow compose to the identity. -/
private lemma universalHom_comp_universalHom {X Z Z' : C} {u : X ⟶ Z} {u' : X ⟶ Z'}
    (hu : Function.Bijective (fun g : Z ⟶ Z' ↦ u ≫ g))
    (hu' : Function.Bijective (fun g : Z' ⟶ Z ↦ u' ≫ g))
    (hZ : Function.Bijective (fun g : Z ⟶ Z ↦ u ≫ g)) :
    universalHom u hu u' ≫ universalHom u' hu' u = 𝟙 Z := by
  apply hZ.1
  change u ≫ _ ≫ _ = u ≫ 𝟙 _
  rw [comp_universalHom_assoc u hu, comp_universalHom u' hu', Category.comp_id]

/-- Recognition of the reflection by a universal arrow. -/
private noncomputable def isoOfUniversal {X Z : C} (hZ : P Z) (u : X ⟶ Z)
    (hu : ∀ Y, P Y → Function.Bijective (fun g : Z ⟶ Y ↦ u ≫ g)) :
    (L ⋙ P.ι).obj X ≅ Z where
  hom := universalHom _ (unit_comp_bijective adj X Z hZ) u
  inv := universalHom _ (hu _ (L.obj X).property) (adj.unit.app X)
  hom_inv_id := universalHom_comp_universalHom _ _ (unit_comp_bijective adj X _ (L.obj X).property)
  inv_hom_id := universalHom_comp_universalHom _ _ (hu _ hZ)

private lemma unit_isoOfUniversal_hom {X Z : C} (hZ : P Z) (u : X ⟶ Z)
    (hu : ∀ Y, P Y → Function.Bijective (fun g : Z ⟶ Y ↦ u ≫ g)) :
    adj.unit.app X ≫ (isoOfUniversal adj hZ u hu).hom = u :=
  comp_universalHom _ (unit_comp_bijective adj X Z hZ) _

/-- A functor with a natural transformation from the identity that is idempotent
and inverted exactly on `P` has universal components. -/
private lemma universal_of_idempotent (G : C ⥤ C) (ε : 𝟭 C ⟶ G)
    (hG : ∀ X, IsIso (G.map (ε.app X))) (hP : ∀ Y, P Y → IsIso (ε.app Y)) (X Y : C) (hY : P Y) :
    Function.Bijective (fun g : G.obj X ⟶ Y ↦ ε.app X ≫ g) := by
  have := hP Y hY
  constructor
  · intro g g' h
    dsimp only at h
    have h1 : G.map g = G.map g' := by
      rw [← cancel_epi (G.map (ε.app X)), ← G.map_comp, ← G.map_comp, h]
    rw [← cancel_mono (ε.app Y)]
    have n1 := ε.naturality g
    have n2 := ε.naturality g'
    dsimp at n1 n2
    rw [n1, n2, h1]
  · intro h
    refine ⟨G.map h ≫ inv (ε.app Y), ?_⟩
    dsimp only
    have n := ε.naturality h
    dsimp at n
    rw [← Category.assoc, ← n, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

end Reflector

/-- The map `1 - f` on the constant tower with value `X`, whose invertibility
characterizes derived completeness. -/
private noncomputable def powerDifference {A : Type u} [CommRing A]
    (X : DerivedCategory (ModuleCat.{v} A)) (a : A) :
    (∏ᶜ fun _ : ℕ ↦ X) ⟶ ∏ᶜ fun _ : ℕ ↦ X :=
  Pi.lift fun m : ℕ ↦ Pi.π (fun _ : ℕ ↦ X) m - Pi.π (fun _ : ℕ ↦ X) (m + 1) ≫ (a • 𝟙 X)

private lemma isDerivedComplete_iff_powerDifference {A : Type u} [CommRing A] (I : Ideal A)
    (X : DerivedCategory (ModuleCat.{v} A)) :
    IsDerivedComplete I X ↔ ∀ a ∈ I, IsIso (powerDifference X a) :=
  Iff.rfl

private lemma powerDifference_shift {A : Type u} [CommRing A]
    (X : DerivedCategory (ModuleCat.{v} A)) (a : A) (n : ℤ) :
    piComparison (shiftFunctor _ n) (fun _ : ℕ ↦ X) ≫ powerDifference (X⟦n⟧) a =
      (shiftFunctor _ n).map (powerDifference X a) ≫
        piComparison (shiftFunctor _ n) (fun _ : ℕ ↦ X) := by
  apply Pi.hom_ext
  intro m
  simp only [powerDifference, Category.assoc, Pi.lift_comp_π, Preadditive.comp_sub,
    piComparison_comp_π, ← Functor.map_comp, Functor.map_sub,
    Linear.comp_smul, Category.comp_id, Functor.map_smul]

private lemma isDerivedComplete_shift {A : Type u} [CommRing A] (I : Ideal A)
    {X : DerivedCategory (ModuleCat.{v} A)} (hX : IsDerivedComplete I X) (n : ℤ) :
    IsDerivedComplete I (X⟦n⟧) := by
  rw [isDerivedComplete_iff_powerDifference] at hX ⊢
  intro a ha
  have := hX a ha
  have e := powerDifference_shift X a n
  have : IsIso (piComparison (shiftFunctor (DerivedCategory (ModuleCat.{v} A)) n)
    (fun _ : ℕ ↦ X)) := inferInstance
  have : IsIso (piComparison (shiftFunctor _ n) (fun _ : ℕ ↦ X) ≫ powerDifference (X⟦n⟧) a) := by
    rw [e]; infer_instance
  exact IsIso.of_isIso_comp_left (piComparison (shiftFunctor _ n) (fun _ : ℕ ↦ X)) _


section Shift
variable {C : Type*} [Category C] [HasShift C ℤ] {P : ObjectProperty C}

private lemma shift_universal {X Z : C} (u : X ⟶ Z) (n : ℤ)
    (hP : ∀ Y, P Y → P (Y⟦-n⟧))
    (hu : ∀ Y, P Y → Function.Bijective (fun g : Z ⟶ Y ↦ u ≫ g)) (Y : C) (hY : P Y) :
    Function.Bijective (fun g : Z⟦n⟧ ⟶ Y ↦ u⟦n⟧' ≫ g) := by
  let e := (shiftFunctorCompIsoId C (-n) n (neg_add_cancel n)).app Y
  have key : ∀ g : Z⟦n⟧ ⟶ Y, g = ((shiftFunctor C n).preimage (g ≫ e.inv))⟦n⟧' ≫ e.hom := by
    intro g; simp
  constructor
  · intro g g' h
    dsimp only at h
    rw [key g, key g']
    congr 2
    apply (hu _ (hP Y hY)).1
    apply (shiftFunctor C n).map_injective
    simp only [Functor.map_comp, Functor.map_preimage]
    rw [reassoc_of% h]
  · intro v
    obtain ⟨h, hh⟩ := (hu _ (hP Y hY)).2 ((shiftFunctor C n).preimage (v ≫ e.inv))
    refine ⟨h⟦n⟧' ≫ e.hom, ?_⟩
    dsimp only at hh ⊢
    rw [← Functor.map_comp_assoc, hh]
    simp
end Shift

section PrincipalTower

open CochainComplex CochainComplex.HomComplex KoszulCoefficientTower

variable {A : Type u} [CommRing A]

private lemma finset_fin_one_cases (S : Finset (Fin 1)) : S = ∅ ∨ S = {0} := by
  by_cases h : 0 ∈ S
  · right
    ext i
    have : i = 0 := Subsingleton.elim _ _
    subst i
    simp [h]
  · left
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i
    have : i = 0 := Subsingleton.elim _ _
    simpa [this] using h

private def coefficientEval (C : CochainComplex (ModuleCat.{v} A) ℤ)
    (t : ℤ) (S : Finset (Fin 1)) : coefficientKoszulTerm (r := 1) C t ⟶ C.X (t + S.card) :=
  ModuleCat.ofHom (LinearMap.proj S)

private def coefficientEmpty (C : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    coefficientKoszulTerm (r := 1) C t ⟶ C.X t :=
  coefficientEval C t ∅ ≫ eqToHom (by simp)

private def coefficientSingleton (C : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    coefficientKoszulTerm (r := 1) C t ⟶ C.X (t + 1) :=
  coefficientEval C t {0} ≫ eqToHom (by simp)

private lemma coefficient_ext (C : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ)
    {X : ModuleCat.{v} A} {a b : X ⟶ coefficientKoszulTerm (r := 1) C t}
    (h₀ : a ≫ coefficientEmpty C t = b ≫ coefficientEmpty C t)
    (h₁ : a ≫ coefficientSingleton C t = b ≫ coefficientSingleton C t) : a = b := by
  have e₀ : a ≫ coefficientEval C t ∅ = b ≫ coefficientEval C t ∅ :=
    (cancel_mono (eqToHom (show C.X (t + (∅ : Finset (Fin 1)).card) = C.X t by simp))).1 h₀
  have e₁ : a ≫ coefficientEval C t {0} = b ≫ coefficientEval C t {0} :=
    (cancel_mono (eqToHom (show C.X (t + ({0} : Finset (Fin 1)).card) = C.X (t + 1) by simp))).1 h₁
  ext x S
  rcases finset_fin_one_cases S with rfl | rfl
  · exact congrArg (fun k => k x) e₀
  · exact congrArg (fun k => k x) e₁

private def principalConeMapTerm (f : A) (C : CochainComplex (ModuleCat.{v} A) ℤ)
    (n : ℕ) (t : ℤ) : (mappingCone (f ^ (n + 1) • 𝟙 C)).X t ⟶
      coefficientKoszulTerm (r := 1) C t :=
  ModuleCat.ofHom (LinearMap.pi fun S => if h : S = ∅ then
    ((mappingCone.snd (f ^ (n + 1) • 𝟙 C)).v t t (add_zero t) ≫
      eqToHom (by simp [h])).hom
    else
      (((t + 1).negOnePow : ℤˣ) • (mappingCone.fst (f ^ (n + 1) • 𝟙 C)).1.v
        t (t + 1) rfl ≫ eqToHom (by
          have hs := (finset_fin_one_cases S).resolve_left h
          simp [hs])).hom)

set_option backward.isDefEq.respectTransparency false in
private lemma principalConeMapTerm_empty (f : A)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (n : ℕ) (t : ℤ) :
    principalConeMapTerm f C n t ≫ coefficientEmpty C t =
      (mappingCone.snd (f ^ (n + 1) • 𝟙 C)).v t t (add_zero t) := by
  have h : principalConeMapTerm f C n t ≫ coefficientEval C t ∅ =
      (mappingCone.snd (f ^ (n + 1) • 𝟙 C)).v t t (add_zero t) ≫
        eqToHom (by simp) := by
    ext x
    simp [principalConeMapTerm, coefficientEval]
  rw [coefficientEmpty, ← Category.assoc, h, Category.assoc, eqToHom_trans]
  simp

set_option backward.isDefEq.respectTransparency false in
private lemma principalConeMapTerm_singleton (f : A)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (n : ℕ) (t : ℤ) :
    principalConeMapTerm f C n t ≫ coefficientSingleton C t =
      (t + 1).negOnePow • (mappingCone.fst (f ^ (n + 1) • 𝟙 C)).1.v
        t (t + 1) rfl := by
  have h : principalConeMapTerm f C n t ≫ coefficientEval C t {0} =
      (t + 1).negOnePow • (mappingCone.fst (f ^ (n + 1) • 𝟙 C)).1.v
        t (t + 1) rfl ≫ eqToHom (by simp) := by
    ext x
    simp [principalConeMapTerm, coefficientEval]
    rfl
  rw [coefficientSingleton, ← Category.assoc, h]
  simp only [eqToHom_refl, Category.comp_id]


set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private lemma coefficientDifferential_empty (f : A)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (n : ℕ) (t : ℤ) :
    coefficientKoszulDifferential (fun _ : Fin 1 => f) n C t ≫ coefficientEmpty C (t + 1) =
      coefficientEmpty C t ≫ C.d t (t + 1) +
        (t + 1).negOnePow • (coefficientSingleton C t ≫ (f ^ (n + 1) • 𝟙 _)) := by
  let : Unique {i : Fin 1 // i ∉ (∅ : Finset (Fin 1))} :=
    { default := ⟨0, by simp⟩
      uniq i := Subtype.ext (Subsingleton.elim _ _) }
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [coefficientKoszulDifferential, coefficientEmpty, coefficientSingleton,
    coefficientEval, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
    LinearMap.proj_apply]
  dsimp only [LinearMap.proj, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Fintype.sum_unique]
  simp only [Finset.card_empty, Int.cast_ofNat_Int, CharP.cast_eq_zero, add_zero,
    Finset.filter_empty, pow_zero, mul_one, Finset.insert_empty, map_add, map_smul,
    Category.assoc, ComplexShape.up_Rel, HomologicalComplex.eqToHom_comp_d, Fin.isValue,
    eqToHom_refl, Category.comp_id, comp_smul, Units.smul_def, ← Int.cast_smul_eq_zsmul A,
    Int.coe_negOnePow, smul_smul, ModuleCat.hom_add, ModuleCat.hom_comp,
    ConcreteCategory.hom_ofHom, ModuleCat.hom_smul, LinearMap.add_apply, LinearMap.coe_comp,
    LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, Function.eval]
  rw [LinearMap.map_add, LinearMap.map_smul]
  congr 1
  · show (C.d (t + 0) (t + 1 + 0) ≫ eqToHom _) (x ∅) =
      (C.d (t + 0) (t + 1)) (x ∅)
    rw [HomologicalComplex.d_comp_eqToHom C (by dsimp; omega) (by dsimp; omega)]
  · rw [← ModuleCat.comp_apply, eqToHom_trans]
    rfl

private lemma coefficientDifferential_singleton (f : A)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (n : ℕ) (t : ℤ) :
    coefficientKoszulDifferential (fun _ : Fin 1 => f) n C t ≫ coefficientSingleton C (t + 1) =
      coefficientSingleton C t ≫ C.d (t + 1) (t + 1 + 1) := by
  let : IsEmpty {i : Fin 1 // i ∉ ({0} : Finset (Fin 1))} :=
    ⟨fun i => i.2 (by simp [Subsingleton.elim i.1 0])⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [coefficientKoszulDifferential, coefficientSingleton, coefficientEval,
    ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply, LinearMap.proj_apply]
  dsimp only [LinearMap.proj, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  rfl


private def principalConeInvTerm (f : A) (C : CochainComplex (ModuleCat.{v} A) ℤ)
    (n : ℕ) (t : ℤ) : coefficientKoszulTerm (r := 1) C t ⟶
      (mappingCone (f ^ (n + 1) • 𝟙 C)).X t :=
  (t + 1).negOnePow • (coefficientSingleton C t ≫
    (mappingCone.inl (f ^ (n + 1) • 𝟙 C)).v (t + 1) t (by omega)) +
  coefficientEmpty C t ≫ (mappingCone.inr (f ^ (n + 1) • 𝟙 C)).f t

private lemma principalConeMapTerm_inv (f : A)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (n : ℕ) (t : ℤ) :
    principalConeMapTerm f C n t ≫ principalConeInvTerm f C n t = 𝟙 _ := by
  simp only [principalConeInvTerm, comp_add, comp_units_smul, ← Category.assoc,
    principalConeMapTerm_singleton, principalConeMapTerm_empty,
    units_smul_comp, smul_smul, Int.units_mul_self, one_smul]
  exact mappingCone.id_X _ t (t + 1) rfl

private lemma principalConeInvTerm_map (f : A)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (n : ℕ) (t : ℤ) :
    principalConeInvTerm f C n t ≫ principalConeMapTerm f C n t = 𝟙 _ := by
  apply coefficient_ext C t
  · simp only [Category.assoc, principalConeMapTerm_empty, Category.id_comp,
      principalConeInvTerm, add_comp, units_smul_comp, Category.assoc,
      mappingCone.inl_v_snd_v, mappingCone.inr_f_snd_v, comp_zero, smul_zero,
      zero_add, Category.comp_id]
  · simp only [Category.assoc, principalConeMapTerm_singleton, Category.id_comp,
      comp_units_smul, principalConeInvTerm, add_comp, units_smul_comp,
      Category.assoc, mappingCone.inl_v_fst_v, mappingCone.inr_f_fst_v,
      Category.comp_id, comp_zero, smul_zero, add_zero, smul_smul, Int.units_mul_self, one_smul]

private def principalConeTermIso (f : A) (C : CochainComplex (ModuleCat.{v} A) ℤ)
    (n : ℕ) (t : ℤ) : (mappingCone (f ^ (n + 1) • 𝟙 C)).X t ≅
      coefficientKoszulTerm (r := 1) C t where
  hom := principalConeMapTerm f C n t
  inv := principalConeInvTerm f C n t
  hom_inv_id := principalConeMapTerm_inv f C n t
  inv_hom_id := principalConeInvTerm_map f C n t

private lemma principalConeMapTerm_comm (f : A)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (n : ℕ) (t : ℤ) :
    principalConeMapTerm f C n t ≫ coefficientKoszulDifferential (fun _ : Fin 1 => f) n C t =
      (mappingCone (f ^ (n + 1) • 𝟙 C)).d t (t + 1) ≫ principalConeMapTerm f C n (t + 1) := by
  apply coefficient_ext C (t + 1)
  · simp only [Category.assoc, coefficientDifferential_empty, comp_add, comp_units_smul,
      principalConeMapTerm_empty]
    simp only [← Category.assoc, principalConeMapTerm_empty, principalConeMapTerm_singleton,
      units_smul_comp, smul_smul, Int.units_mul_self, one_smul]
    rw [mappingCone.d_snd_v _ _ _ rfl]
    simp [add_comm]
  · simp only [Category.assoc, coefficientDifferential_singleton,
      principalConeMapTerm_singleton, comp_units_smul]
    simp only [← Category.assoc, principalConeMapTerm_singleton, units_smul_comp]
    rw [mappingCone.d_fst_v _ _ _ _ rfl rfl]
    simp [Int.negOnePow_add]

private noncomputable def principalStageIso (f : A)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (n : ℕ) :
    mappingCone (f ^ (n + 1) • 𝟙 C) ≅
      ((coefficientKoszulTower (fun _ : Fin 1 => f)).obj C).obj ⟨n⟩ :=
  HomologicalComplex.Hom.isoOfComponents (principalConeTermIso f C n) (by
    intro i j hij
    have h : i + 1 = j := hij
    subst j
    change principalConeMapTerm f C n i ≫ _ = _
    rw [coefficientKoszulTower_d]
    exact principalConeMapTerm_comm f C n i)

set_option backward.isDefEq.respectTransparency false in
private lemma coefficientTransition_empty (f : A)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (m n : ℕ) (t : ℤ) :
    coefficientKoszulTransitionTerm (fun _ : Fin 1 => f) m n C t ≫ coefficientEmpty C t =
      coefficientEmpty C t := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  dsimp [coefficientKoszulTransitionTerm, coefficientEmpty, coefficientEval, LinearMap.proj]
  simp

set_option backward.isDefEq.respectTransparency false in
private lemma coefficientTransition_singleton (f : A)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (m n : ℕ) (t : ℤ) :
    coefficientKoszulTransitionTerm (fun _ : Fin 1 => f) m n C t ≫ coefficientSingleton C t =
      f ^ (m - n) • coefficientSingleton C t := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  dsimp [coefficientKoszulTransitionTerm, coefficientSingleton, coefficientEval, LinearMap.proj]
  simp only [Fin.isValue, Finset.prod_const]
  show (f ^ (m - n)) ^ 1 • x {0} = f ^ (m - n) • x {0}
  rw [pow_one]

set_option backward.isDefEq.respectTransparency false in
private lemma coefficientUnit_empty
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    coefficientKoszulUnitTerm (r := 1) C t ≫ coefficientEmpty C t = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  dsimp [coefficientKoszulUnitTerm, coefficientEmpty, coefficientEval, LinearMap.proj]
  simp only [← ModuleCat.comp_apply, eqToHom_trans, eqToHom_refl, ModuleCat.id_apply]

private lemma coefficientUnit_singleton
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    coefficientKoszulUnitTerm (r := 1) C t ≫ coefficientSingleton C t = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  show ((coefficientKoszulUnitTerm (r := 1) C t).hom x) {0} = 0
  simp [coefficientKoszulUnitTerm]

set_option backward.isDefEq.respectTransparency false in
private lemma principalStageIso_transition (f : A)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (n : ℕ) :
    mappingCone.map (f ^ (n + 2) • 𝟙 C) (f ^ (n + 1) • 𝟙 C) (f • 𝟙 C) (𝟙 C)
        (by simp [comp_smul, smul_smul, pow_succ', mul_comm]) ≫
        (principalStageIso f C n).hom =
      (principalStageIso f C (n + 1)).hom ≫
        ((coefficientKoszulTower (fun _ : Fin 1 => f)).obj C).map
          (homOfLE (Nat.le_succ n)).op := by
  ext t : 1
  dsimp only [HomologicalComplex.comp_f, principalStageIso,
    HomologicalComplex.Hom.isoOfComponents_hom_f, principalConeTermIso]
  rw [coefficientKoszulTower_transition_f]
  apply coefficient_ext C t
  · simp only [Category.assoc, principalConeMapTerm_empty, coefficientTransition_empty]
    rw [mappingCone.map_f_snd_v]
    simp
  · simp only [Category.assoc, principalConeMapTerm_singleton, coefficientTransition_singleton,
      comp_units_smul, comp_smul]
    rw [mappingCone.map_f_fst_v]
    show (t + 1).negOnePow •
        ((mappingCone.fst (f ^ (n + 2) • 𝟙 C)).1.v t (t + 1) rfl ≫
          (f • 𝟙 (C.X (t + 1)))) = _
    rw [comp_smul, Category.comp_id]
    have hn : n.succ - n = 1 := by omega
    rw [hn, pow_one]
    exact smul_comm _ _ _

set_option backward.isDefEq.respectTransparency false in
private lemma principalStageIso_unit (f : A)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) (n : ℕ) :
    mappingCone.inr (f ^ (n + 1) • 𝟙 C) ≫ (principalStageIso f C n).hom =
      (coefficientKoszulAugmentation (fun _ : Fin 1 => f) n).app C := by
  ext t : 1
  dsimp only [HomologicalComplex.comp_f, principalStageIso,
    HomologicalComplex.Hom.isoOfComponents_hom_f, principalConeTermIso]
  rw [coefficientKoszulAugmentation_f]
  apply coefficient_ext C t
  · simp only [Category.assoc, principalConeMapTerm_empty, coefficientUnit_empty,
      mappingCone.inr_f_snd_v]
  · simp only [Category.assoc, principalConeMapTerm_singleton, coefficientUnit_singleton,
      comp_units_smul, mappingCone.inr_f_fst_v, smul_zero]
private noncomputable def principalTowerIso (f : A)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) :
    principalComplexSystem A f C ≅ (coefficientKoszulTower (fun _ : Fin 1 => f)).obj C := by
  let e : principalComplexSystem A f C ⟶
      (coefficientKoszulTower (fun _ : Fin 1 => f)).obj C :=
    NatTrans.ofOpSequence (fun n => (principalStageIso f C n).hom) (fun n => by
      rw [Functor.ofOpSequence_map_homOfLE_succ]
      exact principalStageIso_transition f C n)
  exact NatIso.ofComponents (fun n => principalStageIso f C n.unop) (fun h => e.naturality h)

private noncomputable def principalMilnorIso (f : A)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) :
    (milnorTriangle A (principalComplexSystem A f C)).obj₁ ≅
      DerivedCategory.Q.obj
        ((KoszulCompletion.coefficientCompletionComplex (fun _ : Fin 1 => f)).obj C) :=
  DerivedCategory.Q.mapIso
    (CountableMilnorTower.countableMilnorFunctor.mapIso (principalTowerIso f C))

set_option backward.isDefEq.respectTransparency false in
private lemma principalMilnorIso_unit (f : A)
    (C : CochainComplex (ModuleCat.{v} A) ℤ) :
    DerivedCategory.Q.map (principalCompletionUnit A f C) ≫ (principalMilnorIso f C).hom =
      DerivedCategory.Q.map
        ((KoszulCompletion.coefficientCompletionUnit (fun _ : Fin 1 => f)).app C) := by
  let a : CountableMilnorTower.TowerAugmentation (principalComplexSystem A f C) :=
    { source := C
      app n := mappingCone.inr (f ^ (n + 1) • 𝟙 C)
      naturality n := by
        rw [Functor.ofOpSequence_map_homOfLE_succ]
        simp [mappingCone.map] }
  let b : CountableMilnorTower.TowerAugmentation
      ((coefficientKoszulTower (fun _ : Fin 1 => f)).obj C) :=
    { source := C
      app n := (coefficientKoszulAugmentation (fun _ : Fin 1 => f) n).app C
      naturality n := coefficientKoszulAugmentation_transition _ C (n + 1) n (Nat.le_succ n) }
  have h := CountableMilnorTower.TowerAugmentation.augmentationMap_naturality
    a b (𝟙 C) (principalTowerIso f C).hom (fun n => by
      show 𝟙 C ≫ (coefficientKoszulAugmentation (fun _ : Fin 1 => f) n).app C =
        mappingCone.inr (f ^ (n + 1) • 𝟙 C) ≫ (principalStageIso f C n).hom
      rw [Category.id_comp]
      exact (principalStageIso_unit f C n).symm)
  show DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ = DerivedCategory.Q.map _
  rw [← Functor.map_comp]
  apply congrArg DerivedCategory.Q.map
  have ha : a.augmentationMap = principalCompletionUnit A f C := rfl
  have hb : b.augmentationMap =
      (KoszulCompletion.coefficientCompletionUnit (fun _ : Fin 1 => f)).app C := rfl
  rw [Category.id_comp, ha, hb] at h
  exact h.symm

end PrincipalTower

section Completion

variable (A : Type u) [CommRing A] (f : A)

/-- The object property of derived completeness with respect to `(f)`. -/
private abbrev principalP : ObjectProperty (DerivedCategory (ModuleCat.{v} A)) :=
  fun L ↦ IsDerivedComplete (Ideal.span {f}) L

variable {A f}

/-- Completion commutes with shifts, compatibly with the unit. -/
private noncomputable def completionShift
    {A : Type u} [CommRing A] {f : A}
    {completion : DerivedCategory (ModuleCat.{v} A) ⥤ (principalP A f).FullSubcategory}
    (adj : completion ⊣ (principalP A f).ι) :
    CompletionShift A (completion ⋙ (principalP A f).ι) adj.unit where
  iso X n := isoOfUniversal adj (X := X⟦n⟧)
    (isDerivedComplete_shift _ (completion.obj X).property n) ((adj.unit.app X)⟦n⟧')
    (shift_universal (P := principalP A f) _ n
      (fun _ hY ↦ isDerivedComplete_shift (Ideal.span {f}) hY (-n))
      (fun Y hY ↦ unit_comp_bijective adj X Y hY))
  unit_iso _ _ := unit_isoOfUniversal_hom adj _ _ _

open KoszulCompletion in
private lemma canonicalCompletion_isComplete
    {A : Type u} [CommRing A] (f : A) (X : DerivedCategory (ModuleCat.{v} A)) :
    principalP A f ((completionFunctor (fun _ : Fin 1 => f)).obj X) := by
  let tensor := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct (ULift.{v} A)
  simpa only [completionData_functor, principalP, Set.range_const] using
    koszulPowerCompletion_complete A (fun _ : Fin 1 => f) tensor
      (completionData (fun _ : Fin 1 => f) tensor) X

open KoszulCompletion in
private lemma canonicalCompletion_universal
    {A : Type u} [CommRing A] (f : A) (X Y : DerivedCategory (ModuleCat.{v} A))
    (hY : principalP A f Y) :
    Function.Bijective (fun g : (completionFunctor (fun _ : Fin 1 => f)).obj X ⟶ Y =>
      (completionUnit (fun _ : Fin 1 => f)).app X ≫ g) := by
  let tensor := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct (ULift.{v} A)
  exact universal_of_idempotent (P := principalP A f)
    (completionFunctor (fun _ : Fin 1 => f)) (completionUnit (fun _ : Fin 1 => f))
    (canonicalCompletion_map_unit_isIso _ tensor)
    (fun Y h => (canonicalCompletion_criterion (fun _ : Fin 1 => f) tensor Y).mp
      (by simpa only [principalP, Set.range_const] using h)) X Y hY

open KoszulCompletion in
private noncomputable def canonicalCompletionIso
    {A : Type u} [CommRing A] {f : A}
    {completion : DerivedCategory (ModuleCat.{v} A) ⥤ (principalP A f).FullSubcategory}
    (adj : completion ⊣ (principalP A f).ι)
    (X : DerivedCategory (ModuleCat.{v} A)) :
    (completion ⋙ (principalP A f).ι).obj X ≅
      (completionFunctor (fun _ : Fin 1 => f)).obj X :=
  isoOfUniversal adj (canonicalCompletion_isComplete f X)
    ((completionUnit (fun _ : Fin 1 => f)).app X) (canonicalCompletion_universal f X)

open KoszulCompletion in
@[reassoc]
private lemma canonicalCompletionIso_unit
    {A : Type u} [CommRing A] {f : A}
    {completion : DerivedCategory (ModuleCat.{v} A) ⥤ (principalP A f).FullSubcategory}
    (adj : completion ⊣ (principalP A f).ι)
    (X : DerivedCategory (ModuleCat.{v} A)) :
    adj.unit.app X ≫ (canonicalCompletionIso adj X).hom =
      (completionUnit (fun _ : Fin 1 => f)).app X :=
  unit_isoOfUniversal_hom adj (canonicalCompletion_isComplete f X)
    ((completionUnit (fun _ : Fin 1 => f)).app X) (canonicalCompletion_universal f X)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def principalComparison
    {A : Type u} [CommRing A] {f : A}
    {completion : DerivedCategory (ModuleCat.{v} A) ⥤ (principalP A f).FullSubcategory}
    (adj : completion ⊣ (principalP A f).ι) :
    CompletionComparison A f (completion ⋙ (principalP A f).ι) adj.unit where
  iso C := canonicalCompletionIso adj (DerivedCategory.Q.obj C) ≪≫
    (completionLocalIso (fun _ : Fin 1 => f)).app C ≪≫ (principalMilnorIso f C).symm
  unit_iso C := by
    simp only [Iso.trans_hom, Iso.symm_hom]
    rw [canonicalCompletionIso_unit_assoc adj (DerivedCategory.Q.obj C),
      completionUnit_representative]
    simp only [Category.assoc]
    rw [← principalMilnorIso_unit]
    simp

end Completion

end CompletionSequences
end

end

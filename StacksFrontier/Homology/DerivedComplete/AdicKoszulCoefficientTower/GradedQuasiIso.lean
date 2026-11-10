module

public import StacksFrontier.Homology.DerivedComplete.AdicKoszulCoefficientTower.FiltrationLaws
import all StacksFrontier.Homology.DerivedComplete.AdicKoszulCoefficientTower.Formulas
import all StacksFrontier.Homology.DerivedComplete.AdicKoszulCoefficientTower.FiltrationLaws
import Mathlib
import all Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Koszul towers with coefficients: graded quotients and quasi-isomorphisms

The signed differential squares to zero, the graded quotients of the filtration are the finite
products of shifted coefficient complexes, and every filtered stage preserves
quasi-isomorphisms.  The ordered exterior-basis wedges are compared with the Koszul
differential and with the power transitions.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u v

namespace KoszulCoefficientTower

variable {A : Type u} [CommRing A]

private theorem koszulContraction_sign {r : ℕ} (S : Finset (Fin r)) (i j : Fin r)
    (hi : i ∉ S) (hj : j ∉ S) (hij : i ≠ j) :
    (-1 : A) ^ (S.filter (· < i)).card * (-1 : A) ^ ((insert i S).filter (· < j)).card =
      -((-1 : A) ^ (S.filter (· < j)).card * (-1 : A) ^ ((insert j S).filter (· < i)).card) := by
  have hni : i ∉ S.filter (· < j) := fun h ↦ hi (Finset.mem_filter.mp h).1
  have hnj : j ∉ S.filter (· < i) := fun h ↦ hj (Finset.mem_filter.mp h).1
  rcases lt_or_gt_of_ne hij with hij | hji
  · simp only [Finset.filter_insert, ite_eq_left hij, ite_eq_right (not_lt_of_ge hij.le),
      Finset.card_insert_of_notMem hni, pow_succ]
    ring
  · simp only [Finset.filter_insert, ite_eq_right (not_lt_of_ge hji.le), ite_eq_left hji,
      Finset.card_insert_of_notMem hnj, pow_succ]
    ring

private theorem eqToHom_apply_eq {ι : Type*} (M : ι → ModuleCat.{v} A)
    (x : ∀ i, M i) {i j : ι} {N : ModuleCat.{v} A} (hi : M i = N) (hj : M j = N)
    (hij : i = j) : (eqToHom hi).hom (x i) = (eqToHom hj).hom (x j) := by
  subst j
  rfl

private theorem insertionPair_sum_eq_zero {r : ℕ} {M : Type*} [AddCommMonoid M]
    (S : Finset (Fin r))
    (b : (i : {i : Fin r // i ∉ S}) → {j : Fin r // j ∉ insert i.val S} → M)
    (hb : ∀ i j,
      b i j + b ⟨j.val, fun h ↦ j.property (Finset.mem_insert_of_mem h)⟩
        ⟨i.val, by
          simp only [Finset.mem_insert, not_or]
          exact ⟨fun h ↦ j.property (by simp [h]), i.property⟩⟩ = 0) :
    ∑ i, ∑ j, b i j = 0 := by
  classical
  rw [← Fintype.sum_sigma (fun a : ((i : {i : Fin r // i ∉ S}) ×
    {j : Fin r // j ∉ insert i.val S}) ↦ b a.1 a.2)]
  let swap : ((i : {i : Fin r // i ∉ S}) × {j : Fin r // j ∉ insert i.val S}) →
      ((i : {i : Fin r // i ∉ S}) × {j : Fin r // j ∉ insert i.val S}) :=
    fun x ↦ ⟨⟨x.2.val, fun h ↦ x.2.property (Finset.mem_insert_of_mem h)⟩,
      ⟨x.1.val, by
        simp only [Finset.mem_insert, not_or]
        exact ⟨fun h ↦ x.2.property (by simp [h]), x.1.property⟩⟩⟩
  apply Finset.sum_involution (fun a _ ↦ swap a)
  · intro a _
    exact hb a.1 a.2
  · intro a _ _ heq
    have heq' := congrArg (fun a ↦ a.1.val) heq
    exact a.2.property (by simp [swap] at heq'; simp [heq'])
  · intro _ _
    exact Finset.mem_univ _
  · intro a _
    rfl
set_option backward.isDefEq.respectTransparency false in
private theorem coefficientKoszulDifferential_square {r : ℕ} (f : Fin r → A) (n : ℕ)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    coefficientKoszulDifferential f n K t ≫ coefficientKoszulDifferential f n K (t + 1) = 0 := by
  classical
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext S
  dsimp only [coefficientKoszulDifferential, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
    LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, ModuleCat.hom_zero, LinearMap.zero_apply,
    Pi.zero_apply]
  simp only [map_add, map_sum, map_smul, smul_add, Finset.smul_sum,
    Finset.sum_add_distrib]
  have hd := ConcreteCategory.congr_hom
    (K.d_comp_d (t + S.card) (t + 1 + S.card) (t + 1 + 1 + S.card)) (x S)
  change (K.d (t + 1 + S.card) (t + 1 + 1 + S.card)).hom
    ((K.d (t + S.card) (t + 1 + S.card)).hom (x S)) = 0 at hd
  rw [hd, zero_add, ← add_assoc, ← Finset.sum_add_distrib]
  have hm : ∀ i : {i : Fin r // i ∉ S},
      ((-1 : A) ^ (t + S.card + 1).natAbs * (-1) ^ (S.filter (· < i.val)).card *
        f i.val ^ (n + 1)) •
        (K.d (t + 1 + S.card) (t + 1 + 1 + S.card)).hom
          ((eqToHom (by congr 1; rw [Finset.card_insert_of_notMem i.property]; push_cast; omega) :
            K.X (t + (insert i.val S).card) ⟶ K.X (t + 1 + S.card)).hom (x (insert i.val S))) +
      ((-1 : A) ^ (t + 1 + S.card + 1).natAbs * (-1) ^ (S.filter (· < i.val)).card *
        f i.val ^ (n + 1)) •
        (eqToHom (by congr 1; rw [Finset.card_insert_of_notMem i.property]; push_cast; omega) :
          K.X (t + 1 + (insert i.val S).card) ⟶ K.X (t + 1 + 1 + S.card)).hom
          ((K.d (t + (insert i.val S).card) (t + 1 + (insert i.val S).card)).hom
            (x (insert i.val S))) = 0 := by
    intro i
    have ht := ConcreteCategory.congr_hom
      (eqToHom_d K (t + (insert i.val S).card) (t + 1 + S.card)
        (t + 1 + (insert i.val S).card) (t + 1 + 1 + S.card)
        (by rw [Finset.card_insert_of_notMem i.property]; push_cast; omega)
        (by rw [Finset.card_insert_of_notMem i.property]; push_cast; omega))
      (x (insert i.val S))
    dsimp only [ModuleCat.hom_comp, LinearMap.comp_apply] at ht
    rw [ht]
    have hsign : (-1 : A) ^ (t + 1 + S.card + 1).natAbs =
        -((-1 : A) ^ (t + S.card + 1).natAbs) := by
      rw [show t + 1 + (S.card : ℤ) + 1 = (t + S.card + 1) + 1 by omega,
        neg_one_pow_natAbs_add]
      simp
    rw [hsign, neg_mul, neg_mul, neg_smul, add_neg_cancel]
  rw [Finset.sum_eq_zero (fun i _ ↦ hm i), zero_add]
  apply insertionPair_sum_eq_zero
  intro i j
  simp only [smul_smul]
  simp only [← LinearMap.comp_apply, ← ModuleCat.hom_comp, eqToHom_trans]
  have hj : j.val ∉ S := fun h ↦ j.property (Finset.mem_insert_of_mem h)
  have hij : i.val ≠ j.val := fun h ↦ j.property (by simp [h])
  have hc := koszulContraction_sign (A := A) S i.val j.val i.property hj hij
  have hcoeff :
      ((-1 : A) ^ (t + 1 + S.card + 1).natAbs * (-1) ^ (S.filter (· < i.val)).card *
        f i.val ^ (n + 1)) *
      ((-1 : A) ^ (t + (insert i.val S).card + 1).natAbs *
        (-1) ^ ((insert i.val S).filter (· < j.val)).card * f j.val ^ (n + 1)) =
      -(((-1 : A) ^ (t + 1 + S.card + 1).natAbs * (-1) ^ (S.filter (· < j.val)).card *
        f j.val ^ (n + 1)) *
      ((-1 : A) ^ (t + (insert j.val S).card + 1).natAbs *
        (-1) ^ ((insert j.val S).filter (· < i.val)).card * f i.val ^ (n + 1))) := by
    simp only [Finset.card_insert_of_notMem i.property, Finset.card_insert_of_notMem hj,
      Nat.cast_add, Nat.cast_one]
    rw [show t + ((S.card : ℤ) + 1) + 1 = t + 1 + S.card + 1 by omega]
    linear_combination
      ((-1 : A) ^ (t + 1 + S.card + 1).natAbs) ^ 2 * f i.val ^ (n + 1) *
        f j.val ^ (n + 1) * hc
  rw [hcoeff, neg_smul]
  apply neg_add_eq_zero.mpr
  congr 1
  exact eqToHom_apply_eq (fun T : Finset (Fin r) ↦ K.X (t + T.card)) x _ _
    (Finset.insert_comm j.val i.val S)
set_option backward.isDefEq.respectTransparency false in
private theorem filteredDifferential_square {r : ℕ} (f : Fin r → A) (p : Option ℤ)
    (n : ℕ) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i j k : ℤ) :
    filteredDifferential f p n K i j ≫ filteredDifferential f p n K j k = 0 := by
  apply filteredTerm_hom_ext p K k
  simp only [Category.assoc, filteredDifferential_projection, zero_comp]
  rw [← Category.assoc, filteredDifferential_projection, Category.assoc]
  by_cases hij : i + 1 = j
  · subst j
    by_cases hjk : i + 1 + 1 = k
    · subst k
      simp only [filteredDifferential, eqToHom_refl,
        termProjection_none, termSection_none, Category.id_comp, Category.comp_id]
      erw [coefficientKoszulDifferential_square, comp_zero]
    · simp only [filteredDifferential, dite_eq_right hjk, comp_zero]
  · simp only [filteredDifferential, dite_eq_right hij, zero_comp, comp_zero]

private theorem tensor_mk_naturality {R : Type u} [CommRing R]
    {M N P : ModuleCat.{u} R} (g : M ⟶ N) (e : P) :
    g ≫ ModuleCat.ofHom ((TensorProduct.mk R N P).flip e) =
      ModuleCat.ofHom ((TensorProduct.mk R M P).flip e) ≫ (g ▷ P) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem comparisonTerm_naturality {r : ℕ} (f : Fin r → A) (p : Option ℤ) (n : ℕ)
    {K L : CochainComplex (ModuleCat.{v} A) ℤ} (g : K ⟶ L) (t : ℤ) :
    (AdicKoszul.moduleUniverseLift A).map (filteredMapTerm (r := r) p g t) ≫
        comparisonTerm f p n L t =
      comparisonTerm f p n K t ≫ ((standardCoefficientKoszulStage f p n).map g).f t := by
  classical
  simp only [comparisonTerm, Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
  apply Finset.sum_congr rfl
  intro S _
  change _ = _ ≫ _ ≫ (HomologicalComplex.ιMapBifunctor _ _ _ _ _ _ _ _) ≫
    (HomologicalComplex.mapBifunctorMap ((complexUniverseLift (A := A)).map g) (𝟙 _) _ _).f t
  rw [HomologicalComplex.ι_mapBifunctorMap]
  change _ = _ ≫ _ ≫
    ((AdicKoszul.moduleUniverseLift A).map (g.f (t + S.card)) ▷
      (standardKoszulStage (fun a ↦ (ULift.up (f a) : ULift.{v} A)) p n).X (-(S.card : ℤ))) ≫ _
  have hp : filteredMapTerm (r := r) p g t ≫
      (termProjection p L t ≫ ModuleCat.ofHom (LinearMap.proj S)) =
      (termProjection p K t ≫ ModuleCat.ofHom (LinearMap.proj S)) ≫ g.f (t + S.card) := by
    rw [← Category.assoc, filteredMapTerm_projection, Category.assoc,
      coefficientMapTerm_proj, ← Category.assoc]
  rw [← Category.assoc, ← Functor.map_comp, hp, Functor.map_comp]
  simp only [Category.assoc]
  have ht := tensor_mk_naturality
    ((AdicKoszul.moduleUniverseLift A).map (g.f (t + S.card)))
    (koszulBasisVector (fun a ↦ (ULift.up (f a) : ULift.{v} A)) p n S)
  exact congrArg (fun a ↦
    (AdicKoszul.moduleUniverseLift A).map
      (termProjection p K t ≫ ModuleCat.ofHom (LinearMap.proj S)) ≫ a ≫
      HomologicalComplex.ιTensorObj ((complexUniverseLift (A := A)).obj L)
        (standardKoszulStage (fun a ↦ (ULift.up (f a) : ULift.{v} A)) p n)
        (t + S.card) (-(S.card : ℤ)) t (by omega)) ht


private theorem comparison_naturality {r : ℕ} {f : Fin r → A}
    (h : FormulaLaws.{u, v} f) (p : Option ℤ) (n : ℕ)
    {K L : CochainComplex (ModuleCat.{v} A) ℤ} (g : K ⟶ L) :
    (complexUniverseLift (A := A)).map (h.stageMap p n g) ≫ h.comparisonMap p n L =
      h.comparisonMap p n K ≫ (standardCoefficientKoszulStage f p n).map g := by
  apply HomologicalComplex.hom_ext
  intro t
  exact comparisonTerm_naturality f p n g t
private def gradedTermIso (r : ℕ) (p : ℤ) (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    ((coefficientKoszulGradedPiece (A := A) r p).obj K).X t ≅
      ModuleCat.of A (∀ _ : KoszulBasis r p.natAbs, (K⟦-p⟧).X t) :=
  PreservesProduct.iso (HomologicalComplex.eval (ModuleCat.{v} A) (ComplexShape.up ℤ) t)
    (fun _ : KoszulBasis r p.natAbs ↦ K⟦-p⟧) ≪≫
      ModuleCat.piIsoPi (fun _ : KoszulBasis r p.natAbs ↦ (K⟦-p⟧).X t)

set_option backward.isDefEq.respectTransparency false in
private theorem gradedTermIso_hom_proj (r : ℕ) (p : ℤ)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) (S : KoszulBasis r p.natAbs) :
    (gradedTermIso r p K t).hom ≫ ModuleCat.ofHom (LinearMap.proj S) =
      (Limits.Pi.π (fun _ : KoszulBasis r p.natAbs ↦ K⟦-p⟧) S).f t := by
  simp only [gradedTermIso, Iso.trans_hom, Category.assoc,
    ModuleCat.piIsoPi_hom_ker_subtype, PreservesProduct.iso_hom]
  exact piComparison_comp_π _ _ S

set_option backward.isDefEq.respectTransparency false in
private theorem gradedProjection_f_proj {r : ℕ} {f : Fin r → A} (h : FormulaLaws.{u, v} f)
    (p : ℤ) (hp : p ≤ 0) (n : ℕ) (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (t : ℤ) (S : KoszulBasis r p.natAbs) :
    (h.gradedProjection p hp n K).f t ≫ (gradedTermIso r p K t).hom ≫
      ModuleCat.ofHom (LinearMap.proj S) = gradedComponentTerm p hp K S t := by
  rw [gradedTermIso_hom_proj, ← HomologicalComplex.comp_f]
  simp only [FormulaLaws.gradedProjection, Limits.Pi.lift_comp_π]

private def gradedTermSection {r : ℕ} (p : ℤ) (hp : p ≤ 0)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    ModuleCat.of A (∀ _ : KoszulBasis r p.natAbs, (K⟦-p⟧).X t) ⟶
      filteredTerm (r := r) (some p) K t :=
  ModuleCat.ofHom (LinearMap.pi fun S : Finset (Fin r) ↦
    if hS : S.card = p.natAbs then
      (((-1 : A) ^ (t * (-p)).natAbs) •
        ((CochainComplex.shiftFunctorObjXIso K (-p) t (t + S.card)
          (by simp [hS, abs_of_nonpos hp])).hom.hom.comp (LinearMap.proj ⟨S, hS⟩)))
    else 0) ≫ termSection (some p) K t

set_option backward.isDefEq.respectTransparency false in
private theorem gradedTermSection_component {r : ℕ} (p : ℤ) (hp : p ≤ 0)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) (S : KoszulBasis r p.natAbs) :
    gradedTermSection p hp K t ≫ gradedComponentTerm p hp K S t =
      ModuleCat.ofHom (LinearMap.proj S) := by
  classical
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  dsimp only [gradedTermSection, gradedComponentTerm, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_smul, LinearMap.smul_apply]
  change ((-1 : A) ^ (t * (-p)).natAbs) •
    (CochainComplex.shiftFunctorObjXIso K (-p) t (t + S.val.card)
      (by simp [S.property, abs_of_nonpos hp])).inv.hom
        (((termSection (some p) K t ≫ termProjection (some p) K t).hom _) S.val) = x S
  rw [termSection_projection_apply]
  simp only [CutoffLE, S.property, Int.natCast_natAbs, abs_of_nonpos hp, neg_neg,
    le_refl, ite_true, ModuleCat.hom_ofHom, LinearMap.pi_apply,
    dite_true, LinearMap.smul_apply, LinearMap.comp_apply]
  simp only [map_smul, smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]
  exact ConcreteCategory.congr_hom
    (CochainComplex.shiftFunctorObjXIso K (-p) t (t + S.val.card)
      (by simp [S.property, abs_of_nonpos hp])).hom_inv_id (x S)

set_option backward.isDefEq.respectTransparency false in
private theorem gradedProjection_epi {r : ℕ} {f : Fin r → A} (h : FormulaLaws.{u, v} f)
    (p : ℤ) (hp : p ≤ 0) (n : ℕ) (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    Epi (h.gradedProjection p hp n K) := by
  apply HomologicalComplex.epi_of_epi_f
  intro t
  have hsec : gradedTermSection p hp K t ≫ (h.gradedProjection p hp n K).f t ≫
      (gradedTermIso r p K t).hom = 𝟙 _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext S
    change ((h.gradedProjection p hp n K).f t ≫ (gradedTermIso r p K t).hom).hom
      ((gradedTermSection p hp K t).hom x) S = x S
    have hproj := gradedProjection_f_proj h p hp n K t S
    have heq := congrArg (fun a ↦ gradedTermSection p hp K t ≫ a) hproj
    rw [← Category.assoc, gradedTermSection_component] at heq
    exact ConcreteCategory.congr_hom heq x
  have : SplitEpi ((h.gradedProjection p hp n K).f t) :=
    { section_ := (gradedTermIso r p K t).hom ≫ gradedTermSection p hp K t
      id := by
        apply (cancel_mono (gradedTermIso r p K t).hom).mp
        simpa only [Category.assoc, Category.id_comp, Category.comp_id] using
          congrArg (fun a ↦ (gradedTermIso r p K t).hom ≫ a) hsec }
  exact this.epi

set_option backward.isDefEq.respectTransparency false in
private theorem gradedComponentTerm_eq_zero {r : ℕ} (p : ℤ) (hp : p ≤ 0)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) (S : KoszulBasis r p.natAbs)
    (x : filteredTerm (r := r) (some p) K t)
    (hx : (gradedComponentTerm p hp K S t).hom x = 0) :
    (termProjection (some p) K t).hom x S.val = 0 := by
  change ((-1 : A) ^ (t * (-p)).natAbs) •
    (CochainComplex.shiftFunctorObjXIso K (-p) t (t + S.val.card)
      (by simp [S.property, abs_of_nonpos hp])).inv.hom
        ((termProjection (some p) K t).hom x S.val) = 0 at hx
  have hz := ((isUnit_neg_one (α := A)).pow _).smul_eq_zero.mp hx
  have hz' := congrArg (CochainComplex.shiftFunctorObjXIso K (-p) t (t + S.val.card)
    (by simp [S.property, abs_of_nonpos hp])).hom.hom hz
  have hid := ConcreteCategory.congr_hom
    (CochainComplex.shiftFunctorObjXIso K (-p) t (t + S.val.card)
      (by simp [S.property, abs_of_nonpos hp])).inv_hom_id
    ((termProjection (some p) K t).hom x S.val)
  exact hid.symm.trans (hz'.trans (map_zero _))

set_option backward.isDefEq.respectTransparency false in
private theorem gradedProjection_kernel {r : ℕ} {f : Fin r → A} (h : FormulaLaws.{u, v} f)
    (p : ℤ) (hp : p ≤ 0) (n : ℕ) (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ)
    (x : (h.stage (some p) n K).X t) (hx : (h.gradedProjection p hp n K).f t x = 0) :
    ∃ y : (h.stage (some (p + 1)) n K).X t,
      filtrationInclusionTerm (r := r) (some p) (some (p + 1)) K t y = x := by
  refine ⟨(termSection (some (p + 1)) K t).hom ((termProjection (some p) K t).hom x), ?_⟩
  have hinj : Function.Injective (termProjection (r := r) (some p) K t).hom := by
    intro a b heq
    have ht := congrArg (termSection (some p) K t).hom heq
    have hid := term_projection_section (r := r) (some p) K t
    have ha := ConcreteCategory.congr_hom hid a
    have hb := ConcreteCategory.congr_hom hid b
    exact ha.symm.trans (ht.trans hb)
  apply hinj
  have hinc := filtrationInclusionTerm_projection (r := r) (some p) (some (p + 1))
    (by dsimp [CutoffLE]; omega) K t
  change (filtrationInclusionTerm (some p) (some (p + 1)) K t ≫
    termProjection (some p) K t).hom _ = _
  rw [hinc]
  funext S
  change ((termSection (some (p + 1)) K t ≫ termProjection (some (p + 1)) K t).hom
    ((termProjection (some p) K t).hom x)) S = _
  rw [termSection_projection_apply]
  split_ifs with hS
  · rfl
  · symm
    by_cases hcard : S.card = p.natAbs
    · apply gradedComponentTerm_eq_zero p hp K t ⟨S, hcard⟩ x
      have heq := gradedProjection_f_proj h p hp n K t ⟨S, hcard⟩
      have hval := congrArg (fun a ↦ a.hom x) heq
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, hx, map_zero] using! hval.symm
    · apply termProjection_apply_eq_zero
      simp only [CutoffLE] at hS ⊢
      have hnat : (p.natAbs : ℤ) = -p := by rw [Int.natCast_natAbs, abs_of_nonpos hp]
      omega

set_option backward.isDefEq.respectTransparency false in
private def gradedShortComplex {r : ℕ} {f : Fin r → A} (h : FormulaLaws.{u, v} f)
    (p : ℤ) (hp : p ≤ 0) (n : ℕ) (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    ShortComplex (CochainComplex (ModuleCat.{v} A) ℤ) :=
  ShortComplex.mk
    (((h.inclusion (some p) (some (p + 1)) (by dsimp [CutoffLE]; omega)).app K).app ⟨n⟩)
    (h.gradedProjection p hp n K) (by
      apply Limits.Pi.hom_ext
      intro S
      rw [Category.assoc, FormulaLaws.gradedProjection, Limits.Pi.lift_comp_π, zero_comp]
      exact HomologicalComplex.hom_ext _ _ (h.graded_vanish p hp K S))

private theorem gradedShortComplex_shortExact {r : ℕ} {f : Fin r → A}
    (h : FormulaLaws.{u, v} f) (p : ℤ) (hp : p ≤ 0) (n : ℕ)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    (gradedShortComplex h p hp n K).ShortExact where
  mono_f := inclusion_mono h (some p) (some (p + 1)) (by dsimp [CutoffLE]; omega) n K
  epi_g := gradedProjection_epi h p hp n K
  exact := by
    apply HomologicalComplex.exact_of_degreewise_exact
    intro t
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    exact gradedProjection_kernel h p hp n K t x hx

private theorem graded_isIso {r : ℕ} {f : Fin r → A} (h : FormulaLaws.{u, v} f)
    (p : ℤ) (hp : p ≤ 0) (n : ℕ) (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    IsIso (h.gradedMap p hp n K) :=
  ((cokernelIsCokernel (gradedShortComplex h p hp n K).f).nonempty_isColimit_iff_isIso_desc).mp
    ⟨(gradedShortComplex_shortExact h p hp n K).gIsCokernel⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem quasiIso_middle {C : Type*} [Category* C] [Abelian C]
    {S₁ S₂ : ShortComplex (CochainComplex C ℤ)} (φ : S₁ ⟶ S₂)
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) [QuasiIso φ.τ₁] [QuasiIso φ.τ₃] :
    QuasiIso φ.τ₂ := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hm : Mono (HomologicalComplex.homologyMap φ.τ₂ i) := by
    apply CategoryTheory.Abelian.mono_of_epi_of_mono_of_mono
      ((ComposableArrows.δ₀Functor ⋙ ComposableArrows.δ₀Functor).map
        (HomologicalComplex.HomologySequence.mapComposableArrows₅ φ hS₁ hS₂ (i - 1) i (by
          dsimp
          omega)))
    · exact (HomologicalComplex.HomologySequence.composableArrows₅_exact hS₁ (i - 1) i
        (by dsimp; omega)).δ₀.δ₀
    · exact (HomologicalComplex.HomologySequence.composableArrows₅_exact hS₂ (i - 1) i
        (by dsimp; omega)).δ₀.δ₀
    · exact inferInstanceAs (Epi (HomologicalComplex.homologyMap φ.τ₃ (i - 1)))
    · exact inferInstanceAs (Mono (HomologicalComplex.homologyMap φ.τ₁ i))
    · exact inferInstanceAs (Mono (HomologicalComplex.homologyMap φ.τ₃ i))
  have he : Epi (HomologicalComplex.homologyMap φ.τ₂ i) := by
    apply CategoryTheory.Abelian.epi_of_epi_of_epi_of_mono
      ((ComposableArrows.δlastFunctor ⋙ ComposableArrows.δlastFunctor).map
        (HomologicalComplex.HomologySequence.mapComposableArrows₅ φ hS₁ hS₂ i (i + 1) rfl))
    · exact (HomologicalComplex.HomologySequence.composableArrows₅_exact hS₁ i (i + 1)
      rfl).δlast.δlast
    · exact (HomologicalComplex.HomologySequence.composableArrows₅_exact hS₂ i (i + 1)
      rfl).δlast.δlast
    · exact inferInstanceAs (Epi (HomologicalComplex.homologyMap φ.τ₁ i))
    · exact inferInstanceAs (Epi (HomologicalComplex.homologyMap φ.τ₃ i))
    · exact inferInstanceAs (Mono (HomologicalComplex.homologyMap φ.τ₁ (i + 1)))
  exact isIso_of_mono_of_epi _

set_option backward.isDefEq.respectTransparency false in
private theorem quasiIso_piMap {ι : Type} [Finite ι]
    {K L : ι → CochainComplex (ModuleCat.{v} A) ℤ} (g : ∀ i, K i ⟶ L i)
    [∀ i, QuasiIso (g i)] : QuasiIso (Limits.Pi.map g) := by
  classical
  rw [quasiIso_iff]
  intro t
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let F := HomologicalComplex.homologyFunctor (ModuleCat.{v} A) (ComplexShape.up ℤ) t
  have hnat : F.map (Limits.Pi.map g) ≫ piComparison F L =
      piComparison F K ≫ Limits.Pi.map (fun i ↦ F.map (g i)) := by
    apply Limits.Pi.hom_ext
    intro i
    simp only [Category.assoc, Limits.Pi.map_π, piComparison_comp_π_assoc,
      piComparison_comp_π, ← F.map_comp]
  let : Fintype ι := Fintype.ofFinite ι
  have hK : IsIso (piComparison F K) := (PreservesProduct.iso F K).isIso_hom
  have hL : IsIso (piComparison F L) := (PreservesProduct.iso F L).isIso_hom
  have hg (i : ι) : IsIso (F.map (g i)) := by
    change IsIso (HomologicalComplex.homologyMap (g i) t)
    infer_instance
  have : IsIso (F.map (Limits.Pi.map g) ≫ piComparison F L) := by
    rw [hnat]
    infer_instance
  exact IsIso.of_isIso_comp_right (F.map (Limits.Pi.map g)) (piComparison F L)

set_option backward.isDefEq.respectTransparency false in
private theorem coefficientKoszulGradedPiece_map_quasiIso (r : ℕ) (p : ℤ)
    {K L : CochainComplex (ModuleCat.{v} A) ℤ} (g : K ⟶ L) [QuasiIso g] :
    QuasiIso ((coefficientKoszulGradedPiece (A := A) r p).map g) :=
  quasiIso_piMap (fun _ : KoszulBasis r p.natAbs ↦
    (shiftFunctor (CochainComplex (ModuleCat.{v} A) ℤ) (-p)).map g)

set_option backward.isDefEq.respectTransparency false in
private theorem stageMap_quasiIso_step {r : ℕ} {f : Fin r → A} (h : FormulaLaws.{u, v} f)
    (p : ℤ) (hp : p ≤ 0) (n : ℕ) {K L : CochainComplex (ModuleCat.{v} A) ℤ}
    (g : K ⟶ L) [QuasiIso g] [QuasiIso (h.stageMap (some (p + 1)) n g)] :
    QuasiIso (h.stageMap (some p) n g) := by
  let φ : gradedShortComplex h p hp n K ⟶ gradedShortComplex h p hp n L :=
    { τ₁ := h.stageMap (some (p + 1)) n g
      τ₂ := h.stageMap (some p) n g
      τ₃ := (coefficientKoszulGradedPiece (A := A) r p).map g
      comm₁₂ := by
        apply HomologicalComplex.hom_ext
        intro t
        exact (filtrationInclusionTerm_naturality (some p) (some (p + 1))
          (by dsimp [CutoffLE]; omega) g t)
      comm₂₃ := graded_naturality h p hp n g }
  have : QuasiIso φ.τ₃ := coefficientKoszulGradedPiece_map_quasiIso r p g
  exact quasiIso_middle φ (gradedShortComplex_shortExact h p hp n K)
    (gradedShortComplex_shortExact h p hp n L)

private theorem stageMap_quasiIso_of_pos {r : ℕ} {f : Fin r → A} (h : FormulaLaws.{u, v} f)
    (p : ℤ) (hp : 0 < p) (n : ℕ) {K L : CochainComplex (ModuleCat.{v} A) ℤ}
    (g : K ⟶ L) : QuasiIso (h.stageMap (some p) n g) := by
  have := (stage_isZero h p hp n K).isIso (stage_isZero h p hp n L) (h.stageMap (some p) n g)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem stageMap_quasiIso_neg {r : ℕ} {f : Fin r → A} (h : FormulaLaws.{u, v} f)
    (d n : ℕ) {K L : CochainComplex (ModuleCat.{v} A) ℤ}
    (g : K ⟶ L) [QuasiIso g] : QuasiIso (h.stageMap (some (-(d : ℤ))) n g) := by
  induction d with
  | zero =>
    have : QuasiIso (h.stageMap (some (0 + 1)) n g) :=
      stageMap_quasiIso_of_pos h 1 (by omega) n g
    exact stageMap_quasiIso_step h 0 (le_refl 0) n g
  | succ d ih =>
    have : QuasiIso (h.stageMap (some (-((d + 1 : ℕ) : ℤ) + 1)) n g) := by
      rw [show -((d + 1 : ℕ) : ℤ) + 1 = -(d : ℤ) by omega]
      exact ih
    exact stageMap_quasiIso_step h (-((d + 1 : ℕ) : ℤ)) (by omega) n g

set_option backward.isDefEq.respectTransparency false in
public theorem stageMap_quasiIso {r : ℕ} {f : Fin r → A} (h : FormulaLaws.{u, v} f)
    (p : Option ℤ) (n : ℕ) {K L : CochainComplex (ModuleCat.{v} A) ℤ}
    (g : K ⟶ L) [QuasiIso g] : QuasiIso (h.stageMap p n g) := by
  cases p with
  | some p =>
    by_cases hp : p ≤ 0
    · have heq : -(p.natAbs : ℤ) = p := by rw [Int.natCast_natAbs, abs_of_nonpos hp, neg_neg]
      have hqi := stageMap_quasiIso_neg h p.natAbs n g
      rwa [heq] at hqi
    · exact stageMap_quasiIso_of_pos h p (by omega) n g
  | none =>
    let eK := (((h.inclusion none (some (-(r : ℤ))) trivial).app K).app ⟨n⟩)
    let eL := (((h.inclusion none (some (-(r : ℤ))) trivial).app L).app ⟨n⟩)
    have : IsIso eK := filtration_exhaustive h _ (le_refl _) n K
    have : IsIso eL := filtration_exhaustive h _ (le_refl _) n L
    have := stageMap_quasiIso_neg h r n g
    have heq : eK ≫ h.stageMap none n g = h.stageMap (some (-(r : ℤ))) n g ≫ eL := by
      apply HomologicalComplex.hom_ext
      intro t
      exact (filtrationInclusionTerm_naturality none (some (-(r : ℤ))) trivial g t).symm
    have : QuasiIso (eK ≫ h.stageMap none n g) := by
      rw [heq]
      infer_instance
    exact quasiIso_of_comp_left eK (h.stageMap none n g)

private abbrev orderedWedge {R M I : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [LinearOrder I] (v : I → M) (S : Finset I) : ExteriorAlgebra R M :=
  (S.sort.map fun i ↦ ExteriorAlgebra.ι R (v i)).prod

private theorem orderedWedge_insert {R M I : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [LinearOrder I] (v : I → M) (S : Finset I) (i : I)
    (hi : ∀ j ∈ S, i < j) :
    orderedWedge (R := R) v (insert i S) = ExteriorAlgebra.ι R (v i) * orderedWedge v S := by
  have hnot : i ∉ S := fun h ↦ (hi i h).false
  simp only [orderedWedge, Finset.sort_insert (· ≤ ·) (fun j hj ↦ (hi j hj).le) hnot,
    List.map_cons, List.prod_cons]

private theorem contraction_orderedWedge {R M I : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [LinearOrder I] (φ : Module.Dual R M) (v : I → M) (S : Finset I) :
    Koszul.contraction φ (orderedWedge v S) =
      ∑ i ∈ S, ((-1 : R) ^ (S.filter (· < i)).card * φ (v i)) • orderedWedge v (S.erase i) := by
  classical
  induction S using Finset.induction_on_min with
  | empty => simp [orderedWedge, Koszul.contraction]
  | @insert i S hmin ih =>
    have hi : i ∉ S := fun h ↦ (hmin i h).false
    have hfilter : (insert i S).filter (· < i) = ∅ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.notMem_empty, iff_false,
        not_and, not_lt]
      rintro (rfl | hj)
      · rfl
      · exact (hmin j hj).le
    rw [orderedWedge_insert v S i hmin, Koszul.contraction,
      CliffordAlgebra.contractLeft_ι_mul, ← Koszul.contraction, ih,
      Finset.sum_insert hi, hfilter, Finset.card_empty, pow_zero, one_mul,
      Finset.erase_insert hi]
    rw [sub_eq_add_neg]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hij : i ≠ j := (hmin j hj).ne
    have he : (insert i S).erase j = insert i (S.erase j) := Finset.erase_insert_of_ne hij
    have hf : (insert i S).filter (· < j) = insert i (S.filter (· < j)) := by
      simp [Finset.filter_insert, hmin j hj]
    rw [he, orderedWedge_insert v (S.erase j) i (fun k hk ↦ hmin k (Finset.mem_of_mem_erase hk)),
      hf, Finset.card_insert_of_notMem (fun hh ↦ hi (Finset.mem_filter.mp hh).1),
      pow_succ, mul_smul_comm]
    simp [mul_smul]

private theorem exteriorPower_basis_coe {r : ℕ} (S : Finset (Fin r)) :
    (((Pi.basisFun A (Fin r)).exteriorPower S.card ⟨S, rfl⟩ :
      ExteriorAlgebra A (Fin r → A))) =
      orderedWedge (R := A) (fun i ↦ Pi.single i 1) S := by
  rw [exteriorPower.basis_apply]
  change ExteriorAlgebra.ιMulti A S.card _ = _
  rw [ExteriorAlgebra.ιMulti_apply]
  simp only [Function.comp_apply, Pi.basisFun_apply,
    Set.powersetCard.ofFinEmbEquiv_symm_apply]
  change (List.ofFn (fun i ↦ ExteriorAlgebra.ι A
    (Pi.single ((S.orderEmbOfFin rfl) i) (1 : A) : Fin r → A))).prod = _
  rw [List.ofFn_comp' (S.orderEmbOfFin (k := S.card) rfl)
    (fun j : Fin r ↦ ExteriorAlgebra.ι A (Pi.single j (1 : A) : Fin r → A)),
    List.ofFn_eq_map,
    Finset.listMap_orderEmbOfFin_finRange]

private theorem exteriorPower_basis_coe_of_card {r j : ℕ} (S : Finset (Fin r))
    (hS : S.card = j) :
    (((Pi.basisFun A (Fin r)).exteriorPower j ⟨S, hS⟩ :
      ExteriorAlgebra A (Fin r → A))) =
      orderedWedge (R := A) (fun i ↦ Pi.single i 1) S := by
  subst j
  exact exteriorPower_basis_coe S

private theorem koszul_d_basis {r : ℕ} (f : Fin r → A) (j : ℕ)
    (S : KoszulBasis r (j + 1)) :
    Koszul.d (Koszul.seqDual f) j ((Pi.basisFun A (Fin r)).exteriorPower (j + 1) S) =
      ∑ i : S.1, ((-1 : A) ^ (S.1.filter (· < i.1)).card * f i.1) •
        (Pi.basisFun A (Fin r)).exteriorPower j
          ⟨S.1.erase i.1, by
            change (S.1.erase i.1).card = j
            rw [Finset.card_erase_of_mem i.2, S.2]; omega⟩ := by
  apply Subtype.ext
  erw [Koszul.d_apply_coe, exteriorPower_basis_coe_of_card S.1 S.2,
    contraction_orderedWedge]
  simp only [Koszul.seqDual_single, Submodule.coe_sum, Submodule.coe_smul]
  rw [← Finset.sum_coe_sort S.1]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact (exteriorPower_basis_coe_of_card (S.1.erase i.1) _).symm

set_option backward.isDefEq.respectTransparency false in
private theorem koszulPowerTransition_basis {r : ℕ} (f : Fin r → A)
    (m n : ℕ) (hmn : n ≤ m) (S : Finset (Fin r)) :
    (AdicKoszul.koszulPowerTransition f m n hmn).f S.card
        ((Pi.basisFun A (Fin r)).exteriorPower S.card ⟨S, rfl⟩) =
      (∏ i ∈ S, f i ^ (m - n)) •
        ((Pi.basisFun A (Fin r)).exteriorPower S.card ⟨S, rfl⟩) := by
  classical
  let e := Set.powersetCard.ofFinEmbEquiv.symm (⟨S, rfl⟩ : Set.powersetCard (Fin r) S.card)
  have hτ := (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (_root_.koszulPowerComplexes_form_inverseSystem f))))).2.2.2.2.1
    m n hmn S.card (fun k ↦ (Pi.single (e k) (1 : A) : Fin r → A))
  have hp : (∏ k : Fin S.card, f (e k) ^ (m - n)) = ∏ i ∈ S, f i ^ (m - n) := by
    apply Finset.prod_bij (fun k _ ↦ e k)
    · intro k _
      exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem ⟨S, rfl⟩ (e k)).mp
        ⟨k, rfl⟩
    · intro k _ l _ he
      exact e.injective he
    · intro i hi
      obtain ⟨k, hk⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
        ⟨S, rfl⟩ i).mpr hi
      exact ⟨k, Finset.mem_univ _, hk⟩
    · intros
      rfl
  have hs : (fun k i ↦ f i ^ (m - n) * (Pi.single (e k) 1 : Fin r → A) i) =
      (fun k ↦ (f (e k) ^ (m - n)) • (Pi.single (e k) 1 : Fin r → A)) := by
    funext k i
    by_cases hi : i = e k
    · subst i
      simp
    · simp [hi]
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family]
  have hb : ((Pi.basisFun A (Fin r)) ∘ e) =
      (fun k ↦ (Pi.single (e k) (1 : A) : Fin r → A)) := by
    funext k
    exact Pi.basisFun_apply A (Fin r) (e k)
  change (AdicKoszul.koszulPowerTransition f m n hmn).f S.card
    (exteriorPower.ιMulti A S.card ((Pi.basisFun A (Fin r)) ∘ e)) =
    (∏ i ∈ S, f i ^ (m - n)) • exteriorPower.ιMulti A S.card
      ((Pi.basisFun A (Fin r)) ∘ e)
  rw [hb]
  erw [hτ]
  apply Subtype.ext
  change ExteriorAlgebra.ιMulti A S.card _ =
    (∏ i ∈ S, f i ^ (m - n)) • ExteriorAlgebra.ιMulti A S.card _
  rw [hs, AlternatingMap.map_smul_univ, hp]

private theorem stupidTruncSection_map {K L : CochainComplex (ModuleCat.{v} A) ℤ}
    (g : K ⟶ L) (p j : ℤ) :
    stupidTruncSection K p j ≫ (HomologicalComplex.stupidTruncMap g
      (ComplexShape.embeddingUpIntGE p)).f j = g.f j ≫ stupidTruncSection L p j := by
  by_cases hp : p ≤ j
  · have hj : (ComplexShape.embeddingUpIntGE p).f (j - p).toNat = j := by
      change p + ((j - p).toNat : ℤ) = j
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    simp only [stupidTruncSection, dite_eq_left hp]
    rw [← cancel_mono (L.stupidTruncXIso (ComplexShape.embeddingUpIntGE p) hj).hom,
      Category.assoc, HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom,
      Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · simp [stupidTruncSection, hp]

set_option backward.isDefEq.respectTransparency false in
private theorem koszulBasisVector_transition {r : ℕ} (f : Fin r → A)
    (p : Option ℤ) (m n : ℕ) (hmn : n ≤ m) (S : Finset (Fin r)) :
    (standardKoszulTransition f p m n hmn).f (-(S.card : ℤ))
        (koszulBasisVector f p m S) =
      (∏ i ∈ S, f i ^ (m - n)) • koszulBasisVector f p n S := by
  have hn : (standardKoszulTransition f none m n hmn).f (-(S.card : ℤ))
      (koszulBasisVector f none m S) =
      (∏ i ∈ S, f i ^ (m - n)) • koszulBasisVector f none n S := by
    let em := HomologicalComplex.extendXIso
      (Koszul.seqComplex fun i ↦ f i ^ (m + 1)) ComplexShape.embeddingDownNat
      (i := S.card) rfl
    let en := HomologicalComplex.extendXIso
      (Koszul.seqComplex fun i ↦ f i ^ (n + 1)) ComplexShape.embeddingDownNat
      (i := S.card) rfl
    have he : em.inv ≫ (standardKoszulTransition f none m n hmn).f (-(S.card : ℤ)) =
        (AdicKoszul.koszulPowerTransition f m n hmn).f S.card ≫ en.inv := by
      dsimp only [standardKoszulTransition, ComplexShape.Embedding.extendFunctor]
      erw [HomologicalComplex.extendMap_f _ _ (i := S.card) rfl]
      exact Iso.inv_hom_id_assoc em _
    have hev := ConcreteCategory.congr_hom he
      ((Pi.basisFun A (Fin r)).exteriorPower S.card ⟨S, rfl⟩)
    change _ = en.inv ((AdicKoszul.koszulPowerTransition f m n hmn).f S.card _) at hev
    exact hev.trans (by rw [koszulPowerTransition_basis, map_smul]; rfl)
  cases p with
  | none => exact hn
  | some p =>
    have hmap := ConcreteCategory.congr_hom
      (stupidTruncSection_map (standardKoszulTransition f none m n hmn) p (-(S.card : ℤ)))
      (koszulBasisVector f none m S)
    have hvalue := congrArg
      (fun x ↦ stupidTruncSection (standardKoszulStage f none n) p (-(S.card : ℤ)) x) hn
    exact hmap.trans (hvalue.trans (map_smul _ _ _))

set_option backward.isDefEq.respectTransparency false in
private theorem standardKoszul_section_projection {r : ℕ} (f : Fin r → A)
    (p : Option ℤ) (n : ℕ) (j : ℤ) :
    standardKoszulSectionTerm f p n j ≫ standardKoszulProjectionTerm f p n j =
      (by classical exact if CutoffLE p (some j) then 𝟙 _ else 0) := by
  classical
  cases p with
  | none => simp [standardKoszulSectionTerm, standardKoszulProjectionTerm, CutoffLE]
  | some p =>
    by_cases hp : p ≤ j <;>
      simp [standardKoszulSectionTerm, standardKoszulProjectionTerm,
        stupidTruncSection, stupidTruncProjection, standardKoszulStage, CutoffLE, hp]

private theorem koszulBasisVector_inclusion {r : ℕ} (f : Fin r → A)
    (p q : Option ℤ) (n : ℕ) (S : Finset (Fin r))
    (hS : CutoffLE q (some (-(S.card : ℤ)))) :
    standardKoszulInclusionTerm f p q n (-(S.card : ℤ)) (koszulBasisVector f q n S) =
      koszulBasisVector f p n S := by
  have he : koszulBasisVector f q n S =
      standardKoszulSectionTerm f q n (-(S.card : ℤ)) (koszulBasisVector f none n S) := by
    cases q <;> rfl
  rw [he]
  change ((standardKoszulSectionTerm f q n (-(S.card : ℤ)) ≫
    standardKoszulProjectionTerm f q n (-(S.card : ℤ))) ≫
    standardKoszulSectionTerm f p n (-(S.card : ℤ))) _ = _
  rw [standardKoszul_section_projection, ite_eq_left hS, Category.id_comp]
  cases p <;> rfl

private theorem tensor_mk_map {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R) {N P : ModuleCat.{u} R} (g : N ⟶ P) (e : N) :
    ModuleCat.ofHom ((TensorProduct.mk R M N).flip e) ≫ (M ◁ g) =
      ModuleCat.ofHom ((TensorProduct.mk R M P).flip (g e)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem comparison_inclusion {r : ℕ} {f : Fin r → A}
    (h : FormulaLaws.{u, v} f) (p q : Option ℤ) (hpq : CutoffLE p q) (n : ℕ)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    (complexUniverseLift (A := A)).map (((h.inclusion p q hpq).app K).app ⟨n⟩) ≫
        h.comparisonMap p n K =
      h.comparisonMap q n K ≫
        (𝟙 ((complexUniverseLift (A := A)).obj K) ⊗ₘ h.standardInclusion p q hpq n) := by
  classical
  apply HomologicalComplex.hom_ext
  intro t
  change (AdicKoszul.moduleUniverseLift A).map (filtrationInclusionTerm p q K t) ≫
    comparisonTerm f p n K t = comparisonTerm f q n K t ≫ _
  simp only [comparisonTerm, Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
  apply Finset.sum_congr rfl
  intro S _
  change _ = _ ≫ _ ≫ (HomologicalComplex.ιMapBifunctor _ _ _ _ _ _ _ _) ≫
    (HomologicalComplex.mapBifunctorMap (𝟙 _) (h.standardInclusion p q hpq n) _ _).f t
  rw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f]
  rw [CategoryTheory.Functor.map_id]
  simp only [NatTrans.id_app, Category.id_comp]
  change _ = _ ≫ _ ≫
    (((complexUniverseLift (A := A)).obj K).X (t + S.card) ◁
      standardKoszulInclusionTerm (fun a ↦ (ULift.up (f a) : ULift.{v} A)) p q n
        (-(S.card : ℤ))) ≫ _
  rw [← Category.assoc, ← Functor.map_comp]
  have hpr : filtrationInclusionTerm p q K t ≫
      (termProjection p K t ≫ ModuleCat.ofHom (LinearMap.proj S)) =
      termProjection q K t ≫ ModuleCat.ofHom (LinearMap.proj S) := by
    rw [← Category.assoc, filtrationInclusionTerm_projection p q hpq]
  rw [hpr]
  by_cases hS : CutoffLE q (some (-(S.card : ℤ)))
  · erw [← Category.assoc (ModuleCat.ofHom
        ((TensorProduct.mk (ULift.{v} A)
        (((complexUniverseLift (A := A)).obj K).X (t + S.card)) _).flip
          (koszulBasisVector (fun a ↦ (ULift.up (f a) : ULift.{v} A)) q n S))),
      tensor_mk_map,
      koszulBasisVector_inclusion _ p q n S hS]
    rfl
  · rw [termProjection_proj_eq_zero q K t S hS, Functor.map_zero]
    simp

set_option backward.isDefEq.respectTransparency false in
private theorem tensor_mk_smul {R : Type u} [CommRing R]
    (M N : ModuleCat.{u} R) (a : R) (e : N) :
    (a • 𝟙 M) ≫ ModuleCat.ofHom ((TensorProduct.mk R M N).flip e) =
      ModuleCat.ofHom ((TensorProduct.mk R M N).flip (a • e)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change TensorProduct.tmul R (a • x) e = TensorProduct.tmul R x (a • e)
  exact TensorProduct.smul_tmul a x e

end KoszulCoefficientTower

end

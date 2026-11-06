module

public import StacksFrontier.Homology.DerivedComplete.AdicKoszulCoefficientTower.Formulas
import all StacksFrontier.Homology.DerivedComplete.AdicKoszulCoefficientTower.Formulas
import Mathlib
import all Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Koszul towers with coefficients: laws of the filtration

The termwise laws of the finite exterior-basis formulas for the stupid filtration in the Koszul
direction: inclusions between cutoffs, the augmentation, compatibility with the signed
differential and with the power transitions, and the stupid truncations of the usual Koszul
complex.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u v

namespace KoszulCoefficientTower

variable {A : Type u} [CommRing A]

/-- Two maps into a product module agree if they agree on every coordinate. -/
private theorem hom_ext_pi {ι : Type} {F : ι → ModuleCat.{v} A} {M : ModuleCat.{v} A}
    {g h : M ⟶ ModuleCat.of A (∀ i, F i)} (H : ∀ (x : M) (i : ι), g.hom x i = h.hom x i) :
    g = h :=
  ModuleCat.hom_ext (LinearMap.ext fun x ↦ funext (H x))

private theorem cutoffLE_trans {p q s : Option ℤ} (hpq : CutoffLE p q)
    (hqs : CutoffLE q s) : CutoffLE p s := by
  cases p <;> cases q <;> cases s <;> simp_all [CutoffLE]
  omega

private theorem truncatedSummand_inclusion_projection (p q : Option ℤ)
    (hpq : CutoffLE p q) (j : ℤ) (M : ModuleCat.{v} A) :
    truncatedSummandProjection q j M ≫ truncatedSummandSection p j M ≫
        truncatedSummandProjection p j M = truncatedSummandProjection q j M := by
  rw [truncatedSummand_section_projection]
  by_cases h : CutoffLE p (some j)
  · simp [h, Category.comp_id]
  · have hq : ¬ CutoffLE q (some j) := fun hq ↦ h (cutoffLE_trans hpq hq)
    simp [h, truncatedSummandProjection_eq_zero q j M hq, comp_zero]

private theorem filtrationInclusionTerm_projection {r : ℕ} (p q : Option ℤ)
    (hpq : CutoffLE p q) (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    filtrationInclusionTerm (r := r) p q K t ≫ termProjection p K t =
      termProjection q K t := by
  refine hom_ext_pi fun x S ↦ ?_
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (truncatedSummand_inclusion_projection p q hpq (-(S.card : ℤ))
      (K.X (t + S.card)))) (x S)

private theorem filtrationInclusionTerm_comp {r : ℕ} (p q s : Option ℤ)
    (hpq : CutoffLE p q) (hqs : CutoffLE q s)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    filtrationInclusionTerm (r := r) q s K t ≫ filtrationInclusionTerm p q K t =
      filtrationInclusionTerm p s K t := by
  apply filteredTerm_hom_ext p K t
  simp only [Category.assoc, filtrationInclusionTerm_projection p q hpq,
    filtrationInclusionTerm_projection q s hqs,
    filtrationInclusionTerm_projection p s (cutoffLE_trans hpq hqs)]

private theorem filtrationInclusionTerm_naturality {r : ℕ} (p q : Option ℤ)
    (hpq : CutoffLE p q) {K L : CochainComplex (ModuleCat.{v} A) ℤ}
    (g : K ⟶ L) (t : ℤ) :
    filteredMapTerm (r := r) q g t ≫ filtrationInclusionTerm p q L t =
      filtrationInclusionTerm p q K t ≫ filteredMapTerm p g t := by
  apply filteredTerm_hom_ext p L t
  simp only [Category.assoc, filtrationInclusionTerm_projection p q hpq,
    filteredMapTerm_projection]
  rw [← Category.assoc, filtrationInclusionTerm_projection p q hpq]

private theorem filtrationInclusionTerm_transition {r : ℕ} (f : Fin r → A)
    (p q : Option ℤ) (hpq : CutoffLE p q) (m n : ℕ)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    filteredTransitionTerm f q m n K t ≫ filtrationInclusionTerm p q K t =
      filtrationInclusionTerm p q K t ≫ filteredTransitionTerm f p m n K t := by
  apply filteredTerm_hom_ext p K t
  simp only [Category.assoc, filtrationInclusionTerm_projection p q hpq,
    filteredTransitionTerm_projection]
  rw [← Category.assoc, filtrationInclusionTerm_projection p q hpq]

private theorem truncatedSummandSection_eq_zero (p : Option ℤ) (j : ℤ)
    (M : ModuleCat.{v} A) (h : ¬ CutoffLE p (some j)) :
    truncatedSummandSection p j M = 0 := by
  cases p with
  | none => exact (h trivial).elim
  | some p => exact (truncatedSummand_isZero p j M (lt_of_not_ge h)).eq_of_tgt _ _

private theorem truncatedSummand_section_map (p : Option ℤ) (j : ℤ)
    {M N : ModuleCat.{v} A} (g : M ⟶ N) :
    truncatedSummandSection p j M ≫ truncatedSummandProjection p j M ≫ g ≫
        truncatedSummandSection p j N = g ≫ truncatedSummandSection p j N := by
  rw [← Category.assoc, ← Category.assoc, truncatedSummand_section_projection]
  by_cases h : CutoffLE p (some j)
  · simp [h, Category.id_comp]
  · simp [h, truncatedSummandSection_eq_zero p j N h, zero_comp, comp_zero]

private theorem termSection_filteredMapTerm {r : ℕ} (p : Option ℤ)
    {K L : CochainComplex (ModuleCat.{v} A) ℤ} (g : K ⟶ L) (t : ℤ) :
    termSection (r := r) p K t ≫ filteredMapTerm p g t =
      coefficientMapTerm g t ≫ termSection p L t := by
  refine hom_ext_pi fun x S ↦ ?_
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (truncatedSummand_section_map p (-(S.card : ℤ)) (g.f (t + S.card)))) (x S)

private theorem termSection_filteredTransitionTerm {r : ℕ} (f : Fin r → A)
    (p : Option ℤ) (m n : ℕ) (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    termSection (r := r) p K t ≫ filteredTransitionTerm f p m n K t =
      coefficientKoszulTransitionTerm f m n K t ≫ termSection p K t := by
  refine hom_ext_pi fun x S ↦ ?_
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (truncatedSummand_section_map p (-(S.card : ℤ))
      ((∏ i ∈ S, f i ^ (m - n)) • 𝟙 (K.X (t + S.card))))) (x S)

private theorem hom_f_eqToHom {K L : CochainComplex (ModuleCat.{v} A) ℤ}
    (g : K ⟶ L) (i j : ℤ) (h : i = j) :
    g.f i ≫ eqToHom (congrArg L.X h) = eqToHom (congrArg K.X h) ≫ g.f j := by
  subst j
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem coefficientKoszulUnitTerm_naturality {r : ℕ}
    {K L : CochainComplex (ModuleCat.{v} A) ℤ} (g : K ⟶ L) (t : ℤ) :
    g.f t ≫ coefficientKoszulUnitTerm (r := r) L t =
      coefficientKoszulUnitTerm K t ≫ coefficientMapTerm g t := by
  classical
  refine hom_ext_pi fun x S ↦ ?_
  by_cases h : S = ∅
  · subst S
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (hom_f_eqToHom g t (t + 0) (by omega))) x
  · simp [coefficientKoszulUnitTerm, coefficientMapTerm, h]

private theorem filteredUnitTerm_naturality {r : ℕ} (p : Option ℤ)
    {K L : CochainComplex (ModuleCat.{v} A) ℤ} (g : K ⟶ L) (t : ℤ) :
    g.f t ≫ filteredUnitTerm (r := r) p L t =
      filteredUnitTerm p K t ≫ filteredMapTerm p g t := by
  simp only [filteredUnitTerm, Category.assoc, termSection_filteredMapTerm]
  rw [← Category.assoc, coefficientKoszulUnitTerm_naturality, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem coefficientKoszulUnitTerm_transition {r : ℕ} (f : Fin r → A)
    (m n : ℕ) (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    coefficientKoszulUnitTerm (r := r) K t ≫ coefficientKoszulTransitionTerm f m n K t =
      coefficientKoszulUnitTerm K t := by
  classical
  refine hom_ext_pi fun x S ↦ ?_
  by_cases h : S = ∅
  · subst S
    simp [coefficientKoszulUnitTerm, coefficientKoszulTransitionTerm]
  · simp [coefficientKoszulUnitTerm, coefficientKoszulTransitionTerm, h]

private theorem filteredUnitTerm_transition {r : ℕ} (f : Fin r → A)
    (p : Option ℤ) (m n : ℕ) (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    filteredUnitTerm (r := r) p K t ≫ filteredTransitionTerm f p m n K t =
      filteredUnitTerm p K t := by
  simp only [filteredUnitTerm, Category.assoc, termSection_filteredTransitionTerm]
  rw [← Category.assoc, coefficientKoszulUnitTerm_transition]

private theorem filteredTerm_isZero {r : ℕ} (p : ℤ) (hp : 0 < p)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    IsZero (filteredTerm (r := r) (some p) K t) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  constructor
  intro x y
  funext S
  exact (ModuleCat.isZero_iff_subsingleton.mp
    (truncatedSummand_isZero p (-(S.card : ℤ)) (K.X (t + S.card)) (by omega))).elim _ _

private theorem termProjection_isIso {r : ℕ} (p : Option ℤ)
    (hp : ∀ S : Finset (Fin r), CutoffLE p (some (-(S.card : ℤ))))
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    IsIso (termProjection (r := r) p K t) := by
  let e : filteredTerm (r := r) p K t ≅ coefficientKoszulTerm K t :=
    { hom := termProjection p K t
      inv := termSection p K t
      hom_inv_id := term_projection_section p K t
      inv_hom_id := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        funext S
        have hs := truncatedSummand_section_projection p (-(S.card : ℤ)) (K.X (t + S.card))
        rw [ite_eq_left (hp S)] at hs
        exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hs) (x S) }
  exact e.isIso_hom

private theorem filtrationInclusionTerm_mono {r : ℕ} (p q : Option ℤ)
    (hpq : CutoffLE p q) (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    Mono (filtrationInclusionTerm (r := r) p q K t) where
  right_cancellation g h heq := by
    apply filteredTerm_hom_ext q K t
    simpa only [Category.assoc, filtrationInclusionTerm_projection p q hpq] using
      congrArg (fun a ↦ a ≫ termProjection (r := r) p K t) heq

private theorem stage_isZero {r : ℕ} {f : Fin r → A} (h : FormulaLaws.{u, v} f)
    (p : ℤ) (hp : 0 < p) (n : ℕ) (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    IsZero (h.stage (some p) n K) :=
  (IsZero.iff_id_eq_zero _).mpr <|
    HomologicalComplex.hom_ext _ _ fun t ↦ (filteredTerm_isZero p hp K t).eq_of_src _ _

private theorem inclusion_mono {r : ℕ} {f : Fin r → A} (h : FormulaLaws.{u, v} f)
    (p q : Option ℤ) (hpq : CutoffLE p q) (n : ℕ)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    Mono (((h.inclusion p q hpq).app K).app ⟨n⟩) :=
  HomologicalComplex.mono_of_mono_f _ (filtrationInclusionTerm_mono p q hpq K)

private theorem inclusion_comp {r : ℕ} {f : Fin r → A} (h : FormulaLaws.{u, v} f)
    (p q s : Option ℤ) (hpq : CutoffLE p q) (hqs : CutoffLE q s) (hps : CutoffLE p s) :
    h.inclusion q s hqs ≫ h.inclusion p q hpq = h.inclusion p s hps :=
  NatTrans.ext <| funext fun K ↦ NatTrans.ext <| funext fun _ ↦
    HomologicalComplex.hom_ext _ _ (filtrationInclusionTerm_comp p q s hpq hqs K)

private theorem filtration_exhaustive {r : ℕ} {f : Fin r → A} (h : FormulaLaws.{u, v} f)
    (p : ℤ) (hp : p ≤ -(r : ℤ)) (n : ℕ) (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    IsIso (((h.inclusion none (some p) trivial).app K).app ⟨n⟩) := by
  have hterm (t : ℤ) : IsIso (termProjection (r := r) (some p) K t) := by
    apply termProjection_isIso
    intro S
    dsimp [CutoffLE]
    have hS : S.card ≤ r := by simpa using S.card_le_univ
    omega
  have hcomp (t : ℤ) :
      IsIso ((((h.inclusion none (some p) trivial).app K).app ⟨n⟩).f t) := by
    show IsIso (termProjection (r := r) (some p) K t ≫ 𝟙 (coefficientKoszulTerm K t))
    simpa only [Category.comp_id] using hterm t
  exact HomologicalComplex.Hom.isIso_of_components _

set_option backward.isDefEq.respectTransparency false in
private theorem coefficientKoszulDifferential_naturality {r : ℕ} (f : Fin r → A)
    (n : ℕ) {K L : CochainComplex (ModuleCat.{v} A) ℤ} (g : K ⟶ L) (t : ℤ) :
    coefficientMapTerm (r := r) g t ≫ coefficientKoszulDifferential f n L t =
      coefficientKoszulDifferential f n K t ≫ coefficientMapTerm g (t + 1) := by
  classical
  refine hom_ext_pi fun x S ↦ ?_
  dsimp [coefficientMapTerm, coefficientKoszulDifferential]
  simp only [map_add, map_sum, map_smul]
  congr 1
  · exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (g.comm (t + S.card) (t + 1 + S.card))) (x S)
  · apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (hom_f_eqToHom g (t + (insert i.1 S).card) (t + 1 + S.card) (by
        rw [Finset.card_insert_of_notMem i.2]
        push_cast
        omega))) (x (insert i.1 S))

private theorem termProjection_apply_eq_zero {r : ℕ} (p : Option ℤ)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) (S : Finset (Fin r))
    (hS : ¬ CutoffLE p (some (-(S.card : ℤ)))) (x : filteredTerm (r := r) p K t) :
    (termProjection p K t).hom x S = 0 :=
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (truncatedSummandProjection_eq_zero p (-(S.card : ℤ)) (K.X (t + S.card)) hS)) (x S)

private theorem termSection_projection_apply {r : ℕ} (p : Option ℤ)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ)
    (x : coefficientKoszulTerm (r := r) K t) (S : Finset (Fin r)) :
    ((termSection p K t ≫ termProjection p K t).hom x) S =
      (by classical exact if CutoffLE p (some (-(S.card : ℤ))) then x S else 0) := by
  classical
  have heq := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (truncatedSummand_section_projection p (-(S.card : ℤ)) (K.X (t + S.card)))) (x S)
  split_ifs at heq ⊢ <;> exact heq

private theorem cutoffLE_card_mono {r : ℕ} (p : Option ℤ) {S T : Finset (Fin r)}
    (hST : S ⊆ T) (hT : CutoffLE p (some (-(T.card : ℤ)))) :
    CutoffLE p (some (-(S.card : ℤ))) := by
  apply cutoffLE_trans hT
  dsimp [CutoffLE]
  exact neg_le_neg (Int.ofNat_le.mpr (Finset.card_le_card hST))

set_option backward.isDefEq.respectTransparency false in
private theorem coefficientKoszulDifferential_projection_eq_zero {r : ℕ} (f : Fin r → A)
    (p : Option ℤ) (n : ℕ) (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ)
    (S : Finset (Fin r)) (hS : ¬ CutoffLE p (some (-(S.card : ℤ))))
    (x : filteredTerm (r := r) p K t) :
    (coefficientKoszulDifferential f n K t).hom ((termProjection p K t).hom x) S = 0 := by
  classical
  dsimp only [coefficientKoszulDifferential, ModuleCat.hom_ofHom, LinearMap.coe_mk,
    AddHom.coe_mk]
  rw [termProjection_apply_eq_zero p K t S hS x, map_zero, zero_add]
  apply Finset.sum_eq_zero
  intro i _
  rw [termProjection_apply_eq_zero p K t (insert i.1 S)
    (fun hT ↦ hS (cutoffLE_card_mono p (Finset.subset_insert _ _) hT)) x,
    map_zero, smul_zero]

/-- The untruncated filtered differential is the coefficient differential. -/
private theorem filteredDifferential_none_succ {r : ℕ} (f : Fin r → A) (n : ℕ)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ) :
    filteredDifferential f none n K i (i + 1) = coefficientKoszulDifferential f n K i := by
  simp only [filteredDifferential, ↓reduceDIte]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem filteredDifferential_projection {r : ℕ} (f : Fin r → A) (p : Option ℤ)
    (n : ℕ) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i j : ℤ) :
    filteredDifferential f p n K i j ≫ termProjection p K j =
      termProjection p K i ≫ filteredDifferential f none n K i j := by
  classical
  by_cases hij : i + 1 = j
  · subst j
    simp only [filteredDifferential, eqToHom_refl, Category.comp_id,
      termProjection_none, termSection_none, Category.id_comp]
    refine hom_ext_pi fun x S ↦ ?_
    show ((termSection p K (i + 1) ≫ termProjection p K (i + 1)).hom
      ((coefficientKoszulDifferential f n K i).hom ((termProjection p K i).hom x))) S = _
    rw [termSection_projection_apply]
    split_ifs with hS
    · rfl
    · exact (coefficientKoszulDifferential_projection_eq_zero f p n K i S hS x).symm
  · simp only [filteredDifferential, dite_eq_right hij, comp_zero, zero_comp]

private theorem eqToHom_d (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (i i' j j' : ℤ) (hi : i = i') (hj : j = j') :
    eqToHom (congrArg K.X hi) ≫ K.d i' j' = K.d i j ≫ eqToHom (congrArg K.X hj) := by
  subst i'
  subst j'
  simp

private theorem coefficientKoszulUnitTerm_apply_of_ne {r : ℕ}
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) (S : Finset (Fin r))
    (hS : S ≠ ∅) (x : K.X t) : (coefficientKoszulUnitTerm K t).hom x S = 0 := by
  simp [coefficientKoszulUnitTerm, hS]

private theorem coefficientKoszulUnitTerm_apply_insert {r : ℕ}
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) (S : Finset (Fin r))
    (i : Fin r) (x : K.X t) : (coefficientKoszulUnitTerm K t).hom x (insert i S) = 0 :=
  coefficientKoszulUnitTerm_apply_of_ne K t (insert i S) (Finset.insert_ne_empty _ _) x

set_option backward.isDefEq.respectTransparency false in
private theorem coefficientKoszulUnitTerm_differential {r : ℕ} (f : Fin r → A) (n : ℕ)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    coefficientKoszulUnitTerm (r := r) K t ≫ coefficientKoszulDifferential f n K t =
      K.d t (t + 1) ≫ coefficientKoszulUnitTerm K (t + 1) := by
  classical
  refine hom_ext_pi fun x S ↦ ?_
  dsimp only [ModuleCat.hom_comp, LinearMap.comp_apply, coefficientKoszulDifferential,
    ModuleCat.hom_ofHom, LinearMap.coe_mk, AddHom.coe_mk]
  trans (K.d (t + S.card) (t + 1 + S.card)).hom
    ((coefficientKoszulUnitTerm K t).hom x S)
  · apply add_eq_left.mpr
    apply Finset.sum_eq_zero
    intro i _
    rw [coefficientKoszulUnitTerm_apply_insert K t S i.1 x, map_zero, smul_zero]
  by_cases hS : S = ∅
  · subst S
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (eqToHom_d K t (t + 0) (t + 1) (t + 1 + 0) (by omega) (by omega))) x
  · simp only [coefficientKoszulUnitTerm_apply_of_ne K _ S hS, map_zero]


set_option backward.isDefEq.respectTransparency false in
private theorem filteredMapTerm_comm {r : ℕ} (f : Fin r → A) (p : Option ℤ)
    (n : ℕ) {K L : CochainComplex (ModuleCat.{v} A) ℤ} (g : K ⟶ L) (i j : ℤ) :
    filteredMapTerm (r := r) p g i ≫ filteredDifferential f p n L i j =
      filteredDifferential f p n K i j ≫ filteredMapTerm p g j := by
  apply filteredTerm_hom_ext p L j
  simp only [Category.assoc, filteredDifferential_projection, filteredMapTerm_projection]
  simp only [← Category.assoc, filteredMapTerm_projection, filteredDifferential_projection]
  simp only [Category.assoc]
  congr 1
  by_cases hij : i + 1 = j
  · subst j
    simp only [filteredDifferential_none_succ]
    exact coefficientKoszulDifferential_naturality f n g i
  · simp only [filteredDifferential, dite_eq_right hij, comp_zero, zero_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem filtrationInclusionTerm_comm {r : ℕ} (f : Fin r → A) (p q : Option ℤ)
    (hpq : CutoffLE p q) (n : ℕ) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i j : ℤ) :
    filtrationInclusionTerm (r := r) p q K i ≫ filteredDifferential f p n K i j =
      filteredDifferential f q n K i j ≫ filtrationInclusionTerm p q K j := by
  apply filteredTerm_hom_ext p K j
  simp only [Category.assoc, filteredDifferential_projection,
    filtrationInclusionTerm_projection p q hpq]
  simp only [← Category.assoc, filtrationInclusionTerm_projection p q hpq]

set_option backward.isDefEq.respectTransparency false in
private theorem filteredUnitTerm_projection {r : ℕ} (p : Option ℤ)
    (hp : CutoffLE p (some 0)) (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    filteredUnitTerm (r := r) p K t ≫ termProjection p K t = coefficientKoszulUnitTerm K t := by
  classical
  refine hom_ext_pi fun x S ↦ ?_
  show ((termSection p K t ≫ termProjection p K t).hom
    ((coefficientKoszulUnitTerm (r := r) K t).hom x)) S = _
  rw [termSection_projection_apply]
  split_ifs with hS
  · rfl
  · by_cases h : S = ∅
    · subst S
      exact (hS (by simpa using hp)).elim
    · simp [coefficientKoszulUnitTerm, h]

set_option backward.isDefEq.respectTransparency false in
private theorem filteredUnitTerm_comm {r : ℕ} (f : Fin r → A) (p : Option ℤ)
    (n : ℕ) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i j : ℤ) :
    filteredUnitTerm (r := r) p K i ≫ filteredDifferential f p n K i j =
      K.d i j ≫ filteredUnitTerm p K j := by
  by_cases hp : CutoffLE p (some 0)
  · apply filteredTerm_hom_ext p K j
    simp only [Category.assoc, filteredDifferential_projection,
      filteredUnitTerm_projection p hp]
    simp only [← Category.assoc, filteredUnitTerm_projection p hp]
    by_cases hij : i + 1 = j
    · subst j
      simp only [filteredDifferential_none_succ]
      exact coefficientKoszulUnitTerm_differential f n K i
    · rw [K.shape i j hij]
      simp only [filteredDifferential, dite_eq_right hij, comp_zero, zero_comp]
  · cases p with
    | none => exact (hp trivial).elim
    | some p => exact (filteredTerm_isZero p (lt_of_not_ge hp) K j).eq_of_tgt _ _

private theorem augmentation_factor {r : ℕ} {f : Fin r → A} (h : FormulaLaws.{u, v} f)
    (n : ℕ) (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    (((h.augmentation (some 0)).app ⟨n⟩).app K) ≫
        (((h.inclusion none (some 0) trivial).app K).app ⟨n⟩) =
      (((h.augmentation none).app ⟨n⟩).app K) := by
  apply HomologicalComplex.hom_ext
  intro t
  show filteredUnitTerm (r := r) (some 0) K t ≫
      (termProjection (some 0) K t ≫ termSection none K t) =
    coefficientKoszulUnitTerm K t ≫ termSection none K t
  rw [← Category.assoc, filteredUnitTerm_projection (some 0) (le_refl 0)]

private theorem koszulTransition_coefficient {r : ℕ} (f : Fin r → A)
    (m n : ℕ) (hmn : n ≤ m) (S : Finset (Fin r)) (i : Fin r) (hi : i ∉ S) (c : A) :
    (c * f i ^ (n + 1)) * (∏ j ∈ insert i S, f j ^ (m - n)) =
      (∏ j ∈ S, f j ^ (m - n)) * (c * f i ^ (m + 1)) := by
  have he : f i ^ (n + 1) * f i ^ (m - n) = f i ^ (m + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [Finset.prod_insert hi, ← he]
  ring

set_option backward.isDefEq.respectTransparency false in
private theorem coefficientKoszulTransitionTerm_comm {r : ℕ} (f : Fin r → A)
    (m n : ℕ) (hmn : n ≤ m) (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    coefficientKoszulTransitionTerm f m n K t ≫ coefficientKoszulDifferential f n K t =
      coefficientKoszulDifferential f m K t ≫ coefficientKoszulTransitionTerm f m n K (t + 1) := by
  classical
  refine hom_ext_pi fun x S ↦ ?_
  dsimp [coefficientKoszulTransitionTerm, coefficientKoszulDifferential]
  simp only [map_smul, smul_add, Finset.smul_sum, smul_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [koszulTransition_coefficient f m n hmn S i.1 i.2]

set_option backward.isDefEq.respectTransparency false in
private theorem filteredTransitionTerm_comm {r : ℕ} (f : Fin r → A) (p : Option ℤ)
    (m n : ℕ) (hmn : n ≤ m) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i j : ℤ) :
    filteredTransitionTerm f p m n K i ≫ filteredDifferential f p n K i j =
      filteredDifferential f p m K i j ≫ filteredTransitionTerm f p m n K j := by
  apply filteredTerm_hom_ext p K j
  simp only [Category.assoc, filteredDifferential_projection, filteredTransitionTerm_projection]
  simp only [← Category.assoc, filteredTransitionTerm_projection, filteredDifferential_projection]
  simp only [Category.assoc]
  congr 1
  by_cases hij : i + 1 = j
  · subst j
    simp only [filteredDifferential_none_succ]
    exact coefficientKoszulTransitionTerm_comm f m n hmn K i
  · simp only [filteredDifferential, dite_eq_right hij, comp_zero, zero_comp]

private theorem termProjection_proj_eq_zero {r : ℕ} (p : Option ℤ)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) (S : Finset (Fin r))
    (hS : ¬ CutoffLE p (some (-(S.card : ℤ)))) :
    termProjection (r := r) p K t ≫ ModuleCat.ofHom (LinearMap.proj S) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact termProjection_apply_eq_zero p K t S hS x

set_option backward.isDefEq.respectTransparency false in
private theorem gradedComponentTerm_vanish {r : ℕ} (p : ℤ) (hp : p ≤ 0)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (S : KoszulBasis r p.natAbs) (t : ℤ) :
    filtrationInclusionTerm (r := r) (some p) (some (p + 1)) K t ≫
      gradedComponentTerm p hp K S t = 0 := by
  have hcut : CutoffLE (some p) (some (p + 1)) := by dsimp [CutoffLE]; omega
  have hS : ¬ CutoffLE (some (p + 1)) (some (-(S.val.card : ℤ))) := by
    simp only [CutoffLE, S.property, Int.natCast_natAbs, abs_of_nonpos hp]
    omega
  simp only [gradedComponentTerm, Linear.comp_smul, ← Category.assoc,
    filtrationInclusionTerm_projection (some p) (some (p + 1)) hcut,
    termProjection_proj_eq_zero (some (p + 1)) K t S.val hS, zero_comp, smul_zero]

private theorem stupidTrunc_d_eq {ι κ : Type*} {c : ComplexShape ι} {c' : ComplexShape κ}
    {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
    (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsRelIff]
    {i j : ι} {i' j' : κ} (hi : e.f i = i') (hj : e.f j = j') :
    (K.stupidTrunc e).d i' j' = (K.stupidTruncXIso e hi).hom ≫ K.d i' j' ≫
      (K.stupidTruncXIso e hj).inv := by
  subst i'
  subst j'
  show ((K.restriction e).extend e).d (e.f i) (e.f j) =
    (((K.restriction e).extendXIso e rfl).hom ≫ 𝟙 ((K.restriction e).X i)) ≫
      (K.restriction e).d i j ≫
        (𝟙 ((K.restriction e).X j) ≫ ((K.restriction e).extendXIso e rfl).inv)
  rw [Category.comp_id, Category.id_comp]
  exact HomologicalComplex.extend_d_eq (K.restriction e) e rfl rfl


private theorem stupidTrunc_isZero_X (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (p j : ℤ) (h : j < p) : IsZero ((K.stupidTrunc (ComplexShape.embeddingUpIntGE p)).X j) := by
  apply HomologicalComplex.isZero_stupidTrunc_X
  intro i
  show p + (i : ℤ) ≠ j
  omega

set_option backward.isDefEq.respectTransparency false in
private theorem stupidTruncProjection_comm (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (p i j : ℤ) :
    stupidTruncProjection K p i ≫ K.d i j =
      (K.stupidTrunc (ComplexShape.embeddingUpIntGE p)).d i j ≫ stupidTruncProjection K p j := by
  by_cases hij : i + 1 = j
  · by_cases hpi : p ≤ i
    · have hpj : p ≤ j := by omega
      have hi : (ComplexShape.embeddingUpIntGE p).f (i - p).toNat = i := by
        show p + ((i - p).toNat : ℤ) = i
        rw [Int.toNat_of_nonneg (by omega)]
        omega
      have hj : (ComplexShape.embeddingUpIntGE p).f (j - p).toNat = j := by
        show p + ((j - p).toNat : ℤ) = j
        rw [Int.toNat_of_nonneg (by omega)]
        omega
      rw [stupidTrunc_d_eq K _ hi hj]
      simp [stupidTruncProjection, hpi, hpj, Category.assoc]
    · exact (stupidTrunc_isZero_X K p i (lt_of_not_ge hpi)).eq_of_src _ _
  · rw [K.shape i j hij, (K.stupidTrunc _).shape i j hij, comp_zero, zero_comp]

private theorem stupidTruncProjection_section (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (p j : ℤ) : stupidTruncProjection K p j ≫ stupidTruncSection K p j = 𝟙 _ := by
  by_cases hpj : p ≤ j
  · simp [stupidTruncProjection, stupidTruncSection, hpj]
  · exact (stupidTrunc_isZero_X K p j (lt_of_not_ge hpj)).eq_of_src _ _

private theorem stupidTruncSection_projection_of_le (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (p j : ℤ) (hpj : p ≤ j) :
    stupidTruncSection K p j ≫ stupidTruncProjection K p j = 𝟙 _ := by
  simp [stupidTruncProjection, stupidTruncSection, hpj]

private theorem stupidTruncProjection_mono (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (p j : ℤ) : Mono (stupidTruncProjection K p j) where
  right_cancellation g h heq := by
    have := congrArg (fun a ↦ a ≫ stupidTruncSection K p j) heq
    simpa only [Category.assoc, stupidTruncProjection_section, Category.comp_id] using this

private theorem stupidTruncInclusion_projection (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (p q j : ℤ) (hpq : p ≤ q) :
    stupidTruncProjection K q j ≫ stupidTruncSection K p j ≫ stupidTruncProjection K p j =
      stupidTruncProjection K q j := by
  by_cases hpj : p ≤ j
  · rw [stupidTruncSection_projection_of_le K p j hpj, Category.comp_id]
  · exact (stupidTrunc_isZero_X K q j (by omega)).eq_of_src _ _

private theorem stupidTruncInclusion_comm (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (p q i j : ℤ) (hpq : p ≤ q) :
    (stupidTruncProjection K q i ≫ stupidTruncSection K p i) ≫
        (K.stupidTrunc (ComplexShape.embeddingUpIntGE p)).d i j =
      (K.stupidTrunc (ComplexShape.embeddingUpIntGE q)).d i j ≫
        (stupidTruncProjection K q j ≫ stupidTruncSection K p j) := by
  have := stupidTruncProjection_mono K p j
  apply (cancel_mono (stupidTruncProjection K p j)).mp
  simp only [Category.assoc, stupidTruncInclusion_projection K p q j hpq]
  rw [← stupidTruncProjection_comm K p i j]
  simp only [← Category.assoc]
  rw [Category.assoc (stupidTruncProjection K q i), stupidTruncInclusion_projection K p q i hpq]
  exact stupidTruncProjection_comm K q i j

private theorem standardKoszulInclusionTerm_comm {r : ℕ} (f : Fin r → A)
    (p q : Option ℤ) (hpq : CutoffLE p q) (n : ℕ) (i j : ℤ) :
    standardKoszulInclusionTerm f p q n i ≫ (standardKoszulStage f p n).d i j =
      (standardKoszulStage f q n).d i j ≫ standardKoszulInclusionTerm f p q n j := by
  cases p with
  | none =>
    cases q with
    | none => simp [standardKoszulInclusionTerm, standardKoszulProjectionTerm,
        standardKoszulSectionTerm]
    | some q =>
      show (stupidTruncProjection (standardKoszulStage f none n) q i ≫ 𝟙 _) ≫ _ =
        _ ≫ (stupidTruncProjection (standardKoszulStage f none n) q j ≫ 𝟙 _)
      rw [Category.comp_id, Category.comp_id]
      exact stupidTruncProjection_comm (standardKoszulStage f none n) q i j
  | some p =>
    cases q with
    | none => exact hpq.elim
    | some q => exact stupidTruncInclusion_comm (standardKoszulStage f none n) p q i j hpq

private def coefficientKoszulUnitRetractionTerm {r : ℕ}
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    coefficientKoszulTerm (r := r) K t ⟶ K.X t :=
  ModuleCat.ofHom (LinearMap.proj ∅) ≫ eqToHom (by
    change K.X (t + 0) = K.X t
    rw [add_zero])

private theorem coefficientKoszulUnitTerm_retraction {r : ℕ}
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    coefficientKoszulUnitTerm (r := r) K t ≫ coefficientKoszulUnitRetractionTerm K t = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have h := congrArg ModuleCat.Hom.hom (eqToHom_trans
    (show K.X t = K.X (t + 0) by rw [add_zero])
    (show K.X (t + 0) = K.X t by rw [add_zero]))
  exact LinearMap.congr_fun h x

set_option backward.isDefEq.respectTransparency false in
private theorem termProjection_unitRetraction_unit {r : ℕ}
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    termProjection (r := r) (some 0) K t ≫ coefficientKoszulUnitRetractionTerm K t ≫
      coefficientKoszulUnitTerm K t = termProjection (some 0) K t := by
  classical
  refine hom_ext_pi fun x S ↦ ?_
  by_cases hS : S = ∅
  · subst S
    have h := congrArg ModuleCat.Hom.hom (eqToHom_trans
      (show K.X (t + 0) = K.X t by rw [add_zero])
      (show K.X t = K.X (t + 0) by rw [add_zero]))
    exact LinearMap.congr_fun h ((termProjection (some 0) K t).hom x ∅)
  · show (coefficientKoszulUnitTerm K t).hom _ S = _
    rw [coefficientKoszulUnitTerm_apply_of_ne K t S hS]
    symm
    apply termProjection_apply_eq_zero
    dsimp [CutoffLE]
    have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
    omega

private theorem filteredUnitTerm_zero_isIso {r : ℕ}
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    IsIso (filteredUnitTerm (r := r) (some 0) K t) := by
  let e : K.X t ≅ filteredTerm (r := r) (some 0) K t :=
    { hom := filteredUnitTerm (some 0) K t
      inv := termProjection (some 0) K t ≫ coefficientKoszulUnitRetractionTerm K t
      hom_inv_id := by
        rw [← Category.assoc, filteredUnitTerm_projection (some 0) (le_refl 0),
          coefficientKoszulUnitTerm_retraction]
      inv_hom_id := by
        apply filteredTerm_hom_ext (some 0) K t
        simp only [Category.assoc, filteredUnitTerm_projection (some 0) (le_refl 0),
          Category.id_comp, termProjection_unitRetraction_unit] }
  exact e.isIso_hom

public theorem augmentation_zero_isIso {r : ℕ} {f : Fin r → A}
    (h : FormulaLaws.{u, v} f) (n : ℕ) (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    IsIso (((h.augmentation (some 0)).app ⟨n⟩).app K) := by
  have ht (t : ℤ) : IsIso ((((h.augmentation (some 0)).app ⟨n⟩).app K).f t) :=
    filteredUnitTerm_zero_isIso K t
  exact HomologicalComplex.Hom.isIso_of_components _

private theorem coefficientMapTerm_proj {r : ℕ}
    {K L : CochainComplex (ModuleCat.{v} A) ℤ} (g : K ⟶ L) (t : ℤ) (S : Finset (Fin r)) :
    coefficientMapTerm g t ≫ ModuleCat.ofHom (LinearMap.proj S) =
      ModuleCat.ofHom (LinearMap.proj S) ≫ g.f (t + S.card) := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem gradedComponentTerm_naturality {r : ℕ} (p : ℤ) (hp : p ≤ 0)
    {K L : CochainComplex (ModuleCat.{v} A) ℤ} (g : K ⟶ L)
    (S : KoszulBasis r p.natAbs) (t : ℤ) :
    filteredMapTerm (r := r) (some p) g t ≫ gradedComponentTerm p hp L S t =
      gradedComponentTerm p hp K S t ≫
        ((shiftFunctor (CochainComplex (ModuleCat.{v} A) ℤ) (-p)).map g).f t := by
  simp only [gradedComponentTerm, Linear.comp_smul, Linear.smul_comp]
  congr 1
  simp only [← Category.assoc, filteredMapTerm_projection]
  rw [Category.assoc (termProjection (some p) K t), coefficientMapTerm_proj]
  simp only [Category.assoc]
  congr 2
  exact hom_f_eqToHom g (t + S.val.card) (t + -p) (by
    simp only [S.property, Int.natCast_natAbs, abs_of_nonpos hp])

set_option backward.isDefEq.respectTransparency false in
private theorem graded_naturality {r : ℕ} {f : Fin r → A} (h : FormulaLaws.{u, v} f)
    (p : ℤ) (hp : p ≤ 0) (n : ℕ)
    {K L : CochainComplex (ModuleCat.{v} A) ℤ} (g : K ⟶ L) :
    h.stageMap (some p) n g ≫ h.gradedProjection p hp n L =
      h.gradedProjection p hp n K ≫ (coefficientKoszulGradedPiece (A := A) r p).map g := by
  apply Limits.Pi.hom_ext
  intro S
  simp only [Category.assoc, FormulaLaws.gradedProjection, Limits.Pi.lift_comp_π]
  show _ = h.gradedProjection p hp n K ≫
    (Limits.Pi.map (fun _ : KoszulBasis r p.natAbs ↦
      (shiftFunctor (CochainComplex (ModuleCat.{v} A) ℤ) (-p)).map g)) ≫
        Limits.Pi.π (fun _ : KoszulBasis r p.natAbs ↦ L⟦-p⟧) S
  rw [Limits.Pi.map_π, ← Category.assoc, FormulaLaws.gradedProjection, Limits.Pi.lift_comp_π]
  exact HomologicalComplex.hom_ext _ _ (gradedComponentTerm_naturality p hp g S)

private theorem coefficientKoszulTransitionTerm_proj {r : ℕ} (f : Fin r → A)
    (m n : ℕ) (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) (S : Finset (Fin r)) :
    coefficientKoszulTransitionTerm f m n K t ≫ ModuleCat.ofHom (LinearMap.proj S) =
      ModuleCat.ofHom (LinearMap.proj S) ≫ ((∏ i ∈ S, f i ^ (m - n)) • 𝟙 (K.X (t + S.card))) := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem gradedComponentTerm_transition {r : ℕ} (f : Fin r → A)
    (p : ℤ) (hp : p ≤ 0) (n : ℕ) (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (S : KoszulBasis r p.natAbs) (t : ℤ) :
    filteredTransitionTerm f (some p) (n + 1) n K t ≫ gradedComponentTerm p hp K S t =
      gradedComponentTerm p hp K S t ≫
        ((shiftFunctor (CochainComplex (ModuleCat.{v} A) ℤ) (-p)).map
          ((∏ i ∈ S.val, f i) • 𝟙 K)).f t := by
  simp only [gradedComponentTerm, Linear.comp_smul, Linear.smul_comp]
  congr 1
  simp only [← Category.assoc, filteredTransitionTerm_projection]
  rw [Category.assoc (termProjection (some p) K t), coefficientKoszulTransitionTerm_proj]
  simp [Functor.map_smul, Linear.comp_smul, Linear.smul_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem graded_transition {r : ℕ} {f : Fin r → A} (h : FormulaLaws.{u, v} f)
    (p : ℤ) (hp : p ≤ 0) (n : ℕ) (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    h.transition (some p) (n + 1) n (Nat.le_succ n) K ≫ h.gradedProjection p hp n K =
      h.gradedProjection p hp (n + 1) K ≫ coefficientKoszulGradedTransition f p K := by
  apply Limits.Pi.hom_ext
  intro S
  simp only [Category.assoc, coefficientKoszulGradedTransition, Limits.Pi.map_π,
    FormulaLaws.gradedProjection, Limits.Pi.lift_comp_π]
  rw [← Category.assoc, Limits.Pi.lift_comp_π]
  exact HomologicalComplex.hom_ext _ _ (gradedComponentTerm_transition f p hp n K S)


private theorem neg_one_pow_natAbs_add (i j : ℤ) :
    (-1 : A) ^ (i + j).natAbs = (-1 : A) ^ i.natAbs * (-1 : A) ^ j.natAbs := by
  simp only [← Int.coe_negOnePow, Int.negOnePow_add, Units.val_mul, Int.cast_mul]

set_option backward.isDefEq.respectTransparency false in
private theorem filteredDifferential_proj {r : ℕ} (f : Fin r → A) (p : ℤ) (hp : p ≤ 0)
    (n : ℕ) (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (S : KoszulBasis r p.natAbs) (i j : ℤ) :
    filteredDifferential f (some p) n K i j ≫ termProjection (some p) K j ≫
        ModuleCat.ofHom (LinearMap.proj S.val) =
      termProjection (some p) K i ≫ ModuleCat.ofHom (LinearMap.proj S.val) ≫
        K.d (i + S.val.card) (j + S.val.card) := by
  rw [← Category.assoc, filteredDifferential_projection]
  by_cases hij : i + 1 = j
  · subst j
    simp only [filteredDifferential_none_succ]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    show (coefficientKoszulDifferential f n K i).hom
      ((termProjection (some p) K i).hom x) S.val = _
    dsimp only [coefficientKoszulDifferential, ModuleCat.hom_ofHom, LinearMap.coe_mk, AddHom.coe_mk]
    apply add_eq_left.mpr
    apply Finset.sum_eq_zero
    intro a _
    have hcut : ¬ CutoffLE (some p) (some (-((insert a.val S.val).card : ℤ))) := by
      simp only [CutoffLE, Finset.card_insert_of_notMem a.property, Nat.cast_add, Nat.cast_one,
        S.property, Int.natCast_natAbs, abs_of_nonpos hp]
      omega
    rw [termProjection_apply_eq_zero (some p) K i (insert a.val S.val) hcut x,
      map_zero, smul_zero]
  · rw [K.shape (i + S.val.card) (j + S.val.card) (by
      show ¬ (i + S.val.card) + 1 = j + S.val.card
      omega)]
    simp only [filteredDifferential, dite_eq_right hij, comp_zero, zero_comp]

private theorem shiftFunctorObjXIso_inv_d (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (s i j a b : ℤ) (ha : a = i + s) (hb : b = j + s) :
    (CochainComplex.shiftFunctorObjXIso K s i a ha).inv ≫ (K⟦s⟧).d i j =
      s.negOnePow • (K.d a b ≫ (CochainComplex.shiftFunctorObjXIso K s j b hb).inv) := by
  show eqToHom (congrArg K.X ha) ≫ (s.negOnePow • K.d (i + s) (j + s)) =
    s.negOnePow • (K.d a b ≫ eqToHom (congrArg K.X hb))
  rw [Linear.comp_units_smul, eqToHom_d K a (i + s) b (j + s) ha hb]

set_option backward.isDefEq.respectTransparency false in
private theorem gradedComponentTerm_comm {r : ℕ} (f : Fin r → A) (p : ℤ) (hp : p ≤ 0)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (S : KoszulBasis r p.natAbs)
    (n : ℕ) (i j : ℤ) :
    gradedComponentTerm p hp K S i ≫ (K⟦-p⟧).d i j =
      filteredDifferential f (some p) n K i j ≫ gradedComponentTerm p hp K S j := by
  by_cases hij : i + 1 = j
  · subst j
    have ha : i + S.val.card = i + -p := by
      simp only [S.property, Int.natCast_natAbs, abs_of_nonpos hp]
    have hb : i + 1 + S.val.card = i + 1 + -p := by
      simp only [S.property, Int.natCast_natAbs, abs_of_nonpos hp]
    simp only [gradedComponentTerm, Linear.smul_comp, Linear.comp_smul, Category.assoc]
    rw [shiftFunctorObjXIso_inv_d K (-p) i (i + 1) _ _ ha hb, units_negOnePow_smul_eq (R := A),
      reassoc_of% (filteredDifferential_proj f p hp n K S i (i + 1))]
    simp only [Linear.comp_smul, smul_smul, ← neg_one_pow_natAbs_add, add_mul, one_mul]
  · rw [(K⟦-p⟧).shape i j hij]
    simp only [filteredDifferential, dite_eq_right hij, comp_zero, zero_comp]

end KoszulCoefficientTower

end

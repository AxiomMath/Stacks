module

public import StacksFrontier.Homology.DerivedComplete.AdicKoszulCoefficientTower.GradedQuasiIso
import all StacksFrontier.Homology.DerivedComplete.AdicKoszulCoefficientTower.Formulas
import all StacksFrontier.Homology.DerivedComplete.AdicKoszulCoefficientTower.FiltrationLaws
import all StacksFrontier.Homology.DerivedComplete.AdicKoszulCoefficientTower.GradedQuasiIso
import Mathlib
import all Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Koszul towers with coefficients: compatibility of the wedge comparison

The wedge comparison with the ordinary tensor product commutes with the power transitions, with
the augmentation, and with the differentials.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u v

namespace KoszulCoefficientTower

variable {A : Type u} [CommRing A]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem comparison_transition {r : ℕ} {f : Fin r → A}
    (h : FormulaLaws.{u, v} f) (p : Option ℤ) (m n : ℕ) (hmn : n ≤ m)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    (complexUniverseLift (A := A)).map (h.transition p m n hmn K) ≫ h.comparisonMap p n K =
      h.comparisonMap p m K ≫
        (𝟙 ((complexUniverseLift (A := A)).obj K) ⊗ₘ
          standardKoszulTransition (fun a ↦ (ULift.up (f a) : ULift.{v} A)) p m n hmn) := by
  classical
  apply HomologicalComplex.hom_ext
  intro t
  show (AdicKoszul.moduleUniverseLift A).map (filteredTransitionTerm f p m n K t) ≫
    comparisonTerm f p n K t = comparisonTerm f p m K t ≫ _
  simp only [comparisonTerm, Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
  apply Finset.sum_congr rfl
  intro S _
  show _ = _ ≫ _ ≫ (HomologicalComplex.ιMapBifunctor _ _ _ _ _ _ _ _) ≫
    (HomologicalComplex.mapBifunctorMap (𝟙 _) (standardKoszulTransition _ p m n hmn) _ _).f t
  rw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f]
  rw [CategoryTheory.Functor.map_id]
  simp only [NatTrans.id_app, Category.id_comp]
  show _ = _ ≫ _ ≫
    (((complexUniverseLift (A := A)).obj K).X (t + S.card) ◁
      (standardKoszulTransition (fun a ↦ (ULift.up (f a) : ULift.{v} A)) p m n hmn).f
        (-(S.card : ℤ))) ≫ _
  rw [← Category.assoc, ← Functor.map_comp]
  have hpr : filteredTransitionTerm f p m n K t ≫
      (termProjection p K t ≫ ModuleCat.ofHom (LinearMap.proj S)) =
      (termProjection p K t ≫ ModuleCat.ofHom (LinearMap.proj S)) ≫
        ((∏ i ∈ S, f i ^ (m - n)) • 𝟙 (K.X (t + S.card))) := by
    rw [← Category.assoc, filteredTransitionTerm_projection, Category.assoc,
      coefficientKoszulTransitionTerm_proj, ← Category.assoc]
  rw [hpr, Functor.map_comp]
  try simp only [Category.assoc]
  erw [← Category.assoc (ModuleCat.ofHom
      ((TensorProduct.mk (ULift.{v} A)
        (((complexUniverseLift (A := A)).obj K).X (t + S.card)) _).flip
        (koszulBasisVector (fun a ↦ (ULift.up (f a) : ULift.{v} A)) p m S))),
    tensor_mk_map, koszulBasisVector_transition]
  have hc : (AdicKoszul.moduleUniverseLift A).map
      ((∏ i ∈ S, f i ^ (m - n)) • 𝟙 (K.X (t + S.card))) =
      (∏ i ∈ S, (ULift.up (f i) : ULift.{v} A) ^ (m - n)) •
        𝟙 ((AdicKoszul.moduleUniverseLift A).obj (K.X (t + S.card))) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply ULift.ext
    show (∏ i ∈ S, f i ^ (m - n)) • x.down =
      (∏ i ∈ S, (ULift.up (f i) : ULift.{v} A) ^ (m - n)).down • x.down
    congr 1
    show (∏ i ∈ S, f i ^ (m - n)) =
      (ULift.ringEquiv : ULift.{v} A ≃+* A)
        (∏ i ∈ S, (ULift.up (f i) : ULift.{v} A) ^ (m - n))
    simp only [map_prod, map_pow]
    rfl
  erw [hc, ← Category.assoc
    ((∏ i ∈ S, (ULift.up (f i) : ULift.{v} A) ^ (m - n)) •
      𝟙 (((complexUniverseLift (A := A)).obj K).X (t + S.card))), tensor_mk_smul]

private theorem koszulPowerUnitChain_apply {r : ℕ} (f : Fin r → A) (n : ℕ) (a : A) :
    (AdicKoszul.koszulPowerUnitChain f n).f 0 a =
      a • (Pi.basisFun A (Fin r)).exteriorPower 0 ⟨∅, rfl⟩ := by
  have h := (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (_root_.koszulPowerComplexes_form_inverseSystem f))))).2.2.2.2.2.1 n a
  refine h.trans ?_
  congr 1
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family]
  apply Subtype.ext
  congr 1

private theorem tensor_mk_unit {R : Type u} [CommRing R]
    (M N : ModuleCat.{u} R) (g : ModuleCat.of R R ⟶ N) (e : N)
    (hg : ∀ a, g a = a • e) :
    (ρ_ M).inv ≫ (M ◁ g) = ModuleCat.ofHom ((TensorProduct.mk R M N).flip e) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  show TensorProduct.map LinearMap.id g.hom (TensorProduct.rid R M |>.symm x) = _
  simp [hg]

set_option backward.isDefEq.respectTransparency false in
public theorem comparison_augmentation {r : ℕ} {f : Fin r → A}
    (h : FormulaLaws.{u, v} f) (n : ℕ) (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    (complexUniverseLift (A := A)).map (((h.augmentation none).app ⟨n⟩).app K) ≫
        h.comparisonMap none n K =
      (MonoidalCategory.rightUnitor ((complexUniverseLift (A := A)).obj K)).inv ≫
        (((complexUniverseLift (A := A)).obj K) ◁
          AdicKoszul.koszulPowerUnit (fun a ↦ (ULift.up (f a) : ULift.{v} A)) n) := by
  classical
  apply HomologicalComplex.hom_ext
  intro t
  show (AdicKoszul.moduleUniverseLift A).map (filteredUnitTerm (r := r) none K t) ≫
      comparisonTerm f none n K t = _
  rw [comparisonTerm, Preadditive.comp_sum]
  rw [Finset.sum_eq_single ∅]
  · show _ = (HomologicalComplex.rightUnitor' ((complexUniverseLift (A := A)).obj K)).inv t ≫ _
    rw [HomologicalComplex.rightUnitor'_inv]
    simp only [Category.assoc]
    erw [HomologicalComplex.ι_mapBifunctorMap]
    show _ = (ρ_ (((complexUniverseLift (A := A)).obj K).X t)).inv ≫
      (((complexUniverseLift (A := A)).obj K).X t ◁ _) ≫
      (((complexUniverseLift (A := A)).obj K).X t ◁
        (AdicKoszul.koszulPowerUnit (fun a ↦ (ULift.up (f a) : ULift.{v} A)) n).f 0) ≫ _
    have he : (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (ModuleCat.of (ULift.{v} A) (ULift.{v} A))).inv ≫
          (AdicKoszul.koszulPowerUnit (fun a ↦ (ULift.up (f a) : ULift.{v} A)) n).f 0 =
        (AdicKoszul.koszulPowerUnitChain (fun a ↦ (ULift.up (f a) : ULift.{v} A)) n).f 0 ≫
          (HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat (i := 0) rfl).inv := by
      rw [AdicKoszul.koszulPowerUnit, HomologicalComplex.mkHomFromSingle_f,
        Iso.inv_hom_id_assoc]
    rw [← whiskerLeft_comp_assoc]
    erw [he]
    rw [← Category.assoc (ρ_ _).inv, tensor_mk_unit _ _ _
      (koszulBasisVector (fun a ↦ (ULift.up (f a) : ULift.{v} A)) none n ∅)]
    · simp only [Finset.card_empty,
        filteredUnitTerm, termSection_none, termProjection_none,
        Category.comp_id, Category.id_comp]
      rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp]
      have hu : coefficientKoszulUnitTerm (r := r) K t ≫
          ModuleCat.ofHom (LinearMap.proj ∅) =
            eqToHom (by simp) := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        simp [coefficientKoszulUnitTerm]
      rw [hu]
      cases t <;> rfl
    · intro a
      show ((AdicKoszul.koszulPowerUnitChain
        (fun a ↦ (ULift.up (f a) : ULift.{v} A)) n).f 0 ≫
        (HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat (i := 0) rfl).inv) a = _
      simp only [ModuleCat.comp_apply, koszulPowerUnitChain_apply, map_smul]
      rfl
  · intro S _ hS
    simp only [← Category.assoc]
    have hu : filteredUnitTerm (r := r) none K t ≫
        (termProjection none K t ≫ ModuleCat.ofHom (LinearMap.proj S)) = 0 := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp [filteredUnitTerm, termSection_none, termProjection_none,
        coefficientKoszulUnitTerm, hS]
    rw [← Functor.map_comp, hu, Functor.map_zero, zero_comp, zero_comp]
  · simp

private theorem standardKoszul_d_exteriorBasis
    {rank : ℕ} (family : Fin rank → A) (power degree : ℕ)
    (subset : KoszulBasis rank (degree + 1)) :
    let complex := Koszul.seqComplex (fun index => family index ^ (power + 1))
    let sourceIso := HomologicalComplex.extendXIso complex ComplexShape.embeddingDownNat
      (i := degree + 1) rfl
    let targetIso := HomologicalComplex.extendXIso complex ComplexShape.embeddingDownNat
      (i := degree) rfl
    (standardKoszulStage family none power).d (-((degree + 1 : ℕ) : ℤ)) (-(degree : ℤ))
        (sourceIso.inv ((Pi.basisFun A (Fin rank)).exteriorPower (degree + 1) subset)) =
      ∑ index : subset.1,
        ((-1 : A) ^ (subset.1.filter (· < index.1)).card * family index.1 ^ (power + 1)) •
          targetIso.inv ((Pi.basisFun A (Fin rank)).exteriorPower degree
            ⟨subset.1.erase index.1, by
              change (subset.1.erase index.1).card = degree
              rw [Finset.card_erase_of_mem index.2, subset.2]; omega⟩) := by
  dsimp only
  let complex := Koszul.seqComplex (fun index => family index ^ (power + 1))
  let sourceIso := HomologicalComplex.extendXIso complex ComplexShape.embeddingDownNat
    (i := degree + 1) rfl
  let targetIso := HomologicalComplex.extendXIso complex ComplexShape.embeddingDownNat
    (i := degree) rfl
  have differential := HomologicalComplex.extend_d_eq complex ComplexShape.embeddingDownNat
    (i := degree + 1) (j := degree) rfl rfl
  show (complex.extend ComplexShape.embeddingDownNat).d _ _
    (sourceIso.inv ((Pi.basisFun A (Fin rank)).exteriorPower (degree + 1) subset)) = _
  erw [differential]
  show targetIso.inv (complex.d (degree + 1) degree
    (sourceIso.hom (sourceIso.inv ((Pi.basisFun A (Fin rank)).exteriorPower (degree + 1) subset))))
      = _
  have cancel := ConcreteCategory.congr_hom sourceIso.inv_hom_id
    ((Pi.basisFun A (Fin rank)).exteriorPower (degree + 1) subset)
  change sourceIso.hom (sourceIso.inv _) = _ at cancel
  rw [cancel]
  rw [Koszul.seqComplex_d]
  show targetIso.inv (Koszul.d (Koszul.seqDual (fun index => family index ^ (power + 1))) degree
    ((Pi.basisFun A (Fin rank)).exteriorPower (degree + 1) subset)) = _
  rw [koszul_d_basis]
  show targetIso.inv.hom _ = _
  erw [map_sum]
  apply Finset.sum_congr rfl
  intro index _
  exact map_smul targetIso.inv.hom _ _

private theorem stupidTruncSection_comm_of_le
    (complex : CochainComplex (ModuleCat.{v} A) ℤ) (cutoff source target : ℤ)
    (sourceSurvives : cutoff ≤ source) (targetSurvives : cutoff ≤ target) :
    stupidTruncSection complex cutoff source ≫
        (complex.stupidTrunc (ComplexShape.embeddingUpIntGE cutoff)).d source target =
      complex.d source target ≫ stupidTruncSection complex cutoff target := by
  have index (i : ℤ) (hi : cutoff ≤ i) :
      (ComplexShape.embeddingUpIntGE cutoff).f (i - cutoff).toNat = i := by
    show cutoff + ((i - cutoff).toNat : ℤ) = i
    omega
  rw [stupidTrunc_d_eq complex _ (index source sourceSurvives) (index target targetSurvives)]
  simp only [stupidTruncSection, dite_eq_left sourceSurvives, dite_eq_left targetSurvives,
    Iso.inv_hom_id_assoc]

private theorem standardKoszulSectionTerm_comm_of_survives
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power : ℕ)
    (source target : ℤ) (sourceSurvives : CutoffLE cutoff (some source))
    (targetSurvives : CutoffLE cutoff (some target)) :
    standardKoszulSectionTerm family cutoff power source ≫
        (standardKoszulStage family cutoff power).d source target =
      (standardKoszulStage family none power).d source target ≫
        standardKoszulSectionTerm family cutoff power target := by
  cases cutoff with
  | none => simp [standardKoszulSectionTerm]
  | some cutoff =>
    exact stupidTruncSection_comm_of_le (standardKoszulStage family none power)
      cutoff source target sourceSurvives targetSurvives

private theorem standardKoszul_d_exteriorBasis_cutoff
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power degree : ℕ)
    (subset : KoszulBasis rank (degree + 1))
    (sourceSurvives : CutoffLE cutoff (some (-((degree + 1 : ℕ) : ℤ)))) :
    let complex := Koszul.seqComplex (fun index => family index ^ (power + 1))
    let sourceIso := HomologicalComplex.extendXIso complex ComplexShape.embeddingDownNat
      (i := degree + 1) rfl
    let targetIso := HomologicalComplex.extendXIso complex ComplexShape.embeddingDownNat
      (i := degree) rfl
    (standardKoszulStage family cutoff power).d (-((degree + 1 : ℕ) : ℤ)) (-(degree : ℤ))
        (standardKoszulSectionTerm family cutoff power (-((degree + 1 : ℕ) : ℤ))
          (sourceIso.inv ((Pi.basisFun A (Fin rank)).exteriorPower (degree + 1) subset))) =
      ∑ index : subset.1,
        ((-1 : A) ^ (subset.1.filter (· < index.1)).card * family index.1 ^ (power + 1)) •
          standardKoszulSectionTerm family cutoff power (-(degree : ℤ))
            (targetIso.inv ((Pi.basisFun A (Fin rank)).exteriorPower degree
              ⟨subset.1.erase index.1, by
                change (subset.1.erase index.1).card = degree
                rw [Finset.card_erase_of_mem index.2, subset.2]; omega⟩)) := by
  have targetSurvives : CutoffLE cutoff (some (-(degree : ℤ))) := by
    cases cutoff with
    | none => trivial
    | some cutoff => dsimp only [CutoffLE] at sourceSurvives ⊢; omega
  dsimp only
  show (standardKoszulSectionTerm family cutoff power (-((degree + 1 : ℕ) : ℤ)) ≫
    (standardKoszulStage family cutoff power).d _ _) _ = _
  rw [standardKoszulSectionTerm_comm_of_survives family cutoff power _ _
    sourceSurvives targetSurvives]
  show standardKoszulSectionTerm family cutoff power (-(degree : ℤ))
    ((standardKoszulStage family none power).d _ _ _) = _
  rw [standardKoszul_d_exteriorBasis]
  show (standardKoszulSectionTerm family cutoff power (-(degree : ℤ))).hom _ = _
  erw [map_sum]
  apply Finset.sum_congr rfl
  intro index _
  exact map_smul (standardKoszulSectionTerm family cutoff power (-(degree : ℤ))).hom _ _

private theorem koszulBasisVector_cast
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power : ℕ)
    (subset : Finset (Fin rank)) (degree : ℕ) (cardinality : subset.card = degree) :
    (eqToHom (congrArg
      (fun amount : ℕ => (standardKoszulStage family cutoff power).X (-(amount : ℤ)))
      cardinality)) (koszulBasisVector family cutoff power subset) =
      standardKoszulSectionTerm family cutoff power (-(degree : ℤ))
        ((HomologicalComplex.extendXIso
            (Koszul.seqComplex (fun index => family index ^ (power + 1)))
            ComplexShape.embeddingDownNat (i := degree) rfl).inv
          ((Pi.basisFun A (Fin rank)).exteriorPower degree ⟨subset, cardinality⟩)) := by
  subst degree
  cases cutoff <;> rfl

private theorem tensor_summand_differential
    (coefficient factor : CochainComplex (ModuleCat.{u} A) ℤ)
    (coefficientDegree factorDegree totalDegree : ℤ)
    (totalIndex : coefficientDegree + factorDegree = totalDegree) :
    HomologicalComplex.ιTensorObj coefficient factor coefficientDegree factorDegree
        totalDegree totalIndex ≫
        (HomologicalComplex.tensorObj coefficient factor).d totalDegree (totalDegree + 1) =
      (coefficient.d coefficientDegree (coefficientDegree + 1) ▷ factor.X factorDegree) ≫
        HomologicalComplex.ιTensorObj coefficient factor (coefficientDegree + 1) factorDegree
          (totalDegree + 1) (by omega) +
      coefficientDegree.negOnePow •
        ((coefficient.X coefficientDegree ◁ factor.d factorDegree (factorDegree + 1)) ≫
          HomologicalComplex.ιTensorObj coefficient factor coefficientDegree (factorDegree + 1)
            (totalDegree + 1) (by omega)) := by
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (show (ComplexShape.up ℤ).Rel
      coefficientDegree (coefficientDegree + 1) from rfl) _ _ (by change _ + _ = _; omega),
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _ (show (ComplexShape.up ℤ).Rel
      factorDegree (factorDegree + 1) from rfl) _ (by change _ + _ = _; omega)]
  show (1 : ℤˣ) • _ + _ = _
  rw [one_smul]
  rfl

private theorem tensor_summand_differential_apply
    (coefficient factor : CochainComplex (ModuleCat.{u} A) ℤ)
    (coefficientDegree factorDegree totalDegree : ℤ)
    (totalIndex : coefficientDegree + factorDegree = totalDegree)
    (factorNextDegree : ℤ) (factorNext : factorDegree + 1 = factorNextDegree)
    (left : coefficient.X coefficientDegree) (right : factor.X factorDegree) :
    (HomologicalComplex.tensorObj coefficient factor).d totalDegree (totalDegree + 1)
        (HomologicalComplex.ιTensorObj coefficient factor coefficientDegree factorDegree
          totalDegree totalIndex (left ⊗ₜ[A] right)) =
      HomologicalComplex.ιTensorObj coefficient factor (coefficientDegree + 1) factorDegree
        (totalDegree + 1) (by omega)
        (coefficient.d coefficientDegree (coefficientDegree + 1) left ⊗ₜ[A] right) +
      (-1 : A) ^ coefficientDegree.natAbs •
        HomologicalComplex.ιTensorObj coefficient factor coefficientDegree factorNextDegree
          (totalDegree + 1) (by omega)
          (left ⊗ₜ[A] factor.d factorDegree factorNextDegree right) := by
  subst factorNextDegree
  have equality := congrArg (fun morphism => morphism (left ⊗ₜ[A] right))
    (tensor_summand_differential coefficient factor coefficientDegree factorDegree totalDegree
      totalIndex)
  simpa [Units.smul_def, ← Int.cast_smul_eq_zsmul A, Int.coe_negOnePow] using equality

set_option backward.isDefEq.respectTransparency false in
private theorem tensor_koszul_basis_differential
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power degree : ℕ)
    (coefficient : CochainComplex (ModuleCat.{u} A) ℤ)
    (subset : KoszulBasis rank (degree + 1))
    (sourceSurvives : CutoffLE cutoff (some (-((degree + 1 : ℕ) : ℤ))))
    (coefficientDegree totalDegree : ℤ)
    (totalIndex : coefficientDegree + -((degree + 1 : ℕ) : ℤ) = totalDegree)
    (left : coefficient.X coefficientDegree) :
    let factor := standardKoszulStage family cutoff power
    let complex := Koszul.seqComplex (fun index => family index ^ (power + 1))
    let sourceBasis := standardKoszulSectionTerm family cutoff power (-((degree + 1 : ℕ) : ℤ))
      ((HomologicalComplex.extendXIso complex ComplexShape.embeddingDownNat
        (i := degree + 1) rfl).inv ((Pi.basisFun A (Fin rank)).exteriorPower (degree + 1) subset))
    (HomologicalComplex.tensorObj coefficient factor).d totalDegree (totalDegree + 1)
        (HomologicalComplex.ιTensorObj coefficient factor coefficientDegree (-((degree + 1 : ℕ) :
          ℤ))
          totalDegree totalIndex (left ⊗ₜ[A] sourceBasis)) =
      HomologicalComplex.ιTensorObj coefficient factor (coefficientDegree + 1) (-((degree + 1 : ℕ) :
        ℤ))
        (totalDegree + 1) (by omega)
        (coefficient.d coefficientDegree (coefficientDegree + 1) left ⊗ₜ[A] sourceBasis) +
      ∑ index : subset.1,
        ((-1 : A) ^ coefficientDegree.natAbs *
          ((-1 : A) ^ (subset.1.filter (· < index.1)).card * family index.1 ^ (power + 1))) •
        HomologicalComplex.ιTensorObj coefficient factor coefficientDegree (-(degree : ℤ))
          (totalDegree + 1) (by omega)
          (left ⊗ₜ[A] standardKoszulSectionTerm family cutoff power (-(degree : ℤ))
            ((HomologicalComplex.extendXIso complex ComplexShape.embeddingDownNat
              (i := degree) rfl).inv ((Pi.basisFun A (Fin rank)).exteriorPower degree
                ⟨subset.1.erase index.1, by
                  change (subset.1.erase index.1).card = degree
                  rw [Finset.card_erase_of_mem index.2, subset.2]; omega⟩))) := by
  dsimp only
  rw [tensor_summand_differential_apply coefficient (standardKoszulStage family cutoff power)
    coefficientDegree (-((degree + 1 : ℕ) : ℤ)) totalDegree totalIndex (-(degree : ℤ)) (by omega)]
  congr 1
  rw [standardKoszul_d_exteriorBasis_cutoff family cutoff power degree subset sourceSurvives]
  show (-1 : A) ^ coefficientDegree.natAbs •
    (HomologicalComplex.ιTensorObj coefficient (standardKoszulStage family cutoff power)
      coefficientDegree (-(degree : ℤ)) (totalDegree + 1) (by omega)).hom _ = _
  simp only [TensorProduct.tmul_sum, TensorProduct.tmul_smul, map_sum, map_smul,
    Finset.smul_sum, smul_smul]

private def subsetEraseInsertEquiv {index : Type*} [DecidableEq index] :
    (Σ subset : Finset index, {element // element ∈ subset}) ≃
      (Σ subset : Finset index, {element // element ∉ subset}) where
  toFun pair := ⟨pair.1.erase pair.2.1, pair.2.1, Finset.notMem_erase _ _⟩
  invFun pair := ⟨insert pair.2.1 pair.1, pair.2.1, Finset.mem_insert_self _ _⟩
  left_inv := by
    rintro ⟨subset, element, member⟩
    apply Sigma.ext (Finset.insert_erase member)
    exact (Subtype.heq_iff_coe_eq (fun _ => by dsimp only; rw [Finset.insert_erase member])).2 rfl
  right_inv := by
    rintro ⟨subset, element, notMember⟩
    apply Sigma.ext (Finset.erase_insert notMember)
    exact (Subtype.heq_iff_coe_eq (fun _ => by dsimp only; rw [Finset.erase_insert notMember])).2
      rfl

private theorem sum_erase_eq_sum_insert
    {index target : Type*} [Fintype index] [DecidableEq index] [AddCommMonoid target]
    (term : (subset : Finset index) → {element // element ∉ subset} → target) :
    (∑ subset : Finset index, ∑ element : subset,
        term (subset.erase element.1) ⟨element.1, Finset.notMem_erase _ _⟩) =
      ∑ subset : Finset index, ∑ element : {element // element ∉ subset}, term subset element := by
  classical
  simpa only [Fintype.sum_sigma] using
    Fintype.sum_equiv (subsetEraseInsertEquiv (index := index))
      (fun pair => term (pair.1.erase pair.2.1) ⟨pair.2.1, Finset.notMem_erase _ _⟩)
      (fun pair => term pair.1 pair.2) (fun _ => rfl)

private theorem filter_lt_erase {index : Type*} [LinearOrder index]
    (subset : Finset index) (element : index) :
    (subset.erase element).filter (· < element) = subset.filter (· < element) := by
  ext candidate
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · exact fun member => ⟨member.1.2, member.2⟩
  · exact fun member => ⟨⟨ne_of_lt member.2, member.1⟩, member.2⟩

/-- Erasing an element of a finset shifts the cast cardinality by one. -/
private theorem add_card_erase_eq {rank : ℕ} (degree : ℤ) (subset : Finset (Fin rank))
    (index : subset) : degree + subset.card = degree + 1 + (subset.erase index.1).card := by
  have := Finset.card_erase_of_mem index.2
  have := Finset.card_pos.mpr ⟨index.1, index.2⟩
  omega

/-- Inserting a new element into a finset shifts the cast cardinality by one. -/
private theorem add_card_insert_eq {rank : ℕ} (degree : ℤ) (subset : Finset (Fin rank))
    (index : {element // element ∉ subset}) :
    degree + (insert index.1 subset).card = degree + 1 + subset.card := by
  have := Finset.card_insert_of_notMem index.2
  omega

private theorem signed_koszul_sum_erase_eq_sum_insert
    {rank : ℕ} {target : Type*} [AddCommGroup target] [Module A target]
    (family : Fin rank → A) (power : ℕ) (totalDegree : ℤ)
    (payload : Finset (Fin rank) → Finset (Fin rank) → Fin rank → target) :
    (∑ subset : Finset (Fin rank), ∑ element : subset,
        ((-1 : A) ^ (totalDegree + subset.card).natAbs *
          (-1 : A) ^ (subset.filter (· < element.1)).card * family element.1 ^ (power + 1)) •
          payload (subset.erase element.1) subset element.1) =
      ∑ subset : Finset (Fin rank), ∑ element : {element // element ∉ subset},
        ((-1 : A) ^ (totalDegree + subset.card + 1).natAbs *
          (-1 : A) ^ (subset.filter (· < element.1)).card * family element.1 ^ (power + 1)) •
          payload subset (insert element.1 subset) element.1 := by
  classical
  rw [← sum_erase_eq_sum_insert]
  apply Finset.sum_congr rfl
  intro subset _
  apply Finset.sum_congr rfl
  intro element _
  rw [Finset.insert_erase element.2, filter_lt_erase]
  rw [show totalDegree + subset.card = totalDegree + (subset.erase element.1).card + 1 by
    have := add_card_erase_eq totalDegree subset element
    omega]

private theorem standardKoszulStage_isZero_X_pos
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power : ℕ)
    (degree : ℤ) (positive : 0 < degree) :
    IsZero ((standardKoszulStage family cutoff power).X degree) := by
  have untruncated : IsZero ((standardKoszulStage family none power).X degree) := by
    apply HomologicalComplex.isZero_extend_X
    intro index
    show -(index : ℤ) ≠ degree
    omega
  cases cutoff with
  | none => exact untruncated
  | some cutoff =>
    by_cases survives : cutoff ≤ degree
    · exact untruncated.of_iso ((standardKoszulStage family none power).stupidTruncXIso
        (ComplexShape.embeddingUpIntGE cutoff) (i := (degree - cutoff).toNat) (by
          show cutoff + ((degree - cutoff).toNat : ℤ) = degree
          rw [Int.toNat_of_nonneg (by omega)]; omega))
    · apply HomologicalComplex.isZero_stupidTrunc_X
      intro index
      show cutoff + (index : ℤ) ≠ degree
      omega

private theorem tensor_koszul_degree_zero_differential
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power : ℕ)
    (coefficient : CochainComplex (ModuleCat.{u} A) ℤ) (degree : ℤ)
    (left : coefficient.X degree) (right : (standardKoszulStage family cutoff power).X 0) :
    (HomologicalComplex.tensorObj coefficient (standardKoszulStage family cutoff power)).d
        degree (degree + 1)
        (HomologicalComplex.ιTensorObj coefficient (standardKoszulStage family cutoff power)
          degree 0 degree (by omega) (left ⊗ₜ[A] right)) =
      HomologicalComplex.ιTensorObj coefficient (standardKoszulStage family cutoff power)
        (degree + 1) 0 (degree + 1) (by omega)
        (coefficient.d degree (degree + 1) left ⊗ₜ[A] right) := by
  rw [tensor_summand_differential_apply coefficient (standardKoszulStage family cutoff power)
    degree 0 degree (by omega) 1 (by omega)]
  have differentialZero : (standardKoszulStage family cutoff power).d 0 1 = 0 :=
    (standardKoszulStage_isZero_X_pos family cutoff power 1 (by omega)).eq_of_tgt _ _
  simp [differentialZero]

private theorem comparisonTerm_apply_up
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power : ℕ)
    (complex : CochainComplex (ModuleCat.{v} A) ℤ) (degree : ℤ)
    (element : filteredTerm (r := rank) cutoff complex degree) :
    comparisonTerm family cutoff power complex degree (ULift.up element) =
      ∑ subset : Finset (Fin rank),
        HomologicalComplex.ιTensorObj ((complexUniverseLift (A := A)).obj complex)
          (standardKoszulStage (fun index => (ULift.up (family index) : ULift.{v} A)) cutoff power)
          (degree + subset.card) (-(subset.card : ℤ)) degree (by omega)
          (ULift.up ((termProjection cutoff complex degree).hom element subset) ⊗ₜ[ULift.{v} A]
            koszulBasisVector (fun index => (ULift.up (family index) : ULift.{v} A)) cutoff power
              subset) := by
  classical
  simp only [comparisonTerm, ModuleCat.hom_sum]
  erw [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro subset _
  rfl

private def koszulTensorBasisAt
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power : ℕ)
    (coefficient : CochainComplex (ModuleCat.{u} A) ℤ) (exteriorDegree : ℕ)
    (subset : KoszulBasis rank exteriorDegree) (coefficientDegree totalDegree : ℤ)
    (totalIndex : coefficientDegree + -(exteriorDegree : ℤ) = totalDegree)
    (element : coefficient.X coefficientDegree) :
    (HomologicalComplex.tensorObj coefficient (standardKoszulStage family cutoff power)).X
      totalDegree :=
  HomologicalComplex.ιTensorObj coefficient (standardKoszulStage family cutoff power)
    coefficientDegree (-(exteriorDegree : ℤ)) totalDegree totalIndex
    (element ⊗ₜ[A] standardKoszulSectionTerm family cutoff power (-(exteriorDegree : ℤ))
      ((HomologicalComplex.extendXIso (Koszul.seqComplex (fun index => family index ^ (power + 1)))
        ComplexShape.embeddingDownNat (i := exteriorDegree) rfl).inv
        ((Pi.basisFun A (Fin rank)).exteriorPower exteriorDegree subset)))

private theorem koszulTensorBasisAt_differential
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power : ℕ)
    (coefficient : CochainComplex (ModuleCat.{u} A) ℤ) (exteriorDegree : ℕ)
    (subset : KoszulBasis rank exteriorDegree) (coefficientDegree totalDegree : ℤ)
    (totalIndex : coefficientDegree + -(exteriorDegree : ℤ) = totalDegree)
    (sourceSurvives : CutoffLE cutoff (some (-(exteriorDegree : ℤ))))
    (element : coefficient.X coefficientDegree) :
    (HomologicalComplex.tensorObj coefficient (standardKoszulStage family cutoff power)).d
        totalDegree (totalDegree + 1)
        (koszulTensorBasisAt family cutoff power coefficient exteriorDegree subset
          coefficientDegree totalDegree totalIndex element) =
      koszulTensorBasisAt family cutoff power coefficient exteriorDegree subset
        (coefficientDegree + 1) (totalDegree + 1) (by omega)
        (coefficient.d coefficientDegree (coefficientDegree + 1) element) +
      ∑ index : subset.1,
        ((-1 : A) ^ coefficientDegree.natAbs *
          ((-1 : A) ^ (subset.1.filter (· < index.1)).card * family index.1 ^ (power + 1))) •
          koszulTensorBasisAt family cutoff power coefficient (exteriorDegree - 1)
            ⟨subset.1.erase index.1, by rw [Finset.card_erase_of_mem index.2, subset.2]⟩
            coefficientDegree (totalDegree + 1) (by
              have positive : 0 < exteriorDegree := subset.2 ▸ Finset.card_pos.mpr ⟨index.1,
                index.2⟩
              rw [Nat.cast_sub (by omega : 1 ≤ exteriorDegree)]
              simp only [Nat.cast_one]
              omega) element := by
  cases exteriorDegree with
  | zero =>
    have empty : subset.1 = ∅ := Finset.card_eq_zero.mp subset.2
    let : IsEmpty subset.1 := ⟨fun index => by simpa only [empty, Finset.notMem_empty] using
      index.2⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    have coefficientEquality : coefficientDegree = totalDegree := by omega
    subst coefficientDegree
    simp only [koszulTensorBasisAt]
    exact tensor_koszul_degree_zero_differential family cutoff power coefficient totalDegree element
      _
  | succ degree =>
    simpa only [koszulTensorBasisAt, Nat.succ_sub_one] using!
      tensor_koszul_basis_differential family cutoff power degree coefficient subset sourceSurvives
        coefficientDegree totalDegree totalIndex element

private def koszulTensorBasisValue
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power : ℕ)
    (coefficient : CochainComplex (ModuleCat.{u} A) ℤ) (degree : ℤ)
    (subset : Finset (Fin rank)) (element : coefficient.X (degree + subset.card)) :
    (HomologicalComplex.tensorObj coefficient (standardKoszulStage family cutoff power)).X degree :=
  HomologicalComplex.ιTensorObj coefficient (standardKoszulStage family cutoff power)
    (degree + subset.card) (-(subset.card : ℤ)) degree (by omega)
    (element ⊗ₜ[A] koszulBasisVector family cutoff power subset)

private theorem koszulTensorBasisAt_eq_value
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power : ℕ)
    (coefficient : CochainComplex (ModuleCat.{u} A) ℤ) (exteriorDegree : ℕ)
    (subset : KoszulBasis rank exteriorDegree) (coefficientDegree totalDegree : ℤ)
    (totalIndex : coefficientDegree + -(exteriorDegree : ℤ) = totalDegree)
    (element : coefficient.X coefficientDegree) :
    koszulTensorBasisAt family cutoff power coefficient exteriorDegree subset
        coefficientDegree totalDegree totalIndex element =
      koszulTensorBasisValue family cutoff power coefficient totalDegree subset.1
        ((eqToHom (congrArg coefficient.X (show coefficientDegree = totalDegree + subset.1.card by
          rw [subset.2]; omega))) element) := by
  rcases subset with ⟨subset, cardinality⟩
  dsimp only at *
  subst exteriorDegree
  have coefficientEquality : coefficientDegree = totalDegree + subset.card := by omega
  subst coefficientDegree
  cases cutoff <;> rfl

private theorem koszulTensorBasisValue_eq_at
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power : ℕ)
    (coefficient : CochainComplex (ModuleCat.{u} A) ℤ) (degree : ℤ)
    (subset : Finset (Fin rank)) (element : coefficient.X (degree + subset.card)) :
    koszulTensorBasisValue family cutoff power coefficient degree subset element =
      koszulTensorBasisAt family cutoff power coefficient subset.card ⟨subset, rfl⟩
        (degree + subset.card) degree (by omega) element := by
  cases cutoff <;> rfl

private theorem koszulTensorBasisValue_differential
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power : ℕ)
    (coefficient : CochainComplex (ModuleCat.{u} A) ℤ) (degree : ℤ)
    (subset : Finset (Fin rank)) (sourceSurvives : CutoffLE cutoff (some (-(subset.card : ℤ))))
    (element : coefficient.X (degree + subset.card)) :
    (HomologicalComplex.tensorObj coefficient (standardKoszulStage family cutoff power)).d degree
      (degree + 1)
        (koszulTensorBasisValue family cutoff power coefficient degree subset element) =
      koszulTensorBasisValue family cutoff power coefficient (degree + 1) subset
        (coefficient.d (degree + subset.card) ((degree + 1) + subset.card) element) +
      ∑ index : subset,
        ((-1 : A) ^ (degree + subset.card).natAbs *
          ((-1 : A) ^ (subset.filter (· < index.1)).card * family index.1 ^ (power + 1))) •
          koszulTensorBasisValue family cutoff power coefficient (degree + 1) (subset.erase index.1)
            ((eqToHom (congrArg coefficient.X (add_card_erase_eq degree subset index)))
              element) := by
  have differential := koszulTensorBasisAt_differential family cutoff power coefficient subset.card
    ⟨subset, rfl⟩ (degree + subset.card) degree (by omega) sourceSurvives element
  simp only [koszulTensorBasisAt_eq_value, eqToHom_refl, ModuleCat.id_apply] at differential
  rw [differential]
  congr 2
  have commute := eqToHom_d coefficient (degree + subset.card) (degree + subset.card)
    ((degree + subset.card) + 1) ((degree + 1) + subset.card) rfl (by omega)
  simpa only [eqToHom_refl, Category.id_comp, ModuleCat.comp_apply] using
    (ConcreteCategory.congr_hom commute element).symm

private def koszulTensorBasisMap
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power : ℕ)
    (coefficient : CochainComplex (ModuleCat.{u} A) ℤ) (degree : ℤ) (subset : Finset (Fin rank)) :
    coefficient.X (degree + subset.card) ⟶
      (HomologicalComplex.tensorObj coefficient (standardKoszulStage family cutoff power)).X degree
        :=
  ModuleCat.ofHom ((TensorProduct.mk A _ _).flip (koszulBasisVector family cutoff power subset)) ≫
    HomologicalComplex.ιTensorObj coefficient (standardKoszulStage family cutoff power)
      (degree + subset.card) (-(subset.card : ℤ)) degree (by omega)

private theorem koszulTensorBasisValue_eq_map
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power : ℕ)
    (coefficient : CochainComplex (ModuleCat.{u} A) ℤ) (degree : ℤ) (subset : Finset (Fin rank))
    (element : coefficient.X (degree + subset.card)) :
    koszulTensorBasisValue family cutoff power coefficient degree subset element =
      (koszulTensorBasisMap family cutoff power coefficient degree subset).hom element := rfl

private def movedCoefficient
    {rank : ℕ} (coefficient : CochainComplex (ModuleCat.{u} A) ℤ) (degree : ℤ)
    (elements : ∀ subset : Finset (Fin rank), coefficient.X (degree + subset.card))
    (target source : Finset (Fin rank)) : coefficient.X ((degree + 1) + target.card) :=
  if sameDegree : degree + source.card = (degree + 1) + target.card then
    (eqToHom (congrArg coefficient.X sameDegree)) (elements source)
  else 0

private theorem summedComparison_differential
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power : ℕ)
    (coefficient : CochainComplex (ModuleCat.{u} A) ℤ) (degree : ℤ)
    (elements : ∀ subset : Finset (Fin rank), coefficient.X (degree + subset.card))
    (supported : ∀ subset, ¬ CutoffLE cutoff (some (-(subset.card : ℤ))) → elements subset = 0) :
    (HomologicalComplex.tensorObj coefficient (standardKoszulStage family cutoff power)).d degree
      (degree + 1)
        (∑ subset : Finset (Fin rank), koszulTensorBasisValue family cutoff power coefficient degree
          subset
          (elements subset)) =
      ∑ subset : Finset (Fin rank), koszulTensorBasisValue family cutoff power coefficient (degree +
        1) subset
        ((coefficientKoszulDifferential family power coefficient degree).hom elements subset) := by
  classical
  let payload := fun (target source : Finset (Fin rank)) (_index : Fin rank) =>
    koszulTensorBasisValue family cutoff power coefficient (degree + 1) target
      (movedCoefficient coefficient degree elements target source)
  have summand (subset : Finset (Fin rank)) :
      (HomologicalComplex.tensorObj coefficient (standardKoszulStage family cutoff power)).d degree
        (degree + 1)
          (koszulTensorBasisValue family cutoff power coefficient degree subset (elements subset)) =
        koszulTensorBasisValue family cutoff power coefficient (degree + 1) subset
          (coefficient.d (degree + subset.card) ((degree + 1) + subset.card) (elements subset)) +
        ∑ index : subset,
          ((-1 : A) ^ (degree + subset.card).natAbs *
            (-1 : A) ^ (subset.filter (· < index.1)).card * family index.1 ^ (power + 1)) •
            payload (subset.erase index.1) subset index.1 := by
    have erasedDegree (index : subset) := add_card_erase_eq degree subset index
    by_cases survives : CutoffLE cutoff (some (-(subset.card : ℤ)))
    · simpa only [payload, movedCoefficient, dite_eq_left (erasedDegree _), mul_assoc] using
        koszulTensorBasisValue_differential family cutoff power coefficient degree subset survives
          (elements subset)
    · simp only [payload, movedCoefficient, dite_eq_left (erasedDegree _), supported subset
      survives,
        koszulTensorBasisValue_eq_map, map_zero, smul_zero, Finset.sum_const_zero, add_zero]
  show ((HomologicalComplex.tensorObj coefficient (standardKoszulStage family cutoff power)).d
    degree (degree + 1)).hom _ = _
  rw [map_sum]
  simp_rw [summand]
  rw [Finset.sum_add_distrib, signed_koszul_sum_erase_eq_sum_insert family power degree payload,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro subset _
  show _ = koszulTensorBasisValue family cutoff power coefficient (degree + 1) subset
    ((coefficient.d (degree + subset.card) ((degree + 1) + subset.card)).hom (elements subset) + _)
  simp only [koszulTensorBasisValue_eq_map, map_add]
  congr 1
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro index _
  simp only [payload, movedCoefficient, dite_eq_left (add_card_insert_eq degree subset index),
    koszulTensorBasisValue_eq_map, map_smul]

private theorem lifted_coefficient_eqToHom
    (coefficient : CochainComplex (ModuleCat.{v} A) ℤ)
    {source target : ℤ} (equality : source = target) (element : coefficient.X source) :
    ((eqToHom (congrArg ((complexUniverseLift (A := A)).obj coefficient).X equality))
        (ULift.up element)).down =
      (eqToHom (congrArg coefficient.X equality)) element := by
  subst target
  rfl

private theorem liftedCoefficientDifferential_apply
    {rank : ℕ} (family : Fin rank → A) (power : ℕ)
    (coefficient : CochainComplex (ModuleCat.{v} A) ℤ) (degree : ℤ)
    (elements : ∀ subset : Finset (Fin rank), coefficient.X (degree + subset.card))
    (subset : Finset (Fin rank)) :
    (coefficientKoszulDifferential (fun index => (ULift.up (family index) : ULift.{v} A)) power
        ((complexUniverseLift (A := A)).obj coefficient) degree).hom
        (fun subset => ULift.up (elements subset)) subset =
      ULift.up ((coefficientKoszulDifferential family power coefficient degree).hom elements subset)
        := by
  dsimp only [coefficientKoszulDifferential, ModuleCat.hom_ofHom, LinearMap.coe_mk, AddHom.coe_mk]
  apply ULift.ext
  show (ULift.moduleEquiv : ULift.{u} (coefficient.X ((degree + 1) + subset.card)) ≃ₗ[A]
    coefficient.X ((degree + 1) + subset.card)) (_ + _) = _
  erw [map_add, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro index _
  show ((-1 : ULift.{v} A) ^ (degree + subset.card + 1).natAbs *
      (-1 : ULift.{v} A) ^ (subset.filter (· < index.1)).card *
        (ULift.up (family index.1) : ULift.{v} A) ^ (power + 1)).down •
          (_ : coefficient.X ((degree + 1) + subset.card)) =
    ((-1 : A) ^ (degree + subset.card + 1).natAbs *
      (-1 : A) ^ (subset.filter (· < index.1)).card * family index.1 ^ (power + 1)) •
        (_ : coefficient.X ((degree + 1) + subset.card))
  have scalarEquality : ((-1 : ULift.{v} A) ^ (degree + subset.card + 1).natAbs *
      (-1 : ULift.{v} A) ^ (subset.filter (· < index.1)).card *
        (ULift.up (family index.1) : ULift.{v} A) ^ (power + 1)).down =
    (-1 : A) ^ (degree + subset.card + 1).natAbs *
      (-1 : A) ^ (subset.filter (· < index.1)).card * family index.1 ^ (power + 1) := by
    rfl
  rw [scalarEquality]
  congr 1
  exact lifted_coefficient_eqToHom coefficient (add_card_insert_eq degree subset index) _

set_option backward.isDefEq.respectTransparency false in
private theorem comparison_comm_succ
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power : ℕ)
    (coefficient : CochainComplex (ModuleCat.{v} A) ℤ) (degree : ℤ) :
    comparisonTerm family cutoff power coefficient degree ≫
        ((standardCoefficientKoszulStage family cutoff power).obj coefficient).d degree (degree + 1)
          =
      (AdicKoszul.moduleUniverseLift A).map
          (filteredDifferential family cutoff power coefficient degree (degree + 1)) ≫
        comparisonTerm family cutoff power coefficient (degree + 1) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro element
  obtain ⟨element⟩ := element
  let lifted := (complexUniverseLift (A := A)).obj coefficient
  let elements := fun subset : Finset (Fin rank) =>
    (ULift.up ((termProjection cutoff coefficient degree).hom element subset) : lifted.X (degree +
      subset.card))
  have supported : ∀ subset, ¬ CutoffLE cutoff (some (-(subset.card : ℤ))) → elements subset = 0 :=
    by
    intro subset removed
    show ULift.up ((termProjection cutoff coefficient degree).hom element subset) = 0
    rw [termProjection_apply_eq_zero cutoff coefficient degree subset removed element]
    rfl
  have differential := summedComparison_differential
    (fun index => (ULift.up (family index) : ULift.{v} A)) cutoff power lifted degree elements
      supported
  show ((standardCoefficientKoszulStage family cutoff power).obj coefficient).d degree (degree +
    1)
      (comparisonTerm family cutoff power coefficient degree (ULift.up element)) =
    comparisonTerm family cutoff power coefficient (degree + 1)
      (ULift.up ((filteredDifferential family cutoff power coefficient degree (degree + 1)).hom
        element))
  rw [comparisonTerm_apply_up, comparisonTerm_apply_up]
  show _ = ∑ subset : Finset (Fin rank),
    koszulTensorBasisValue (fun index => (ULift.up (family index) : ULift.{v} A)) cutoff power
      lifted
      (degree + 1) subset (ULift.up ((termProjection cutoff coefficient (degree + 1)).hom
        ((filteredDifferential family cutoff power coefficient degree (degree + 1)).hom element)
          subset))
  erw [differential]
  apply Finset.sum_congr rfl
  intro subset _
  congr 1
  rw [liftedCoefficientDifferential_apply]
  apply congrArg ULift.up
  have projection := filteredDifferential_projection family cutoff power coefficient degree (degree
    + 1)
  have equality := ConcreteCategory.congr_hom projection element
  simpa only [filteredDifferential, dite_eq_left rfl, eqToHom_refl, termProjection_none,
    termSection_none, Category.comp_id, Category.id_comp, ModuleCat.comp_apply] using!
    (congrFun equality subset).symm

end KoszulCoefficientTower

end

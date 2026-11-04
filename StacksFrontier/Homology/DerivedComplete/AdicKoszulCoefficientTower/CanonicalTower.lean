module

public import StacksFrontier.Homology.DerivedComplete.AdicKoszulCoefficientTower.ComparisonLaws
import all StacksFrontier.Homology.DerivedComplete.AdicKoszulCoefficientTower.Formulas
import all StacksFrontier.Homology.DerivedComplete.AdicKoszulCoefficientTower.FiltrationLaws
import all StacksFrontier.Homology.DerivedComplete.AdicKoszulCoefficientTower.GradedQuasiIso
import all StacksFrontier.Homology.DerivedComplete.AdicKoszulCoefficientTower.ComparisonLaws
import Mathlib
import all Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Koszul towers with coefficients

For a finite sequence in a commutative ring, this file constructs the tower obtained by
tensoring its Koszul complexes on positive powers with an arbitrary cochain complex.  The
construction uses finite exterior-basis copies of the coefficient modules, so its values remain
in the universe of the coefficient complex.

## Main definitions

* `KoszulCoefficientTower.coefficientKoszulTower` is the strictly functorial coefficient
  Koszul tower.
* `KoszulCoefficientTower.coefficientKoszulAugmentation` is its natural augmentation.
* `KoszulCoefficientTower.coefficientKoszulFiltration` is the finite stupid filtration in
  the Koszul direction.

## Main results

* `KoszulCoefficientTower.canonicalFormulaLaws` verifies the signed differential,
  functor laws, canonical comparisons, graded quotients, and preservation of quasi-isomorphisms.

## References

* [Stacks Project, Tag 091Z](https://stacks.math.columbia.edu/tag/091Z)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u v

namespace KoszulCoefficientTower

variable {A : Type u} [CommRing A]

private theorem comparison_comm_complete
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power : ℕ)
    (coefficient : CochainComplex (ModuleCat.{v} A) ℤ) (source target : ℤ) :
    comparisonTerm family cutoff power coefficient source ≫
        ((standardCoefficientKoszulStage family cutoff power).obj coefficient).d source target =
      (AdicKoszul.moduleUniverseLift A).map
          (filteredDifferential family cutoff power coefficient source target) ≫
        comparisonTerm family cutoff power coefficient target := by
  by_cases successor : source + 1 = target
  · subst target
    exact comparison_comm_succ family cutoff power coefficient source
  · have offShape : ¬ (ComplexShape.up ℤ).Rel source target := successor
    rw [HomologicalComplex.shape _ source target offShape]
    simp only [comp_zero, filteredDifferential, dite_eq_right successor,
      Functor.map_zero, zero_comp]

private theorem formulaLaws_complete {rank : ℕ} (family : Fin rank → A) :
    FormulaLaws.{u, v} family where
  square := filteredDifferential_square family
  map_comm := filteredMapTerm_comm family
  map_id := filteredMapTerm_id
  map_comp := filteredMapTerm_comp
  transition_comm := filteredTransitionTerm_comm family
  transition_id := filteredTransitionTerm_id family
  transition_comp := filteredTransitionTerm_comp family
  transition_naturality := fun cutoff source target _ {left right} morphism =>
    filteredTransitionTerm_naturality family cutoff source target (K := left) (L := right) morphism
  unit_comm := filteredUnitTerm_comm family
  unit_naturality := filteredUnitTerm_naturality
  unit_transition := fun cutoff source target _ coefficient degree =>
    filteredUnitTerm_transition family cutoff source target coefficient degree
  inclusion_comm := filtrationInclusionTerm_comm family
  inclusion_naturality := filtrationInclusionTerm_naturality
  inclusion_transition := fun lower upper ordered source target _ coefficient degree =>
    filtrationInclusionTerm_transition family lower upper ordered source target coefficient degree
  comparison_comm := comparison_comm_complete family
  standard_inclusion_comm := standardKoszulInclusionTerm_comm (fun index => ULift.up (family index))
  graded_comm := gradedComponentTerm_comm family
  graded_vanish := gradedComponentTerm_vanish


/-- Above the cutoff, a stupid truncation of the Koszul stage has the untruncated term. -/
private def koszulStageTruncXIso
    {rank : ℕ} (family : Fin rank → A) (cutoff : ℤ) (power : ℕ) (degree : ℤ)
    (survives : cutoff ≤ degree) :
    (standardKoszulStage family (some cutoff) power).X degree ≅
      (standardKoszulStage family none power).X degree :=
  (standardKoszulStage family none power).stupidTruncXIso
    (ComplexShape.embeddingUpIntGE cutoff) (i := (degree - cutoff).toNat) (by
      change cutoff + ((degree - cutoff).toNat : ℤ) = degree
      rw [Int.toNat_of_nonneg (sub_nonneg.mpr survives)]
      omega)

private def koszulStageXIso
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power exteriorDegree : ℕ)
    (survives : CutoffLE cutoff (some (-(exteriorDegree : ℤ)))) :
    (standardKoszulStage family cutoff power).X (-(exteriorDegree : ℤ)) ≅
      ModuleCat.of A (⋀[A]^exteriorDegree (Fin rank → A)) := by
  let original := Koszul.seqComplex (fun index => family index ^ (power + 1))
  let extension := HomologicalComplex.extendXIso original ComplexShape.embeddingDownNat
    (i := exteriorDegree) rfl
  cases cutoff with
  | none => exact extension
  | some cutoff => exact koszulStageTruncXIso family cutoff power _ survives ≪≫ extension

private def koszulStageBasis
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power exteriorDegree : ℕ)
    (survives : CutoffLE cutoff (some (-(exteriorDegree : ℤ)))) :
    Module.Basis (KoszulBasis rank exteriorDegree) A
      ((standardKoszulStage family cutoff power).X (-(exteriorDegree : ℤ))) :=
  ((Pi.basisFun A (Fin rank)).exteriorPower exteriorDegree).map
    (koszulStageXIso family cutoff power exteriorDegree survives).toLinearEquiv.symm

private theorem koszulStageBasis_apply
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power exteriorDegree : ℕ)
    (survives : CutoffLE cutoff (some (-(exteriorDegree : ℤ))))
    (subset : KoszulBasis rank exteriorDegree) :
    koszulStageBasis family cutoff power exteriorDegree survives subset =
      standardKoszulSectionTerm family cutoff power (-(exteriorDegree : ℤ))
        ((HomologicalComplex.extendXIso (Koszul.seqComplex (fun index => family index ^ (power +
          1)))
          ComplexShape.embeddingDownNat (i := exteriorDegree) rfl).inv
          ((Pi.basisFun A (Fin rank)).exteriorPower exteriorDegree subset)) := by
  show (koszulStageXIso family cutoff power exteriorDegree survives).inv
    ((Pi.basisFun A (Fin rank)).exteriorPower exteriorDegree subset) = _
  cases cutoff with
  | none => rfl
  | some cutoff =>
    dsimp only [koszulStageXIso, koszulStageTruncXIso, Iso.trans_inv, ModuleCat.comp_apply,
      standardKoszulSectionTerm, stupidTruncSection]
    rw [dite_eq_left (show cutoff ≤ -(exteriorDegree : ℤ) from survives)]
    rfl

private theorem koszulStageBasis_apply_card
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power : ℕ)
    (subset : Finset (Fin rank)) (survives : CutoffLE cutoff (some (-(subset.card : ℤ)))) :
    koszulStageBasis family cutoff power subset.card survives ⟨subset, rfl⟩ =
      koszulBasisVector family cutoff power subset := by
  rw [koszulStageBasis_apply]
  cases cutoff <;> rfl

private def koszulStageCoordinate
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power exteriorDegree : ℕ)
    (survives : CutoffLE cutoff (some (-(exteriorDegree : ℤ))))
    (subset : KoszulBasis rank exteriorDegree) :
    (standardKoszulStage family cutoff power).X (-(exteriorDegree : ℤ)) →ₗ[A] A :=
  (Finsupp.lapply subset).comp
    (koszulStageBasis family cutoff power exteriorDegree survives).repr.toLinearMap

private theorem koszulStageCoordinate_basis
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power exteriorDegree : ℕ)
    (survives : CutoffLE cutoff (some (-(exteriorDegree : ℤ))))
    (source target : KoszulBasis rank exteriorDegree) :
    koszulStageCoordinate family cutoff power exteriorDegree survives target
        (koszulStageBasis family cutoff power exteriorDegree survives source) =
      if source = target then 1 else 0 := by
  classical
  exact (koszulStageBasis family cutoff power exteriorDegree survives).repr_self_apply source target

private def tensorKoszulCoordinate
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power : ℕ)
    (coefficient : CochainComplex (ModuleCat.{u} A) ℤ) (totalDegree : ℤ) (exteriorDegree : ℕ)
    (survives : CutoffLE cutoff (some (-(exteriorDegree : ℤ))))
    (subset : KoszulBasis rank exteriorDegree) :
    (HomologicalComplex.tensorObj coefficient (standardKoszulStage family cutoff power)).X
      totalDegree ⟶
      coefficient.X (totalDegree + exteriorDegree) :=
  HomologicalComplex.mapBifunctorDesc (fun leftDegree rightDegree totalIndex =>
    if rightIndex : rightDegree = -(exteriorDegree : ℤ) then
      (coefficient.X leftDegree ◁ eqToHom (congrArg
        (standardKoszulStage family cutoff power).X rightIndex)) ≫
      ModuleCat.ofHom ((Finsupp.lapply subset).comp
        (TensorProduct.equivFinsuppOfBasisRight (M := coefficient.X leftDegree)
          (koszulStageBasis family cutoff power exteriorDegree survives)).toLinearMap) ≫
      eqToHom (congrArg coefficient.X (show leftDegree = totalDegree + exteriorDegree by
        change leftDegree + rightDegree = totalDegree at totalIndex
        rw [rightIndex] at totalIndex
        omega))
    else 0)

private theorem tensorKoszulCoordinate_ι
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power : ℕ)
    (coefficient : CochainComplex (ModuleCat.{u} A) ℤ) (totalDegree : ℤ) (exteriorDegree : ℕ)
    (survives : CutoffLE cutoff (some (-(exteriorDegree : ℤ))))
    (subset : KoszulBasis rank exteriorDegree) :
    HomologicalComplex.ιTensorObj coefficient (standardKoszulStage family cutoff power)
        (totalDegree + exteriorDegree) (-(exteriorDegree : ℤ)) totalDegree (by omega) ≫
        tensorKoszulCoordinate family cutoff power coefficient totalDegree exteriorDegree survives
          subset =
      ModuleCat.ofHom ((Finsupp.lapply subset).comp
        (TensorProduct.equivFinsuppOfBasisRight (M := coefficient.X (totalDegree + exteriorDegree))
          (koszulStageBasis family cutoff power exteriorDegree survives)).toLinearMap) := by
  dsimp only [tensorKoszulCoordinate]
  rw [HomologicalComplex.ι_mapBifunctorDesc]
  simp only [eqToHom_refl, whiskerLeft_id, Category.comp_id,
    dite_true]
  erw [Category.id_comp]

private theorem tensorKoszulCoordinate_ι_tmul
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power : ℕ)
    (coefficient : CochainComplex (ModuleCat.{u} A) ℤ) (totalDegree : ℤ) (exteriorDegree : ℕ)
    (survives : CutoffLE cutoff (some (-(exteriorDegree : ℤ))))
    (subset : KoszulBasis rank exteriorDegree)
    (left : coefficient.X (totalDegree + exteriorDegree))
    (right : (standardKoszulStage family cutoff power).X (-(exteriorDegree : ℤ))) :
    tensorKoszulCoordinate family cutoff power coefficient totalDegree exteriorDegree survives
      subset
        (HomologicalComplex.ιTensorObj coefficient (standardKoszulStage family cutoff power)
          (totalDegree + exteriorDegree) (-(exteriorDegree : ℤ)) totalDegree (by omega)
          (left ⊗ₜ[A] right)) =
      (koszulStageBasis family cutoff power exteriorDegree survives).repr right subset • left := by
  show (HomologicalComplex.ιTensorObj coefficient (standardKoszulStage family cutoff power)
    (totalDegree + exteriorDegree) (-(exteriorDegree : ℤ)) totalDegree (by omega) ≫
      tensorKoszulCoordinate family cutoff power coefficient totalDegree exteriorDegree survives
        subset)
      (left ⊗ₜ[A] right) = _
  rw [tensorKoszulCoordinate_ι]
  exact TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply _ left right subset

private theorem tensorKoszulCoordinate_wrong_degree
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power : ℕ)
    (coefficient : CochainComplex (ModuleCat.{u} A) ℤ) (totalDegree : ℤ) (exteriorDegree : ℕ)
    (survives : CutoffLE cutoff (some (-(exteriorDegree : ℤ))))
    (subset : KoszulBasis rank exteriorDegree) (leftDegree rightDegree : ℤ)
    (totalIndex : leftDegree + rightDegree = totalDegree)
    (different : rightDegree ≠ -(exteriorDegree : ℤ)) :
    HomologicalComplex.ιTensorObj coefficient (standardKoszulStage family cutoff power)
        leftDegree rightDegree totalDegree totalIndex ≫
        tensorKoszulCoordinate family cutoff power coefficient totalDegree exteriorDegree survives
          subset = 0 := by
  dsimp only [tensorKoszulCoordinate]
  rw [HomologicalComplex.ι_mapBifunctorDesc, dite_eq_right different]

private theorem tensorKoszulBasis_transport
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power : ℕ)
    (coefficient : CochainComplex (ModuleCat.{u} A) ℤ) (totalDegree : ℤ)
    (source : Finset (Fin rank)) (exteriorDegree : ℕ) (cardinality : source.card = exteriorDegree)
    (survives : CutoffLE cutoff (some (-(exteriorDegree : ℤ))))
    (element : coefficient.X (totalDegree + source.card)) :
    HomologicalComplex.ιTensorObj coefficient (standardKoszulStage family cutoff power)
        (totalDegree + source.card) (-(source.card : ℤ)) totalDegree (by omega)
        (element ⊗ₜ[A] koszulBasisVector family cutoff power source) =
      HomologicalComplex.ιTensorObj coefficient (standardKoszulStage family cutoff power)
        (totalDegree + exteriorDegree) (-(exteriorDegree : ℤ)) totalDegree (by omega)
        ((eqToHom (congrArg coefficient.X (by rw [cardinality] :
          totalDegree + source.card = totalDegree + exteriorDegree))) element ⊗ₜ[A]
            koszulStageBasis family cutoff power exteriorDegree survives ⟨source, cardinality⟩) :=
              by
  subst exteriorDegree
  rw [koszulStageBasis_apply_card]
  rfl

private theorem tensorKoszulCoordinate_basis_ne
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power : ℕ)
    (coefficient : CochainComplex (ModuleCat.{u} A) ℤ) (totalDegree : ℤ) (exteriorDegree : ℕ)
    (survives : CutoffLE cutoff (some (-(exteriorDegree : ℤ))))
    (target : KoszulBasis rank exteriorDegree) (source : Finset (Fin rank))
    (different : source ≠ target.1) (element : coefficient.X (totalDegree + source.card)) :
    tensorKoszulCoordinate family cutoff power coefficient totalDegree exteriorDegree survives
      target
        (HomologicalComplex.ιTensorObj coefficient (standardKoszulStage family cutoff power)
          (totalDegree + source.card) (-(source.card : ℤ)) totalDegree (by omega)
          (element ⊗ₜ[A] koszulBasisVector family cutoff power source)) = 0 := by
  classical
  by_cases cardinality : source.card = exteriorDegree
  · rw [tensorKoszulBasis_transport family cutoff power coefficient totalDegree source
    exteriorDegree
      cardinality survives, tensorKoszulCoordinate_ι_tmul]
    have subtypeDifferent : (⟨source, cardinality⟩ : KoszulBasis rank exteriorDegree) ≠ target := by
      intro equality
      exact different (congrArg Subtype.val equality)
    rw [(koszulStageBasis family cutoff power exteriorDegree survives).repr_self_apply]
    simp only [ite_eq_right subtypeDifferent, zero_smul]
  · show (HomologicalComplex.ιTensorObj coefficient (standardKoszulStage family cutoff power)
      (totalDegree + source.card) (-(source.card : ℤ)) totalDegree (by omega) ≫
        tensorKoszulCoordinate family cutoff power coefficient totalDegree exteriorDegree survives
          target)
        (element ⊗ₜ[A] koszulBasisVector family cutoff power source) = 0
    rw [tensorKoszulCoordinate_wrong_degree family cutoff power coefficient totalDegree
      exteriorDegree survives
      target _ _ _ (by omega)]
    rfl

private theorem tensorKoszulCoordinate_basis_self
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power : ℕ)
    (coefficient : CochainComplex (ModuleCat.{u} A) ℤ) (totalDegree : ℤ)
    (subset : Finset (Fin rank)) (survives : CutoffLE cutoff (some (-(subset.card : ℤ))))
    (element : coefficient.X (totalDegree + subset.card)) :
    tensorKoszulCoordinate family cutoff power coefficient totalDegree subset.card survives ⟨subset,
      rfl⟩
        (HomologicalComplex.ιTensorObj coefficient (standardKoszulStage family cutoff power)
          (totalDegree + subset.card) (-(subset.card : ℤ)) totalDegree (by omega)
          (element ⊗ₜ[A] koszulBasisVector family cutoff power subset)) = element := by
  rw [← koszulStageBasis_apply_card family cutoff power subset survives,
    tensorKoszulCoordinate_ι_tmul,
    (koszulStageBasis family cutoff power subset.card survives).repr_self_apply]
  simp only [ite_true, one_smul]

private def tensorKoszulSynthesis
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power : ℕ)
    (coefficient : CochainComplex (ModuleCat.{u} A) ℤ) (totalDegree : ℤ) :
    ModuleCat.of A (∀ subset : Finset (Fin rank), coefficient.X (totalDegree + subset.card)) ⟶
      (HomologicalComplex.tensorObj coefficient (standardKoszulStage family cutoff power)).X
        totalDegree :=
  ∑ subset : Finset (Fin rank), ModuleCat.ofHom (LinearMap.proj subset) ≫
    ModuleCat.ofHom ((TensorProduct.mk A _ _).flip (koszulBasisVector family cutoff power subset)) ≫
      HomologicalComplex.ιTensorObj coefficient (standardKoszulStage family cutoff power)
        (totalDegree + subset.card) (-(subset.card : ℤ)) totalDegree (by omega)

private theorem tensorKoszulSynthesis_apply
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power : ℕ)
    (coefficient : CochainComplex (ModuleCat.{u} A) ℤ) (totalDegree : ℤ)
    (elements : ∀ subset : Finset (Fin rank), coefficient.X (totalDegree + subset.card)) :
    tensorKoszulSynthesis family cutoff power coefficient totalDegree elements =
      ∑ subset : Finset (Fin rank),
        HomologicalComplex.ιTensorObj coefficient (standardKoszulStage family cutoff power)
          (totalDegree + subset.card) (-(subset.card : ℤ)) totalDegree (by omega)
          (elements subset ⊗ₜ[A] koszulBasisVector family cutoff power subset) := by
  simp only [tensorKoszulSynthesis, ModuleCat.hom_sum]
  rw [LinearMap.sum_apply]
  rfl

private theorem tensorKoszulSynthesis_coordinate
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power : ℕ)
    (coefficient : CochainComplex (ModuleCat.{u} A) ℤ) (totalDegree : ℤ)
    (subset : Finset (Fin rank)) (survives : CutoffLE cutoff (some (-(subset.card : ℤ)))) :
    tensorKoszulSynthesis family cutoff power coefficient totalDegree ≫
        tensorKoszulCoordinate family cutoff power coefficient totalDegree subset.card survives
          ⟨subset, rfl⟩ =
      ModuleCat.ofHom (LinearMap.proj subset) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro elements
  show (tensorKoszulCoordinate family cutoff power coefficient totalDegree subset.card survives
    ⟨subset, rfl⟩)
    (tensorKoszulSynthesis family cutoff power coefficient totalDegree elements) = elements subset
  rw [tensorKoszulSynthesis_apply]
  show (tensorKoszulCoordinate family cutoff power coefficient totalDegree subset.card survives
    ⟨subset, rfl⟩).hom
    (∑ source, _) = _
  rw [map_sum, Finset.sum_eq_single subset]
  · exact
      tensorKoszulCoordinate_basis_self family cutoff power coefficient totalDegree subset
        survives _
  · intro source _ different
    exact tensorKoszulCoordinate_basis_ne family cutoff power coefficient totalDegree subset.card
      survives
      ⟨subset, rfl⟩ source different _
  · simp

private theorem tensorKoszulSynthesis_single
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power : ℕ)
    (coefficient : CochainComplex (ModuleCat.{u} A) ℤ) (totalDegree : ℤ)
    (subset : Finset (Fin rank)) (element : coefficient.X (totalDegree + subset.card)) :
    tensorKoszulSynthesis family cutoff power coefficient totalDegree (Pi.single subset element) =
      HomologicalComplex.ιTensorObj coefficient (standardKoszulStage family cutoff power)
        (totalDegree + subset.card) (-(subset.card : ℤ)) totalDegree (by omega)
        (element ⊗ₜ[A] koszulBasisVector family cutoff power subset) := by
  classical
  rw [tensorKoszulSynthesis_apply, Finset.sum_eq_single subset]
  · simp only [Pi.single_eq_same]
  · intro source _ different
    simp only [Pi.single_eq_of_ne different, TensorProduct.zero_tmul, map_zero]
  · simp

private theorem koszulStage_isZero_of_not_supported
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power : ℕ) (degree : ℤ)
    (unsupported : ¬ (degree ≤ 0 ∧ CutoffLE cutoff (some degree))) :
    IsZero ((standardKoszulStage family cutoff power).X degree) := by
  cases cutoff with
  | none =>
    apply HomologicalComplex.isZero_extend_X
    intro index
    change -(index : ℤ) ≠ degree
    have : ¬ degree ≤ 0 := fun nonpositive => unsupported ⟨nonpositive, trivial⟩
    omega
  | some cutoff =>
    by_cases survives : cutoff ≤ degree
    · have : IsZero ((standardKoszulStage family none power).X degree) := by
        apply HomologicalComplex.isZero_extend_X
        intro index
        change -(index : ℤ) ≠ degree
        have : ¬ degree ≤ 0 := fun nonpositive => unsupported ⟨nonpositive, survives⟩
        omega
      exact this.of_iso (koszulStageTruncXIso family cutoff power degree survives)
    · apply HomologicalComplex.isZero_stupidTrunc_X
      intro index
      change cutoff + (index : ℤ) ≠ degree
      omega

private theorem tensorKoszulSynthesis_epi
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power : ℕ)
    (coefficient : CochainComplex (ModuleCat.{u} A) ℤ) (totalDegree : ℤ) :
    Epi (tensorKoszulSynthesis family cutoff power coefficient totalDegree) := by
  constructor
  intro target first second equality
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro leftDegree rightDegree totalIndex
  change leftDegree + rightDegree = totalDegree at totalIndex
  by_cases supported : rightDegree ≤ 0 ∧ CutoffLE cutoff (some rightDegree)
  · obtain ⟨exteriorDegree, rightEquality⟩ : ∃ exteriorDegree : ℕ,
        rightDegree = -(exteriorDegree : ℤ) :=
      ⟨rightDegree.natAbs, by rw [Int.natCast_natAbs, abs_of_nonpos supported.1, neg_neg]⟩
    subst rightDegree
    have leftEquality : leftDegree = totalDegree + exteriorDegree := by omega
    subst leftDegree
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro element
    apply (koszulStageBasis family cutoff power exteriorDegree supported.2).ext
    intro subset
    rcases subset with ⟨subset, cardinality⟩
    subst exteriorDegree
    show first (HomologicalComplex.ιTensorObj coefficient (standardKoszulStage family cutoff
      power)
      (totalDegree + subset.card) (-(subset.card : ℤ)) totalDegree (by omega)
      (element ⊗ₜ[A] koszulStageBasis family cutoff power subset.card supported.2 ⟨subset, rfl⟩)) =
        second (HomologicalComplex.ιTensorObj coefficient (standardKoszulStage family cutoff power)
          (totalDegree + subset.card) (-(subset.card : ℤ)) totalDegree (by omega)
          (element ⊗ₜ[A] koszulStageBasis family cutoff power subset.card supported.2 ⟨subset,
            rfl⟩))
    rw [koszulStageBasis_apply_card]
    have generators := ConcreteCategory.congr_hom equality (Pi.single subset element)
    change first (tensorKoszulSynthesis family cutoff power coefficient totalDegree (Pi.single
      subset element)) =
      second (tensorKoszulSynthesis family cutoff power coefficient totalDegree (Pi.single subset
        element)) at generators
    rwa [tensorKoszulSynthesis_single] at generators
  · exact (((curriedTensor (ModuleCat.{u} A)).obj (coefficient.X leftDegree)).map_isZero
      (koszulStage_isZero_of_not_supported family cutoff power rightDegree supported)).eq_of_src _ _

private theorem comparisonTerm_eq_synthesis_apply
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power : ℕ)
    (coefficient : CochainComplex (ModuleCat.{v} A) ℤ) (degree : ℤ)
    (element : filteredTerm (r := rank) cutoff coefficient degree) :
    comparisonTerm family cutoff power coefficient degree (ULift.up element) =
      tensorKoszulSynthesis (fun index => (ULift.up (family index) : ULift.{v} A)) cutoff power
        ((complexUniverseLift (A := A)).obj coefficient) degree
        (fun subset => ULift.up ((termProjection cutoff coefficient degree).hom element subset)) :=
          by
  erw [comparisonTerm_apply_up, tensorKoszulSynthesis_apply]

private theorem comparisonTerm_mono
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power : ℕ)
    (coefficient : CochainComplex (ModuleCat.{v} A) ℤ) (degree : ℤ) :
    Mono (comparisonTerm family cutoff power coefficient degree) := by
  apply (ModuleCat.mono_iff_injective _).2
  rintro ⟨first⟩ ⟨second⟩ equality
  apply ULift.ext
  have projections : (termProjection cutoff coefficient degree).hom first =
      (termProjection cutoff coefficient degree).hom second := by
    funext subset
    by_cases survives : CutoffLE cutoff (some (-(subset.card : ℤ)))
    · rw [comparisonTerm_eq_synthesis_apply, comparisonTerm_eq_synthesis_apply] at equality
      have coordinates := congrArg
        (tensorKoszulCoordinate (fun index => (ULift.up (family index) : ULift.{v} A)) cutoff power
          ((complexUniverseLift (A := A)).obj coefficient) degree subset.card survives ⟨subset,
            rfl⟩) equality
      have recover := tensorKoszulSynthesis_coordinate
        (fun index => (ULift.up (family index) : ULift.{v} A)) cutoff power
        ((complexUniverseLift (A := A)).obj coefficient) degree subset survives
      change ((tensorKoszulSynthesis _ _ _ _ _ ≫ tensorKoszulCoordinate _ _ _ _ _ _ _ _) _ =
        (tensorKoszulSynthesis _ _ _ _ _ ≫ tensorKoszulCoordinate _ _ _ _ _ _ _ _) _) at coordinates
      rw [recover] at coordinates
      exact congrArg ULift.down coordinates
    · rw [termProjection_apply_eq_zero cutoff coefficient degree subset survives first,
        termProjection_apply_eq_zero cutoff coefficient degree subset survives second]
  have retract := congrArg (termSection cutoff coefficient degree).hom projections
  change ((termProjection cutoff coefficient degree ≫ termSection cutoff coefficient degree).hom
    first) =
    ((termProjection cutoff coefficient degree ≫ termSection cutoff coefficient degree).hom second)
      at retract
  rw [term_projection_section] at retract
  exact retract

private theorem comparisonTerm_epi
    {rank : ℕ} (family : Fin rank → A) (cutoff : Option ℤ) (power : ℕ)
    (coefficient : CochainComplex (ModuleCat.{v} A) ℤ) (degree : ℤ) :
    Epi (comparisonTerm family cutoff power coefficient degree) := by
  let lifted := (complexUniverseLift (A := A)).obj coefficient
  let liftedFamily := fun index => (ULift.up (family index) : ULift.{v} A)
  have synthesisEpi := tensorKoszulSynthesis_epi liftedFamily cutoff power lifted degree
  apply (ModuleCat.epi_iff_surjective _).2
  intro target
  obtain ⟨elements, representation⟩ := (ModuleCat.epi_iff_surjective _).1 synthesisEpi target
  let originalElements := fun subset : Finset (Fin rank) => (elements subset).down
  refine ⟨ULift.up ((termSection cutoff coefficient degree).hom originalElements), ?_⟩
  rw [comparisonTerm_eq_synthesis_apply, ← representation]
  erw [tensorKoszulSynthesis_apply, tensorKoszulSynthesis_apply]
  apply Finset.sum_congr rfl
  intro subset _
  by_cases survives : CutoffLE cutoff (some (-(subset.card : ℤ)))
  · have projected := termSection_projection_apply cutoff coefficient degree originalElements subset
    rw [ite_eq_left survives] at projected
    have liftedProjection := congrArg (fun element => (ULift.up element : lifted.X (degree +
      subset.card))) projected
    change ULift.up ((termProjection cutoff coefficient degree).hom
      ((termSection cutoff coefficient degree).hom originalElements) subset) = elements subset
      at liftedProjection
    rw [liftedProjection]
  · have zeroTerm := koszulStage_isZero_of_not_supported liftedFamily cutoff power (-(subset.card :
    ℤ))
      (fun supported => survives supported.2)
    have basisZero : koszulBasisVector liftedFamily cutoff power subset = 0 :=
      (ModuleCat.subsingleton_of_isZero zeroTerm).elim _ _
    show HomologicalComplex.ιTensorObj lifted (standardKoszulStage liftedFamily cutoff power)
      (degree + subset.card) (-(subset.card : ℤ)) degree (by omega)
      (_ ⊗ₜ[ULift.{v} A] koszulBasisVector liftedFamily cutoff power subset) =
      HomologicalComplex.ιTensorObj lifted (standardKoszulStage liftedFamily cutoff power)
        (degree + subset.card) (-(subset.card : ℤ)) degree (by omega)
        (_ ⊗ₜ[ULift.{v} A] koszulBasisVector liftedFamily cutoff power subset)
    rw [basisZero]
    simp only [TensorProduct.tmul_zero, map_zero]
    erw [TensorProduct.tmul_zero, map_zero]

private theorem comparison_isIso_complete
    {rank : ℕ} {family : Fin rank → A} (laws : FormulaLaws.{u, v} family)
    (cutoff : Option ℤ) (power : ℕ) (coefficient : CochainComplex (ModuleCat.{v} A) ℤ) :
    IsIso (laws.comparisonMap cutoff power coefficient) := by
  have components (degree : ℤ) : IsIso ((laws.comparisonMap cutoff power coefficient).f degree) :=
    by
    show IsIso (comparisonTerm family cutoff power coefficient degree)
    have := comparisonTerm_mono family cutoff power coefficient degree
    have := comparisonTerm_epi family cutoff power coefficient degree
    exact isIso_of_mono_of_epi _
  exact HomologicalComplex.Hom.isIso_of_components _


end KoszulCoefficientTower


open KoszulCoefficientTower in
/-- The finite exterior-basis formulas satisfy all the laws required to construct the
coefficient Koszul tower and its filtered comparison maps. -/
public theorem KoszulCoefficientTower.canonicalFormulaLaws
    {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A) :
    FormulaLaws.{u, v} f ∧ ∀ h : FormulaLaws.{u, v} f, Verification f h := by
  refine ⟨formulaLaws_complete f, ?_⟩
  intro h
  refine {
    comparison_isIso := comparison_isIso_complete h
    comparison_naturality := comparison_naturality h
    comparison_transition := comparison_transition h
    comparison_augmentation := comparison_augmentation h
    comparison_inclusion := comparison_inclusion h
    inclusion_comp := inclusion_comp h
    augmentation_factor := augmentation_factor h
    augmentation_zero_isIso := augmentation_zero_isIso h
    filtration_exhaustive := filtration_exhaustive h _ (le_refl _)
    filtration_bounded := stage_isZero h 1 (by omega)
    inclusion_mono := fun p n K ↦ inclusion_mono h (some p) (some (p + 1))
      (by dsimp [CutoffLE]; omega) n K
    graded_isIso := graded_isIso h
    graded_naturality := graded_naturality h
    graded_transition := graded_transition h
    map_quasiIso := stageMap_quasiIso h }


end


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u v

namespace KoszulCoefficientTower

variable {A : Type u} [CommRing A]

namespace FormulaLaws

variable {r : ℕ} {f : Fin r → A} (h : FormulaLaws.{u, v} f)

end FormulaLaws

/-- The coefficient Koszul tower, with all data supplied by the explicit finite-basis formulas. -/
public def coefficientKoszulTower {r : ℕ} (f : Fin r → A) :
    CochainComplex (ModuleCat.{v} A) ℤ ⥤
      (ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} A) ℤ) :=
  (canonicalFormulaLaws f).1.tower none

/-- The finite stupid filtration in the Koszul direction. -/
public def coefficientKoszulFiltration {r : ℕ} (f : Fin r → A) (p : ℤ) :
    CochainComplex (ModuleCat.{v} A) ℤ ⥤
      (ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} A) ℤ) :=
  (canonicalFormulaLaws f).1.tower (some p)

/-- The natural augmentation from the constant coefficient tower. -/
public def coefficientKoszulUnit {r : ℕ} (f : Fin r → A) :
    Functor.const ℕᵒᵖ ⟶ coefficientKoszulTower f where
  app K :=
    { app n := (((canonicalFormulaLaws f).1.augmentation none).app n).app K
      naturality _ _ a := HomologicalComplex.hom_ext _ _ fun t ↦
        ((canonicalFormulaLaws f).1.unit_transition none _ _ (leOfHom a.unop) K t).symm }
  naturality _ _ g := NatTrans.ext <| funext fun _ ↦
    HomologicalComplex.hom_ext _ _ ((canonicalFormulaLaws f).1.unit_naturality none g)

/-- The canonical augmentation at one positive-power stage. -/
public def coefficientKoszulAugmentation {r : ℕ} (f : Fin r → A) (n : ℕ) :
    𝟭 (CochainComplex (ModuleCat.{v} A) ℤ) ⟶
      coefficientKoszulTower f ⋙
        (evaluation ℕᵒᵖ (CochainComplex (ModuleCat.{v} A) ℤ)).obj ⟨n⟩ :=
  ((canonicalFormulaLaws f).1.augmentation none).app ⟨n⟩

/-- Inclusion of a filtered tower in the full tower. -/
public def coefficientKoszulFiltrationι {r : ℕ} (f : Fin r → A) (p : ℤ) :
    coefficientKoszulFiltration f p ⟶ coefficientKoszulTower f :=
  (canonicalFormulaLaws f).1.inclusion none (some p) trivial

/-- Inclusion of successive stupid truncations. -/
public def coefficientKoszulFiltrationStep {r : ℕ} (f : Fin r → A) (p : ℤ) :
    coefficientKoszulFiltration f (p + 1) ⟶ coefficientKoszulFiltration f p :=
  (canonicalFormulaLaws f).1.inclusion (some p) (some (p + 1)) (by dsimp [CutoffLE]; omega)

/-- The degree-zero part of the filtration is canonically the coefficient complex. -/
public def coefficientKoszulFiltrationZeroIso {r : ℕ} (f : Fin r → A) (n : ℕ) :
    𝟭 (CochainComplex (ModuleCat.{v} A) ℤ) ≅
      coefficientKoszulFiltration f 0 ⋙
        (evaluation ℕᵒᵖ (CochainComplex (ModuleCat.{v} A) ℤ)).obj ⟨n⟩ := by
  let h := (canonicalFormulaLaws.{u, v} f).1
  let e := (h.augmentation (some 0)).app ⟨n⟩
  exact NatIso.ofComponents (fun K ↦
    @asIso _ _ _ _ (e.app K)
      (((canonicalFormulaLaws f).2 (canonicalFormulaLaws f).1).augmentation_zero_isIso n K))
    (fun g ↦ e.naturality g)

/-- The canonical wedge comparison for any stupid cutoff, naturally in the coefficient complex. -/
public def coefficientKoszulComparison {r : ℕ} (f : Fin r → A) (p : Option ℤ) (n : ℕ) :
    (canonicalFormulaLaws f).1.tower p ⋙
        (evaluation ℕᵒᵖ (CochainComplex (ModuleCat.{v} A) ℤ)).obj ⟨n⟩ ⋙
        complexUniverseLift (A := A) ≅ standardCoefficientKoszulStage f p n :=
  NatIso.ofComponents
    (fun K ↦ @asIso _ _ _ _ ((canonicalFormulaLaws f).1.comparisonMap p n K)
      (((canonicalFormulaLaws f).2 (canonicalFormulaLaws f).1).comparison_isIso p n K))
    (fun g ↦ ((canonicalFormulaLaws f).2 (canonicalFormulaLaws f).1).comparison_naturality p n g)

/-- The specified quotient isomorphism for consecutive stupid truncations. -/
public def coefficientKoszulGradedPieceIso {r : ℕ} (f : Fin r → A) (p : ℤ) (hp : p ≤ 0)
    (n : ℕ) (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    cokernel (((coefficientKoszulFiltrationStep f p).app K).app ⟨n⟩) ≅
      (coefficientKoszulGradedPiece (A := A) r p).obj K :=
  @asIso _ _ _ _ ((canonicalFormulaLaws f).1.gradedMap p hp n K)
    (((canonicalFormulaLaws f).2 (canonicalFormulaLaws f).1).graded_isIso p hp n K)

/-- Each finite-free Koszul stage preserves quasi-isomorphisms in the original module universe. -/
public instance coefficientKoszulTower_map_quasiIso {r : ℕ} (f : Fin r → A) (n : ℕ)
    {K L : CochainComplex (ModuleCat.{v} A) ℤ} (g : K ⟶ L) [QuasiIso g] :
    QuasiIso (((coefficientKoszulTower f).map g).app ⟨n⟩) :=
  ((canonicalFormulaLaws f).2 (canonicalFormulaLaws f).1).map_quasiIso none n g

/-- The full tower has exactly the finite exterior-basis coefficient terms. -/
@[simp] public theorem coefficientKoszulTower_X {r : ℕ} (f : Fin r → A)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (n : ℕ) (t : ℤ) :
    (((coefficientKoszulTower f).obj K).obj ⟨n⟩).X t =
      coefficientKoszulTerm (r := r) K t := rfl

/-- Component formula for the differential of the full tower. -/
public theorem coefficientKoszulTower_d {r : ℕ} (f : Fin r → A)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (n : ℕ) (t : ℤ) :
    (((coefficientKoszulTower f).obj K).obj ⟨n⟩).d t (t + 1) =
      coefficientKoszulDifferential f n K t := by
  show filteredDifferential f none n K t (t + 1) = _
  simp only [filteredDifferential, dite_eq_ite, eqToHom_refl, Category.comp_id]
  rfl

/-- Component formula for a coefficient chain map. -/
@[simp] public theorem coefficientKoszulTower_map_f {r : ℕ} (f : Fin r → A)
    {K L : CochainComplex (ModuleCat.{v} A) ℤ} (g : K ⟶ L) (n : ℕ) (t : ℤ) :
    (((coefficientKoszulTower f).map g).app ⟨n⟩).f t = coefficientMapTerm g t := rfl

/-- Component formula for every power transition, with the inverse-system direction. -/
public theorem coefficientKoszulTower_transition_f {r : ℕ} (f : Fin r → A)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (m n : ℕ) (hmn : n ≤ m) (t : ℤ) :
    (((coefficientKoszulTower f).obj K).map (homOfLE hmn).op).f t =
      coefficientKoszulTransitionTerm f m n K t := rfl

/-- The augmentation is the empty-subset inclusion. -/
@[simp] public theorem coefficientKoszulAugmentation_f {r : ℕ} (f : Fin r → A)
    (n : ℕ) (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    ((coefficientKoszulAugmentation f n).app K).f t =
      coefficientKoszulUnitTerm (r := r) K t := rfl

/-- The augmentations commute with all power transitions. -/
@[reassoc] public theorem coefficientKoszulAugmentation_transition {r : ℕ} (f : Fin r → A)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (m n : ℕ) (hmn : n ≤ m) :
    (coefficientKoszulAugmentation f m).app K ≫
        ((coefficientKoszulTower f).obj K).map (homOfLE hmn).op =
      (coefficientKoszulAugmentation f n).app K :=
  HomologicalComplex.hom_ext _ _ ((canonicalFormulaLaws f).1.unit_transition none m n hmn K)

/-- Successive inclusions agree with inclusion in the full tower. -/
@[reassoc] public theorem coefficientKoszulFiltrationStep_ι {r : ℕ} (f : Fin r → A) (p : ℤ) :
    coefficientKoszulFiltrationStep f p ≫ coefficientKoszulFiltrationι f p =
      coefficientKoszulFiltrationι f (p + 1) :=
  ((canonicalFormulaLaws f).2 (canonicalFormulaLaws f).1).inclusion_comp
    none (some p) (some (p + 1)) trivial (by dsimp [CutoffLE]; omega) trivial

/-- The degree-zero filtration isomorphism factors the augmentation. -/
@[reassoc] public theorem coefficientKoszulFiltrationZeroIso_ι {r : ℕ} (f : Fin r → A)
    (n : ℕ) (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    (coefficientKoszulFiltrationZeroIso f n).hom.app K ≫
        ((coefficientKoszulFiltrationι f 0).app K).app ⟨n⟩ =
      (coefficientKoszulAugmentation f n).app K :=
  ((canonicalFormulaLaws f).2 (canonicalFormulaLaws f).1).augmentation_factor n K

/-- The filtration starts at exterior degree `-r`. -/
public instance coefficientKoszulFiltration_exhaustive {r : ℕ} (f : Fin r → A)
    (n : ℕ) (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    IsIso (((coefficientKoszulFiltrationι f (-(r : ℤ))).app K).app ⟨n⟩) :=
  ((canonicalFormulaLaws f).2 (canonicalFormulaLaws f).1).filtration_exhaustive n K

/-- There are no positive Koszul degrees. -/
public theorem coefficientKoszulFiltration_bounded {r : ℕ} (f : Fin r → A)
    (n : ℕ) (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    IsZero (((coefficientKoszulFiltration f 1).obj K).obj ⟨n⟩) :=
  ((canonicalFormulaLaws f).2 (canonicalFormulaLaws f).1).filtration_bounded n K

/-- Consecutive filtration inclusions are monomorphisms. -/
public instance coefficientKoszulFiltrationStep_mono {r : ℕ} (f : Fin r → A) (p : ℤ)
    (n : ℕ) (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    Mono (((coefficientKoszulFiltrationStep f p).app K).app ⟨n⟩) :=
  ((canonicalFormulaLaws f).2 (canonicalFormulaLaws f).1).inclusion_mono p n K

/-- Every filtered stage also preserves quasi-isomorphisms. -/
public instance coefficientKoszulFiltration_map_quasiIso {r : ℕ} (f : Fin r → A) (p : ℤ)
    (n : ℕ) {K L : CochainComplex (ModuleCat.{v} A) ℤ} (g : K ⟶ L) [QuasiIso g] :
    QuasiIso (((coefficientKoszulFiltration f p).map g).app ⟨n⟩) :=
  ((canonicalFormulaLaws f).2 (canonicalFormulaLaws f).1).map_quasiIso (some p) n g

/-- The comparison is the specified sum of tensors with ordered basis wedges. -/
@[simp] public theorem coefficientKoszulComparison_hom_f {r : ℕ} (f : Fin r → A)
    (p : Option ℤ) (n : ℕ) (K : CochainComplex (ModuleCat.{v} A) ℤ) (t : ℤ) :
    ((coefficientKoszulComparison f p n).hom.app K).f t = comparisonTerm f p n K t := rfl

/-- The wedge comparison preserves the canonical augmentation. -/
@[reassoc] public theorem coefficientKoszulComparison_augmentation {r : ℕ} (f : Fin r → A)
    (n : ℕ) (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    (complexUniverseLift (A := A)).map ((coefficientKoszulAugmentation f n).app K) ≫
        (coefficientKoszulComparison f none n).hom.app K =
      (MonoidalCategory.rightUnitor ((complexUniverseLift (A := A)).obj K)).inv ≫
        (((complexUniverseLift (A := A)).obj K) ◁
          AdicKoszul.koszulPowerUnit (fun a ↦ (ULift.up (f a) : ULift.{v} A)) n) :=
  ((canonicalFormulaLaws f).2 (canonicalFormulaLaws f).1).comparison_augmentation n K

/-- The comparison preserves every transition, including its direction and its exponent. -/
@[reassoc] public theorem coefficientKoszulComparison_transition {r : ℕ} (f : Fin r → A)
    (m n : ℕ) (hmn : n ≤ m) (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    (complexUniverseLift (A := A)).map
          (((coefficientKoszulTower f).obj K).map (homOfLE hmn).op) ≫
        (coefficientKoszulComparison f none n).hom.app K =
      (coefficientKoszulComparison f none m).hom.app K ≫
        (𝟙 ((complexUniverseLift (A := A)).obj K) ⊗ₘ
          standardKoszulTransition (fun a ↦ (ULift.up (f a) : ULift.{v} A)) none m n hmn) :=
  ((canonicalFormulaLaws f).2 (canonicalFormulaLaws f).1).comparison_transition none m n hmn K

set_option backward.isDefEq.respectTransparency false in
/-- The transition on the graded quotient is the diagonal product of the scalars in its subset. -/
@[reassoc] public theorem coefficientKoszulGradedPieceIso_transition {r : ℕ} (f : Fin r → A)
    (p : ℤ) (hp : p ≤ 0) (n : ℕ) (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    cokernel.map
          (((coefficientKoszulFiltrationStep f p).app K).app ⟨n + 1⟩)
          (((coefficientKoszulFiltrationStep f p).app K).app ⟨n⟩)
          (((coefficientKoszulFiltration f (p + 1)).obj K).map
            (show (⟨n + 1⟩ : ℕᵒᵖ) ⟶ ⟨n⟩ from (homOfLE (Nat.le_succ n)).op))
          (((coefficientKoszulFiltration f p).obj K).map
            (show (⟨n + 1⟩ : ℕᵒᵖ) ⟶ ⟨n⟩ from (homOfLE (Nat.le_succ n)).op))
          (((coefficientKoszulFiltrationStep f p).app K).naturality
            (show (⟨n + 1⟩ : ℕᵒᵖ) ⟶ ⟨n⟩ from (homOfLE (Nat.le_succ n)).op)).symm ≫
        (coefficientKoszulGradedPieceIso f p hp n K).hom =
      (coefficientKoszulGradedPieceIso f p hp (n + 1) K).hom ≫
        coefficientKoszulGradedTransition f p K := by
  dsimp only [coefficientKoszulGradedPieceIso, asIso_hom, FormulaLaws.gradedMap]
  apply cokernel.map_desc
  exact (((canonicalFormulaLaws f).2 (canonicalFormulaLaws f).1).graded_transition p hp n K).symm

end KoszulCoefficientTower

end

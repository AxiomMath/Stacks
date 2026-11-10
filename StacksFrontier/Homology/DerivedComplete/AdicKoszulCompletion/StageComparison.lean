module

public import StacksFrontier.Homology.DerivedComplete.AdicKoszulCompletion.Construction
import all Mathlib.CategoryTheory.Discrete.Basic
import all Mathlib.CategoryTheory.Functor.Basic
import all Mathlib.CategoryTheory.Functor.OfSequence
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Functorial Koszul power completion: naturality of the stage comparisons

The K-flat-resolution comparison `KoszulCompletion.tensorComparisonIso` is natural in both
factors. Consequently the coefficient-to-tensor stage comparisons are natural, and they are
compatible with the augmentations and with the transition maps of the towers.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u v

namespace KoszulTensorNaturalityAudit

attribute [local instance] KoszulCompletion.derivedCountableProducts

attribute [local instance] HasDerivedCategory.standard


private theorem kFlat_common_cover
    {ring : Type u} [CommRing ring]
    {source cover target : CochainComplex (ModuleCat.{u} ring) ℤ}
    (morphism : source ⟶ target) (resolution : cover ⟶ target)
    [Epi resolution] [QuasiIso resolution] :
    ∃ (refinement : CochainComplex (ModuleCat.{u} ring) ℤ)
      (left : refinement ⟶ source) (right : refinement ⟶ cover),
      refinement.KFlat ∧ QuasiIso left ∧ left ≫ morphism = right ≫ resolution := by
  have := Stacks.KernelQuasiIso.pullback_fst_quasiIso_of_epi morphism resolution
  obtain ⟨refinement, refinementMap, flat, _, quasiIso, _⟩ :=
    CochainComplex.KFlat.exists_kFlat_resolution (pullback morphism resolution)
  let : QuasiIso refinementMap := quasiIso
  refine ⟨refinement, refinementMap ≫ pullback.fst morphism resolution,
    refinementMap ≫ pullback.snd morphism resolution, flat, inferInstance, ?_⟩
  simp only [Category.assoc, pullback.condition]

private abbrev ordinaryTensorFunctor
    {ring : Type u} [CommRing ring]
    (factor : CochainComplex (ModuleCat.{u} ring) ℤ) :=
  (curriedTensor (CochainComplex (ModuleCat.{u} ring) ℤ)).flip.obj factor ⋙ DerivedCategory.Q

private abbrev derivedTensorFunctor
    {ring : Type u} [CommRing ring] (tensor : CochainComplex.DerivedTensor.DerivedTensorProduct
      ring)
    (factor : CochainComplex (ModuleCat.{u} ring) ℤ) :=
  DerivedCategory.Q ⋙ tensor.tensor.flip.obj (DerivedCategory.Q.obj factor)

private theorem tensor_quasiIso
    {ring : Type u} [CommRing ring]
    (factor : CochainComplex (ModuleCat.{u} ring) ℤ) (factorFlat : factor.KFlat)
    {source target : CochainComplex (ModuleCat.{u} ring) ℤ}
    (morphism : source ⟶ target) [QuasiIso morphism] : QuasiIso (morphism ⊗ₘ 𝟙 factor) := by
  have transported := CochainComplex.KFlat.kFlat_tright_preserves_quasiIso factor factorFlat
    ((HomotopyCategory.quotient _ _).map morphism)
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff morphism).2
      (show QuasiIso morphism from inferInstance))
  change HomotopyCategory.quasiIso _ _ ((HomotopyCategory.quotient _ _).map
    ((TrightCochain factor).map morphism)) at transported
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).1 transported

private theorem ordinaryTensorFunctor_map_isIso
    {ring : Type u} [CommRing ring]
    (factor : CochainComplex (ModuleCat.{u} ring) ℤ) (factorFlat : factor.KFlat)
    {source target : CochainComplex (ModuleCat.{u} ring) ℤ}
    (morphism : source ⟶ target) [QuasiIso morphism] :
    IsIso ((ordinaryTensorFunctor factor).map morphism) := by
  have := tensor_quasiIso factor factorFlat morphism
  exact inferInstanceAs (IsIso (DerivedCategory.Q.map (morphism ⊗ₘ 𝟙 factor)))

private theorem comparison_inverse_naturality
    {ring : Type u} [CommRing ring] (tensor : CochainComplex.DerivedTensor.DerivedTensorProduct
      ring)
    {source target : CochainComplex (ModuleCat.{u} ring) ℤ}
    (factor : CochainComplex (ModuleCat.{u} ring) ℤ) (morphism : source ⟶ target)
    (sourceFlat : source.KFlat) (targetFlat : target.KFlat) (factorFlat : factor.KFlat) :
    (ordinaryTensorFunctor factor).map morphism ≫
        (tensor.comparison target factor targetFlat factorFlat).inv =
      (tensor.comparison source factor sourceFlat factorFlat).inv ≫
        (derivedTensorFunctor tensor factor).map morphism := by
  have naturality := tensor.comparison_naturality morphism (𝟙 factor)
    sourceFlat targetFlat factorFlat factorFlat
  have identity := (DerivedCategory.Q (C := ModuleCat.{u} ring)).map_id factor
  rw [identity, (tensor.tensor.obj (DerivedCategory.Q.obj target)).map_id,
    Category.id_comp] at naturality
  apply (cancel_mono (tensor.comparison target factor targetFlat factorFlat).hom).1
  simp only [Category.assoc]
  change DerivedCategory.Q.map (morphism ⊗ₘ 𝟙 factor) ≫
      (tensor.comparison target factor targetFlat factorFlat).inv ≫
      (tensor.comparison target factor targetFlat factorFlat).hom = _
  rw [Iso.inv_hom_id, Category.comp_id]
  change _ = (tensor.comparison source factor sourceFlat factorFlat).inv ≫
    ((tensor.tensor.map (DerivedCategory.Q.map morphism)).app (DerivedCategory.Q.obj factor) ≫
      (tensor.comparison target factor targetFlat factorFlat).hom)
  rw [naturality, Iso.inv_hom_id_assoc]
  rfl

private theorem tensorComparisonIso_naturality_from_kFlat
    {ring : Type u} [CommRing ring] (tensor : CochainComplex.DerivedTensor.DerivedTensorProduct
      ring)
    {source target : CochainComplex (ModuleCat.{u} ring) ℤ}
    (factor : CochainComplex (ModuleCat.{u} ring) ℤ) (morphism : source ⟶ target)
    (sourceFlat : source.KFlat) (factorFlat : factor.KFlat) :
    (ordinaryTensorFunctor factor).map morphism ≫
        (KoszulCompletion.tensorComparisonIso tensor target factor factorFlat).hom =
      (tensor.comparison source factor sourceFlat factorFlat).inv ≫
        (derivedTensorFunctor tensor factor).map morphism := by
  let witness := CochainComplex.KFlat.exists_kFlat_resolution target
  let chosen := witness.choose
  let resolution : chosen ⟶ target := witness.choose_spec.choose
  have chosenFlat : chosen.KFlat := witness.choose_spec.choose_spec.1
  let : QuasiIso resolution := witness.choose_spec.choose_spec.2.2.1
  let : Epi resolution := HomologicalComplex.epi_of_epi_f resolution fun degree =>
    (ModuleCat.epi_iff_surjective _).2 (witness.choose_spec.choose_spec.2.2.2 degree)
  let ordinary := ordinaryTensorFunctor factor
  let derived := derivedTensorFunctor tensor factor
  have : IsIso (ordinary.map resolution) :=
    ordinaryTensorFunctor_map_isIso factor factorFlat resolution
  have chosenEquation : ordinary.map resolution ≫
      (KoszulCompletion.tensorComparisonIso tensor target factor factorFlat).hom =
      (tensor.comparison chosen factor chosenFlat factorFlat).inv ≫ derived.map resolution := by
    change ordinary.map resolution ≫
      (inv (ordinary.map resolution) ≫ (tensor.comparison chosen factor chosenFlat factorFlat).inv ≫
        derived.map resolution) = _
    rw [IsIso.hom_inv_id_assoc]
  obtain ⟨refinement, left, right, refinementFlat, leftQuasiIso, square⟩ :=
    kFlat_common_cover morphism resolution
  let : QuasiIso left := leftQuasiIso
  have : IsIso (ordinary.map left) := ordinaryTensorFunctor_map_isIso factor factorFlat left
  apply (cancel_epi (ordinary.map left)).1
  change ordinary.map left ≫ (ordinary.map morphism ≫ _) = _
  calc
    ordinary.map left ≫ (ordinary.map morphism ≫
        (KoszulCompletion.tensorComparisonIso tensor target factor factorFlat).hom) =
      ordinary.map right ≫ (ordinary.map resolution ≫
        (KoszulCompletion.tensorComparisonIso tensor target factor factorFlat).hom) := by
      rw [← ordinary.map_comp_assoc, square, ordinary.map_comp, Category.assoc]
    _ = (ordinary.map right ≫ (tensor.comparison chosen factor chosenFlat factorFlat).inv) ≫
        derived.map resolution := by rw [chosenEquation, Category.assoc]
    _ = ((tensor.comparison refinement factor refinementFlat factorFlat).inv ≫
        derived.map right) ≫ derived.map resolution := by
      rw [comparison_inverse_naturality tensor factor right refinementFlat chosenFlat factorFlat]
    _ = (tensor.comparison refinement factor refinementFlat factorFlat).inv ≫
        (derived.map left ≫ derived.map morphism) := by
      rw [Category.assoc, ← derived.map_comp, ← square, derived.map_comp]
    _ = (ordinary.map left ≫ (tensor.comparison source factor sourceFlat factorFlat).inv) ≫
        derived.map morphism := by
      rw [comparison_inverse_naturality tensor factor left refinementFlat sourceFlat factorFlat,
        Category.assoc]
    _ = ordinary.map left ≫ ((tensor.comparison source factor sourceFlat factorFlat).inv ≫
        derived.map morphism) := Category.assoc _ _ _

private theorem tensorComparisonIso_naturality
    {ring : Type u} [CommRing ring] (tensor : CochainComplex.DerivedTensor.DerivedTensorProduct
      ring)
    {source target : CochainComplex (ModuleCat.{u} ring) ℤ}
    (factor : CochainComplex (ModuleCat.{u} ring) ℤ) (morphism : source ⟶ target)
    (factorFlat : factor.KFlat) :
    (ordinaryTensorFunctor factor).map morphism ≫
        (KoszulCompletion.tensorComparisonIso tensor target factor factorFlat).hom =
      (KoszulCompletion.tensorComparisonIso tensor source factor factorFlat).hom ≫
        (derivedTensorFunctor tensor factor).map morphism := by
  obtain ⟨resolution, projection, resolutionFlat, _, projectionQuasiIso, _⟩ :=
    CochainComplex.KFlat.exists_kFlat_resolution source
  let : QuasiIso projection := projectionQuasiIso
  let ordinary := ordinaryTensorFunctor factor
  let derived := derivedTensorFunctor tensor factor
  have : IsIso (ordinary.map projection) :=
    ordinaryTensorFunctor_map_isIso factor factorFlat projection
  apply (cancel_epi (ordinary.map projection)).1
  change ordinary.map projection ≫ (ordinary.map morphism ≫ _) =
    ordinary.map projection ≫ (_ ≫ derived.map morphism)
  calc
    ordinary.map projection ≫ (ordinary.map morphism ≫
        (KoszulCompletion.tensorComparisonIso tensor target factor factorFlat).hom) =
      ordinary.map (projection ≫ morphism) ≫
        (KoszulCompletion.tensorComparisonIso tensor target factor factorFlat).hom := by
      rw [ordinary.map_comp, Category.assoc]
    _ = (tensor.comparison resolution factor resolutionFlat factorFlat).inv ≫
        derived.map (projection ≫ morphism) :=
      tensorComparisonIso_naturality_from_kFlat tensor factor (projection ≫ morphism)
        resolutionFlat factorFlat
    _ = (ordinary.map projection ≫
        (KoszulCompletion.tensorComparisonIso tensor source factor factorFlat).hom) ≫
        derived.map morphism := by
      rw [tensorComparisonIso_naturality_from_kFlat tensor factor projection
        resolutionFlat factorFlat, Category.assoc, derived.map_comp]
    _ = ordinary.map projection ≫
        ((KoszulCompletion.tensorComparisonIso tensor source factor factorFlat).hom ≫
          derived.map morphism) := Category.assoc _ _ _

private def tensorComparisonNatIso
    {ring : Type u} [CommRing ring] (tensor : CochainComplex.DerivedTensor.DerivedTensorProduct
      ring)
    (factor : CochainComplex (ModuleCat.{u} ring) ℤ) (factorFlat : factor.KFlat) :
    ordinaryTensorFunctor factor ≅ derivedTensorFunctor tensor factor :=
  NatIso.ofComponents
    (fun complex => KoszulCompletion.tensorComparisonIso tensor complex factor factorFlat)
    (fun morphism => tensorComparisonIso_naturality tensor factor morphism factorFlat)

private theorem comparison_inverse_right_naturality
    {ring : Type u} [CommRing ring] (tensor : CochainComplex.DerivedTensor.DerivedTensorProduct
      ring)
    (coefficient : CochainComplex (ModuleCat.{u} ring) ℤ)
    {source target : CochainComplex (ModuleCat.{u} ring) ℤ}
    (morphism : source ⟶ target) (coefficientFlat : coefficient.KFlat)
    (sourceFlat : source.KFlat) (targetFlat : target.KFlat) :
    DerivedCategory.Q.map (𝟙 coefficient ⊗ₘ morphism) ≫
        (tensor.comparison coefficient target coefficientFlat targetFlat).inv =
      (tensor.comparison coefficient source coefficientFlat sourceFlat).inv ≫
        (tensor.tensor.obj (DerivedCategory.Q.obj coefficient)).map
          (DerivedCategory.Q.map morphism) := by
  have naturality := tensor.comparison_naturality (𝟙 coefficient) morphism
    coefficientFlat coefficientFlat sourceFlat targetFlat
  have identity := (DerivedCategory.Q (C := ModuleCat.{u} ring)).map_id coefficient
  rw [identity, tensor.tensor.map_id, NatTrans.id_app, Category.id_comp] at naturality
  apply (cancel_mono (tensor.comparison coefficient target coefficientFlat targetFlat).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [naturality, Iso.inv_hom_id_assoc]
  rfl

/-- **`KoszulCompletion.tensorComparisonIso` is natural in its K-flat right factor.**  With the
levelwise comparison itself this is what makes the K-flat comparison an isomorphism of *towers*:
a transition map of a tower of K-flat complexes is carried by the comparison to the map the
derived tensor product makes of it. -/
private theorem tensorComparisonIso_right_naturality
    {ring : Type u} [CommRing ring] (tensor : CochainComplex.DerivedTensor.DerivedTensorProduct
      ring)
    (coefficient : CochainComplex (ModuleCat.{u} ring) ℤ)
    {source target : CochainComplex (ModuleCat.{u} ring) ℤ}
    (morphism : source ⟶ target) (sourceFlat : source.KFlat) (targetFlat : target.KFlat) :
    DerivedCategory.Q.map (𝟙 coefficient ⊗ₘ morphism) ≫
        (KoszulCompletion.tensorComparisonIso tensor coefficient target targetFlat).hom =
      (KoszulCompletion.tensorComparisonIso tensor coefficient source sourceFlat).hom ≫
        (tensor.tensor.obj (DerivedCategory.Q.obj coefficient)).map
          (DerivedCategory.Q.map morphism) := by
  obtain ⟨resolution, projection, resolutionFlat, _, projectionQuasiIso, _⟩ :=
    CochainComplex.KFlat.exists_kFlat_resolution coefficient
  let : QuasiIso projection := projectionQuasiIso
  have : IsIso ((ordinaryTensorFunctor source).map projection) :=
    ordinaryTensorFunctor_map_isIso source sourceFlat projection
  have square : DerivedCategory.Q.map (projection ⊗ₘ 𝟙 source) ≫
        DerivedCategory.Q.map (𝟙 coefficient ⊗ₘ morphism) =
      DerivedCategory.Q.map (𝟙 resolution ⊗ₘ morphism) ≫
        DerivedCategory.Q.map (projection ⊗ₘ 𝟙 target) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  apply (cancel_epi ((ordinaryTensorFunctor source).map projection)).1
  change DerivedCategory.Q.map (projection ⊗ₘ 𝟙 source) ≫ _ = _
  calc
    DerivedCategory.Q.map (projection ⊗ₘ 𝟙 source) ≫
        (DerivedCategory.Q.map (𝟙 coefficient ⊗ₘ morphism) ≫
          (KoszulCompletion.tensorComparisonIso tensor coefficient target targetFlat).hom) =
      DerivedCategory.Q.map (𝟙 resolution ⊗ₘ morphism) ≫
        ((ordinaryTensorFunctor target).map projection ≫
          (KoszulCompletion.tensorComparisonIso tensor coefficient target targetFlat).hom) := by
      rw [← Category.assoc, square, Category.assoc]
      rfl
    _ = (DerivedCategory.Q.map (𝟙 resolution ⊗ₘ morphism) ≫
        (tensor.comparison resolution target resolutionFlat targetFlat).inv) ≫
        (derivedTensorFunctor tensor target).map projection := by
      rw [tensorComparisonIso_naturality_from_kFlat tensor target projection resolutionFlat
        targetFlat,
        Category.assoc]
    _ = ((tensor.comparison resolution source resolutionFlat sourceFlat).inv ≫
        (tensor.tensor.obj (DerivedCategory.Q.obj resolution)).map (DerivedCategory.Q.map morphism))
          ≫
        (derivedTensorFunctor tensor target).map projection := by
      rw [comparison_inverse_right_naturality tensor resolution morphism resolutionFlat sourceFlat
        targetFlat]
    _ = (tensor.comparison resolution source resolutionFlat sourceFlat).inv ≫
        ((derivedTensorFunctor tensor source).map projection ≫
          (tensor.tensor.obj (DerivedCategory.Q.obj coefficient)).map (DerivedCategory.Q.map
            morphism)) := by
      rw [Category.assoc]
      exact congrArg (fun value => (tensor.comparison resolution source resolutionFlat
        sourceFlat).inv ≫ value)
        ((tensor.tensor.map (DerivedCategory.Q.map projection)).naturality (DerivedCategory.Q.map
          morphism))
    _ = (ordinaryTensorFunctor source).map projection ≫
        ((KoszulCompletion.tensorComparisonIso tensor coefficient source sourceFlat).hom ≫
          (tensor.tensor.obj (DerivedCategory.Q.obj coefficient)).map (DerivedCategory.Q.map
            morphism)) := by
      rw [← Category.assoc, ← tensorComparisonIso_naturality_from_kFlat tensor source projection
        resolutionFlat sourceFlat, Category.assoc]

private theorem tensorComparisonIso_rightUnitor_arbitrary
    {ring : Type u} [CommRing ring] (tensor : CochainComplex.DerivedTensor.DerivedTensorProduct
      ring)
    (coefficient : CochainComplex (ModuleCat.{u} ring) ℤ)
    (unitFlat : (𝟙_ (CochainComplex (ModuleCat.{u} ring) ℤ)).KFlat) :
    (KoszulCompletion.tensorComparisonIso tensor coefficient (𝟙_ _) unitFlat).inv ≫
        DerivedCategory.Q.map (ρ_ coefficient).hom =
      tensor.rightUnitor.hom.app (DerivedCategory.Q.obj coefficient) := by
  obtain ⟨resolution, projection, resolutionFlat, _, projectionQuasiIso, _⟩ :=
    CochainComplex.KFlat.exists_kFlat_resolution coefficient
  let : QuasiIso projection := projectionQuasiIso
  have : IsIso ((derivedTensorFunctor tensor (𝟙_ _)).map projection) :=
    inferInstanceAs (IsIso ((tensor.tensor.flip.obj (DerivedCategory.Q.obj (𝟙_ _))).map
      (DerivedCategory.Q.map projection)))
  have naturality := (tensorComparisonNatIso tensor (𝟙_ _) unitFlat).inv.naturality projection
  simp only [tensorComparisonNatIso, NatIso.ofComponents_inv_app] at naturality
  apply (cancel_epi ((derivedTensorFunctor tensor (𝟙_ _)).map projection)).1
  rw [← Category.assoc, naturality, Category.assoc]
  change _ ≫ (DerivedCategory.Q.map (projection ⊗ₘ 𝟙 _) ≫
    DerivedCategory.Q.map (ρ_ coefficient).hom) = _
  rw [← Functor.map_comp, tensorHom_id, rightUnitor_naturality, Functor.map_comp, ← Category.assoc,
    KoszulCompletion.tensorComparisonIso_rightUnitor tensor resolution resolutionFlat unitFlat]
  exact (tensor.rightUnitor.hom.naturality (DerivedCategory.Q.map projection)).symm

private theorem tensorUnit_kFlat {ring : Type u} [CommRing ring] :
    (𝟙_ (CochainComplex (ModuleCat.{u} ring) ℤ)).KFlat := by
  let complex := (HomologicalComplex.single (ModuleCat.{u} ring) (ComplexShape.up ℤ) 0).obj
    (ModuleCat.of ring ring)
  let (degree : ℤ) : Projective (complex.X degree) := by
    dsimp only [complex]
    infer_instance
  let (degree : ℤ) : Module.Flat ring (complex.X degree) := inferInstance
  exact CochainComplex.KFlat.kFlat_of_flat complex 0

private theorem tensorComparisonIso_unit_map
    {ring : Type u} [CommRing ring] (tensor : CochainComplex.DerivedTensor.DerivedTensorProduct
      ring)
    (coefficient factor : CochainComplex (ModuleCat.{u} ring) ℤ)
    (morphism : 𝟙_ _ ⟶ factor) (factorFlat : factor.KFlat) :
    DerivedCategory.Q.map ((ρ_ coefficient).inv ≫ (coefficient ◁ morphism)) ≫
        (KoszulCompletion.tensorComparisonIso tensor coefficient factor factorFlat).hom =
      tensor.rightUnitor.inv.app (DerivedCategory.Q.obj coefficient) ≫
        (tensor.tensor.obj (DerivedCategory.Q.obj coefficient)).map
          (DerivedCategory.Q.map morphism) := by
  have unitFlat := tensorUnit_kFlat (ring := ring)
  have normalize : DerivedCategory.Q.map (ρ_ coefficient).inv ≫
        (KoszulCompletion.tensorComparisonIso tensor coefficient (𝟙_ _) unitFlat).hom =
      tensor.rightUnitor.inv.app (DerivedCategory.Q.obj coefficient) := by
    apply (cancel_mono (tensor.rightUnitor.hom.app (DerivedCategory.Q.obj coefficient))).1
    rw [← tensorComparisonIso_rightUnitor_arbitrary tensor coefficient unitFlat]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, Iso.inv_hom_id]
    rw [tensorComparisonIso_rightUnitor_arbitrary,
      (DerivedCategory.Q (C := ModuleCat.{u} ring)).map_id]
    exact (tensor.rightUnitor.app (DerivedCategory.Q.obj coefficient)).inv_hom_id.symm
  rw [Functor.map_comp, ← id_tensorHom, Category.assoc,
    tensorComparisonIso_right_naturality tensor coefficient morphism unitFlat factorFlat,
    ← Category.assoc, normalize]

open KoszulCompletion KoszulCoefficientTower
open scoped ExteriorAlgebra

private theorem standardKoszulStage_flat
    {ring : Type u} [CommRing ring] {rank : ℕ} (family : Fin rank → ring) (power : ℕ) :
    (standardKoszulStage family none power).KFlat := by
  let complex := Koszul.seqComplex (fun index => family index ^ (power + 1))
  let (degree : ℕ) : Projective (complex.X degree) := by
    change Projective (ModuleCat.of ring (⋀[ring]^degree (Fin rank → ring)))
    exact ModuleCat.projective_of_free ((Pi.basisFun ring (Fin rank)).exteriorPower degree)
  let (degree : ℤ) : Module.Flat ring ((complex.extend ComplexShape.embeddingDownNat).X degree) :=
    inferInstance
  exact CochainComplex.KFlat.kFlat_of_flat (complex.extend ComplexShape.embeddingDownNat) 0

private def coefficientStageNatIso
    {ring : Type u} [CommRing ring] {rank : ℕ} (family : Fin rank → ring)
    (tensor : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{v} ring)) (power : ℕ) :
    coefficientCompletionStage family power ⋙ DerivedCategory.Q ⋙
        AdicKoszul.derivedUniverseLift.{u, v} ring ≅
      DerivedCategory.Q ⋙ AdicKoszul.derivedUniverseLift.{u, v} ring ⋙
        tensor.tensor.flip.obj (DerivedCategory.Q.obj
          (standardKoszulStage (fun index => (ULift.up (family index) : ULift.{v} ring))
            none power)) := by
  let lift := complexUniverseLift.{u, v} (A := ring)
  let factor := standardKoszulStage
    (fun index => (ULift.up (family index) : ULift.{v} ring)) none power
  let factorFlat := standardKoszulStage_flat
    (fun index => (ULift.up (family index) : ULift.{v} ring)) power
  let stage := coefficientCompletionStage family power
  let ordinaryRight := (curriedTensor (CochainComplex (ModuleCat.{max u v} (ULift.{v} ring))
    ℤ)).flip.obj factor
  let derivedRight := tensor.tensor.flip.obj (DerivedCategory.Q.obj factor)
  let factors := (AdicKoszul.moduleUniverseLift.{u, v} ring).mapDerivedCategoryFactors
  let coefficientComparison : stage ⋙ lift ≅ lift ⋙ ordinaryRight :=
    Functor.associator _ _ _ ≪≫ coefficientKoszulComparison family none power
  exact Functor.isoWhiskerLeft stage factors ≪≫
    (Functor.associator stage lift DerivedCategory.Q).symm ≪≫
    Functor.isoWhiskerRight coefficientComparison DerivedCategory.Q ≪≫
    Functor.associator lift ordinaryRight DerivedCategory.Q ≪≫
    Functor.isoWhiskerLeft lift (tensorComparisonNatIso tensor factor factorFlat) ≪≫
    (Functor.associator lift DerivedCategory.Q derivedRight).symm ≪≫
    Functor.isoWhiskerRight factors.symm derivedRight ≪≫
    Functor.associator DerivedCategory.Q (AdicKoszul.derivedUniverseLift.{u, v} ring) derivedRight

private theorem derivedTensorUnit_naturality
    {ring : Type u} [CommRing ring] (tensor : CochainComplex.DerivedTensor.DerivedTensorProduct
      ring)
    {source target : CochainComplex.DerivedTensor.DObj ring} (morphism : source ⟶ target)
    {factor : CochainComplex.DerivedTensor.DObj ring}
    (unitMap : DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{u} ring) ℤ)) ⟶ factor) :
    morphism ≫ (tensor.rightUnitor.inv.app target ≫ (tensor.tensor.obj target).map unitMap) =
      (tensor.rightUnitor.inv.app source ≫ (tensor.tensor.obj source).map unitMap) ≫
        (tensor.tensor.map morphism).app factor := by
  have naturality := tensor.rightUnitor.inv.naturality morphism
  change morphism ≫ tensor.rightUnitor.inv.app target =
    tensor.rightUnitor.inv.app source ≫ (tensor.tensor.map morphism).app _ at naturality
  rw [← Category.assoc, naturality]
  rw [Category.assoc]
  simp only [Category.assoc]
  exact whisker_eq _ ((tensor.tensor.map morphism).naturality unitMap).symm

/-- Precomposing the stage comparison with the image of a map into a coefficient stage. -/
private theorem lift_map_comp_coefficientStageComparisonIso_hom
    {ring : Type u} [CommRing ring] {rank : ℕ} (family : Fin rank → ring)
    (tensor : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{v} ring)) (power : ℕ)
    {complex source : CochainComplex (ModuleCat.{v} ring) ℤ}
    (morphism : source ⟶ (coefficientCompletionStage family power).obj complex) :
    (AdicKoszul.derivedUniverseLift.{u, v} ring).map (DerivedCategory.Q.map morphism) ≫
        (coefficientStageComparisonIso family tensor power complex).hom =
      ((AdicKoszul.moduleUniverseLift.{u, v} ring).mapDerivedCategoryFactors.app source).hom ≫
        DerivedCategory.Q.map ((complexUniverseLift.{u, v} (A := ring)).map morphism) ≫
        DerivedCategory.Q.map ((coefficientKoszulComparison family none power).hom.app complex) ≫
        (tensorComparisonIso tensor ((complexUniverseLift.{u, v} (A := ring)).obj complex)
          (standardKoszulStage (fun index => (ULift.up (family index) : ULift.{v} ring)) none power)
          (standardKoszulStage_flat
            (fun index => (ULift.up (family index) : ULift.{v} ring)) power)).hom ≫
        (tensor.tensor.flip.obj (DerivedCategory.Q.obj (standardKoszulStage
          (fun index => (ULift.up (family index) : ULift.{v} ring)) none power))).map
          ((AdicKoszul.moduleUniverseLift.{u, v} ring).mapDerivedCategoryFactors.app
            complex).inv := by
  have factorNaturality :=
    (AdicKoszul.moduleUniverseLift.{u, v} ring).mapDerivedCategoryFactors.hom.naturality morphism
  change (AdicKoszul.derivedUniverseLift ring).map (DerivedCategory.Q.map morphism) ≫
      (((AdicKoszul.moduleUniverseLift.{u, v} ring).mapDerivedCategoryFactors).app
        ((coefficientCompletionStage family power).obj complex)).hom =
    ((AdicKoszul.moduleUniverseLift.{u, v} ring).mapDerivedCategoryFactors.app source).hom ≫
      DerivedCategory.Q.map ((complexUniverseLift.{u, v} (A := ring)).map morphism)
    at factorNaturality
  change (AdicKoszul.derivedUniverseLift ring).map (DerivedCategory.Q.map morphism) ≫
    (_ ≫ DerivedCategory.Q.map ((coefficientKoszulComparison family none power).hom.app complex) ≫
      _ ≫ _) = _
  erw [reassoc_of% factorNaturality]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem coefficientStageComparisonIso_augmentation
    {ring : Type u} [CommRing ring] {rank : ℕ} (family : Fin rank → ring)
    (tensor : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{v} ring)) (power : ℕ)
    (complex : CochainComplex (ModuleCat.{v} ring) ℤ) :
    (AdicKoszul.derivedUniverseLift.{u, v} ring).map
        (DerivedCategory.Q.map ((coefficientKoszulAugmentation family power).app complex)) ≫
        (coefficientStageComparisonIso family tensor power complex).hom =
      AdicKoszul.derivedTensorKoszulPowerUnit family tensor (DerivedCategory.Q.obj complex) power :=
        by
  let factors := (AdicKoszul.moduleUniverseLift.{u, v} ring).mapDerivedCategoryFactors
  let lift := complexUniverseLift.{u, v} (A := ring)
  let factor := standardKoszulStage
    (fun index => (ULift.up (family index) : ULift.{v} ring)) none power
  let factorFlat := standardKoszulStage_flat
    (fun index => (ULift.up (family index) : ULift.{v} ring)) power
  let unitMap := AdicKoszul.koszulPowerUnit
    (fun index => (ULift.up (family index) : ULift.{v} ring)) power
  rw [lift_map_comp_coefficientStageComparisonIso_hom family tensor power]
  rw [← Functor.map_comp_assoc, coefficientKoszulComparison_augmentation]
  rw [← Category.assoc (DerivedCategory.Q.map _)]
  rw [tensorComparisonIso_unit_map tensor (lift.obj complex) factor unitMap factorFlat]
  rw [← Category.assoc]
  refine (derivedTensorUnit_naturality tensor (factors.app complex).hom
    (DerivedCategory.Q.map unitMap) =≫ _).trans ?_
  simp only [Category.assoc]
  change _ ≫ _ ≫ ((tensor.tensor.map (factors.app complex).hom).app (DerivedCategory.Q.obj factor) ≫
    (tensor.tensor.map (factors.app complex).inv).app (DerivedCategory.Q.obj factor)) = _
  rw [← NatTrans.comp_app, ← Functor.map_comp, Iso.hom_inv_id, tensor.tensor.map_id,
    NatTrans.id_app, Category.comp_id]
  rfl

private theorem coefficientStageNatIso_app
    {ring : Type u} [CommRing ring] {rank : ℕ} (family : Fin rank → ring)
    (tensor : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{v} ring)) (power : ℕ)
    (complex : CochainComplex (ModuleCat.{v} ring) ℤ) :
    (coefficientStageNatIso family tensor power).app complex =
      coefficientStageComparisonIso family tensor power complex := by
  apply Iso.ext
  simp only [coefficientStageNatIso, coefficientStageComparisonIso, Iso.app_hom,
    Iso.trans_hom, Iso.symm_hom, tensorComparisonNatIso, NatIso.ofComponents_hom_app,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]
  rfl

theorem stageComparisonNaturality
    {ring : Type u} [CommRing ring] {rank : ℕ} (family : Fin rank → ring)
    (tensor : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{v} ring)) :
    StageComparisonNaturality family tensor := by
  refine ⟨fun power source target morphism ↦ ?_⟩
  have naturality := (coefficientStageNatIso family tensor power).hom.naturality morphism
  change _ ≫ ((coefficientStageNatIso family tensor power).app target).hom =
    ((coefficientStageNatIso family tensor power).app source).hom ≫ _ at naturality
  rwa [coefficientStageNatIso_app, coefficientStageNatIso_app] at naturality

set_option backward.isDefEq.respectTransparency false in
private theorem completionUnit_projection_representative
    {ring : Type u} [CommRing ring] {rank : ℕ} {family : Fin rank → ring}
    {tensor : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{v} ring)}
    (comparisonLaws : StageComparisonNaturality family tensor)
    (complex : CochainComplex (ModuleCat.{v} ring) ℤ) (power : ℕ) :
    (AdicKoszul.derivedUniverseLift.{u, v} ring).map
        ((completionUnit family).app (DerivedCategory.Q.obj complex)) ≫
        (comparisonLaws.projection power).app (DerivedCategory.Q.obj complex) =
      AdicKoszul.derivedTensorKoszulPowerUnit family tensor (DerivedCategory.Q.obj complex) power :=
        by
  simp only [completionUnit, StageComparisonNaturality.projection, Localization.liftNatTrans_app,
    Functor.whiskerRight_app, NatTrans.comp_app, StageComparisonNaturality.comparison,
    NatIso.ofComponents_hom_app, Functor.map_comp, Category.assoc]
  simp only [Localization.Lifting.iso, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.rightUnitor_hom_app, Iso.refl_inv, NatTrans.id_app,
    Category.comp_id]
  refine ((AdicKoszul.derivedUniverseLift.{u, v} ring).map_id _ =≫ _).trans
    ((Category.id_comp _).trans ?_)
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc]
  rw [← (DerivedCategory.Q (C := ModuleCat.{v} ring)).map_comp,
    coefficientCompletionUnit_projection]
  exact coefficientStageComparisonIso_augmentation family tensor power complex

private def tensorKoszulUnitNatTrans
    {ring : Type u} [CommRing ring] {rank : ℕ} (family : Fin rank → ring)
    (tensor : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{v} ring)) (power : ℕ) :
    AdicKoszul.derivedUniverseLift.{u, v} ring ⟶
      AdicKoszul.derivedUniverseLift.{u, v} ring ⋙ tensor.tensor.flip.obj
        ((AdicKoszul.canonicalKoszulPowerSystem
          (fun index => (ULift.up (family index) : ULift.{v} ring))).obj ⟨power⟩) where
  app object := AdicKoszul.derivedTensorKoszulPowerUnit family tensor object power
  naturality _ _ morphism :=
    derivedTensorUnit_naturality tensor
      ((AdicKoszul.derivedUniverseLift.{u, v} ring).map morphism)
      (DerivedCategory.Q.map (AdicKoszul.koszulPowerUnit
        (fun index => (ULift.up (family index) : ULift.{v} ring)) power))

theorem completionUnit_projection
    {ring : Type u} [CommRing ring] {rank : ℕ} {family : Fin rank → ring}
    {tensor : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{v} ring)}
    (comparisonLaws : StageComparisonNaturality family tensor)
    (object : DerivedCategory (ModuleCat.{v} ring)) (power : ℕ) :
    (AdicKoszul.derivedUniverseLift.{u, v} ring).map ((completionUnit family).app object) ≫
        (comparisonLaws.projection power).app object =
      AdicKoszul.derivedTensorKoszulPowerUnit family tensor object power := by
  have equality : Functor.whiskerRight (completionUnit family)
        (AdicKoszul.derivedUniverseLift.{u, v} ring) ≫ comparisonLaws.projection power =
      tensorKoszulUnitNatTrans family tensor power :=
    Localization.natTrans_ext (DerivedCategory.Q (C := ModuleCat.{v} ring))
      (HomologicalComplex.quasiIso (ModuleCat.{v} ring) (ComplexShape.up ℤ)) fun complex ↦
        completionUnit_projection_representative comparisonLaws complex power
  exact congr_app equality object

set_option backward.isDefEq.respectTransparency false in
theorem coefficientStageComparisonIso_transition
    {ring : Type u} [CommRing ring] {rank : ℕ} (family : Fin rank → ring)
    (tensor : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{v} ring))
    (sourcePower targetPower : ℕ) (powerOrder : targetPower ≤ sourcePower)
    (complex : CochainComplex (ModuleCat.{v} ring) ℤ) :
    (AdicKoszul.derivedUniverseLift.{u, v} ring).map
        (DerivedCategory.Q.map (((coefficientKoszulTower family).obj complex).map
          (homOfLE powerOrder).op)) ≫
        (coefficientStageComparisonIso family tensor targetPower complex).hom =
      (coefficientStageComparisonIso family tensor sourcePower complex).hom ≫
        (tensor.tensor.obj ((AdicKoszul.derivedUniverseLift ring).obj (DerivedCategory.Q.obj
          complex))).map
          (DerivedCategory.Q.map (standardKoszulTransition
            (fun index => (ULift.up (family index) : ULift.{v} ring)) none
            sourcePower targetPower powerOrder)) := by
  let factors := (AdicKoszul.moduleUniverseLift.{u, v} ring).mapDerivedCategoryFactors
  let lift := complexUniverseLift.{u, v} (A := ring)
  let sourceFactor := standardKoszulStage
    (fun index => (ULift.up (family index) : ULift.{v} ring)) none sourcePower
  let targetFactor := standardKoszulStage
    (fun index => (ULift.up (family index) : ULift.{v} ring)) none targetPower
  let sourceFlat := standardKoszulStage_flat
    (fun index => (ULift.up (family index) : ULift.{v} ring)) sourcePower
  let targetFlat := standardKoszulStage_flat
    (fun index => (ULift.up (family index) : ULift.{v} ring)) targetPower
  let transition := ((coefficientKoszulTower family).obj complex).map (homOfLE powerOrder).op
  let koszulTransition := standardKoszulTransition
    (fun index => (ULift.up (family index) : ULift.{v} ring)) none sourcePower targetPower
      powerOrder
  rw [lift_map_comp_coefficientStageComparisonIso_hom family tensor targetPower transition]
  rw [← Functor.map_comp_assoc, coefficientKoszulComparison_transition, Functor.map_comp]
  simp only [Category.assoc]
  have tensorNaturality := tensorComparisonIso_right_naturality tensor (lift.obj complex)
    (source := sourceFactor) (target := targetFactor) koszulTransition sourceFlat targetFlat
  have tensorNaturalityAssoc := congrArg (fun morphism => morphism ≫
    (tensor.tensor.flip.obj (DerivedCategory.Q.obj targetFactor)).map (factors.app complex).inv)
    tensorNaturality
  simp only [Category.assoc] at tensorNaturalityAssoc
  conv_rhs =>
    simp only [coefficientStageComparisonIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      Category.assoc]
  apply congrArg (fun morphism =>
    (factors.app ((coefficientCompletionStage family sourcePower).obj complex)).hom ≫
      DerivedCategory.Q.map ((coefficientKoszulComparison family none sourcePower).hom.app complex)
        ≫
        morphism)
  refine tensorNaturalityAssoc.trans ?_
  exact congrArg (fun morphism => (tensorComparisonIso tensor (lift.obj complex) sourceFactor
    sourceFlat).hom ≫
    morphism) ((tensor.tensor.map (factors.app complex).inv).naturality (DerivedCategory.Q.map
      koszulTransition))

end KoszulTensorNaturalityAudit

end

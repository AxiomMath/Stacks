module

public import StacksFrontier.Homology.DerivedComplete.AdicDerivedCompletion.StageMilnorComparison

/-!
# Derived completion as a limit of Koszul complexes: the completion unit

## Main results

* `canonicalCompletion_map_unit_isIso`: the Koszul completion functor inverts its unit.
-/


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory
open KoszulCoefficientTower KoszulCompletion

attribute [local instance 2000] HasDerivedCategory.standard

universe ringLevel moduleLevel

variable {ring : Type ringLevel} [CommRing ring] {rank : ℕ} (family : Fin rank → ring)

private instance coefficientLift_full :
    (complexUniverseLift.{ringLevel, moduleLevel} (A := ring)).Full := by
  infer_instance

private instance coefficientLift_faithful :
    (complexUniverseLift.{ringLevel, moduleLevel} (A := ring)).Faithful := by
  infer_instance

private def coefficientStageLiftIso (stage : ℕ) :
    coefficientCompletionStage.{ringLevel, moduleLevel} family stage ⋙ complexUniverseLift ≅
      complexUniverseLift ⋙ tensorRight
        (standardKoszulStage (fun index => (ULift.up (family index) : ULift.{moduleLevel} ring))
          none stage) :=
  coefficientKoszulComparison family none stage

private def coefficientDoubleStageLiftIso (first second : ℕ) :
    (coefficientCompletionStage.{ringLevel, moduleLevel} family first ⋙
        coefficientCompletionStage family second) ⋙ complexUniverseLift ≅
      complexUniverseLift ⋙
        (tensorRight (standardKoszulStage
          (fun index => (ULift.up (family index) : ULift.{moduleLevel} ring)) none first) ⋙
        tensorRight (standardKoszulStage
          (fun index => (ULift.up (family index) : ULift.{moduleLevel} ring)) none second)) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (coefficientStageLiftIso family second) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (coefficientStageLiftIso family first) _ ≪≫
    Functor.associator _ _ _

private def coefficientStagesSwapLift (first second : ℕ) :
    (coefficientCompletionStage.{ringLevel, moduleLevel} family first ⋙
        coefficientCompletionStage family second) ⋙ complexUniverseLift ≅
      (coefficientCompletionStage family second ⋙ coefficientCompletionStage family first) ⋙
        complexUniverseLift := by
  letI := Classical.choose
    (TotalTensorComplex.cochainComplex_symmetricMonoidalCategory (ULift.{moduleLevel} ring))
  let firstFactor := standardKoszulStage
    (fun index => (ULift.up (family index) : ULift.{moduleLevel} ring)) none first
  let secondFactor := standardKoszulStage
    (fun index => (ULift.up (family index) : ULift.{moduleLevel} ring)) none second
  let swap : tensorRight firstFactor ⋙ tensorRight secondFactor ≅
      tensorRight secondFactor ⋙ tensorRight firstFactor :=
    (tensorRightTensor firstFactor secondFactor).symm ≪≫
      (curriedTensor _).flip.mapIso (β_ firstFactor secondFactor) ≪≫
      tensorRightTensor secondFactor firstFactor
  exact coefficientDoubleStageLiftIso family first second ≪≫
    Functor.isoWhiskerLeft _ swap ≪≫ (coefficientDoubleStageLiftIso family second first).symm

private def coefficientStagesSwap (first second : ℕ) :
    coefficientCompletionStage.{ringLevel, moduleLevel} family first ⋙
        coefficientCompletionStage family second ≅
      coefficientCompletionStage family second ⋙ coefficientCompletionStage family first :=
  ((Functor.whiskeringRight _ _ _).obj
    (complexUniverseLift.{ringLevel, moduleLevel} (A := ring))).preimageIso
      (coefficientStagesSwapLift family first second)

/-- The universe lift of the swap isomorphism at `complex` is the lifted swap isomorphism. -/
private theorem map_coefficientStagesSwap_hom_app (first second : ℕ)
    (complex : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ) :
    complexUniverseLift.map
        ((coefficientStagesSwap.{ringLevel, moduleLevel} family first second).hom.app complex) =
      (coefficientStagesSwapLift family first second).hom.app complex :=
  NatTrans.congr_app (((Functor.whiskeringRight _ _ _).obj
    (complexUniverseLift.{ringLevel, moduleLevel} (A := ring))).map_preimage _) complex


private theorem tensorSwap_map
    {category : Type*} [Category category] [MonoidalCategory category] [BraidedCategory category]
    (object first source target : category) (morphism : source ⟶ target) :
    ((object ⊗ first) ◁ morphism) ≫ (α_ object first target).hom ≫
        (object ◁ (β_ first target).hom) ≫ (α_ object target first).inv =
      (α_ object first source).hom ≫ (object ◁ (β_ first source).hom) ≫
        (α_ object source first).inv ≫ ((object ◁ morphism) ▷ first) := by
  rw [associator_naturality_right_assoc]
  rw [← whiskerLeft_comp_assoc, braiding_naturality_right, whiskerLeft_comp]
  simp only [Category.assoc, associator_inv_naturality_middle]


private theorem tensorSwap_unit
    {category : Type*} [Category category] [MonoidalCategory category] [BraidedCategory category]
    (object first second : category) (unitMap : 𝟙_ category ⟶ second) :
    (ρ_ (object ⊗ first)).inv ≫ ((object ⊗ first) ◁ unitMap) ≫
        (α_ object first second).hom ≫ (object ◁ (β_ first second).hom) ≫
        (α_ object second first).inv =
      ((ρ_ object).inv ≫ (object ◁ unitMap)) ▷ first := by
  rw [tensorSwap_map]
  simp only [braiding_tensorUnit_right, comp_whiskerRight]
  monoidal


private theorem coefficientStagesSwap_unit (first second : ℕ)
    (complex : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ) :
    (coefficientKoszulAugmentation family second).app
        ((coefficientCompletionStage family first).obj complex) ≫
      (coefficientStagesSwap family first second).hom.app complex =
    (coefficientCompletionStage family first).map
      ((coefficientKoszulAugmentation family second).app complex) := by
  let := Classical.choose
    (TotalTensorComplex.cochainComplex_symmetricMonoidalCategory (ULift.{moduleLevel} ring))
  have augmentation := coefficientKoszulComparison_augmentation family second
    ((coefficientCompletionStage family first).obj complex)
  apply (complexUniverseLift.{ringLevel, moduleLevel} (A := ring)).map_injective
  rw [Functor.map_comp]
  rw [map_coefficientStagesSwap_hom_app]
  apply (cancel_mono ((coefficientDoubleStageLiftIso family second first).hom.app complex)).mp
  simp only [coefficientStagesSwapLift, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  simp only [coefficientDoubleStageLiftIso, coefficientStageLiftIso, Iso.trans_hom,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp, Category.comp_id,
    Iso.symm_hom, Functor.mapIso_hom, tensorRightTensor_inv_app, tensorRightTensor_hom_app]
  simp only [Category.assoc]
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc, ← Category.assoc]
  rw [augmentation]
  have comparisonNaturality := (coefficientStageLiftIso family first).hom.naturality
    ((coefficientKoszulAugmentation family second).app complex)
  simp only [Functor.comp_map, coefficientStageLiftIso] at comparisonNaturality
  rw [← Category.assoc (complexUniverseLift.map _)]
  erw [comparisonNaturality]
  simp only [Category.assoc]
  conv_rhs =>
    arg 2
    rw [← CategoryTheory.Functor.map_comp]
    rw [coefficientKoszulComparison_augmentation family second complex]
  simp only [tensorRight, Functor.flip_obj_map, Functor.flip_map_app,
    curriedTensor_obj_map, curriedTensor_map_app]
  erw [whisker_exchange_assoc]
  erw [← rightUnitor_inv_naturality_assoc]
  erw [tensorSwap_unit]
  rfl


private theorem coefficientDoubleStageLiftIso_transition_outer
    (first upper lower : ℕ) (order : lower ≤ upper)
    (complex : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ) :
    complexUniverseLift.map
        (((coefficientKoszulTower family).obj
          ((coefficientCompletionStage family first).obj complex)).map (homOfLE order).op) ≫
        (coefficientDoubleStageLiftIso family first lower).hom.app complex =
      (coefficientDoubleStageLiftIso family first upper).hom.app complex ≫
        ((complexUniverseLift.obj complex ⊗ standardKoszulStage
          (fun index => (ULift.up (family index) : ULift.{moduleLevel} ring)) none first) ◁
          standardKoszulTransition
            (fun index => (ULift.up (family index) : ULift.{moduleLevel} ring))
            none upper lower order) := by
  have comparison := coefficientKoszulComparison_transition family upper lower order
    ((coefficientCompletionStage family first).obj complex)
  simp only [coefficientDoubleStageLiftIso, coefficientStageLiftIso, Iso.trans_hom,
    NatTrans.comp_app, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp, Category.comp_id]
  rw [← Category.assoc, comparison]
  simp only [tensorRight, Functor.flip_obj_map, curriedTensor_map_app,
    id_tensorHom, Category.assoc]
  exact congrArg
    (fun morphism => (coefficientKoszulComparison family none upper).hom.app
      ((coefficientCompletionStage family first).obj complex) ≫ morphism)
    (whisker_exchange ((coefficientStageLiftIso family first).hom.app complex)
      (standardKoszulTransition
        (fun index => (ULift.up (family index) : ULift.{moduleLevel} ring))
        none upper lower order))


private theorem coefficientDoubleStageLiftIso_transition_inner
    (first upper lower : ℕ) (order : lower ≤ upper)
    (complex : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ) :
    complexUniverseLift.map
        ((coefficientCompletionStage family first).map
          (((coefficientKoszulTower family).obj complex).map (homOfLE order).op)) ≫
        (coefficientDoubleStageLiftIso family lower first).hom.app complex =
      (coefficientDoubleStageLiftIso family upper first).hom.app complex ≫
        ((complexUniverseLift.obj complex ◁ standardKoszulTransition
          (fun index => (ULift.up (family index) : ULift.{moduleLevel} ring))
          none upper lower order) ▷ standardKoszulStage
            (fun index => (ULift.up (family index) : ULift.{moduleLevel} ring)) none first) := by
  have comparisonNaturality := (coefficientStageLiftIso family first).hom.naturality
    (((coefficientKoszulTower family).obj complex).map (homOfLE order).op)
  simp only [Functor.comp_map, coefficientStageLiftIso] at comparisonNaturality
  simp only [coefficientDoubleStageLiftIso, coefficientStageLiftIso, Iso.trans_hom,
    NatTrans.comp_app, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp, Category.comp_id]
  rw [← Category.assoc]
  erw [comparisonNaturality]
  simp only [Category.assoc]
  have comparison := congrArg
    (fun morphism => (coefficientStageLiftIso family first).hom.app
        ((coefficientCompletionStage family upper).obj complex) ≫
      (tensorRight (standardKoszulStage
        (fun index => (ULift.up (family index) : ULift.{moduleLevel} ring)) none first)).map
        morphism)
    (coefficientKoszulComparison_transition family upper lower order complex)
  simpa only [CategoryTheory.Functor.map_comp, id_tensorHom, Category.assoc,
    Iso.symm_hom, Functor.associator_inv_app, Category.id_comp,
    coefficientStageLiftIso, tensorRight, Functor.flip_obj_map,
    curriedTensor_map_app, NatTrans.comp_app, coefficientCompletionStage,
    Functor.comp_obj, evaluation_obj_obj] using comparison


private theorem coefficientStagesSwap_transition
    (first upper lower : ℕ) (order : lower ≤ upper)
    (complex : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ) :
    (((coefficientKoszulTower family).obj
        ((coefficientCompletionStage family first).obj complex)).map (homOfLE order).op) ≫
        (coefficientStagesSwap family first lower).hom.app complex =
      (coefficientStagesSwap family first upper).hom.app complex ≫
        (coefficientCompletionStage family first).map
          (((coefficientKoszulTower family).obj complex).map (homOfLE order).op) := by
  let := Classical.choose
    (TotalTensorComplex.cochainComplex_symmetricMonoidalCategory (ULift.{moduleLevel} ring))
  apply (complexUniverseLift.{ringLevel, moduleLevel} (A := ring)).map_injective
  simp only [CategoryTheory.Functor.map_comp]
  rw [map_coefficientStagesSwap_hom_app, map_coefficientStagesSwap_hom_app]
  apply (cancel_mono ((coefficientDoubleStageLiftIso family lower first).hom.app complex)).mp
  simp only [coefficientStagesSwapLift, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [coefficientDoubleStageLiftIso_transition_inner family first upper lower order complex]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← Category.assoc (complexUniverseLift.map _),
    coefficientDoubleStageLiftIso_transition_outer family first upper lower order complex]
  simp only [Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Functor.mapIso_hom,
    tensorRightTensor_inv_app, tensorRightTensor_hom_app,
    Functor.flip_map_app, curriedTensor_obj_map, Category.assoc]
  exact congrArg
    (fun morphism => (coefficientDoubleStageLiftIso family first upper).hom.app complex ≫ morphism)
    (tensorSwap_map (complexUniverseLift.obj complex)
      (standardKoszulStage
        (fun index => (ULift.up (family index) : ULift.{moduleLevel} ring)) none first)
      (standardKoszulStage
        (fun index => (ULift.up (family index) : ULift.{moduleLevel} ring)) none upper)
      (standardKoszulStage
        (fun index => (ULift.up (family index) : ULift.{moduleLevel} ring)) none lower)
      (standardKoszulTransition
        (fun index => (ULift.up (family index) : ULift.{moduleLevel} ring))
        none upper lower order))


private def coefficientStageTowerSwap (first : ℕ) :
    coefficientCompletionStage.{ringLevel, moduleLevel} family first ⋙
        coefficientKoszulTower family ≅
      coefficientKoszulTower family ⋙
        (Functor.whiskeringRight ℕᵒᵖ
          (CochainComplex (ModuleCat.{moduleLevel} ring) ℤ)
          (CochainComplex (ModuleCat.{moduleLevel} ring) ℤ)).obj
            (coefficientCompletionStage family first) := by
  refine NatIso.ofComponents (fun complex => ?_) ?_
  · refine NatIso.ofComponents
      (fun stage => (coefficientStagesSwap family first stage.unop).app complex) ?_
    intro upper lower morphism
    have arrow : (homOfLE (leOfHom morphism.unop)).op = morphism := Subsingleton.elim _ _
    simpa only [arrow, Iso.app_hom, Functor.comp_obj, Functor.comp_map,
      Functor.whiskeringRight_obj_obj, evaluation_obj_obj, Opposite.op_unop]
      using coefficientStagesSwap_transition family first
      upper.unop lower.unop (leOfHom morphism.unop) complex
  · intro source target morphism
    apply NatTrans.ext
    funext stage
    exact (coefficientStagesSwap family first stage.unop).hom.naturality morphism


private theorem coefficientStageTowerSwap_unit (first : ℕ)
    (complex : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ) (stage : ℕᵒᵖ) :
    (coefficientKoszulAugmentation family stage.unop).app
        ((coefficientCompletionStage family first).obj complex) ≫
      ((coefficientStageTowerSwap family first).hom.app complex).app stage =
    (coefficientCompletionStage family first).map
      ((coefficientKoszulAugmentation family stage.unop).app complex) := by
  simpa only [coefficientStageTowerSwap, NatIso.ofComponents_hom_app, Iso.app_hom]
    using coefficientStagesSwap_unit family first stage.unop complex


end


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
open KoszulCoefficientTower KoszulCompletion CountableMilnorTower

universe ringLevel moduleLevel

variable {ring : Type ringLevel} [CommRing ring] {rank : ℕ} (family : Fin rank → ring)

private def coefficientStageCompletionObjectIso (stage : ℕ)
    (complex : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ) :
    (coefficientCompletionComplex family).obj ((coefficientCompletionStage family stage).obj
      complex) ≅
      (coefficientCompletionStage family stage).obj ((coefficientCompletionComplex family).obj
        complex) :=
  countableMilnorFunctor.mapIso ((coefficientStageTowerSwap family stage).app complex) ≪≫
    (coefficientStageMilnorObjectIso family stage ((coefficientKoszulTower family).obj
      complex)).symm

private theorem stage_quasiIso_of_pointwise_exchange (stage : ℕ)
    (complex : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ)
    (exchange :
      (coefficientCompletionComplex family).obj ((coefficientCompletionStage family stage).obj
        complex) ≅
        (coefficientCompletionStage family stage).obj ((coefficientCompletionComplex family).obj
          complex))
    (unitCompatibility :
      (coefficientCompletionUnit family).app ((coefficientCompletionStage family stage).obj complex)
        ≫
          exchange.hom =
        (coefficientCompletionStage family stage).map ((coefficientCompletionUnit family).app
          complex))
    [QuasiIso ((coefficientCompletionUnit family).app
      ((coefficientCompletionStage family stage).obj complex))] :
    QuasiIso (((coefficientKoszulTower family).map
      ((coefficientCompletionUnit family).app complex)).app ⟨stage⟩) := by
  have composed : QuasiIso
      ((coefficientCompletionUnit family).app ((coefficientCompletionStage family stage).obj
        complex) ≫
        exchange.hom) := inferInstance
  rw [unitCompatibility] at composed
  exact composed




private theorem completionUnit_towerSwap (stage : ℕ)
    (complex : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ) :
    (coefficientCompletionUnit family).app ((coefficientCompletionStage family stage).obj complex) ≫
        countableMilnorFunctor.map ((coefficientStageTowerSwap family stage).hom.app complex) =
      (stageWhiskeredAugmentation family stage complex).augmentationMap := by
  let augmented : TowerAugmentation ((coefficientKoszulTower family).obj
      ((coefficientCompletionStage family stage).obj complex)) :=
    { source := (coefficientCompletionStage family stage).obj complex
      app index := (coefficientKoszulAugmentation family index).app
        ((coefficientCompletionStage family stage).obj complex)
      naturality index := coefficientKoszulAugmentation_transition family
        ((coefficientCompletionStage family stage).obj complex) (index + 1) index (Nat.le_succ
          index) }
  have naturality := augmented.augmentationMap_naturality
    (stageWhiskeredAugmentation family stage complex) (𝟙 _)
    ((coefficientStageTowerSwap family stage).hom.app complex) (fun index => by
      simpa only [stageWhiskeredAugmentation, Category.id_comp]
        using (coefficientStageTowerSwap_unit family stage complex ⟨index⟩).symm)
  simpa only [Category.id_comp, augmented, coefficientCompletionUnit, augmentationNatTrans,
    Functor.id_obj, Functor.comp_obj, Functor.whiskeringRight_obj_obj] using naturality.symm

private theorem completionObjectIso_unit_of_milnorAugmentation (stage : ℕ)
    (complex : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ)
    (preservesAugmentation :
      (coefficientCompletionStage family stage).map ((coefficientCompletionUnit family).app complex)
        ≫
          (coefficientStageMilnorObjectIso family stage ((coefficientKoszulTower family).obj
            complex)).hom =
        (stageWhiskeredAugmentation family stage complex).augmentationMap) :
    (coefficientCompletionUnit family).app ((coefficientCompletionStage family stage).obj complex) ≫
        (coefficientStageCompletionObjectIso family stage complex).hom =
      (coefficientCompletionStage family stage).map ((coefficientCompletionUnit family).app complex)
        := by
  simp only [coefficientStageCompletionObjectIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_hom]
  rw [← Category.assoc]
  rw [completionUnit_towerSwap family stage complex, ← preservesAugmentation]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]


end

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance 2000] HasDerivedCategory.standard

universe ringLevel moduleLevel

namespace FiniteStageAudit

open AdicKoszul (tensor_map_smul_id)

variable {ring : Type ringLevel} [CommRing ring]

private theorem isDerivedComplete_of_nilpotent_scalars
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max ringLevel moduleLevel} ring))]
    (ideal : Ideal ring)
    (object : DerivedCategory (ModuleCat.{max ringLevel moduleLevel} ring))
    (nilpotent : ∀ scalar ∈ ideal, ∃ exponent : ℕ,
      scalar ^ exponent • 𝟙 object = (0 : object ⟶ object)) :
    IsDerivedComplete ideal object := by
  intro scalar membership
  obtain ⟨exponent, vanishing⟩ := nilpotent scalar membership
  exact isDerivedCompleteAt_of_isNilpotent
    ⟨exponent, End.ext (by rw [smul_id_pow, End.zero_asHom]; exact vanishing)⟩

private theorem tensorKoszulStage_isDerivedComplete
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{ringLevel} ring))]
    {rank : ℕ} (family : Fin rank → ring)
    (transition : ∀ stage : ℕ,
      Koszul.seqComplex (fun index => family index ^ (stage + 2)) ⟶
        Koszul.seqComplex (fun index => family index ^ (stage + 1)))
    (tensor : CochainComplex.DerivedTensor.DerivedTensorProduct ring)
    (object : DerivedCategory (ModuleCat.{ringLevel} ring)) (stage : ℕ) :
    IsDerivedComplete (Ideal.span (Set.range family))
      ((tensor.tensor.obj object).obj ((AdicKoszul.koszulPowerSystem family transition).obj
        ⟨stage⟩)) := by
  apply isDerivedComplete_of_nilpotent_scalars.{ringLevel, 0}
  intro scalar membership
  obtain ⟨exponent, vanishing⟩ :=
    AdicKoszul.koszulPower_smul_id_nilpotent (n := stage) family transition scalar membership
  refine ⟨exponent, ?_⟩
  have mapped := congrArg (tensor.tensor.obj object).map vanishing
  erw [tensor_map_smul_id tensor.toGeneral, Functor.map_zero] at mapped
  exact mapped


private theorem coefficientKoszulStage_isDerivedComplete
    {rank : ℕ} (family : Fin rank → ring)
    (tensor : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{moduleLevel} ring))
    (stage : ℕ) (complex : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ) :
    IsDerivedComplete (Ideal.span (Set.range family))
      (DerivedCategory.Q.obj
        ((KoszulCompletion.coefficientCompletionStage family stage).obj complex)) := by
  apply _root_.isDerivedComplete_of_universeLift
  have spanEquality :
      (Ideal.span (Set.range family)).map
        (ULift.ringEquiv.symm : ring ≃+* ULift.{moduleLevel} ring).toRingHom =
      Ideal.span (Set.range fun index => (ULift.up (family index) : ULift.{moduleLevel} ring)) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  rw [spanEquality]
  apply isDerivedComplete_of_nilpotent_scalars.{max ringLevel moduleLevel, 0}
  intro scalar membership
  let liftedFamily := fun index => (ULift.up (family index) : ULift.{moduleLevel} ring)
  let transition := fun power =>
    AdicKoszul.koszulPowerTransition liftedFamily (power + 1) power (Nat.le_succ power)
  obtain ⟨exponent, vanishing⟩ :=
    AdicKoszul.koszulPower_smul_id_nilpotent (n := stage) liftedFamily transition scalar
      membership
  let liftedObject := (AdicKoszul.derivedUniverseLift ring).obj (DerivedCategory.Q.obj complex)
  have mapped := congrArg (tensor.tensor.obj liftedObject).map vanishing
  erw [tensor_map_smul_id tensor.toGeneral, Functor.map_zero] at mapped
  let comparison := KoszulCompletion.coefficientStageComparisonIso family tensor stage complex
  refine ⟨exponent, ?_⟩
  apply (cancel_mono comparison.hom).mp
  calc
    (scalar ^ exponent • 𝟙 _) ≫ comparison.hom =
        comparison.hom ≫ (scalar ^ exponent • 𝟙 _) := by
      simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]
    _ = 0 ≫ comparison.hom := by
      erw [mapped]
      simp


private theorem coefficientCompletionUnit_stage_quasiIso
    {rank : ℕ} (family : Fin rank → ring)
    (tensor : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{moduleLevel} ring))
    (stage : ℕ) (complex : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ) :
    QuasiIso ((KoszulCompletion.coefficientCompletionUnit family).app
      ((KoszulCompletion.coefficientCompletionStage family stage).obj complex)) :=
  AdicKoszul.coefficientCompletionUnit_quasiIso_of_isDerivedComplete family _
    (coefficientKoszulStage_isDerivedComplete family tensor stage complex)


end FiniteStageAudit

end

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open KoszulCompletion KoszulCoefficientTower
attribute [local instance 2000] HasDerivedCategory.standard
universe ringLevel moduleLevel
variable {ring : Type ringLevel} [CommRing ring] {rank : ℕ} (family : Fin rank → ring)

private theorem completion_map_unit_isIso_of_stage_quasiIso
    (stageQuasiIso : ∀ (complex : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ)
      (stage : ℕ), QuasiIso
        (((KoszulCoefficientTower.coefficientKoszulTower family).map
          ((coefficientCompletionUnit family).app complex)).app ⟨stage⟩))
    (object : DerivedCategory (ModuleCat.{moduleLevel} ring)) :
    IsIso ((completionFunctor family).map ((completionUnit family).app object)) := by
  let transformation := Functor.whiskerRight (completionUnit family) (completionFunctor family)
  show IsIso (transformation.app object)
  rw [← NatTrans.isIso_app_iff_of_iso transformation
    ((DerivedCategory.Q (C := ModuleCat.{moduleLevel} ring)).objObjPreimageIso object)]
  let complex := (DerivedCategory.Q (C := ModuleCat.{moduleLevel} ring)).objPreimage object
  have mappedQuasiIso : QuasiIso
      ((coefficientCompletionComplex family).map ((coefficientCompletionUnit family).app complex))
        :=
    CountableMilnorTower.map_quasiIso_and_milnor_triangle.1 _ (stageQuasiIso complex)
  have mappedIso : IsIso ((completionFunctor family).map
      (DerivedCategory.Q.map ((coefficientCompletionUnit family).app complex))) :=
    (NatIso.isIso_map_iff (completionLocalIso family)
      ((coefficientCompletionUnit family).app complex)).mpr (by
        show IsIso (DerivedCategory.Q.map
          ((coefficientCompletionComplex family).map ((coefficientCompletionUnit family).app
            complex)))
        infer_instance)
  show IsIso ((completionFunctor family).map
    ((completionUnit family).app (DerivedCategory.Q.obj complex)))
  rw [completionUnit_representative, Functor.map_comp]
  infer_instance

/-- For a derived tensor product `tensor`, the Koszul completion functor of `family` sends the
completion unit at every object of `D(R)` to an isomorphism. -/
public theorem canonicalCompletion_map_unit_isIso
    (tensor : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{moduleLevel} ring))
    (object : DerivedCategory (ModuleCat.{moduleLevel} ring)) :
    IsIso ((completionFunctor family).map ((completionUnit family).app object)) := by
  refine completion_map_unit_isIso_of_stage_quasiIso family ?_ object
  intro complex stage
  let := FiniteStageAudit.coefficientCompletionUnit_stage_quasiIso family tensor stage complex
  exact stage_quasiIso_of_pointwise_exchange family stage complex
    (coefficientStageCompletionObjectIso family stage complex)
    (completionObjectIso_unit_of_milnorAugmentation family stage complex
      (coefficientStageMilnorObjectIso_augmentation family stage complex))

end

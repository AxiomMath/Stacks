module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Pi
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedColimits
public import StacksFrontier.Homology.TensorComplex.ExactFunctor
public import StacksFrontier.Homology.DerivedComplete.AdicDerivedCompletionKoszul
public import StacksFrontier.Homology.TensorComplex.Monoidal

/-!
# Koszul coefficient stages and the Milnor construction

The coefficient Koszul stages preserve countable products and mapping cocones, so they commute with
the Milnor mapping fiber of a tower, compatibly with augmentations. These comparisons are used in
`AdicDerivedCompletion.CompletionUnitIsIso` to show that the Koszul completion functor inverts its
unit.
-/


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
open KoszulCoefficientTower KoszulCompletion

universe ringLevel moduleLevel

variable {ring : Type ringLevel} [CommRing ring] {rank : ℕ} (family : Fin rank → ring)

private def degreeComponents (degree : ℤ) :
    CochainComplex (ModuleCat.{moduleLevel} ring) ℤ ⥤
      (Finset (Fin rank) → ModuleCat.{moduleLevel} ring) :=
  Functor.pi' fun subset =>
    HomologicalComplex.eval (ModuleCat.{moduleLevel} ring) (ComplexShape.up ℤ)
      (degree + subset.card)

private def stageDegreeIso (stage : ℕ) (degree : ℤ) :
    coefficientCompletionStage.{ringLevel, moduleLevel} family stage ⋙
        HomologicalComplex.eval (ModuleCat.{moduleLevel} ring) (ComplexShape.up ℤ) degree ≅
      degreeComponents.{ringLevel, moduleLevel} (ring := ring) (rank := rank) degree ⋙
        Pi.functor (Finset (Fin rank)) := by
  refine NatIso.ofComponents (fun complex =>
    (ModuleCat.piIsoPi (fun subset : Finset (Fin rank) => complex.X (degree + subset.card))).symm)
      ?_
  intro source target morphism
  change coefficientMapTerm (r := rank) morphism degree ≫
      (ModuleCat.piIsoPi (fun subset : Finset (Fin rank) => target.X (degree + subset.card))).inv =
    (ModuleCat.piIsoPi (fun subset : Finset (Fin rank) => source.X (degree + subset.card))).inv ≫
      Limits.Pi.map (fun subset : Finset (Fin rank) => morphism.f (degree + subset.card))
  apply Pi.hom_ext
  intro subset
  simp only [Category.assoc, ModuleCat.piIsoPi_inv_kernel_ι, Pi.map_π]
  rw [← Category.assoc, ModuleCat.piIsoPi_inv_kernel_ι]
  rfl


private instance degreeComponents_preservesProducts (degree : ℤ) :
    PreservesLimitsOfShape (Discrete ℕ)
      (degreeComponents.{ringLevel, moduleLevel} (ring := ring) (rank := rank) degree) := by
  let comparison := piEquivalenceFunctorDiscrete (Finset (Fin rank)) (ModuleCat.{moduleLevel} ring)
  have : PreservesLimitsOfShape (Discrete ℕ)
      (degreeComponents.{ringLevel, moduleLevel} (ring := ring) (rank := rank) degree ⋙
        comparison.functor) := by
    apply preservesLimitsOfShape_of_evaluation
    intro subset
    change PreservesLimitsOfShape (Discrete ℕ)
      (HomologicalComplex.eval (ModuleCat.{moduleLevel} ring) (ComplexShape.up ℤ)
        (degree + subset.as.card))
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves
    (degreeComponents.{ringLevel, moduleLevel} (ring := ring) (rank := rank) degree)
    comparison.functor

private instance pi_preservesProducts :
    PreservesLimitsOfShape (Discrete ℕ)
      (Pi.functor (C := ModuleCat.{moduleLevel} ring) (Finset (Fin rank))) :=
  preservesLimitsOfShape_of_natIso
    (piEquivalenceFunctorDiscreteCompLim (C := ModuleCat.{moduleLevel} ring) (Finset (Fin rank)))

private instance stage_preservesProducts (stage : ℕ) :
    PreservesLimitsOfShape (Discrete ℕ)
      (coefficientCompletionStage.{ringLevel, moduleLevel} family stage) := by
  apply HomologicalComplex.preservesLimitsOfShape_of_eval
  intro degree
  exact preservesLimitsOfShape_of_natIso (stageDegreeIso family stage degree).symm


private instance stage_additive (stage : ℕ) :
    (coefficientCompletionStage.{ringLevel, moduleLevel} family stage).Additive where
  map_add := by
    intro source target left right
    apply HomologicalComplex.hom_ext
    intro degree
    rfl


private def coefficientStageProductIso (stage : ℕ)
    (complexes : ℕ → CochainComplex (ModuleCat.{moduleLevel} ring) ℤ) :
    (coefficientCompletionStage family stage).obj (∏ᶜ complexes) ≅
      ∏ᶜ (fun index => (coefficientCompletionStage family stage).obj (complexes index)) :=
  PreservesProduct.iso (coefficientCompletionStage family stage) complexes

private theorem coefficientStageProductIso_π (stage : ℕ)
    (complexes : ℕ → CochainComplex (ModuleCat.{moduleLevel} ring) ℤ) (index : ℕ) :
    (coefficientStageProductIso family stage complexes).hom ≫
        Limits.Pi.π (fun index => (coefficientCompletionStage family stage).obj (complexes index))
          index =
      (coefficientCompletionStage family stage).map (Limits.Pi.π complexes index) :=
  piComparison_comp_π _ _ _


end


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open KoszulCoefficientTower KoszulCompletion

universe ringLevel moduleLevel targetRingLevel targetModuleLevel

variable {ring : Type ringLevel} [CommRing ring]
  {targetRing : Type targetRingLevel} [CommRing targetRing]

private def coconeCongrIso
    {source target source' target' : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ}
    {morphism : source ⟶ target} {morphism' : source' ⟶ target'}
    (left : source ≅ source') (right : target ≅ target')
    (commutes : left.hom ≫ morphism' = morphism ≫ right.hom) :
    CochainComplex.mappingCocone morphism ≅ CochainComplex.mappingCocone morphism' :=
  (shiftFunctor (CochainComplex (ModuleCat.{moduleLevel} ring) ℤ) (-1 : ℤ)).mapIso
    (HomologicalComplex.homotopyCofiber.mapArrowIso morphism morphism'
      (fun degree => ⟨degree - 1, by simp⟩) (Arrow.isoMk left right commutes))

private def coconeComparisonOfCone
    (transformer : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ ⥤
      CochainComplex (ModuleCat.{targetModuleLevel} targetRing) ℤ)
    [transformer.CommShift ℤ]
    (coneComparison : ∀ {source target : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ}
      (morphism : source ⟶ target),
      transformer.obj (CochainComplex.mappingCone morphism) ≅
        CochainComplex.mappingCone (transformer.map morphism))
    {source target : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ}
    (morphism : source ⟶ target) :
    transformer.obj (CochainComplex.mappingCocone morphism) ≅
      CochainComplex.mappingCocone (transformer.map morphism) :=
  (transformer.commShiftIso (-1 : ℤ)).app (CochainComplex.mappingCone morphism) ≪≫
    (shiftFunctor (CochainComplex (ModuleCat.{targetModuleLevel} targetRing) ℤ) (-1 : ℤ)).mapIso
      (coneComparison morphism)

private def coconeComparisonOfModuleFunctor
    (moduleTransformer : ModuleCat.{moduleLevel} ring ⥤ ModuleCat.{targetModuleLevel} targetRing)
    [moduleTransformer.Additive]
    {source target : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ}
    (morphism : source ⟶ target) :
    (moduleTransformer.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (CochainComplex.mappingCocone morphism) ≅
      CochainComplex.mappingCocone
        ((moduleTransformer.mapHomologicalComplex (ComplexShape.up ℤ)).map morphism) :=
  coconeComparisonOfCone (moduleTransformer.mapHomologicalComplex (ComplexShape.up ℤ))
    (fun map => CochainComplex.mappingCone.mapHomologicalComplexIso map moduleTransformer) morphism

private def tensorCoconeComparison
    (factor : CochainComplex (ModuleCat.{ringLevel} ring) ℤ)
    {source target : CochainComplex (ModuleCat.{ringLevel} ring) ℤ}
    (morphism : source ⟶ target) :
    (tensorRight factor).obj (CochainComplex.mappingCocone morphism) ≅
      CochainComplex.mappingCocone ((tensorRight factor).map morphism) := by
  letI : (TrightCochain factor).CommShift ℤ := by unfold TrightCochain; infer_instance
  exact coconeComparisonOfCone (TrightCochain factor)
    (fun map => TrightCochain_mappingCone_iso factor map) morphism


private def coefficientStageCoconeComparison
    {rank : ℕ} (family : Fin rank → ring) (stage : ℕ)
    {source target : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ}
    (morphism : source ⟶ target) :
    (coefficientCompletionStage family stage).obj (CochainComplex.mappingCocone morphism) ≅
      CochainComplex.mappingCocone ((coefficientCompletionStage family stage).map morphism) := by
  let lift := complexUniverseLift.{ringLevel, moduleLevel} (A := ring)
  let stageFunctor := coefficientCompletionStage.{ringLevel, moduleLevel} family stage
  let factor := standardKoszulStage
    (fun index => (ULift.up (family index) : ULift.{moduleLevel} ring)) none stage
  let comparison : stageFunctor ⋙ lift ≅ lift ⋙ tensorRight factor :=
    coefficientKoszulComparison family none stage
  letI : lift.Full := by dsimp [lift]; infer_instance
  letI : lift.Faithful := by dsimp [lift]; infer_instance
  apply lift.preimageIso
  exact (comparison.app (CochainComplex.mappingCocone morphism)) ≪≫
    (tensorRight factor).mapIso
      (coconeComparisonOfModuleFunctor (AdicKoszul.moduleUniverseLift ring) morphism) ≪≫
    tensorCoconeComparison factor (lift.map morphism) ≪≫
    coconeCongrIso (comparison.app source).symm (comparison.app target).symm
      (comparison.inv.naturality morphism).symm ≪≫
    (coconeComparisonOfModuleFunctor (AdicKoszul.moduleUniverseLift ring)
      (stageFunctor.map morphism)).symm


end


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
open CountableMilnorTower

universe ringLevel moduleLevel targetRingLevel targetModuleLevel

variable {ring : Type ringLevel} [CommRing ring]
  {targetRing : Type targetRingLevel} [CommRing targetRing]
  (transformer : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ ⥤
    CochainComplex (ModuleCat.{targetModuleLevel} targetRing) ℤ)
  [transformer.Additive] [PreservesLimitsOfShape (Discrete ℕ) transformer]

private def milnorProductIso (tower : Tower.{ringLevel, moduleLevel} (A := ring)) :
    transformer.obj (towerProductObj tower) ≅ towerProductObj (tower ⋙ transformer) :=
  PreservesProduct.iso transformer (fun index : ℕ => tower.obj ⟨index⟩)

omit [transformer.Additive] in
private theorem milnorProductIso_π (tower : Tower.{ringLevel, moduleLevel} (A := ring))
    (index : ℕ) :
    (milnorProductIso transformer tower).hom ≫
        Limits.Pi.π (fun index : ℕ => (tower ⋙ transformer).obj ⟨index⟩) index =
      transformer.map (Limits.Pi.π (fun index : ℕ => tower.obj ⟨index⟩) index) :=
  piComparison_comp_π _ _ _

private theorem milnorProductIso_difference
    (tower : Tower.{ringLevel, moduleLevel} (A := ring)) :
    transformer.map (oneMinusShift tower) ≫ (milnorProductIso transformer tower).hom =
      (milnorProductIso transformer tower).hom ≫ oneMinusShift (tower ⋙ transformer) := by
  apply Limits.Pi.hom_ext
  intro index
  simp only [Category.assoc, milnorProductIso_π, oneMinusShift_π, Preadditive.comp_sub]
  rw [← Category.assoc, milnorProductIso_π]
  rw [← CategoryTheory.Functor.map_comp, oneMinusShift_π,
    Functor.map_sub, CategoryTheory.Functor.map_comp]
  rfl


omit [transformer.Additive] in
private theorem milnorProductIso_naturality
    {source target : Tower.{ringLevel, moduleLevel} (A := ring)} (morphism : source ⟶ target) :
    transformer.map (towerProductMap morphism) ≫ (milnorProductIso transformer target).hom =
      (milnorProductIso transformer source).hom ≫
        towerProductMap (Functor.whiskerRight morphism transformer) := by
  apply Limits.Pi.hom_ext
  intro index
  simp only [Category.assoc, milnorProductIso_π, towerProductMap, Limits.Pi.map_π,
    Functor.whiskerRight_app]
  rw [← Category.assoc, milnorProductIso_π]
  rw [← CategoryTheory.Functor.map_comp, Limits.Pi.map_π, CategoryTheory.Functor.map_comp]


private def mappedDifferenceCoconeIso
    (tower : Tower.{ringLevel, moduleLevel} (A := ring)) :
    CochainComplex.mappingCocone (transformer.map (oneMinusShift tower)) ≅
      countableMilnorFunctor.obj (tower ⋙ transformer) :=
  coconeCongrIso (milnorProductIso transformer tower) (milnorProductIso transformer tower)
    (milnorProductIso_difference transformer tower).symm


private def milnorObjectIsoOfCoconeComparison
    (coconeComparison : ∀ {source target : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ}
      (morphism : source ⟶ target),
      transformer.obj (CochainComplex.mappingCocone morphism) ≅
        CochainComplex.mappingCocone (transformer.map morphism))
    (tower : Tower.{ringLevel, moduleLevel} (A := ring)) :
    transformer.obj (countableMilnorFunctor.obj tower) ≅
      countableMilnorFunctor.obj (tower ⋙ transformer) :=
  coconeComparison (oneMinusShift tower) ≪≫ mappedDifferenceCoconeIso transformer tower


private def milnorObjectIsoOfConeComparison [transformer.CommShift ℤ]
    (coneComparison : ∀ {source target : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ}
      (morphism : source ⟶ target),
      transformer.obj (CochainComplex.mappingCone morphism) ≅
        CochainComplex.mappingCone (transformer.map morphism))
    (tower : Tower.{ringLevel, moduleLevel} (A := ring)) :
    transformer.obj (countableMilnorFunctor.obj tower) ≅
      countableMilnorFunctor.obj (tower ⋙ transformer) :=
  (transformer.commShiftIso (-1 : ℤ)).app (CochainComplex.mappingCone (oneMinusShift tower)) ≪≫
    (shiftFunctor (CochainComplex (ModuleCat.{targetModuleLevel} targetRing) ℤ) (-1 : ℤ)).mapIso
      (coneComparison (oneMinusShift tower)) ≪≫
    mappedDifferenceCoconeIso transformer tower


private def milnorMapHomologicalComplexIso
    (moduleTransformer : ModuleCat.{moduleLevel} ring ⥤
      ModuleCat.{targetModuleLevel} targetRing)
    [moduleTransformer.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) moduleTransformer]
    (tower : Tower.{ringLevel, moduleLevel} (A := ring)) :
    (moduleTransformer.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (countableMilnorFunctor.obj tower) ≅
      countableMilnorFunctor.obj
        (tower ⋙ moduleTransformer.mapHomologicalComplex (ComplexShape.up ℤ)) :=
  milnorObjectIsoOfConeComparison
    (moduleTransformer.mapHomologicalComplex (ComplexShape.up ℤ))
    (fun morphism => CochainComplex.mappingCone.mapHomologicalComplexIso morphism moduleTransformer)
    tower


end

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
open KoszulCoefficientTower KoszulCompletion CountableMilnorTower

universe ringLevel moduleLevel

variable {ring : Type ringLevel} [CommRing ring] {rank : ℕ} (family : Fin rank → ring)

public def coefficientStageMilnorObjectIso (stage : ℕ)
    (tower : Tower.{ringLevel, moduleLevel} (A := ring)) :
    (coefficientCompletionStage family stage).obj (countableMilnorFunctor.obj tower) ≅
      countableMilnorFunctor.obj (tower ⋙ coefficientCompletionStage family stage) :=
  milnorObjectIsoOfCoconeComparison (coefficientCompletionStage family stage)
    (fun morphism => coefficientStageCoconeComparison family stage morphism) tower


@[expose] public def stageWhiskeredAugmentation (stage : ℕ)
    (complex : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ) :
    TowerAugmentation ((coefficientKoszulTower family).obj complex ⋙
      coefficientCompletionStage family stage) where
  source := (coefficientCompletionStage family stage).obj complex
  app index := (coefficientCompletionStage family stage).map
    ((coefficientKoszulAugmentation family index).app complex)
  naturality index := by
    change (coefficientCompletionStage family stage).map _ ≫
        (coefficientCompletionStage family stage).map _ = _
    rw [← CategoryTheory.Functor.map_comp,
      coefficientKoszulAugmentation_transition family complex (index + 1) index (Nat.le_succ index)]


end

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe ringLevel moduleLevel targetRingLevel targetModuleLevel

variable {ring : Type ringLevel} [CommRing ring]
  {targetRing : Type targetRingLevel} [CommRing targetRing]

private theorem coconeComparisonOfModuleFunctor_inl
    (moduleTransformer : ModuleCat.{moduleLevel} ring ⥤ ModuleCat.{targetModuleLevel} targetRing)
    [moduleTransformer.Additive]
    {source target : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ}
    (morphism : source ⟶ target) (degree : ℤ) :
    moduleTransformer.map ((CochainComplex.mappingCocone.inl morphism).v
        degree degree (add_zero degree)) ≫
      (coconeComparisonOfModuleFunctor moduleTransformer morphism).hom.f degree =
    (CochainComplex.mappingCocone.inl
      ((moduleTransformer.mapHomologicalComplex (ComplexShape.up ℤ)).map morphism)).v
        degree degree (add_zero degree) := by
  simp only [coconeComparisonOfModuleFunctor, coconeComparisonOfCone, Iso.trans_hom,
    Iso.app_hom, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
    Functor.mapIso_hom]
  change _ ≫ (CochainComplex.mappingCone.mapHomologicalComplexIso morphism moduleTransformer).hom.f
    (degree + (-1 : ℤ)) = _
  dsimp only [CochainComplex.mappingCone.mapHomologicalComplexIso,
    HomologicalComplex.Hom.isoOfComponents]
  rw [CochainComplex.mappingCone.mapHomologicalComplexXIso_eq morphism moduleTransformer
    (degree + -1) degree (by omega)]
  simp only [CochainComplex.mappingCone.mapHomologicalComplexXIso'_hom,
    Preadditive.comp_add, ← moduleTransformer.map_comp_assoc]
  simp [CochainComplex.mappingCocone.inl,
    CochainComplex.HomComplex.Cochain.rightShift_v (n := -1)
      _ _ _ _ degree _ _ (degree + -1) (by omega),
    CochainComplex.mappingCone.inl_v_fst_v,
    CochainComplex.mappingCone.inl_v_snd_v]


/-- An additive functor sends a zero composite to a zero composite. -/
private theorem map_comp_eq_zero_of_comp_eq_zero {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (functor : C ⥤ D) [functor.Additive]
    {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (zeroComposite : f ≫ g = 0) :
    functor.map f ≫ functor.map g = 0 := by
  rw [← functor.map_comp, zeroComposite, functor.map_zero]

private theorem cocone_pureLift_f
    {source target input : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ}
    (morphism : source ⟶ target) (augmentation : input ⟶ source)
    (zeroComposite : augmentation ≫ morphism = 0) (degree : ℤ) :
    (CochainComplex.mappingCocone.lift morphism augmentation 0 (by simp [zeroComposite])).f degree =
      augmentation.f degree ≫
        (CochainComplex.mappingCocone.inl morphism).v degree degree (add_zero degree) := by
  have identity := congrArg (fun component =>
    (CochainComplex.mappingCocone.lift morphism augmentation 0 (by simp [zeroComposite])).f
      degree ≫ component)
    (CochainComplex.mappingCocone.id_X morphism degree (degree + -1) rfl)
  simpa only [Preadditive.comp_add, ← Category.assoc,
    CochainComplex.mappingCocone.lift_f_fst_f,
    CochainComplex.mappingCocone.lift_f_snd_v,
    CochainComplex.HomComplex.Cochain.zero_v, zero_comp, add_zero, Category.comp_id]
    using identity.symm

private theorem coconeComparisonOfModuleFunctor_pureLift
    (moduleTransformer : ModuleCat.{moduleLevel} ring ⥤ ModuleCat.{targetModuleLevel} targetRing)
    [moduleTransformer.Additive]
    {source target input : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ}
    (morphism : source ⟶ target) (augmentation : input ⟶ source)
    (zeroComposite : augmentation ≫ morphism = 0) :
    (moduleTransformer.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (CochainComplex.mappingCocone.lift morphism augmentation 0 (by simp [zeroComposite])) ≫
      (coconeComparisonOfModuleFunctor moduleTransformer morphism).hom =
    CochainComplex.mappingCocone.lift
      ((moduleTransformer.mapHomologicalComplex (ComplexShape.up ℤ)).map morphism)
      ((moduleTransformer.mapHomologicalComplex (ComplexShape.up ℤ)).map augmentation) 0
      (by simp [map_comp_eq_zero_of_comp_eq_zero _ zeroComposite]) := by
  have zeroMapped := map_comp_eq_zero_of_comp_eq_zero
    (moduleTransformer.mapHomologicalComplex (ComplexShape.up ℤ)) zeroComposite
  apply HomologicalComplex.hom_ext
  intro degree
  rw [HomologicalComplex.comp_f, cocone_pureLift_f _ _ zeroMapped degree]
  change moduleTransformer.map _ ≫ _ = moduleTransformer.map _ ≫ _
  rw [cocone_pureLift_f morphism augmentation zeroComposite degree,
    Functor.map_comp, Category.assoc, coconeComparisonOfModuleFunctor_inl]


private theorem tensorCoconePureLift_shiftComparison
    (factor : CochainComplex (ModuleCat.{ringLevel} ring) ℤ)
    {source target input : CochainComplex (ModuleCat.{ringLevel} ring) ℤ}
    (morphism : source ⟶ target) (augmentation : input ⟶ source)
    (zeroComposite : augmentation ≫ morphism = 0) :
    (TrightCochain factor).map
        (CochainComplex.mappingCocone.lift morphism augmentation 0 (by simp [zeroComposite])) ≫
      (CochainComplex.mapBifunctorShift₁Iso (CochainComplex.mappingCone morphism) factor
        (curriedTensor (ModuleCat.{ringLevel} ring)) (-1)).hom =
    CochainComplex.mappingCocone.lift ((TrightCochain factor).map morphism)
      ((TrightCochain factor).map augmentation) 0
      (by simp [map_comp_eq_zero_of_comp_eq_zero _ zeroComposite]) ≫
      (shiftFunctor (CochainComplex (ModuleCat.{ringLevel} ring) ℤ) (-1 : ℤ)).map
        (TrightCochain_mappingCone_iso factor morphism).inv := by
  have zeroMapped := map_comp_eq_zero_of_comp_eq_zero (TrightCochain factor) zeroComposite
  apply HomologicalComplex.hom_ext
  intro degree
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    cocone_pureLift_f _ _ zeroMapped degree]
  have inlDescription :
      (CochainComplex.mappingCocone.inl ((TrightCochain factor).map morphism)).v
          degree degree (add_zero degree) ≫
        ((shiftFunctor (CochainComplex (ModuleCat.{ringLevel} ring) ℤ) (-1 : ℤ)).map
          (TrightCochain_mappingCone_iso factor morphism).inv).f degree =
      HomologicalComplex.mapBifunctorDesc (fun leftDegree rightDegree
        (_ : leftDegree + rightDegree = degree) =>
        ((curriedTensor (ModuleCat.{ringLevel} ring)).map
          ((CochainComplex.mappingCone.inl morphism).v leftDegree (leftDegree - 1)
            (by omega))).app (factor.X rightDegree) ≫
          HomologicalComplex.ιMapBifunctor (CochainComplex.mappingCone morphism) factor
            (curriedTensor (ModuleCat.{ringLevel} ring)) (ComplexShape.up ℤ)
            (leftDegree - 1) rightDegree (degree + -1) (by
              change (leftDegree - 1) + rightDegree = degree + -1
              omega)) := by
    simp only [CochainComplex.mappingCocone.inl,
      CochainComplex.HomComplex.Cochain.rightShift_v (n := -1)
        _ _ _ _ degree _ _ (degree + -1) (by omega)]
    change (CochainComplex.mappingCone.inl ((TrightCochain factor).map morphism)).v
      degree (degree + -1) (by omega) ≫
        (TrightCochain_mappingCone_iso factor morphism).inv.f (degree + -1) = _
    simp only [TrightCochain_mappingCone_iso]
    unfold TrightCochain_mappingCone_inv
    rw [CochainComplex.mappingCone.inl_v_desc_f]
    rfl
  rw [Category.assoc, inlDescription]
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro leftDegree rightDegree degreeEquality
  change HomologicalComplex.ιMapBifunctor input factor
      (curriedTensor (ModuleCat.{ringLevel} ring)) (ComplexShape.up ℤ)
      leftDegree rightDegree degree degreeEquality ≫ _ = _
  have tensorMap {left right : CochainComplex (ModuleCat.{ringLevel} ring) ℤ}
      (map : left ⟶ right) : (TrightCochain factor).map map =
      HomologicalComplex.mapBifunctorMap map (𝟙 factor)
        (curriedTensor (ModuleCat.{ringLevel} ring)) (ComplexShape.up ℤ) := rfl
  rw [tensorMap, tensorMap]
  simp only [← Category.assoc, HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f, Category.assoc]
  rw [HomologicalComplex.ι_mapBifunctorDesc]
  erw [CochainComplex.ι_mapBifunctorShift₁Iso_hom_f
      (CochainComplex.mappingCone morphism) factor (curriedTensor (ModuleCat.{ringLevel} ring))
      (-1) leftDegree rightDegree degree degreeEquality (leftDegree - 1) (degree + -1)
      (by omega) rfl]
  rw [cocone_pureLift_f morphism augmentation zeroComposite leftDegree]
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
  simp only [curriedTensor_obj_obj, Int.reduceNeg, CochainComplex.shiftFunctor_obj_X',
    curriedTensor_map_app, CochainComplex.mappingCocone.inl,
    CochainComplex.HomComplex.Cochain.rightShift_v (n := -1)
      _ _ _ _ leftDegree _ _ (leftDegree - 1) (by omega),
    CochainComplex.shiftFunctor_obj_X, CochainComplex.shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, Functor.map_comp, NatTrans.comp_app,
    curriedTensor_obj_map, whiskerLeft_id, Iso.refl_hom, CategoryTheory.Functor.map_id,
    NatTrans.id_app, Category.comp_id, Category.id_comp, Category.assoc]
  erw [id_whiskerRight, Category.id_comp]


private theorem tensorCoconeComparison_pureLift
    (factor : CochainComplex (ModuleCat.{ringLevel} ring) ℤ)
    {source target input : CochainComplex (ModuleCat.{ringLevel} ring) ℤ}
    (morphism : source ⟶ target) (augmentation : input ⟶ source)
    (zeroComposite : augmentation ≫ morphism = 0) :
    (TrightCochain factor).map
        (CochainComplex.mappingCocone.lift morphism augmentation 0 (by simp [zeroComposite])) ≫
      (tensorCoconeComparison factor morphism).hom =
    CochainComplex.mappingCocone.lift ((TrightCochain factor).map morphism)
      ((TrightCochain factor).map augmentation) 0
      (by simp [map_comp_eq_zero_of_comp_eq_zero _ zeroComposite]) := by
  let comparison := (shiftFunctor (CochainComplex (ModuleCat.{ringLevel} ring) ℤ) (-1 : ℤ)).mapIso
    (TrightCochain_mappingCone_iso factor morphism)
  change _ ≫ ((CochainComplex.mapBifunctorShift₁Iso (CochainComplex.mappingCone morphism)
    factor (curriedTensor (ModuleCat.{ringLevel} ring)) (-1)).hom ≫ comparison.hom) = _
  rw [← Category.assoc,
    tensorCoconePureLift_shiftComparison factor morphism augmentation zeroComposite]
  change (_ ≫ comparison.inv) ≫ comparison.hom = _
  rw [Category.assoc, comparison.inv_hom_id, Category.comp_id]


end

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CountableMilnorTower KoszulCompletion KoszulCoefficientTower
universe ringLevel moduleLevel targetRingLevel targetModuleLevel
variable {ring : Type ringLevel} [CommRing ring]
  {targetRing : Type targetRingLevel} [CommRing targetRing]

private def coconeArrowMap
    {source target source' target' : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ}
    {morphism : source ⟶ target} {morphism' : source' ⟶ target'}
    (square : Arrow.mk morphism ⟶ Arrow.mk morphism') :
    CochainComplex.mappingCocone morphism ⟶ CochainComplex.mappingCocone morphism' :=
  (shiftFunctor (CochainComplex (ModuleCat.{moduleLevel} ring) ℤ) (-1 : ℤ)).map
    (HomologicalComplex.homotopyCofiber.mapArrowHom morphism morphism'
      (fun degree => ⟨degree - 1, by simp⟩) square)

private theorem coconeArrowMap_f
    {source target source' target' : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ}
    {morphism : source ⟶ target} {morphism' : source' ⟶ target'}
    (square : Arrow.mk morphism ⟶ Arrow.mk morphism') (degree : ℤ) :
    (coconeArrowMap square).f degree =
      (CochainComplex.mappingCocone.fst morphism).f degree ≫ square.left.f degree ≫
        (CochainComplex.mappingCocone.inl morphism').v degree degree (add_zero degree) +
      (CochainComplex.mappingCocone.snd morphism).v degree (degree + -1) rfl ≫
        square.right.f (degree + -1) ≫
          (CochainComplex.mappingCocone.inr morphism').1.v (degree + -1) degree (by omega) := by
  change (HomologicalComplex.homotopyCofiber.mapArrowHom _ _ _ square).f
    (degree + (-1 : ℤ)) = _
  dsimp only [HomologicalComplex.homotopyCofiber.mapArrowHom]
  rw [HomologicalComplex.homotopyCofiber.desc_f _ _ _ (degree + (-1 : ℤ)) degree
    (by simp : (ComplexShape.up ℤ).Rel (degree + (-1 : ℤ)) degree)]
  dsimp only [Homotopy.trans, Homotopy.ofEq, Homotopy.compLeft]
  simp only [Pi.zero_apply, Pi.add_apply, add_zero, zero_add]
  rw [HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom morphism'
    (fun index => ⟨index - 1, by simp⟩) degree (degree + (-1 : ℤ))
    (by simp : (ComplexShape.up ℤ).Rel (degree + (-1 : ℤ)) degree)]
  simp [CochainComplex.mappingCocone.fst, CochainComplex.mappingCocone.snd,
    CochainComplex.mappingCocone.inl, CochainComplex.mappingCocone.inr,
    CochainComplex.mappingCone.fst, CochainComplex.mappingCone.snd,
    CochainComplex.mappingCone.inl, CochainComplex.mappingCone.inr,
    CochainComplex.HomComplex.Cochain.leftShift_v (n := 1)
      _ _ _ _ _ degree _ (degree + -1) (by omega),
    CochainComplex.HomComplex.Cochain.leftShift_v (n := 0)
      _ (-1) (-1) _ degree (degree + -1) _ (degree + -1) (by omega),
    CochainComplex.HomComplex.Cochain.rightShift_v (n := -1)
      _ _ _ _ degree _ _ (degree + -1) (by omega),
    CochainComplex.HomComplex.Cochain.rightShift_v (n := 0)
      _ _ _ _ (degree + -1) _ _ (degree + -1) (by omega),
    Int.negOnePow_even 2 ⟨1, rfl⟩]

private theorem coconeArrowMap_pureLift
    {source target source' target' input : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ}
    {morphism : source ⟶ target} {morphism' : source' ⟶ target'}
    (square : Arrow.mk morphism ⟶ Arrow.mk morphism')
    (augmentation : input ⟶ source) (zeroComposite : augmentation ≫ morphism = 0) :
    CochainComplex.mappingCocone.lift morphism augmentation 0 (by simp [zeroComposite]) ≫
        coconeArrowMap square =
      CochainComplex.mappingCocone.lift morphism' (augmentation ≫ square.left) 0
        (by
          have zeroMapped : (augmentation ≫ square.left) ≫ morphism' = 0 := by
            have commutes : square.left ≫ morphism' = morphism ≫ square.right := square.w
            rw [Category.assoc, commutes, ← Category.assoc, zeroComposite, zero_comp]
          simp [zeroMapped]) := by
  have zeroMapped : (augmentation ≫ square.left) ≫ morphism' = 0 := by
    have commutes : square.left ≫ morphism' = morphism ≫ square.right := square.w
    rw [Category.assoc, commutes, ← Category.assoc, zeroComposite, zero_comp]
  apply HomologicalComplex.hom_ext
  intro degree
  rw [HomologicalComplex.comp_f, cocone_pureLift_f morphism augmentation zeroComposite degree,
    cocone_pureLift_f morphism' (augmentation ≫ square.left) zeroMapped degree,
    coconeArrowMap_f]
  simp only [HomologicalComplex.comp_f, Preadditive.comp_add, Category.assoc,
    CochainComplex.mappingCocone.inl_v_fst_f_assoc,
    CochainComplex.mappingCocone.inl_v_snd_v_assoc,
    zero_comp, comp_zero, add_zero]


private def pureLift
    {source target input : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ}
    (morphism : source ⟶ target) (augmentation : input ⟶ source)
    (zeroComposite : augmentation ≫ morphism = 0) :
    input ⟶ CochainComplex.mappingCocone morphism :=
  CochainComplex.mappingCocone.lift morphism augmentation 0 (by simp [zeroComposite])

private theorem pureLift_precomp
    {source target input input' : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ}
    (morphism : source ⟶ target) (augmentation : input ⟶ source)
    (zeroComposite : augmentation ≫ morphism = 0) (before : input' ⟶ input) :
    before ≫ pureLift morphism augmentation zeroComposite =
      pureLift morphism (before ≫ augmentation) (by
        rw [Category.assoc, zeroComposite, comp_zero]) := by
  apply HomologicalComplex.hom_ext
  intro degree
  have zeroBefore : (before ≫ augmentation) ≫ morphism = 0 := by
    rw [Category.assoc, zeroComposite, comp_zero]
  simp only [pureLift, HomologicalComplex.comp_f]
  rw [cocone_pureLift_f morphism augmentation zeroComposite degree,
    cocone_pureLift_f morphism (before ≫ augmentation) zeroBefore degree]
  simp only [HomologicalComplex.comp_f, Category.assoc]

private theorem pureLift_congr
    {source target input : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ}
    (morphism : source ⟶ target) {left right : input ⟶ source}
    (zeroLeft : left ≫ morphism = 0) (zeroRight : right ≫ morphism = 0)
    (same : left = right) : pureLift morphism left zeroLeft = pureLift morphism right zeroRight :=
      by
  subst right
  rfl

private theorem pureLift_coconeCongrIso
    {source target source' target' input : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ}
    {morphism : source ⟶ target} {morphism' : source' ⟶ target'}
    (left : source ≅ source') (right : target ≅ target')
    (commutes : left.hom ≫ morphism' = morphism ≫ right.hom)
    (augmentation : input ⟶ source) (zeroComposite : augmentation ≫ morphism = 0) :
    pureLift morphism augmentation zeroComposite ≫ (coconeCongrIso left right commutes).hom =
      pureLift morphism' (augmentation ≫ left.hom) (by
        rw [Category.assoc, commutes, ← Category.assoc, zeroComposite, zero_comp]) := by
  simpa only [pureLift, coconeCongrIso, Functor.mapIso_hom,
    HomologicalComplex.homotopyCofiber.mapArrowIso_hom, coconeArrowMap, Arrow.isoMk_hom_left]
    using coconeArrowMap_pureLift (Arrow.isoMk left right commutes).hom augmentation zeroComposite

private theorem moduleComparison_pureLift
    (moduleTransformer : ModuleCat.{moduleLevel} ring ⥤ ModuleCat.{targetModuleLevel} targetRing)
    [moduleTransformer.Additive]
    {source target input : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ}
    (morphism : source ⟶ target) (augmentation : input ⟶ source)
    (zeroComposite : augmentation ≫ morphism = 0) :
    (moduleTransformer.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (pureLift morphism augmentation zeroComposite) ≫
      (coconeComparisonOfModuleFunctor moduleTransformer morphism).hom =
    pureLift ((moduleTransformer.mapHomologicalComplex (ComplexShape.up ℤ)).map morphism)
      ((moduleTransformer.mapHomologicalComplex (ComplexShape.up ℤ)).map augmentation)
      (map_comp_eq_zero_of_comp_eq_zero _ zeroComposite) :=
  coconeComparisonOfModuleFunctor_pureLift moduleTransformer morphism augmentation zeroComposite

private instance tensorRight_additive
    (factor : CochainComplex (ModuleCat.{ringLevel} ring) ℤ) :
    (tensorRight factor).Additive :=
  inferInstanceAs ((TrightCochain factor).Additive)

private theorem tensorComparison_pureLift
    (factor : CochainComplex (ModuleCat.{ringLevel} ring) ℤ)
    {source target input : CochainComplex (ModuleCat.{ringLevel} ring) ℤ}
    (morphism : source ⟶ target) (augmentation : input ⟶ source)
    (zeroComposite : augmentation ≫ morphism = 0) :
    (tensorRight factor).map (pureLift morphism augmentation zeroComposite) ≫
      (tensorCoconeComparison factor morphism).hom =
    pureLift ((tensorRight factor).map morphism) ((tensorRight factor).map augmentation)
      (map_comp_eq_zero_of_comp_eq_zero _ zeroComposite) :=
  tensorCoconeComparison_pureLift factor morphism augmentation zeroComposite


set_option maxHeartbeats 1200000 in
-- the comparison is the composite of five isomorphisms of mapping cocones
private theorem coefficientStageCoconeComparison_pureLift
    {rank : ℕ} (family : Fin rank → ring) (stage : ℕ)
    {source target input : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ}
    (morphism : source ⟶ target) (augmentation : input ⟶ source)
    (zeroComposite : augmentation ≫ morphism = 0) :
    (coefficientCompletionStage family stage).map (pureLift morphism augmentation zeroComposite) ≫
      (coefficientStageCoconeComparison family stage morphism).hom =
    pureLift ((coefficientCompletionStage family stage).map morphism)
      ((coefficientCompletionStage family stage).map augmentation)
      (map_comp_eq_zero_of_comp_eq_zero _ zeroComposite) := by
  let lift := complexUniverseLift.{ringLevel, moduleLevel} (A := ring)
  let stageFunctor := coefficientCompletionStage.{ringLevel, moduleLevel} family stage
  let factor := standardKoszulStage
    (fun index => (ULift.up (family index) : ULift.{moduleLevel} ring)) none stage
  let tensor := tensorRight factor
  let comparison : stageFunctor ⋙ lift ≅ lift ⋙ tensor :=
    coefficientKoszulComparison family none stage
  let first := coconeComparisonOfModuleFunctor (AdicKoszul.moduleUniverseLift ring) morphism
  let last := coconeComparisonOfModuleFunctor (AdicKoszul.moduleUniverseLift ring)
    (stageFunctor.map morphism)
  let middle := tensorCoconeComparison factor (lift.map morphism)
  let congruence := coconeCongrIso (comparison.app source).symm (comparison.app target).symm
    (comparison.inv.naturality morphism).symm
  let : lift.Full := by dsimp [lift]; infer_instance
  let : lift.Faithful := by dsimp [lift]; infer_instance
  have mapComparison : lift.map (coefficientStageCoconeComparison family stage morphism).hom =
      (comparison.app (CochainComplex.mappingCocone morphism)).hom ≫
        tensor.map first.hom ≫ middle.hom ≫ congruence.hom ≫ last.inv := by
    change lift.map (lift.preimage _) = _
    rw [Functor.map_preimage]
    rfl
  have naturality := comparison.hom.naturality (pureLift morphism augmentation zeroComposite)
  change lift.map (stageFunctor.map (pureLift morphism augmentation zeroComposite)) ≫
      (comparison.app (CochainComplex.mappingCocone morphism)).hom =
    (comparison.app input).hom ≫ tensor.map (lift.map (pureLift morphism augmentation
      zeroComposite))
      at naturality
  apply lift.map_injective
  rw [Functor.map_comp, mapComparison]
  apply (cancel_mono last.hom).mp
  simp only [Category.assoc, last.inv_hom_id]
  rw [moduleComparison_pureLift (AdicKoszul.moduleUniverseLift ring)]
  rw [← Category.assoc (lift.map (stageFunctor.map (pureLift morphism augmentation zeroComposite)))
    ((comparison.app (CochainComplex.mappingCocone morphism)).hom), naturality]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc]
  rw [moduleComparison_pureLift (AdicKoszul.moduleUniverseLift ring) morphism augmentation
    zeroComposite]
  have zeroLift := map_comp_eq_zero_of_comp_eq_zero lift zeroComposite
  have zeroTensor := map_comp_eq_zero_of_comp_eq_zero tensor zeroLift
  erw [Category.comp_id]
  rw [← Category.assoc (tensor.map (pureLift (lift.map morphism) (lift.map augmentation) zeroLift))
    middle.hom]
  rw [tensorComparison_pureLift factor (lift.map morphism) (lift.map augmentation) zeroLift]
  dsimp only [congruence]
  erw [pureLift_coconeCongrIso (comparison.app source).symm (comparison.app target).symm
    (comparison.inv.naturality morphism).symm (tensor.map (lift.map augmentation)) zeroTensor]
  rw [pureLift_precomp]
  simp only [Iso.symm_hom]
  have augmentationNaturality : (comparison.app input).hom ≫
      (tensor.map (lift.map augmentation) ≫ (comparison.app source).inv) =
    lift.map (stageFunctor.map augmentation) := by
    have naturality := comparison.hom.naturality augmentation
    change lift.map (stageFunctor.map augmentation) ≫ (comparison.app source).hom =
      (comparison.app input).hom ≫ tensor.map (lift.map augmentation) at naturality
    rw [← Category.assoc, ← naturality, Category.assoc,
      (comparison.app source).hom_inv_id]
    exact Category.comp_id _
  exact pureLift_congr ((stageFunctor ⋙ lift).map morphism) _ _ augmentationNaturality


private def mapTowerAugmentation
    (transformer : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ ⥤
      CochainComplex (ModuleCat.{targetModuleLevel} targetRing) ℤ)
    {tower : Tower.{ringLevel, moduleLevel} (A := ring)}
    (augmented : TowerAugmentation tower) : TowerAugmentation (tower ⋙ transformer) where
  source := transformer.obj augmented.source
  app index := transformer.map (augmented.app index)
  naturality index := by
    change transformer.map _ ≫ transformer.map _ = _
    rw [← Functor.map_comp, augmented.naturality]

private theorem mapTowerAugmentation_productLift
    (transformer : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ ⥤
      CochainComplex (ModuleCat.{targetModuleLevel} targetRing) ℤ)
    [PreservesLimitsOfShape (Discrete ℕ) transformer]
    {tower : Tower.{ringLevel, moduleLevel} (A := ring)}
    (augmented : TowerAugmentation tower) :
    transformer.map augmented.productLift ≫
        (PreservesProduct.iso transformer (fun index : ℕ => tower.obj ⟨index⟩)).hom =
      (mapTowerAugmentation transformer augmented).productLift := by
  change transformer.map (Limits.Pi.lift augmented.app) ≫
    piComparison transformer (fun index : ℕ => tower.obj ⟨index⟩) =
      Limits.Pi.lift (fun index => transformer.map (augmented.app index))
  apply Limits.Pi.hom_ext
  intro index
  rw [Category.assoc, piComparison_comp_π, ← Functor.map_comp]
  simp only [Limits.Pi.lift_comp_π]


section
variable (transformer : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ ⥤
  CochainComplex (ModuleCat.{targetModuleLevel} targetRing) ℤ)
  [transformer.Additive] [PreservesLimitsOfShape (Discrete ℕ) transformer]

private theorem milnorObjectIsoOfCoconeComparison_augmentation
    (coconeComparison : ∀ {source target : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ}
      (morphism : source ⟶ target),
      transformer.obj (CochainComplex.mappingCocone morphism) ≅
        CochainComplex.mappingCocone (transformer.map morphism))
    (compatible : ∀ {source target input : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ}
      (morphism : source ⟶ target) (augmentation : input ⟶ source)
      (zeroComposite : augmentation ≫ morphism = 0),
      transformer.map (pureLift morphism augmentation zeroComposite) ≫
        (coconeComparison morphism).hom =
      pureLift (transformer.map morphism) (transformer.map augmentation)
        (map_comp_eq_zero_of_comp_eq_zero _ zeroComposite))
    {tower : Tower.{ringLevel, moduleLevel} (A := ring)}
    (augmented : TowerAugmentation tower) :
    transformer.map augmented.augmentationMap ≫
        (milnorObjectIsoOfCoconeComparison transformer coconeComparison tower).hom =
      (mapTowerAugmentation transformer augmented).augmentationMap := by
  change transformer.map
      (pureLift (oneMinusShift tower) augmented.productLift augmented.productLift_oneMinusShift) ≫
    ((coconeComparison (oneMinusShift tower)).hom ≫
      (mappedDifferenceCoconeIso transformer tower).hom) = _
  rw [← Category.assoc,
    compatible (oneMinusShift tower) augmented.productLift augmented.productLift_oneMinusShift]
  rw [mappedDifferenceCoconeIso, pureLift_coconeCongrIso]
  change pureLift (oneMinusShift (tower ⋙ transformer)) _ _ =
    pureLift (oneMinusShift (tower ⋙ transformer))
      (mapTowerAugmentation transformer augmented).productLift
      (mapTowerAugmentation transformer augmented).productLift_oneMinusShift
  apply pureLift_congr
  exact mapTowerAugmentation_productLift transformer augmented

end

section
variable {rank : ℕ} (family : Fin rank → ring)

public theorem coefficientStageMilnorObjectIso_augmentation (stage : ℕ)
    (complex : CochainComplex (ModuleCat.{moduleLevel} ring) ℤ) :
    (coefficientCompletionStage family stage).map ((coefficientCompletionUnit family).app complex) ≫
        (coefficientStageMilnorObjectIso family stage ((coefficientKoszulTower family).obj
          complex)).hom =
      (stageWhiskeredAugmentation family stage complex).augmentationMap := by
  let augmented : TowerAugmentation ((coefficientKoszulTower family).obj complex) :=
    { source := complex
      app index := (coefficientKoszulAugmentation family index).app complex
      naturality index := coefficientKoszulAugmentation_transition family complex
        (index + 1) index (Nat.le_succ index) }
  have normalized := milnorObjectIsoOfCoconeComparison_augmentation
    (coefficientCompletionStage family stage)
    (fun morphism => coefficientStageCoconeComparison family stage morphism)
    (fun morphism augmentation zeroComposite =>
      coefficientStageCoconeComparison_pureLift family stage morphism augmentation zeroComposite)
    augmented
  simpa only [coefficientStageMilnorObjectIso, coefficientCompletionUnit, augmentationNatTrans,
    stageWhiskeredAugmentation, mapTowerAugmentation, augmented, Functor.id_obj, Functor.comp_obj,
    Functor.whiskeringRight_obj_obj] using normalized

end
end

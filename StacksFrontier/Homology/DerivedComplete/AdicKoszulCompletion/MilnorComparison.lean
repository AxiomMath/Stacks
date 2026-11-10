module

public import StacksFrontier.Homology.DerivedComplete.AdicKoszulCompletion.LiftReflection
public import StacksFrontier.Homology.DerivedComplete.AdicKoszulCompletion.StageComparison
import all Mathlib.CategoryTheory.Discrete.Basic
import all Mathlib.CategoryTheory.Functor.Basic
import all Mathlib.CategoryTheory.Functor.OfSequence
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Functorial Koszul power completion: the Milnor triangle and the completion data

## Main definitions

* `KoszulCompletion.completionData` is the descended functorial Koszul completion.

## Main results

* `KoszulCompletion.completionComparison_laws` records naturality, the Milnor and unit
  identities for the fixed maps, and scalar-tower zero reflection.

## References

* [Stacks Project, Tag 091Z](https://stacks.math.columbia.edu/tag/091Z)
* [Stacks Project, Tag 091J](https://stacks.math.columbia.edu/tag/091J)
* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
* [Bhatt--Scholze, *Projectivity of the Witt vector affine Grassmannian*][BS]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u v

namespace KoszulTensorNaturalityAudit

attribute [local instance] KoszulCompletion.derivedCountableProducts

attribute [local instance] HasDerivedCategory.standard

open KoszulCompletion KoszulCoefficientTower
open scoped ExteriorAlgebra

private def completionLocalIso
    {ring : Type u} [CommRing ring] {rank : ℕ} (family : Fin rank → ring) :
    DerivedCategory.Q (C := ModuleCat.{v} ring) ⋙ completionFunctor family ≅
      coefficientCompletionComplex family ⋙ DerivedCategory.Q :=
  Localization.fac _ (coefficientCompletion_isInvertedBy family) _

set_option backward.isDefEq.respectTransparency false in
private theorem completionProjection_representative
    {ring : Type u} [CommRing ring] {rank : ℕ} {family : Fin rank → ring}
    {tensor : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{v} ring)}
    (comparisonLaws : StageComparisonNaturality family tensor)
    (complex : CochainComplex (ModuleCat.{v} ring) ℤ) (power : ℕ) :
    (AdicKoszul.derivedUniverseLift.{u, v} ring).map
        (DerivedCategory.Q.map ((coefficientCompletionProjection family power).app complex)) ≫
        (coefficientStageComparisonIso family tensor power complex).hom =
      ((AdicKoszul.derivedUniverseLift ring).mapIso ((completionLocalIso family).app complex)).inv ≫
        (comparisonLaws.projection power).app (DerivedCategory.Q.obj complex) := by
  simp only [StageComparisonNaturality.projection, Localization.liftNatTrans_app,
    NatTrans.comp_app, Functor.whiskerRight_app, StageComparisonNaturality.comparison,
    NatIso.ofComponents_hom_app, Functor.mapIso_inv, completionLocalIso, Localization.fac,
    Localization.Lifting.iso, Functor.isoWhiskerRight_hom, Iso.refl_inv, NatTrans.id_app,
    Functor.whiskerRight_app, Category.comp_id]
  simp only [← Functor.map_comp_assoc, Iso.app_inv]
  rw [Iso.inv_hom_id_app_assoc]

open CategoryTheory.Pretriangulated

private theorem milnor_triangle_transport
    {category : Type*} [Category* category] [Preadditive category] [HasZeroObject category]
    [HasShift category ℤ] [∀ degree : ℤ, (shiftFunctor category degree).Additive]
    [Pretriangulated category] [HasProductsOfShape ℕ category]
    {sourceLimit targetLimit : category} (limitIso : sourceLimit ≅ targetLimit)
    {sourceObjects targetObjects : ℕ → category} (stageIso : ∀ index, sourceObjects index ≅
      targetObjects index)
    (sourceTransition : ∀ index, sourceObjects (index + 1) ⟶ sourceObjects index)
    (targetTransition : ∀ index, targetObjects (index + 1) ⟶ targetObjects index)
    (sourceProjection : ∀ index, sourceLimit ⟶ sourceObjects index)
    (targetProjection : ∀ index, targetLimit ⟶ targetObjects index)
    (transition_comm : ∀ index, sourceTransition index ≫ (stageIso index).hom =
      (stageIso (index + 1)).hom ≫ targetTransition index)
    (projection_comm : ∀ index, sourceProjection index ≫ (stageIso index).hom =
      limitIso.hom ≫ targetProjection index)
    (boundary : (∏ᶜ sourceObjects) ⟶ sourceLimit⟦(1 : ℤ)⟧)
    (distinguished : Triangle.mk (Pi.lift sourceProjection)
      (Pi.lift fun index => Pi.π sourceObjects index -
        Pi.π sourceObjects (index + 1) ≫ sourceTransition index) boundary ∈ distTriang category) :
    ∃ targetBoundary : (∏ᶜ targetObjects) ⟶ targetLimit⟦(1 : ℤ)⟧,
      Triangle.mk (Pi.lift targetProjection)
        (Pi.lift fun index => Pi.π targetObjects index -
          Pi.π targetObjects (index + 1) ≫ targetTransition index) targetBoundary ∈
        distTriang category := by
  let productIso := Pi.mapIso stageIso
  let targetBoundary := productIso.inv ≫ boundary ≫ (shiftFunctor category (1 : ℤ)).map limitIso.hom
  refine ⟨targetBoundary, ?_⟩
  let sourceTriangle := Triangle.mk (Pi.lift sourceProjection)
    (Pi.lift fun index => Pi.π sourceObjects index -
      Pi.π sourceObjects (index + 1) ≫ sourceTransition index) boundary
  let targetTriangle := Triangle.mk (Pi.lift targetProjection)
    (Pi.lift fun index => Pi.π targetObjects index -
      Pi.π targetObjects (index + 1) ≫ targetTransition index) targetBoundary
  have projectionSquare : sourceTriangle.mor₁ ≫ productIso.hom =
      limitIso.hom ≫ targetTriangle.mor₁ := by
    apply Pi.hom_ext
    intro index
    dsimp only [sourceTriangle, targetTriangle, Triangle.mk_mor₁, productIso]
    rw [Category.assoc, Pi.mapIso_hom_π, ← Category.assoc, Pi.lift_comp_π,
      Category.assoc, Pi.lift_comp_π, projection_comm]
  have transitionSquare : sourceTriangle.mor₂ ≫ productIso.hom =
      productIso.hom ≫ targetTriangle.mor₂ := by
    apply Pi.hom_ext
    intro index
    dsimp only [sourceTriangle, targetTriangle, Triangle.mk_mor₂, productIso]
    rw [Category.assoc, Pi.mapIso_hom_π, ← Category.assoc, Pi.lift_comp_π,
      Category.assoc, Pi.lift_comp_π, Preadditive.sub_comp, Preadditive.comp_sub,
      Pi.mapIso_hom_π, ← Category.assoc, Pi.mapIso_hom_π]
    rw [Category.assoc, transition_comm, ← Category.assoc]
  have boundarySquare : sourceTriangle.mor₃ ≫ limitIso.hom⟦(1 : ℤ)⟧' =
      productIso.hom ≫ targetTriangle.mor₃ := by
    simp only [sourceTriangle, targetTriangle, Triangle.mk_mor₃, targetBoundary,
      Iso.hom_inv_id_assoc]
  let triangleIso := Triangle.isoMk sourceTriangle targetTriangle limitIso productIso productIso
    projectionSquare transitionSquare boundarySquare
  exact isomorphic_distinguished sourceTriangle distinguished targetTriangle triangleIso.symm

private theorem map_milnor_triangle
    {sourceCategory targetCategory : Type*} [Category* sourceCategory] [Category* targetCategory]
    [Preadditive sourceCategory] [Preadditive targetCategory]
    [HasZeroObject sourceCategory] [HasZeroObject targetCategory]
    [HasShift sourceCategory ℤ] [HasShift targetCategory ℤ]
    [∀ degree : ℤ, (shiftFunctor sourceCategory degree).Additive]
    [∀ degree : ℤ, (shiftFunctor targetCategory degree).Additive]
    [Pretriangulated sourceCategory] [Pretriangulated targetCategory]
    [HasProductsOfShape ℕ sourceCategory] [HasProductsOfShape ℕ targetCategory]
    (functor : sourceCategory ⥤ targetCategory) [functor.Additive] [functor.CommShift ℤ]
    [functor.IsTriangulated] [PreservesLimitsOfShape (Discrete ℕ) functor]
    {limitObject : sourceCategory} (objects : ℕ → sourceCategory)
    (transition : ∀ index, objects (index + 1) ⟶ objects index)
    (projection : ∀ index, limitObject ⟶ objects index)
    (boundary : (∏ᶜ objects) ⟶ limitObject⟦(1 : ℤ)⟧)
    (distinguished : Triangle.mk (Pi.lift projection)
      (Pi.lift fun index => Pi.π objects index - Pi.π objects (index + 1) ≫ transition index)
        boundary ∈ distTriang sourceCategory) :
    ∃ targetBoundary : (∏ᶜ fun index => functor.obj (objects index)) ⟶
        (functor.obj limitObject)⟦(1 : ℤ)⟧,
      Triangle.mk (Pi.lift fun index => functor.map (projection index))
        (Pi.lift fun index => Pi.π (fun index => functor.obj (objects index)) index -
          Pi.π (fun index => functor.obj (objects index)) (index + 1) ≫ functor.map (transition
            index))
        targetBoundary ∈ distTriang targetCategory := by
  let sourceTriangle := Triangle.mk (Pi.lift projection)
    (Pi.lift fun index => Pi.π objects index - Pi.π objects (index + 1) ≫ transition index) boundary
  let mappedTriangle := functor.mapTriangle.obj sourceTriangle
  let productIso := asIso (piComparison functor objects)
  let targetBoundary := productIso.inv ≫ mappedTriangle.mor₃
  refine ⟨targetBoundary, ?_⟩
  let targetTriangle := Triangle.mk (Pi.lift fun index => functor.map (projection index))
    (Pi.lift fun index => Pi.π (fun index => functor.obj (objects index)) index -
      Pi.π (fun index => functor.obj (objects index)) (index + 1) ≫ functor.map (transition index))
    targetBoundary
  have projectionSquare : mappedTriangle.mor₁ ≫ productIso.hom = targetTriangle.mor₁ := by
    apply Pi.hom_ext
    intro index
    change (functor.map (Pi.lift projection) ≫ piComparison functor objects) ≫ _ = _
    rw [Category.assoc, piComparison_comp_π, ← functor.map_comp, Pi.lift_comp_π]
    exact (Pi.lift_comp_π (fun index => functor.map (projection index)) index).symm
  have transitionSquare : mappedTriangle.mor₂ ≫ productIso.hom =
      productIso.hom ≫ targetTriangle.mor₂ := by
    apply Pi.hom_ext
    intro index
    change (functor.map (Pi.lift fun index => Pi.π objects index -
      Pi.π objects (index + 1) ≫ transition index) ≫ piComparison functor objects) ≫ _ = _
    rw [Category.assoc, piComparison_comp_π, ← functor.map_comp, Pi.lift_comp_π,
      functor.map_sub, functor.map_comp]
    change _ = (piComparison functor objects ≫ (Pi.lift fun index =>
      Pi.π (fun index => functor.obj (objects index)) index -
        Pi.π (fun index => functor.obj (objects index)) (index + 1) ≫
          functor.map (transition index))) ≫ _
    rw [Category.assoc, Pi.lift_comp_π, Preadditive.comp_sub, piComparison_comp_π,
      ← Category.assoc, piComparison_comp_π]
  have boundarySquare : mappedTriangle.mor₃ ≫
      (Iso.refl mappedTriangle.obj₁).hom⟦(1 : ℤ)⟧' = productIso.hom ≫ targetTriangle.mor₃ := by
    change mappedTriangle.mor₃ ≫ (shiftFunctor targetCategory (1 : ℤ)).map
      (𝟙 mappedTriangle.obj₁) = productIso.hom ≫ (productIso.inv ≫ mappedTriangle.mor₃)
    rw [(shiftFunctor targetCategory (1 : ℤ)).map_id, Category.comp_id]
    exact (Iso.hom_inv_id_assoc _ _).symm
  let triangleIso := Triangle.isoMk mappedTriangle targetTriangle (Iso.refl _) productIso productIso
    (by
      change mappedTriangle.mor₁ ≫ productIso.hom =
        𝟙 (functor.obj limitObject) ≫ (Pi.lift fun index => functor.map (projection index))
      rw [Category.id_comp]
      exact projectionSquare)
    transitionSquare boundarySquare
  exact isomorphic_distinguished mappedTriangle (functor.map_distinguished sourceTriangle
    distinguished)
    targetTriangle triangleIso.symm

private theorem coefficientStageComparisonIso_transition_succ
    {ring : Type u} [CommRing ring] {rank : ℕ} (family : Fin rank → ring)
    (tensor : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{v} ring))
    (power : ℕ) (complex : CochainComplex (ModuleCat.{v} ring) ℤ) :
    (AdicKoszul.derivedUniverseLift.{u, v} ring).map
        (DerivedCategory.Q.map (((coefficientKoszulTower family).obj complex).map
          (homOfLE (Nat.le_succ power)).op)) ≫
        (coefficientStageComparisonIso family tensor power complex).hom =
      (coefficientStageComparisonIso family tensor (power + 1) complex).hom ≫
        (AdicKoszul.tensorKoszulPowerSystem family tensor (DerivedCategory.Q.obj complex)).map
          (homOfLE (Nat.le_succ power)).op := by
  simpa only [AdicKoszul.tensorKoszulPowerSystem, Functor.comp_map,
    AdicKoszul.canonicalKoszulPowerSystem,
    AdicKoszul.koszulPowerSystem, Functor.ofOpSequence_map_homOfLE_succ, standardKoszulTransition]
      using!
    coefficientStageComparisonIso_transition family tensor (power + 1) power (Nat.le_succ power)
      complex

private theorem completion_milnor_representative
    {ring : Type u} [CommRing ring] {rank : ℕ} {family : Fin rank → ring}
    {tensor : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{v} ring)}
    (comparisonLaws : StageComparisonNaturality family tensor)
    (complex : CochainComplex (ModuleCat.{v} ring) ℤ) :
    ∃ boundary : (∏ᶜ fun power : ℕ =>
        (AdicKoszul.tensorKoszulPowerSystem family tensor (DerivedCategory.Q.obj complex)).obj
          ⟨power⟩) ⟶
        ((AdicKoszul.derivedUniverseLift ring).obj
          ((completionFunctor family).obj (DerivedCategory.Q.obj complex)))⟦(1 : ℤ)⟧,
      Triangle.mk (Pi.lift fun power => (comparisonLaws.projection power).app (DerivedCategory.Q.obj
        complex))
        (Pi.lift fun power : ℕ =>
          Pi.π (fun power : ℕ =>
            (AdicKoszul.tensorKoszulPowerSystem family tensor (DerivedCategory.Q.obj complex)).obj
              ⟨power⟩) power -
          Pi.π (fun power : ℕ =>
            (AdicKoszul.tensorKoszulPowerSystem family tensor (DerivedCategory.Q.obj complex)).obj
              ⟨power⟩) (power + 1) ≫
            (AdicKoszul.tensorKoszulPowerSystem family tensor (DerivedCategory.Q.obj complex)).map
              (homOfLE (Nat.le_succ power)).op) boundary ∈
        distTriang (DerivedCategory (ModuleCat.{max u v} (ULift.{v} ring))) := by
  let tower := (coefficientKoszulTower family).obj complex
  let enlarge := AdicKoszul.derivedUniverseLift.{u, v} ring
  obtain ⟨boundary, distinguished⟩ := CountableMilnorTower.map_quasiIso_and_milnor_triangle.2 tower
  obtain ⟨mappedBoundary, mappedDistinguished⟩ := map_milnor_triangle enlarge
    (fun power => DerivedCategory.Q.obj (tower.obj ⟨power⟩))
    (fun power => DerivedCategory.Q.map (tower.map (homOfLE (Nat.le_succ power)).op))
    (fun power => DerivedCategory.Q.map ((CountableMilnorTower.projection power).app tower))
    boundary distinguished
  exact milnor_triangle_transport
    (enlarge.mapIso ((completionLocalIso family).app complex)).symm
    (fun power => coefficientStageComparisonIso family tensor power complex)
    (fun power => enlarge.map (DerivedCategory.Q.map (tower.map (homOfLE (Nat.le_succ power)).op)))
    (fun power => (AdicKoszul.tensorKoszulPowerSystem family tensor (DerivedCategory.Q.obj
      complex)).map
      (homOfLE (Nat.le_succ power)).op)
    (fun power => enlarge.map (DerivedCategory.Q.map ((CountableMilnorTower.projection power).app
      tower)))
    (fun power => (comparisonLaws.projection power).app (DerivedCategory.Q.obj complex))
    (fun power => coefficientStageComparisonIso_transition_succ family tensor power complex)
    (fun power => completionProjection_representative comparisonLaws complex power)
    mappedBoundary mappedDistinguished

private theorem completionComparisonLaws
    {ring : Type u} [CommRing ring] {rank : ℕ} {family : Fin rank → ring}
    {tensor : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{v} ring)}
    (comparisonLaws : StageComparisonNaturality family tensor) :
    CompletionComparisonLaws comparisonLaws := by
  refine ⟨?_, completionUnit_projection comparisonLaws⟩
  intro object
  let complex := (DerivedCategory.Q (C := ModuleCat.{v} ring)).objPreimage object
  let representativeIso := (DerivedCategory.Q (C := ModuleCat.{v} ring)).objObjPreimageIso object
  let enlarge := AdicKoszul.derivedUniverseLift.{u, v} ring
  let stage := AdicKoszul.canonicalKoszulPowerSystem
    (fun index => (ULift.up (family index) : ULift.{v} ring))
  obtain ⟨boundary, distinguished⟩ := completion_milnor_representative comparisonLaws complex
  exact milnor_triangle_transport
    ((completionFunctor family ⋙ enlarge).mapIso representativeIso)
    (fun power => (enlarge ⋙ tensor.tensor.flip.obj (stage.obj ⟨power⟩)).mapIso representativeIso)
    (fun power => (AdicKoszul.tensorKoszulPowerSystem family tensor (DerivedCategory.Q.obj
      complex)).map
      (homOfLE (Nat.le_succ power)).op)
    (fun power => (AdicKoszul.tensorKoszulPowerSystem family tensor object).map
      (homOfLE (Nat.le_succ power)).op)
    (fun power => (comparisonLaws.projection power).app (DerivedCategory.Q.obj complex))
    (fun power => (comparisonLaws.projection power).app object)
    (fun power => (tensor.tensor.map (enlarge.map representativeIso.hom)).naturality
      (stage.map (homOfLE (Nat.le_succ power)).op))
    (fun power => ((comparisonLaws.projection power).naturality representativeIso.hom).symm)
    boundary distinguished


end KoszulTensorNaturalityAudit

end

@[expose] public noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

public theorem KoszulCompletion.completionComparison_lawsAux (A : Type u) [CommRing A] :
    KoszulCompletion.UniverseLiftComparisonLaws.{u, v} A ∧
      ∀ {r : ℕ} (f : Fin r → A) (T : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{v}
        A)),
        KoszulCompletion.StageComparisonNaturality f T ∧
          ∀ h : KoszulCompletion.StageComparisonNaturality f T,
            KoszulCompletion.CompletionComparisonLaws h := by
  refine ⟨KoszulLiftReflectionAudit.universeLiftComparisonLaws A, ?_⟩
  intro r f T
  exact ⟨KoszulTensorNaturalityAudit.stageComparisonNaturality f T,
    KoszulTensorNaturalityAudit.completionComparisonLaws⟩


end






@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.MonoidalCategory

universe u v

namespace KoszulCompletion

variable {A : Type u} [CommRing A]

attribute [local instance] HasDerivedCategory.standard

open scoped ExteriorAlgebra

attribute [local instance] derivedCountableProducts

/-- Exact countable products and the K-flat tensor comparisons verify the fixed localization
construction. Naturality is checked through `DerivedTensorProduct.comparison_naturality`, and
the augmentation identity through `DerivedTensorProduct.rightUnitor_comparison`. The product
comparison and scalar-tower reflection use only the essential image of universe enlargement. -/
public theorem completionComparison_laws (A : Type u) [CommRing A] :
    UniverseLiftComparisonLaws.{u, v} A ∧
      ∀ {r : ℕ} (f : Fin r → A) (T : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{v}
        A)),
        StageComparisonNaturality f T ∧
          ∀ h : StageComparisonNaturality f T, CompletionComparisonLaws h :=
  completionComparison_lawsAux A

/-- Vanishing of a scalar-tower derived limit is reflected along universe enlargement
for a coefficient object in the original universe. -/
public theorem derivedUniverseLift_scalarTower_zero_iff (a : A)
    (K : DerivedCategory (ModuleCat.{v} A)) :
    (∃ L, IsDerivedLimit
        (Functor.ofOpSequence (X := fun _ : ℕ ↦ (AdicKoszul.derivedUniverseLift A).obj K)
          (fun _ ↦ (ULift.up a : ULift.{v} A) • 𝟙 _)) L ∧ IsZero L) ↔
      (∃ L, IsDerivedLimit
        (Functor.ofOpSequence (X := fun _ : ℕ ↦ K) (fun _ ↦ a • 𝟙 K)) L ∧ IsZero L) :=
  (completionComparison_laws A).1.scalar_zero a K

/-- The canonical natural projection from the descended strict completion to a tensor stage. -/
public def completionProjection {r : ℕ} (f : Fin r → A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{v} A)) (n : ℕ) :
    completionFunctor f ⋙ AdicKoszul.derivedUniverseLift A ⟶
      AdicKoszul.derivedUniverseLift A ⋙ T.tensor.flip.obj
        ((AdicKoszul.canonicalKoszulPowerSystem
          (fun i ↦ (ULift.up (f i) : ULift.{v} A))).obj ⟨n⟩) :=
  ((completionComparison_laws A).2 f T).1.projection n

/-- Functorial Koszul power completion for every coefficient complex. Its data are the actual
localization of the strict coefficient construction and its explicit comparison projections. -/
public def completionData {r : ℕ} (f : Fin r → A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{v} A)) :
    AdicKoszul.KoszulPowerCompletion f T where
  functor := completionFunctor f
  unit := completionUnit f
  projection := completionProjection f T
  milnor := (((completionComparison_laws A).2 f T).2 _).milnor
  unit_projection := (((completionComparison_laws A).2 f T).2 _).unit_projection

/-- The completion constructor retains the explicitly localized functor. -/
@[simp] public theorem completionData_functor {r : ℕ} (f : Fin r → A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{v} A)) :
    (completionData f T).functor = completionFunctor f := rfl

/-- The completion constructor retains the localization of the strict augmentation. -/
@[simp] public theorem completionData_unit {r : ℕ} (f : Fin r → A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{v} A)) :
    (completionData f T).unit = completionUnit f := rfl

end KoszulCompletion

end

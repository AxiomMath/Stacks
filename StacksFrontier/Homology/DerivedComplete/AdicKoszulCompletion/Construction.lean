module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
public import StacksFrontier.Algebra.Homology.QuasiIsoOfAcyclicKernel
public import StacksFrontier.Homology.DerivedComplete.AdicKoszulCoefficientTower
public import StacksFrontier.Homology.DerivedComplete.CountableMilnorTower
public import StacksFrontier.Homology.KFlat.QuasiIso
public import StacksFrontier.Homology.QuasiIsoKernel
import all Mathlib.CategoryTheory.Discrete.Basic
import all Mathlib.CategoryTheory.Functor.Basic
import all Mathlib.CategoryTheory.Functor.OfSequence
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Functorial Koszul power completion: the construction

For a finite sequence in a commutative ring, the small-universe coefficient Koszul tower and
the strict countable Milnor mapping-fiber construction combine to give a functor on complexes.
It descends to the derived category and agrees, after universe enlargement, with the derived
tensor--Koszul tower for any chosen derived tensor product.

## Main definitions

* `KoszulCompletion.coefficientCompletionComplex` is the strict completion functor on
  coefficient complexes.
* `KoszulCompletion.coefficientCompletionUnit` is its canonical augmentation.
* `KoszulCompletion.coefficientStageComparisonIso` is the explicit K-flat-resolution
  comparison with an arbitrary derived tensor product.

## Main results

* `KoszulCompletion.coefficientCompletion_preserves_quasiIso` says that the strict
  completion functor preserves quasi-isomorphisms.
* `KoszulCompletion.derivedUniverseLift_preservesProducts` proves preservation of
  countable products in the original universe.

## Implementation notes

The construction first forms the finite-basis coefficient Koszul tower and then applies the
strict mapping-fiber model for a countable derived limit.  Its descent uses the localization of
cochain complexes at quasi-isomorphisms.  Comparison with an arbitrary derived tensor product is
made only after universe enlargement and only on representatives in the essential image of that
enlargement; no essential-surjectivity assertion for the larger module universe is used.

## References

* [Stacks Project, Tag 091Z](https://stacks.math.columbia.edu/tag/091Z)
* [Stacks Project, Tag 091J](https://stacks.math.columbia.edu/tag/091J)
* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
* [Bhatt--Scholze, *Projectivity of the Witt vector affine Grassmannian*][BS]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.MonoidalCategory

universe u v

namespace KoszulCompletion

variable {A : Type u} [CommRing A]

attribute [local instance] HasDerivedCategory.standard

/-- The strict coefficient-level Koszul completion: form the small-universe Koszul power tower
and take its countable Milnor mapping fiber. -/
public noncomputable def coefficientCompletionComplex {r : ℕ} (f : Fin r → A) :
    CochainComplex (ModuleCat.{v} A) ℤ ⥤ CochainComplex (ModuleCat.{v} A) ℤ :=
  KoszulCoefficientTower.coefficientKoszulTower f ⋙
    CountableMilnorTower.countableMilnorFunctor

/-- The natural map from a coefficient complex to its strict Koszul power completion. -/
public noncomputable def coefficientCompletionUnit {r : ℕ} (f : Fin r → A) :
    𝟭 (CochainComplex (ModuleCat.{v} A) ℤ) ⟶ coefficientCompletionComplex f :=
  CountableMilnorTower.augmentationNatTrans
    (𝟭 (CochainComplex (ModuleCat.{v} A) ℤ))
    (KoszulCoefficientTower.coefficientKoszulTower f)
    (fun n ↦ KoszulCoefficientTower.coefficientKoszulAugmentation f n)
    (fun K n ↦ KoszulCoefficientTower.coefficientKoszulAugmentation_transition
      f K (n + 1) n (Nat.le_succ n))

/-- The strict coefficient completion preserves quasi-isomorphisms. -/
public theorem coefficientCompletion_preserves_quasiIso {r : ℕ} (f : Fin r → A)
    {K L : CochainComplex (ModuleCat.{v} A) ℤ} (g : K ⟶ L) [QuasiIso g] :
    QuasiIso ((coefficientCompletionComplex f).map g) := by
  apply CountableMilnorTower.map_quasiIso_and_milnor_triangle.1
  intro n
  exact KoszulCoefficientTower.coefficientKoszulTower_map_quasiIso f n g

/-- The strict completion functor, followed by localization, inverts quasi-isomorphisms. -/
public theorem coefficientCompletion_isInvertedBy {r : ℕ} (f : Fin r → A) :
    (HomologicalComplex.quasiIso (ModuleCat.{v} A) (ComplexShape.up ℤ)).IsInvertedBy
      (coefficientCompletionComplex f ⋙ DerivedCategory.Q (C := ModuleCat.{v} A)) := by
  intro K L g hg
  show IsIso (DerivedCategory.Q.map ((coefficientCompletionComplex f).map g))
  let : QuasiIso g := hg
  let : QuasiIso ((coefficientCompletionComplex f).map g) :=
    coefficientCompletion_preserves_quasiIso f g
  infer_instance

/-- The derived completion functor obtained by localizing the strict coefficient construction. -/
public noncomputable def completionFunctor {r : ℕ} (f : Fin r → A) :
    DerivedCategory (ModuleCat.{v} A) ⥤ DerivedCategory (ModuleCat.{v} A) :=
  Localization.lift
    (coefficientCompletionComplex f ⋙ DerivedCategory.Q (C := ModuleCat.{v} A))
    (coefficientCompletion_isInvertedBy f) (DerivedCategory.Q (C := ModuleCat.{v} A))

/-- The unit of the derived completion, obtained by localizing the strict augmentation. -/
public noncomputable def completionUnit {r : ℕ} (f : Fin r → A) :
    𝟭 (DerivedCategory (ModuleCat.{v} A)) ⟶ completionFunctor f := by
  letI : Localization.Lifting (DerivedCategory.Q (C := ModuleCat.{v} A))
      (HomologicalComplex.quasiIso (ModuleCat.{v} A) (ComplexShape.up ℤ))
      (coefficientCompletionComplex f ⋙ DerivedCategory.Q (C := ModuleCat.{v} A))
      (completionFunctor f) :=
    Localization.liftingLift _ (coefficientCompletion_isInvertedBy f) _
  exact Localization.liftNatTrans (DerivedCategory.Q (C := ModuleCat.{v} A))
    (HomologicalComplex.quasiIso (ModuleCat.{v} A) (ComplexShape.up ℤ))
    (DerivedCategory.Q (C := ModuleCat.{v} A))
    (coefficientCompletionComplex f ⋙ DerivedCategory.Q (C := ModuleCat.{v} A))
    (𝟭 _) (completionFunctor f)
    (Functor.whiskerRight (coefficientCompletionUnit f)
      (DerivedCategory.Q (C := ModuleCat.{v} A)))

/-- The `n`-th strict coefficient Koszul stage. -/
public abbrev coefficientCompletionStage {r : ℕ} (f : Fin r → A) (n : ℕ) :
    CochainComplex (ModuleCat.{v} A) ℤ ⥤ CochainComplex (ModuleCat.{v} A) ℤ :=
  KoszulCoefficientTower.coefficientKoszulTower f ⋙
    (evaluation ℕᵒᵖ (CochainComplex (ModuleCat.{v} A) ℤ)).obj ⟨n⟩

/-- The strict projection from the Milnor mapping fiber to the `n`-th coefficient stage. -/
public noncomputable def coefficientCompletionProjection {r : ℕ} (f : Fin r → A) (n : ℕ) :
    coefficientCompletionComplex f ⟶ coefficientCompletionStage f n :=
  Functor.whiskerLeft (KoszulCoefficientTower.coefficientKoszulTower f)
    (CountableMilnorTower.projection n)

/-- The strict completion unit followed by a projection is the given Koszul augmentation. -/
@[reassoc (attr := simp)]
public theorem coefficientCompletionUnit_projection {r : ℕ} (f : Fin r → A)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) (n : ℕ) :
    (coefficientCompletionUnit f).app K ≫ (coefficientCompletionProjection f n).app K =
      (KoszulCoefficientTower.coefficientKoszulAugmentation f n).app K :=
  CountableMilnorTower.augmentationNatTrans_projection _ _ _ _ K n

open scoped ExteriorAlgebra
/-- Ordinary tensor with a K-flat right factor preserves quasi-isomorphisms. -/
private theorem tensor_quasiIso (E : CochainComplex (ModuleCat.{u} A) ℤ) (hE : E.KFlat)
    {K L : CochainComplex (ModuleCat.{u} A) ℤ} (g : K ⟶ L) [QuasiIso g] :
    QuasiIso (g ⊗ₘ 𝟙 E) := by
  have h := CochainComplex.KFlat.kFlat_tright_preserves_quasiIso E hE
    ((HomotopyCategory.quotient _ _).map g)
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff g).2 (show QuasiIso g from inferInstance))
  change HomotopyCategory.quasiIso _ _ ((HomotopyCategory.quotient _ _).map
    ((TrightCochain E).map g)) at h
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).1 h

/-- Compare ordinary tensor with a K-flat right factor to any derived tensor product,
using a K-flat resolution of the left factor and its specified quasi-isomorphism. -/
public def tensorComparisonIso (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (K E : CochainComplex (ModuleCat.{u} A) ℤ) (hE : E.KFlat) :
    DerivedCategory.Q.obj (K ⊗ E) ≅
      (T.tensor.obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj E) := by
  let h := CochainComplex.KFlat.exists_kFlat_resolution K
  let P := h.choose
  let q : P ⟶ K := h.choose_spec.choose
  have hP : P.KFlat := h.choose_spec.choose_spec.1
  letI : QuasiIso q := h.choose_spec.choose_spec.2.2.1
  letI : QuasiIso (q ⊗ₘ 𝟙 E) := by exact tensor_quasiIso E hE q
  exact (asIso (DerivedCategory.Q.map (q ⊗ₘ 𝟙 E))).symm ≪≫
    (T.comparison P E hP hE).symm ≪≫
    (T.tensor.flip.obj (DerivedCategory.Q.obj E)).mapIso (asIso (DerivedCategory.Q.map q))

set_option backward.isDefEq.respectTransparency false in
/-- On two K-flat complexes the resolution comparison is the specified comparison of `T`. -/
public theorem tensorComparisonIso_of_kFlat (T : CochainComplex.DerivedTensor.DerivedTensorProduct
  A)
    (K E : CochainComplex (ModuleCat.{u} A) ℤ) (hK : K.KFlat) (hE : E.KFlat) :
    tensorComparisonIso T K E hE = (T.comparison K E hK hE).symm := by
  let h := CochainComplex.KFlat.exists_kFlat_resolution K
  let P := h.choose
  let q : P ⟶ K := h.choose_spec.choose
  have hP : P.KFlat := h.choose_spec.choose_spec.1
  let : QuasiIso q := h.choose_spec.choose_spec.2.2.1
  let : QuasiIso (q ⊗ₘ 𝟙 E) := tensor_quasiIso E hE q
  have hn := T.comparison_naturality q (𝟙 E) hP hK hE hE
  have hq : DerivedCategory.Q.map (𝟙 E) = 𝟙 (DerivedCategory.Q.obj E) :=
    (DerivedCategory.Q (C := ModuleCat.{u} A)).map_id E
  rw [hq, (T.tensor.obj (DerivedCategory.Q.obj K)).map_id,
    Category.id_comp] at hn
  apply Iso.ext
  show inv (DerivedCategory.Q.map (q ⊗ₘ 𝟙 E)) ≫
    (T.comparison P E hP hE).inv ≫
    (T.tensor.map (DerivedCategory.Q.map q)).app (DerivedCategory.Q.obj E) =
      (T.comparison K E hK hE).inv
  rw [← cancel_mono (T.comparison K E hK hE).hom]
  simp only [Category.assoc, hn, Iso.inv_hom_id_assoc, Iso.inv_hom_id]
  show inv (DerivedCategory.Q.map (q ⊗ₘ 𝟙 E)) ≫
    DerivedCategory.Q.map (q ⊗ₘ 𝟙 E) = 𝟙 _
  exact IsIso.inv_hom_id _

/-- The resolution comparison recovers the specified right unit on K-flat representatives. -/
public theorem tensorComparisonIso_rightUnitor (T :
  CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (hK : K.KFlat)
    (hUnit : (𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ)).KFlat) :
    (tensorComparisonIso T K (𝟙_ _) hUnit).inv ≫ DerivedCategory.Q.map (ρ_ K).hom =
      T.rightUnitor.hom.app (DerivedCategory.Q.obj K) := by
  rw [tensorComparisonIso_of_kFlat T K _ hK hUnit]
  exact T.rightUnitor_comparison K hK hUnit

/-- The fixed comparison from a coefficient Koszul stage to its derived tensor model.
It is the exterior-basis isomorphism followed by the K-flat-resolution comparison; the two
universe-change isomorphisms are the canonical factors of the exact derived functor. -/
public def coefficientStageComparisonIso {r : ℕ} (f : Fin r → A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{v} A)) (n : ℕ)
    (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    (AdicKoszul.derivedUniverseLift A).obj
        (DerivedCategory.Q.obj ((coefficientCompletionStage f n).obj K)) ≅
      (AdicKoszul.tensorKoszulPowerSystem f T (DerivedCategory.Q.obj K)).obj ⟨n⟩ := by
  let E := KoszulCoefficientTower.standardKoszulStage
    (fun i ↦ (ULift.up (f i) : ULift.{v} A)) none n
  have hE : E.KFlat := by
    let C := Koszul.seqComplex (fun i ↦ (ULift.up (f i) : ULift.{v} A) ^ (n + 1))
    let (j : ℕ) : Projective (C.X j) := by
      change Projective (ModuleCat.of (ULift.{v} A) (⋀[ULift.{v} A]^j (Fin r → ULift.{v} A)))
      exact ModuleCat.projective_of_free ((Pi.basisFun (ULift.{v} A) (Fin r)).exteriorPower j)
    let (j : ℤ) : Module.Flat (ULift.{v} A)
        ((C.extend ComplexShape.embeddingDownNat).X j) := by infer_instance
    exact CochainComplex.KFlat.kFlat_of_flat (C.extend ComplexShape.embeddingDownNat) 0
  exact (AdicKoszul.moduleUniverseLift.{u, v} A).mapDerivedCategoryFactors.app
      ((coefficientCompletionStage f n).obj K) ≪≫
    DerivedCategory.Q.mapIso
      ((KoszulCoefficientTower.coefficientKoszulComparison f none n).app K) ≪≫
    tensorComparisonIso T ((KoszulCoefficientTower.complexUniverseLift (A := A)).obj K)
      E hE ≪≫
    (T.tensor.flip.obj (DerivedCategory.Q.obj E)).mapIso
      ((AdicKoszul.moduleUniverseLift.{u, v} A).mapDerivedCategoryFactors.app K).symm

/-- Naturality of the already specified coefficient-to-tensor isomorphisms. -/
public structure StageComparisonNaturality {r : ℕ} (f : Fin r → A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{v} A)) : Prop where
  naturality (n : ℕ) {K L : CochainComplex (ModuleCat.{v} A) ℤ} (g : K ⟶ L) :
    (AdicKoszul.derivedUniverseLift A).map
        (DerivedCategory.Q.map ((coefficientCompletionStage f n).map g)) ≫
        (coefficientStageComparisonIso f T n L).hom =
      (coefficientStageComparisonIso f T n K).hom ≫
        (T.tensor.map ((AdicKoszul.derivedUniverseLift A).map (DerivedCategory.Q.map g))).app
          ((AdicKoszul.canonicalKoszulPowerSystem
            (fun i ↦ (ULift.up (f i) : ULift.{v} A))).obj ⟨n⟩)

/-- The fixed coefficient-to-tensor comparison, as a natural isomorphism. The argument
supplies only a proof of naturality of its prescribed components. -/
public def StageComparisonNaturality.comparison {r : ℕ} {f : Fin r → A}
    {T : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{v} A)}
    (h : StageComparisonNaturality f T) (n : ℕ) :
    coefficientCompletionStage f n ⋙
        DerivedCategory.Q (C := ModuleCat.{v} A) ⋙ AdicKoszul.derivedUniverseLift A ≅
      DerivedCategory.Q (C := ModuleCat.{v} A) ⋙ AdicKoszul.derivedUniverseLift A ⋙
        T.tensor.flip.obj ((AdicKoszul.canonicalKoszulPowerSystem
          (fun i ↦ (ULift.up (f i) : ULift.{v} A))).obj ⟨n⟩) :=
  NatIso.ofComponents (coefficientStageComparisonIso f T n) (h.naturality n)

/-- Localize the strict Milnor projection composed with the fixed tensor comparison.
Only the naturality proof is an argument; all component maps have been specified. -/
public def StageComparisonNaturality.projection {r : ℕ} {f : Fin r → A}
    {T : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{v} A)}
    (h : StageComparisonNaturality f T) (n : ℕ) :
    completionFunctor f ⋙ AdicKoszul.derivedUniverseLift A ⟶
      AdicKoszul.derivedUniverseLift A ⋙ T.tensor.flip.obj
        ((AdicKoszul.canonicalKoszulPowerSystem
          (fun i ↦ (ULift.up (f i) : ULift.{v} A))).obj ⟨n⟩) := by
  letI : Localization.Lifting (DerivedCategory.Q (C := ModuleCat.{v} A))
      (HomologicalComplex.quasiIso (ModuleCat.{v} A) (ComplexShape.up ℤ))
      (coefficientCompletionComplex f ⋙ DerivedCategory.Q (C := ModuleCat.{v} A))
      (completionFunctor f) :=
    Localization.liftingLift _ (coefficientCompletion_isInvertedBy f) _
  letI : Localization.Lifting (DerivedCategory.Q (C := ModuleCat.{v} A))
      (HomologicalComplex.quasiIso (ModuleCat.{v} A) (ComplexShape.up ℤ))
      (coefficientCompletionComplex f ⋙ DerivedCategory.Q ⋙
        AdicKoszul.derivedUniverseLift A)
      (completionFunctor f ⋙ AdicKoszul.derivedUniverseLift A) :=
    Localization.Lifting.compRight
      (DerivedCategory.Q (C := ModuleCat.{v} A))
      (HomologicalComplex.quasiIso (ModuleCat.{v} A) (ComplexShape.up ℤ))
      (coefficientCompletionComplex f ⋙ DerivedCategory.Q)
      (completionFunctor f) (AdicKoszul.derivedUniverseLift A)
  exact Localization.liftNatTrans (DerivedCategory.Q (C := ModuleCat.{v} A))
    (HomologicalComplex.quasiIso (ModuleCat.{v} A) (ComplexShape.up ℤ))
    (coefficientCompletionComplex f ⋙ DerivedCategory.Q ⋙
      AdicKoszul.derivedUniverseLift A)
    (DerivedCategory.Q ⋙ AdicKoszul.derivedUniverseLift A ⋙ T.tensor.flip.obj
      ((AdicKoszul.canonicalKoszulPowerSystem
        (fun i ↦ (ULift.up (f i) : ULift.{v} A))).obj ⟨n⟩))
    (completionFunctor f ⋙ AdicKoszul.derivedUniverseLift A)
    (AdicKoszul.derivedUniverseLift A ⋙ T.tensor.flip.obj
      ((AdicKoszul.canonicalKoszulPowerSystem
        (fun i ↦ (ULift.up (f i) : ULift.{v} A))).obj ⟨n⟩))
    (Functor.whiskerRight (Functor.whiskerRight (coefficientCompletionProjection f n)
      DerivedCategory.Q) (AdicKoszul.derivedUniverseLift A) ≫ (h.comparison n).hom)

public local instance derivedCountableProducts (R : Type*) [CommRing R] :
    HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} R)) :=
  Stacks.DerivedProducts.hasProductsOfShape_derivedCategory

/-- The Milnor and unit identities for the fixed localized projections. This proposition
contains no choice of functor, transformation, or comparison map. -/
public structure CompletionComparisonLaws {r : ℕ} {f : Fin r → A}
    {T : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{v} A)}
    (h : StageComparisonNaturality f T) : Prop where
  milnor (K : DerivedCategory (ModuleCat.{v} A)) :
    ∃ δ : (∏ᶜ fun n : ℕ ↦ (AdicKoszul.tensorKoszulPowerSystem f T K).obj ⟨n⟩) ⟶
        ((AdicKoszul.derivedUniverseLift A).obj ((completionFunctor f).obj K))⟦(1 : ℤ)⟧,
      Triangle.mk (Pi.lift fun n ↦ (h.projection n).app K)
        (Pi.lift fun n : ℕ ↦
          Pi.π (fun n : ℕ ↦ (AdicKoszul.tensorKoszulPowerSystem f T K).obj ⟨n⟩) n -
            Pi.π (fun n : ℕ ↦ (AdicKoszul.tensorKoszulPowerSystem f T K).obj ⟨n⟩) (n + 1) ≫
              (AdicKoszul.tensorKoszulPowerSystem f T K).map
                (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory (ModuleCat.{max u v} (ULift.{v} A)))
  unit_projection (K : DerivedCategory (ModuleCat.{v} A)) (n : ℕ) :
    (AdicKoszul.derivedUniverseLift A).map ((completionUnit f).app K) ≫
        (h.projection n).app K = AdicKoszul.derivedTensorKoszulPowerUnit f T K n

/-- Universe enlargement preserves countable products in the derived category. The proof
uses complex representatives only in the source category. -/
public instance derivedUniverseLift_preservesProducts :
    PreservesLimitsOfShape (Discrete ℕ) (AdicKoszul.derivedUniverseLift.{u, v} A) := by
  let Q := DerivedCategory.Q (C := ModuleCat.{v} A)
  let U := AdicKoszul.derivedUniverseLift.{u, v} A
  let V := KoszulCoefficientTower.complexUniverseLift.{u, v} (A := A)
  let : PreservesLimitsOfShape (Discrete ℕ) Q :=
    Stacks.DerivedProducts.preservesLimitsOfShape_Q
  let : PreservesLimitsOfShape (Discrete ℕ)
      (DerivedCategory.Q (C := ModuleCat.{max u v} (ULift.{v} A))) :=
    Stacks.DerivedProducts.preservesLimitsOfShape_Q
  let : PreservesLimitsOfSize.{0, 0} (ModuleCat.uliftFunctor.{u, v} A) :=
    preservesSmallestLimits_of_preservesLimits _
  let : PreservesLimitsOfShape (Discrete ℕ) V := by infer_instance
  let : PreservesLimitsOfShape (Discrete ℕ) (Q ⋙ U) :=
    preservesLimitsOfShape_of_natIso
      (AdicKoszul.moduleUniverseLift.{u, v} A).mapDerivedCategoryFactors.symm
  let : ∀ K : ℕ → DerivedCategory (ModuleCat.{v} A),
      PreservesLimit (Discrete.functor K) U := by
    intro K
    let P : ℕ → CochainComplex (ModuleCat.{v} A) ℤ := fun n ↦ Q.objPreimage (K n)
    have hc := limit.isLimit (Discrete.functor P)
    let : PreservesLimit (Discrete.functor P ⋙ Q) U :=
      preservesLimit_of_preserves_limit_cone (isLimitOfPreserves Q hc)
        (isLimitOfPreserves (Q ⋙ U) hc)
    exact preservesLimit_of_iso_diagram (K₁ := Discrete.functor P ⋙ Q) U
      (Discrete.natIso (fun n ↦ Q.objObjPreimageIso (K n.as)))
  exact preservesLimitsOfShape_of_discrete U

/-- Universe enlargement reflects vanishing of scalar-tower derived limits on objects in
its image. These assertions concern only towers
whose terms come from the original module universe. -/
public structure UniverseLiftComparisonLaws (A : Type u) [CommRing A] : Prop where
  scalar_zero (a : A) (K : DerivedCategory (ModuleCat.{v} A)) :
    (∃ L, IsDerivedLimit
        (Functor.ofOpSequence (X := fun _ : ℕ ↦ (AdicKoszul.derivedUniverseLift A).obj K)
          (fun _ ↦ (ULift.up a : ULift.{v} A) • 𝟙 _)) L ∧ IsZero L) ↔
      (∃ L, IsDerivedLimit
        (Functor.ofOpSequence (X := fun _ : ℕ ↦ K) (fun _ ↦ a • 𝟙 K)) L ∧ IsZero L)

end KoszulCompletion
end

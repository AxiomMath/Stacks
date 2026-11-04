module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Fractions
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
public import Mathlib.Tactic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedBoundedCohomologicalDimension
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.ShortComplex.InverseLimit
public import StacksFrontier.CategoryTheory.EssentiallyConstant.IndObject
public import StacksFrontier.CategoryTheory.Functor.Derived.DefinedAt
public import StacksFrontier.CategoryTheory.MittagLefflerSections
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.DoubleResolution
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleInverseLimitFunctor.MittagLefflerPrefix
import all StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleInverseLimitFunctor.MittagLefflerPrefix

/-!
# Existence of the derived inverse-limit functor for modules

Exactness of the inverse-limit functor on short exact sequences with Mittag--Leffler first term,
additivity, the adapted-class existence on `K⁺`, the vanishing in degree two, existence on the
unbounded derived category, and the computation of the derived limit on single module systems.
Part of `ModuleInverseLimitFunctor`.
-/

section

open CategoryTheory Limits

universe u v

private instance moduleDiagramFunctor_preservesZeroMorphisms
    (rings : ℕᵒᵖ ⥤ RingCat.{u}) :
    (ModuleInverseLimit.moduleDiagramFunctor.{u, v} rings).PreservesZeroMorphisms where
  map_zero := by
    intro source target
    ext index element
    rfl

private instance inverseLimit_preservesZeroMorphisms
    (rings : ℕᵒᵖ ⥤ RingCat.{u}) :
    (ModuleInverseLimit.inverseLimit.{u, v} rings).PreservesZeroMorphisms := by
  unfold ModuleInverseLimit.inverseLimit
  infer_instance

private theorem inverseLimit_shortExact_of_pointwise
    (rings : ℕᵒᵖ ⥤ RingCat.{u})
    (sequence : ShortComplex (PresheafOfModules.{v} rings))
    (pointwise : ∀ index : ℕᵒᵖ,
      ((sequence.map (ModuleInverseLimit.moduleDiagramFunctor rings)).map
        ((evaluation ℕᵒᵖ (ModuleCat.{v} (limit rings : RingCat.{u}))).obj index)).ShortExact)
    (mittagLeffler : (ModuleInverseLimit.moduleDiagram rings sequence.X₁ ⋙
      forget (ModuleCat.{v} (limit rings : RingCat.{u}))).IsMittagLeffler) :
    (sequence.map (ModuleInverseLimit.inverseLimit rings)).ShortExact :=
  CategoryTheory.ShortComplex.shortExact_map_lim_of_isMittagLeffler
    (sequence.map (ModuleInverseLimit.moduleDiagramFunctor rings)) pointwise mittagLeffler

private theorem moduleDiagram_pointwise_shortExact
    (rings : ℕᵒᵖ ⥤ RingCat.{u})
    (sequence : ShortComplex (PresheafOfModules.{v} rings))
    (shortExact : sequence.ShortExact) (index : ℕᵒᵖ) :
    ((sequence.map (ModuleInverseLimit.moduleDiagramFunctor rings)).map
      ((evaluation ℕᵒᵖ (ModuleCat.{v} (limit rings : RingCat.{u}))).obj index)).ShortExact := by
  have evaluated := shortExact.map_of_exact (PresheafOfModules.evaluation rings index)
  refine
    { exact := ?_
      mono_f := ?_
      epi_g := ?_ }
  · exact (ShortComplex.moduleCat_exact_iff _).2
      ((ShortComplex.moduleCat_exact_iff
        (sequence.map (PresheafOfModules.evaluation rings index))).1 evaluated.exact)
  · exact (ModuleCat.mono_iff_injective _).2
      ((ModuleCat.mono_iff_injective (sequence.f.app index)).1 evaluated.mono_f)
  · exact (ModuleCat.epi_iff_surjective _).2
      ((ModuleCat.epi_iff_surjective (sequence.g.app index)).1 evaluated.epi_g)

@[ega "0 13.2.2" "Case I = ℕ"]
private theorem inverseLimit_shortExact_of_isMittagLeffler
    (rings : ℕᵒᵖ ⥤ RingCat.{u})
    (sequence : ShortComplex (PresheafOfModules.{v} rings))
    (shortExact : sequence.ShortExact)
    (mittagLeffler : (ModuleInverseLimit.moduleDiagram rings sequence.X₁ ⋙
      forget (ModuleCat.{v} (limit rings : RingCat.{u}))).IsMittagLeffler) :
    (sequence.map (ModuleInverseLimit.inverseLimit rings)).ShortExact :=
  inverseLimit_shortExact_of_pointwise rings sequence
    (moduleDiagram_pointwise_shortExact rings sequence shortExact) mittagLeffler

@[ega "0 13.2.2" "Case I = ℕ"]
private theorem inverseLimit_shortExact_of_presheaf_isMittagLeffler
    (rings : ℕᵒᵖ ⥤ RingCat.{u})
    (sequence : ShortComplex (PresheafOfModules.{v} rings))
    (shortExact : sequence.ShortExact)
    (mittagLeffler : (sequence.X₁.presheaf ⋙ forget Ab).IsMittagLeffler) :
    (sequence.map (ModuleInverseLimit.inverseLimit rings)).ShortExact :=
  inverseLimit_shortExact_of_isMittagLeffler rings sequence shortExact mittagLeffler

namespace ModuleInverseLimit

/-- Restricting every term of a compatible module system to the inverse-limit ring is additive. -/
public theorem moduleDiagramFunctor_additive
    (rings : ℕᵒᵖ ⥤ RingCat.{u}) :
    (ModuleInverseLimit.moduleDiagramFunctor.{u, v} rings).Additive where
  map_add := by
    intro source target first second
    ext index element
    rfl

/-- The inverse-limit functor of compatible module systems is additive. -/
public theorem inverseLimit_additive
    (rings : ℕᵒᵖ ⥤ RingCat.{u}) :
    (ModuleInverseLimit.inverseLimit.{u, v} rings).Additive := by
  let : (lim : (ℕᵒᵖ ⥤ ModuleCat.{v} (limit rings : RingCat.{u})) ⥤
      ModuleCat.{v} (limit rings : RingCat.{u})).Additive :=
    Functor.additive_of_preserves_binary_products _
  let := moduleDiagramFunctor_additive.{u, v} rings
  unfold ModuleInverseLimit.inverseLimit
  infer_instance

end ModuleInverseLimit

attribute [local instance] ModuleInverseLimit.moduleDiagramFunctor_additive
  ModuleInverseLimit.inverseLimit_additive


private theorem presheaf_mittagLeffler_of_epi
    {rings : ℕᵒᵖ ⥤ RingCat.{u}}
    {source target : PresheafOfModules.{v} rings}
    (quotient : source ⟶ target) [Epi quotient]
    (mittagLeffler : (source.presheaf ⋙ forget Ab).IsMittagLeffler) :
    (target.presheaf ⋙ forget Ab).IsMittagLeffler :=
  Functor.isMittagLeffler_of_surjective_natTrans
    (Functor.whiskerRight ((PresheafOfModules.toPresheaf rings).map quotient) (forget Ab))
    (fun index => PresheafOfModules.surjective_of_epi quotient index) mittagLeffler

private theorem inverseLimit_adapted_shortExact
    (rings : ℕᵒᵖ ⥤ RingCat.{u})
    (sequence : ShortComplex (PresheafOfModules.{v} rings))
    (shortExact : sequence.ShortExact)
    (firstML : (sequence.X₁.presheaf ⋙ forget Ab).IsMittagLeffler)
    (secondML : (sequence.X₂.presheaf ⋙ forget Ab).IsMittagLeffler) :
    (sequence.X₃.presheaf ⋙ forget Ab).IsMittagLeffler ∧
      (sequence.map (ModuleInverseLimit.inverseLimit rings)).ShortExact := by
  have : Epi sequence.g := shortExact.epi_g
  exact ⟨presheaf_mittagLeffler_of_epi sequence.g secondML,
    inverseLimit_shortExact_of_presheaf_isMittagLeffler rings sequence shortExact firstML⟩


attribute [local instance] HasDerivedCategory.standard

private theorem inverseLimit_hasPointwiseRightDerivedFunctor_of_enough_ml
    (rings : ℕᵒᵖ ⥤ RingCat.{u})
    (enough : ∀ system : PresheafOfModules.{v} rings,
      ∃ (envelope : PresheafOfModules.{v} rings)
        (_ : (envelope.presheaf ⋙ forget Ab).IsMittagLeffler)
        (embedding : system ⟶ envelope), Mono embedding) :
    ∃ derived : ((ModuleInverseLimit.inverseLimit rings).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh).HasPointwiseRightDerivedFunctor
          (HomotopyCategory.Plus.quasiIso (PresheafOfModules.{v} rings)),
      letI := derived
      (fun system : PresheafOfModules.{v} rings =>
        (system.presheaf ⋙ forget Ab).IsMittagLeffler) ≤
          (ModuleInverseLimit.inverseLimit rings).rightAcyclic :=
  (ModuleInverseLimit.inverseLimit rings).hasPointwiseRightDerivedFunctor_and_le_rightAcyclic
    (fun system => (system.presheaf ⋙ forget Ab).IsMittagLeffler) enough
    (inverseLimit_adapted_shortExact rings)

namespace ModuleInverseLimit

private theorem inverseLimit_bounded_pointwise
    (rings : ℕᵒᵖ ⥤ RingCat.{u}) :
    ∃ derived : ((ModuleInverseLimit.inverseLimit rings).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh).HasPointwiseRightDerivedFunctor
          (HomotopyCategory.Plus.quasiIso (PresheafOfModules.{v} rings)),
      letI := derived
      (fun system : PresheafOfModules.{v} rings =>
        (system.presheaf ⋙ forget Ab).IsMittagLeffler) ≤
          (ModuleInverseLimit.inverseLimit rings).rightAcyclic :=
  inverseLimit_hasPointwiseRightDerivedFunctor_of_enough_ml rings fun system =>
    ⟨prefixSystem rings system, prefixSystem_isMittagLeffler rings system,
      prefixUnitMap rings system, prefixUnitMap_mono rings system⟩

end ModuleInverseLimit


-- The prefix systems below are compared with limits and products of restricted modules, whose
-- scalar actions agree only after unfolding the module structures involved.
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace ModuleInverseLimit

private theorem mittagLeffler_computes_source
    (rings : ℕᵒᵖ ⥤ RingCat.{u}) (system : PresheafOfModules.{v} rings)
    (mittagLeffler : (system.presheaf ⋙ forget Ab).IsMittagLeffler) :
    CategoryTheory.Functor.ComputesRightDerived
      ((ModuleInverseLimit.inverseLimit rings).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
      (HomotopyCategory.Plus.quasiIso (PresheafOfModules.{v} rings))
      ((HomotopyCategory.Plus.singleFunctor (PresheafOfModules.{v} rings) 0).obj system) := by
  classical
  let functor := ModuleInverseLimit.inverseLimit.{u, v} rings
  let mlObjects : ObjectProperty (PresheafOfModules.{v} rings) := fun object =>
    (object.presheaf ⋙ forget Ab).IsMittagLeffler
  have enough : ∀ object : PresheafOfModules.{v} rings,
      ∃ (envelope : PresheafOfModules.{v} rings) (_ : mlObjects envelope)
        (embedding : object ⟶ envelope), Mono embedding := fun object =>
    ⟨prefixSystem rings object, prefixSystem_isMittagLeffler rings object,
      prefixUnitMap rings object, prefixUnitMap_mono rings object⟩
  let weakEquivalences := HomotopyCategory.Plus.quasiIso (PresheafOfModules.{v} rings)
  let localizer := CategoryTheory.Functor.RightAcyclicCriterion.inclusionLocalizerMorphism
    weakEquivalences (CategoryTheory.Functor.RightAcyclicCriterion.termwise mlObjects)
  obtain ⟨structureProof, derives⟩ :=
    functor.isRightDerivabilityStructure_and_derives_of_adapted mlObjects enough
      (inverseLimit_adapted_shortExact rings)
  have : localizer.IsRightDerivabilityStructure := structureProof
  obtain ⟨derived, acyclic⟩ := inverseLimit_bounded_pointwise rings
  let := derived
  let original := functor.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh
  let derivedFunctor := original.totalRightDerived DerivedCategory.Plus.Qh weakEquivalences
  let unit := original.totalRightDerivedUnit DerivedCategory.Plus.Qh weakEquivalences
  have cofinal : ∀ object : HomotopyCategory.Plus (PresheafOfModules.{v} rings),
      ∃ (resolution : HomotopyCategory.Plus (PresheafOfModules.{v} rings))
        (comparison : object ⟶ resolution) (_ : weakEquivalences comparison),
        IsIso (unit.app resolution) := by
    intro object
    let resolution : localizer.RightResolution object := Classical.arbitrary _
    exact ⟨resolution.X₁.obj, resolution.w, resolution.hw,
      derives.isIso_of_isRightDerivedFunctor unit resolution.X₁⟩
  have : weakEquivalences.HasLeftCalculusOfFractions := by
    dsimp [weakEquivalences]
    rw [HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW]
    infer_instance
  exact (CategoryTheory.Functor.computesRightDerived_iff_isIso_app original
    DerivedCategory.Plus.Qh derivedFunctor weakEquivalences unit _ cofinal).2
    (acyclic system mittagLeffler)


private theorem inverseLimit_enough_source_acyclic
    (rings : ℕᵒᵖ ⥤ RingCat.{u}) (system : PresheafOfModules.{v} rings) :
    ∃ (envelope : PresheafOfModules.{v} rings) (embedding : system ⟶ envelope),
      Mono embedding ∧ CategoryTheory.Functor.ComputesRightDerived
        ((ModuleInverseLimit.inverseLimit rings).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
        (HomotopyCategory.Plus.quasiIso (PresheafOfModules.{v} rings))
        ((HomotopyCategory.Plus.singleFunctor (PresheafOfModules.{v} rings) 0).obj envelope) :=
  ⟨prefixSystem rings system, prefixUnitMap rings system,
    prefixUnitMap_mono rings system,
    mittagLeffler_computes_source rings (prefixSystem rings system)
      (prefixSystem_isMittagLeffler rings system)⟩

/-- `inverseLimit_enough_source_acyclic` with the monomorphism as a dependent witness. -/
private theorem inverseLimit_enough_source_acyclic_exists
    (rings : ℕᵒᵖ ⥤ RingCat.{u}) (system : PresheafOfModules.{v} rings) :
    ∃ (envelope : PresheafOfModules.{v} rings) (embedding : system ⟶ envelope)
      (_ : Mono embedding), CategoryTheory.Functor.ComputesRightDerived
        ((ModuleInverseLimit.inverseLimit rings).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
        (HomotopyCategory.Plus.quasiIso (PresheafOfModules.{v} rings))
        ((HomotopyCategory.Plus.singleFunctor (PresheafOfModules.{v} rings) 0).obj envelope) := by
  obtain ⟨envelope, embedding, mono, computes⟩ := inverseLimit_enough_source_acyclic rings system
  exact ⟨envelope, embedding, mono, computes⟩

private instance moduleDiagramFunctor_preservesFiniteLimits
    (rings : ℕᵒᵖ ⥤ RingCat.{u}) :
    PreservesFiniteLimits (ModuleInverseLimit.moduleDiagramFunctor.{u, v} rings) where
  preservesFiniteLimits shape _ _ := by
    apply preservesLimitsOfShape_of_evaluation
    intro index
    constructor
    intro diagram
    change PreservesLimit diagram
      (PresheafOfModules.evaluation rings index ⋙
        ModuleCat.restrictScalars.{v} (limit.π rings index).hom)
    infer_instance

private instance inverseLimit_preservesFiniteLimits
    (rings : ℕᵒᵖ ⥤ RingCat.{u}) :
    PreservesFiniteLimits (ModuleInverseLimit.inverseLimit.{u, v} rings) := by
  unfold ModuleInverseLimit.inverseLimit
  exact comp_preservesFiniteLimits (ModuleInverseLimit.moduleDiagramFunctor.{u, v} rings) lim


private theorem inverseLimit_unbounded_exists_of_bound_two
    (rings : ℕᵒᵖ ⥤ RingCat.{u})
    (derivedFunctor : DerivedCategory.Plus (PresheafOfModules.{v} rings) ⥤
      DerivedCategory.Plus (ModuleCat.{v} (limit rings : RingCat.{u})))
    (unit : (ModuleInverseLimit.inverseLimit rings).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh ⟶ DerivedCategory.Plus.Qh ⋙ derivedFunctor)
    [derivedFunctor.IsRightDerivedFunctor unit
      (HomotopyCategory.Plus.quasiIso (PresheafOfModules.{v} rings))]
    (bound : ∀ system : PresheafOfModules.{v} rings,
      IsZero ((DerivedCategory.Plus.homologyFunctor
        (ModuleCat.{v} (limit rings : RingCat.{u})) 2).obj
          (derivedFunctor.obj
            ((DerivedCategory.Plus.singleFunctor (PresheafOfModules.{v} rings) 0).obj system)))) :
    ((ModuleInverseLimit.inverseLimit rings).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso (PresheafOfModules.{v} rings) (ComplexShape.up ℤ)) := by
  let predicate : ObjectProperty (PresheafOfModules.{v} rings) := fun system =>
    CategoryTheory.Functor.ComputesRightDerived
      ((ModuleInverseLimit.inverseLimit rings).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
      (HomotopyCategory.Plus.quasiIso (PresheafOfModules.{v} rings))
      ((HomotopyCategory.Plus.singleFunctor (PresheafOfModules.{v} rings) 0).obj system)
  exact (CategoryTheory.Functor.hasRightDerivedFunctor_of_isZero_rightDerived
    (ModuleInverseLimit.inverseLimit.{u, v} rings) derivedFunctor unit predicate
    (fun _ => Iff.rfl) (inverseLimit_enough_source_acyclic_exists rings) 2 bound).1


end ModuleInverseLimit

open CategoryTheory Limits ZeroObject DerivedCategory Pretriangulated

namespace ModuleInverseLimit.BoundTwo
universe categoryLevel targetLevel morphismLevel targetMorphismLevel
variable {A : Type categoryLevel} {B : Type targetLevel}
  [Category.{morphismLevel} A] [Category.{targetMorphismLevel} B]
  [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
private lemma exists_distTriang_singleFunctor
    {S : ShortComplex A} (hS : S.ShortExact) :
    ∃ δ, Triangle.mk ((Plus.singleFunctor A 0).map S.f) ((Plus.singleFunctor A 0).map S.g) δ
      ∈ distTriang (DerivedCategory.Plus A) := by
  obtain ⟨δ, hδ⟩ : ∃ δ : (Plus.singleFunctor A 0).obj S.X₃ ⟶
      ((Plus.singleFunctor A 0).obj S.X₁)⟦(1 : ℤ)⟧,
      Plus.ι.map δ ≫ (Plus.ι.commShiftIso (1 : ℤ)).hom.app
        ((Plus.singleFunctor A 0).obj S.X₁) = hS.singleδ :=
    ⟨Plus.ι.preimage (hS.singleδ ≫ (Plus.ι.commShiftIso (1 : ℤ)).inv.app
      ((Plus.singleFunctor A 0).obj S.X₁)), by
        rw [Functor.map_preimage]
        exact (Iso.eq_comp_inv ((Plus.ι.commShiftIso (1 : ℤ)).app
          ((Plus.singleFunctor A 0).obj S.X₁))).1 rfl⟩
  refine ⟨δ, ?_⟩
  rw [← Plus.ι.map_distinguished_iff]
  refine isomorphic_distinguished _ hS.singleTriangle_distinguished _
    (Triangle.isoMk _ _ ((Plus.singleFunctorιIso A 0).app S.X₁)
      ((Plus.singleFunctorιIso A 0).app S.X₂) ((Plus.singleFunctorιIso A 0).app S.X₃)
      ?_ ?_ ?_)
  · exact (Plus.singleFunctorιIso A 0).hom.naturality S.f
  · exact (Plus.singleFunctorιIso A 0).hom.naturality S.g
  · show (Plus.ι.map δ ≫ (Plus.ι.commShiftIso (1 : ℤ)).hom.app
          ((Plus.singleFunctor A 0).obj S.X₁)) ≫
        (shiftFunctor (DerivedCategory A) (1 : ℤ)).map
          (𝟙 ((DerivedCategory.singleFunctor A 0).obj S.X₁)) =
      𝟙 ((DerivedCategory.singleFunctor A 0).obj S.X₃) ≫ hS.singleδ
    exact (congrArg (fun v => (Plus.ι.map δ ≫ (Plus.ι.commShiftIso (1 : ℤ)).hom.app
          ((Plus.singleFunctor A 0).obj S.X₁)) ≫ v)
        (CategoryTheory.Functor.map_id (shiftFunctor (DerivedCategory A) (1 : ℤ))
          ((DerivedCategory.singleFunctor A 0).obj S.X₁))).trans
      ((Category.comp_id _).trans (hδ.trans (Category.id_comp _).symm))

variable (F : A ⥤ B) [F.Additive]



end ModuleInverseLimit.BoundTwo

namespace ModuleInverseLimit

private theorem inverseLimit_bound_two
    (rings : ℕᵒᵖ ⥤ RingCat.{u})
    (derivedFunctor : DerivedCategory.Plus (PresheafOfModules.{v} rings) ⥤
      DerivedCategory.Plus (ModuleCat.{v} (limit rings : RingCat.{u})))
    (unit : (ModuleInverseLimit.inverseLimit rings).mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh ⟶ DerivedCategory.Plus.Qh ⋙ derivedFunctor)
    [derivedFunctor.IsRightDerivedFunctor unit
      (HomotopyCategory.Plus.quasiIso (PresheafOfModules.{v} rings))]
    [derivedFunctor.CommShift ℤ] [derivedFunctor.IsTriangulated]
    (system : PresheafOfModules.{v} rings) :
    IsZero ((DerivedCategory.Plus.homologyFunctor
      (ModuleCat.{v} (limit rings : RingCat.{u})) 2).obj
        (derivedFunctor.obj
          ((DerivedCategory.Plus.singleFunctor (PresheafOfModules.{v} rings) 0).obj system))) := by
  let embedding := prefixUnitMap rings system
  have : Mono embedding := prefixUnitMap_mono rings system
  let sequence := ShortComplex.mk embedding (cokernel.π embedding) (cokernel.condition embedding)
  have shortExact : sequence.ShortExact := { exact := ShortComplex.exact_cokernel embedding }
  have unitIso (object : PresheafOfModules.{v} rings)
      (mittagLeffler : (object.presheaf ⋙ forget Ab).IsMittagLeffler) :
      IsIso (unit.app
        ((HomotopyCategory.Plus.singleFunctor (PresheafOfModules.{v} rings) 0).obj object)) :=
    (CategoryTheory.Functor.computesRightDerived_iff_isIso_unit_of_enough_source_acyclic_objects
      (ModuleInverseLimit.inverseLimit.{u, v} rings) (inverseLimit_enough_source_acyclic rings)
      derivedFunctor unit _).1 (mittagLeffler_computes_source rings object mittagLeffler)
  exact StacksDraft.RightDerivedBoundedDimension.isZero_homology_left_of_shortExact
    derivedFunctor sequence shortExact 1
    (StacksDraft.RightDerivedBoundedDimension.isZero_homology_of_isIso_unit
      (ModuleInverseLimit.inverseLimit.{u, v} rings)
      derivedFunctor unit (prefixSystem rings system)
      (unitIso _ (prefixSystem_isMittagLeffler rings system)) 2 (by decide))
    (StacksDraft.RightDerivedBoundedDimension.isZero_homology_of_isIso_unit
      (ModuleInverseLimit.inverseLimit.{u, v} rings)
      derivedFunctor unit (cokernel embedding)
      (unitIso _ (prefixCokernel_isMittagLeffler rings system)) 1 (by decide))

/-- A right derived functor on `D⁺` of the inverse limit whose degree-two cohomology vanishes
on single systems. -/
private theorem inverseLimit_exists_derived_bound_two
    (rings : ℕᵒᵖ ⥤ RingCat.{u}) :
    ∃ (derivedFunctor : DerivedCategory.Plus (PresheafOfModules.{v} rings) ⥤
      DerivedCategory.Plus (ModuleCat.{v} (limit rings : RingCat.{u})))
      (unit : (ModuleInverseLimit.inverseLimit rings).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh ⟶ DerivedCategory.Plus.Qh ⋙ derivedFunctor)
      (_ : derivedFunctor.IsRightDerivedFunctor unit
        (HomotopyCategory.Plus.quasiIso (PresheafOfModules.{v} rings))),
      ∀ system : PresheafOfModules.{v} rings,
        IsZero ((DerivedCategory.Plus.homologyFunctor
          (ModuleCat.{v} (limit rings : RingCat.{u})) 2).obj
            (derivedFunctor.obj
              ((DerivedCategory.Plus.singleFunctor (PresheafOfModules.{v} rings) 0).obj
                system))) := by
  obtain ⟨derived, triangulated, _⟩ :=
    CategoryTheory.Functor.hasRightDerivedFunctor_of_enough_source_acyclic_objects
      (ModuleInverseLimit.inverseLimit.{u, v} rings) (inverseLimit_enough_source_acyclic rings)
  let := derived
  let original := (ModuleInverseLimit.inverseLimit.{u, v} rings).mapHomotopyCategoryPlus ⋙
    DerivedCategory.Plus.Qh
  let weakEquivalences := HomotopyCategory.Plus.quasiIso (PresheafOfModules.{v} rings)
  let derivedFunctor := original.totalRightDerived DerivedCategory.Plus.Qh weakEquivalences
  let unit := original.totalRightDerivedUnit DerivedCategory.Plus.Qh weakEquivalences
  have : derivedFunctor.IsTriangulated := triangulated
  exact ⟨derivedFunctor, unit, inferInstance, inverseLimit_bound_two rings derivedFunctor unit⟩

private theorem inverseLimit_unbounded_exists
    (rings : ℕᵒᵖ ⥤ RingCat.{u}) :
    ((ModuleInverseLimit.inverseLimit.{u, v} rings).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso (PresheafOfModules.{v} rings) (ComplexShape.up ℤ)) := by
  obtain ⟨boundedFunctor, boundedUnit, _, bound⟩ := inverseLimit_exists_derived_bound_two rings
  exact inverseLimit_unbounded_exists_of_bound_two rings boundedFunctor boundedUnit bound


private abbrev sourceAcyclicSystem (rings : ℕᵒᵖ ⥤ RingCat.{u}) :
    ObjectProperty (PresheafOfModules.{v} rings) := fun system =>
  CategoryTheory.Functor.ComputesRightDerived
    ((ModuleInverseLimit.inverseLimit rings).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
    (HomotopyCategory.Plus.quasiIso (PresheafOfModules.{v} rings))
    ((HomotopyCategory.Plus.singleFunctor (PresheafOfModules.{v} rings) 0).obj system)

private theorem inverseLimit_unbounded_controls
    (rings : ℕᵒᵖ ⥤ RingCat.{u})
    (derivedFunctor : DerivedCategory (PresheafOfModules.{v} rings) ⥤
      DerivedCategory (ModuleCat.{v} (limit rings : RingCat.{u})))
    (unit : (ModuleInverseLimit.inverseLimit rings).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ derivedFunctor)
    [derivedFunctor.IsRightDerivedFunctor unit
      (HomotopyCategory.quasiIso (PresheafOfModules.{v} rings) (ComplexShape.up ℤ))] :
    (∀ (system : PresheafOfModules.{v} rings) (degree : ℤ), 1 < degree →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} (limit rings : RingCat.{u}))
        degree).obj (derivedFunctor.obj
          ((DerivedCategory.singleFunctor (PresheafOfModules.{v} rings) 0).obj system)))) ∧
    (∀ complex : CochainComplex (PresheafOfModules.{v} rings) ℤ,
      ∃ (replacement : CochainComplex (PresheafOfModules.{v} rings) ℤ)
        (comparison : complex ⟶ replacement) (_ : QuasiIso comparison),
        ∀ degree, sourceAcyclicSystem rings (replacement.X degree)) ∧
    (∀ complex : CochainComplex (PresheafOfModules.{v} rings) ℤ,
      (∀ degree, sourceAcyclicSystem rings (complex.X degree)) →
        IsIso (unit.app
          ((HomotopyCategory.quotient (PresheafOfModules.{v} rings) (ComplexShape.up ℤ)).obj
            complex))) := by
  obtain ⟨boundedFunctor, boundedUnit, _, bound⟩ := inverseLimit_exists_derived_bound_two rings
  obtain ⟨_, replacements, universal⟩ :=
    CategoryTheory.Functor.hasRightDerivedFunctor_of_isZero_rightDerived
      (ModuleInverseLimit.inverseLimit.{u, v} rings) boundedFunctor boundedUnit
      (sourceAcyclicSystem rings) (fun _ => Iff.rfl)
      (inverseLimit_enough_source_acyclic_exists rings) 2
      bound
  have controls := universal derivedFunctor unit
  refine ⟨?_, replacements, controls.1⟩
  intro system degree greater
  let object := (DerivedCategory.singleFunctor (PresheafOfModules.{v} rings) 0).obj system
  have : (derivedFunctor.obj object).IsLE 1 := by
    simpa using (controls.2 object).2.2.2 0 inferInstance
  exact (derivedFunctor.obj object).isZero_of_isLE 1 degree greater


private theorem zeroSystem_mittagLeffler (rings : ℕᵒᵖ ⥤ RingCat.{u}) :
    ((0 : PresheafOfModules.{v} rings).presheaf ⋙ forget Ab).IsMittagLeffler := by
  apply Functor.isMittagLeffler_of_surjective
  intro source target transition value
  have targetZero : IsZero ((PresheafOfModules.evaluation rings target).obj
      (0 : PresheafOfModules.{v} rings)) :=
    (PresheafOfModules.evaluation rings target).map_isZero (isZero_zero _)
  have targetSubsingleton : Subsingleton ((0 : PresheafOfModules.{v} rings).obj target) :=
    ModuleCat.subsingleton_of_isZero targetZero
  exact ⟨0, @Subsingleton.elim _ targetSubsingleton _ _⟩

private theorem sourceAcyclicSystem_of_isZero
    (rings : ℕᵒᵖ ⥤ RingCat.{u}) (system : PresheafOfModules.{v} rings)
    (zero : IsZero system) : sourceAcyclicSystem rings system :=
  mittagLeffler_computes_source rings system
    (presheaf_mittagLeffler_of_epi zero.isoZero.inv (zeroSystem_mittagLeffler rings))

private theorem single_has_source_acyclic_terms
    (rings : ℕᵒᵖ ⥤ RingCat.{u}) (system : PresheafOfModules.{v} rings)
    (computes : sourceAcyclicSystem rings system) (degree : ℤ) :
    sourceAcyclicSystem rings
      (((CochainComplex.singleFunctor (PresheafOfModules.{v} rings) 0).obj system).X degree) := by
  by_cases same : degree = 0
  · subst degree
    show sourceAcyclicSystem rings system
    exact computes
  · exact sourceAcyclicSystem_of_isZero rings _
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 system degree same)

private theorem inverseLimit_unbounded_unit_single_of_source
    (rings : ℕᵒᵖ ⥤ RingCat.{u})
    (derivedFunctor : DerivedCategory (PresheafOfModules.{v} rings) ⥤
      DerivedCategory (ModuleCat.{v} (limit rings : RingCat.{u})))
    (unit : (ModuleInverseLimit.inverseLimit rings).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ derivedFunctor)
    [derivedFunctor.IsRightDerivedFunctor unit
      (HomotopyCategory.quasiIso (PresheafOfModules.{v} rings) (ComplexShape.up ℤ))]
    (system : PresheafOfModules.{v} rings) (computes : sourceAcyclicSystem rings system) :
    IsIso (unit.app ((HomotopyCategory.singleFunctor (PresheafOfModules.{v} rings) 0).obj system))
      :=
  (inverseLimit_unbounded_controls rings derivedFunctor unit).2.2
    ((CochainComplex.singleFunctor (PresheafOfModules.{v} rings) 0).obj system)
    (single_has_source_acyclic_terms rings system computes)

private theorem inverseLimit_unbounded_homology_of_source
    (rings : ℕᵒᵖ ⥤ RingCat.{u})
    (derivedFunctor : DerivedCategory (PresheafOfModules.{v} rings) ⥤
      DerivedCategory (ModuleCat.{v} (limit rings : RingCat.{u})))
    (unit : (ModuleInverseLimit.inverseLimit rings).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ derivedFunctor)
    [derivedFunctor.IsRightDerivedFunctor unit
      (HomotopyCategory.quasiIso (PresheafOfModules.{v} rings) (ComplexShape.up ℤ))]
    (system : PresheafOfModules.{v} rings) (computes : sourceAcyclicSystem rings system)
    (degree : ℤ) (nonzero : degree ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} (limit rings : RingCat.{u}))
      degree).obj (derivedFunctor.obj
        ((DerivedCategory.singleFunctor (PresheafOfModules.{v} rings) 0).obj system))) := by
  have : IsIso (unit.app
      ((HomotopyCategory.singleFunctor (PresheafOfModules.{v} rings) 0).obj system)) :=
    inverseLimit_unbounded_unit_single_of_source rings derivedFunctor unit system computes
  let sourceIso :
      ((ModuleInverseLimit.inverseLimit rings).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).obj
          ((HomotopyCategory.singleFunctor (PresheafOfModules.{v} rings) 0).obj system) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{v} (limit rings : RingCat.{u})) 0).obj
        ((ModuleInverseLimit.inverseLimit rings).obj system) :=
    DerivedCategory.Qh.mapIso
      ((CategoryTheory.Functor.mapHomotopyCategorySingleFunctor
        (ModuleInverseLimit.inverseLimit.{u, v} rings)
        0).app system) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQh
        (ModuleCat.{v} (limit rings : RingCat.{u})) 0).app
          ((ModuleInverseLimit.inverseLimit rings).obj system)).symm
  let objectIso := derivedFunctor.mapIso
      ((DerivedCategory.singleFunctorIsoCompQh (PresheafOfModules.{v} rings) 0).app system) ≪≫
    (asIso (unit.app
      ((HomotopyCategory.singleFunctor (PresheafOfModules.{v} rings) 0).obj system))).symm ≪≫
    sourceIso
  have zero : IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{v} (limit rings : RingCat.{u})) degree).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{v} (limit rings : RingCat.{u})) 0).obj
          ((ModuleInverseLimit.inverseLimit rings).obj system))) := by
    rcases nonzero.lt_or_gt with less | greater
    · exact ((DerivedCategory.singleFunctor (ModuleCat.{v} (limit rings : RingCat.{u})) 0).obj
        ((ModuleInverseLimit.inverseLimit rings).obj system)).isZero_of_isGE 0 degree less
    · exact ((DerivedCategory.singleFunctor (ModuleCat.{v} (limit rings : RingCat.{u})) 0).obj
        ((ModuleInverseLimit.inverseLimit rings).obj system)).isZero_of_isLE 0 degree greater
  exact zero.of_iso ((DerivedCategory.homologyFunctor
    (ModuleCat.{v} (limit rings : RingCat.{u})) degree).mapIso objectIso)

private theorem inverseLimit_unbounded_replacements
    (rings : ℕᵒᵖ ⥤ RingCat.{u})
    (derivedFunctor : DerivedCategory (PresheafOfModules.{v} rings) ⥤
      DerivedCategory (ModuleCat.{v} (limit rings : RingCat.{u})))
    (unit : (ModuleInverseLimit.inverseLimit rings).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ derivedFunctor)
    [derivedFunctor.IsRightDerivedFunctor unit
      (HomotopyCategory.quasiIso (PresheafOfModules.{v} rings) (ComplexShape.up ℤ))]
    (complex : CochainComplex (PresheafOfModules.{v} rings) ℤ) :
    ∃ (replacement : CochainComplex (PresheafOfModules.{v} rings) ℤ)
      (comparison : complex ⟶ replacement) (_ : QuasiIso comparison),
      ∀ degree, IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{v} (limit rings : RingCat.{u})) 1).obj
          (derivedFunctor.obj ((DerivedCategory.singleFunctor
            (PresheafOfModules.{v} rings) 0).obj (replacement.X degree)))) := by
  obtain ⟨replacement, comparison, quasiIso, computes⟩ :=
    (inverseLimit_unbounded_controls rings derivedFunctor unit).2.1 complex
  exact ⟨replacement, comparison, quasiIso, fun degree =>
    inverseLimit_unbounded_homology_of_source rings derivedFunctor unit
      (replacement.X degree) (computes degree) 1 (by decide)⟩

private theorem inverseLimit_unbounded_ml_homology_one
    (rings : ℕᵒᵖ ⥤ RingCat.{u})
    (derivedFunctor : DerivedCategory (PresheafOfModules.{v} rings) ⥤
      DerivedCategory (ModuleCat.{v} (limit rings : RingCat.{u})))
    (unit : (ModuleInverseLimit.inverseLimit rings).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ derivedFunctor)
    [derivedFunctor.IsRightDerivedFunctor unit
      (HomotopyCategory.quasiIso (PresheafOfModules.{v} rings) (ComplexShape.up ℤ))]
    (system : PresheafOfModules.{v} rings)
    (mittagLeffler : (system.presheaf ⋙ forget Ab).IsMittagLeffler) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} (limit rings : RingCat.{u})) 1).obj
      (derivedFunctor.obj
        ((DerivedCategory.singleFunctor (PresheafOfModules.{v} rings) 0).obj system))) :=
  inverseLimit_unbounded_homology_of_source rings derivedFunctor unit system
    (mittagLeffler_computes_source rings system mittagLeffler) 1 (by decide)

end ModuleInverseLimit

end

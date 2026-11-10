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
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleInverseLimitFunctor.TwoTermModel
import all StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleInverseLimitFunctor.MittagLefflerPrefix
import all StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleInverseLimitFunctor.Existence
import all StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleInverseLimitFunctor.TwoTermModel

/-!
# Termwise computation of the derived inverse limit

Naturality of the two-term product model, right acyclicity of systems whose first derived
limit vanishes, the termwise computation for complexes of right-acyclic terms, and Stacks 091D.
Part of `ModuleInverseLimitFunctor`.
-/

section

open CategoryTheory Limits

universe u v

attribute [local instance] ModuleInverseLimit.moduleDiagramFunctor_additive
  ModuleInverseLimit.inverseLimit_additive

attribute [local instance] HasDerivedCategory.standard

-- The prefix systems below are compared with limits and products of restricted modules, whose
-- scalar actions agree only after unfolding the module structures involved.
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits ZeroObject DerivedCategory Pretriangulated

noncomputable section

open CategoryTheory Limits

namespace ModuleInverseLimit.Naturality

attribute [local instance] HasDerivedCategory.standard

private abbrev product (rings : ℕᵒᵖ ⥤ RingCat.{u})
    (system : PresheafOfModules.{v} rings) :=
  ∏ᶜ fun index : ℕ => (ModuleInverseLimit.moduleDiagram rings system).obj (Opposite.op index)

private def shift (rings : ℕᵒᵖ ⥤ RingCat.{u})
    (system : PresheafOfModules.{v} rings) : product rings system ⟶ product rings system :=
  Pi.lift fun index =>
    Pi.π (fun index : ℕ =>
      (ModuleInverseLimit.moduleDiagram rings system).obj (Opposite.op index)) (index + 1) ≫
        (ModuleInverseLimit.moduleDiagram rings system).map (homOfLE (Nat.le_succ index)).op

private def delta (rings : ℕᵒᵖ ⥤ RingCat.{u})
    (system : PresheafOfModules.{v} rings) : product rings system ⟶ product rings system :=
  𝟙 _ - shift rings system

@[reassoc]
private theorem inverseLimitToProduct_pi (rings : ℕᵒᵖ ⥤ RingCat.{u})
    (system : PresheafOfModules.{v} rings) (index : ℕ) :
    ModuleInverseLimit.inverseLimitToProduct rings system ≫
      Pi.π (fun index : ℕ =>
        (ModuleInverseLimit.moduleDiagram rings system).obj (Opposite.op index)) index =
      limit.π (ModuleInverseLimit.moduleDiagram rings system) (Opposite.op index) :=
  Pi.lift_comp_π (fun index : ℕ =>
    limit.π (ModuleInverseLimit.moduleDiagram rings system) (Opposite.op index)) index

private theorem inverseLimitToProduct_naturality (rings : ℕᵒᵖ ⥤ RingCat.{u})
    {source target : PresheafOfModules.{v} rings} (morphism : source ⟶ target) :
    ModuleInverseLimit.inverseLimitToProduct rings source ≫ ModuleInverseLimit.productMap rings
      morphism =
      (ModuleInverseLimit.inverseLimit rings).map morphism ≫
        ModuleInverseLimit.inverseLimitToProduct rings target := by
  apply Pi.hom_ext
  intro index
  simp only [ModuleInverseLimit.productMap, Category.assoc, Pi.lift_comp_π,
    inverseLimitToProduct_pi_assoc, inverseLimitToProduct_pi, ModuleInverseLimit.inverseLimit_map_π]

private theorem shift_naturality (rings : ℕᵒᵖ ⥤ RingCat.{u})
    {source target : PresheafOfModules.{v} rings} (morphism : source ⟶ target) :
    shift rings source ≫ ModuleInverseLimit.productMap rings morphism =
      ModuleInverseLimit.productMap rings morphism ≫ shift rings target := by
  apply Pi.hom_ext
  intro index
  simp only [shift, ModuleInverseLimit.productMap, Category.assoc, Pi.lift_comp_π_assoc,
    Pi.lift_comp_π]
  rw [(ModuleInverseLimit.moduleDiagramMap rings morphism).naturality]

private theorem delta_naturality (rings : ℕᵒᵖ ⥤ RingCat.{u})
    {source target : PresheafOfModules.{v} rings} (morphism : source ⟶ target) :
    delta rings source ≫ ModuleInverseLimit.productMap rings morphism =
      ModuleInverseLimit.productMap rings morphism ≫ delta rings target := by
  simp only [delta, Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp,
    Category.comp_id, shift_naturality]

private theorem inverseLimitToProduct_delta (rings : ℕᵒᵖ ⥤ RingCat.{u})
    (system : PresheafOfModules.{v} rings) :
    ModuleInverseLimit.inverseLimitToProduct rings system ≫ delta rings system = 0 := by
  have fixed : ModuleInverseLimit.inverseLimitToProduct rings system ≫ shift rings system =
      ModuleInverseLimit.inverseLimitToProduct rings system := by
    apply Pi.hom_ext
    intro index
    simp only [shift, Category.assoc, Pi.lift_comp_π,
      inverseLimitToProduct_pi_assoc, inverseLimitToProduct_pi]
    exact limit.w (ModuleInverseLimit.moduleDiagram rings system) (homOfLE (Nat.le_succ index)).op
  simp only [delta, Preadditive.comp_sub, Category.comp_id, fixed, sub_self]

private theorem inverseLimitToProduct_mono (rings : ℕᵒᵖ ⥤ RingCat.{u})
    (system : PresheafOfModules.{v} rings) :
    Mono (ModuleInverseLimit.inverseLimitToProduct rings system) := by
  constructor
  intro point first second equal
  apply limit.hom_ext
  intro index
  have projected := congrArg (fun arrow : point ⟶ product rings system =>
    arrow ≫ Pi.π (fun index : ℕ =>
      (ModuleInverseLimit.moduleDiagram rings system).obj (Opposite.op index)) index.unop) equal
  simp only [Category.assoc, inverseLimitToProduct_pi] at projected
  exact projected

private def kernelCone (rings : ℕᵒᵖ ⥤ RingCat.{u})
    (system : PresheafOfModules.{v} rings)
    {point : ModuleCat.{v} (limit rings : RingCat.{u})}
    (arrow : point ⟶ product rings system) (annihilates : arrow ≫ delta rings system = 0) :
    Cone (ModuleInverseLimit.moduleDiagram rings system) := by
  let diagram := ModuleInverseLimit.moduleDiagram rings system
  let coordinate (index : ℕ) := arrow ≫ Pi.π (fun index : ℕ =>
    diagram.obj (Opposite.op index)) index
  have fixed : arrow = arrow ≫ shift rings system := by
    apply sub_eq_zero.mp
    simpa only [delta, Preadditive.comp_sub, Category.comp_id] using annihilates
  have successor (index : ℕ) :
      coordinate (index + 1) ≫ diagram.map (homOfLE (Nat.le_succ index)).op =
        coordinate index := by
    calc
      _ = (arrow ≫ shift rings system) ≫
          Pi.π (fun index : ℕ => diagram.obj (Opposite.op index)) index := by
        simp only [coordinate, shift, diagram, Category.assoc, Pi.lift_comp_π]
      _ = coordinate index := by rw [← fixed]
  have comparable (lower upper : ℕ) (ordered : lower ≤ upper) :
      coordinate upper ≫ diagram.map (homOfLE ordered).op = coordinate lower := by
    induction upper, ordered using Nat.le_induction with
    | base => simp
    | succ upper ordered inductionHypothesis =>
      have factorization : (homOfLE (Nat.le_succ_of_le ordered)).op =
          (homOfLE (Nat.le_succ upper)).op ≫ (homOfLE ordered).op := Subsingleton.elim _ _
      rw [factorization, Functor.map_comp, ← Category.assoc, successor, inductionHypothesis]
  refine ⟨point, { app := fun index => coordinate index.unop, naturality := ?_ }⟩
  intro source target morphism
  change 𝟙 point ≫ coordinate target.unop = coordinate source.unop ≫ diagram.map morphism
  rw [Category.id_comp]
  have ordered : target.unop ≤ source.unop := leOfHom morphism.unop
  have identify : morphism = (homOfLE ordered).op := Subsingleton.elim _ _
  rw [identify]
  exact (comparable target.unop source.unop ordered).symm

private def inverseLimitToProduct_isKernel (rings : ℕᵒᵖ ⥤ RingCat.{u})
    (system : PresheafOfModules.{v} rings) :
    IsLimit (KernelFork.ofι (ModuleInverseLimit.inverseLimitToProduct rings system)
      (inverseLimitToProduct_delta rings system)) := by
  letI := inverseLimitToProduct_mono rings system
  apply KernelFork.IsLimit.ofι'
  intro point arrow annihilates
  let lift : point ⟶ (ModuleInverseLimit.inverseLimit rings).obj system := by
    exact limit.lift _ (kernelCone rings system arrow annihilates)
  refine ⟨lift, ?_⟩
  apply Pi.hom_ext
  intro index
  rw [Category.assoc, inverseLimitToProduct_pi]
  exact limit.lift_π (kernelCone rings system arrow annihilates) (Opposite.op index)

private theorem inverseLimitToProduct_delta_exact (rings : ℕᵒᵖ ⥤ RingCat.{u})
    (system : PresheafOfModules.{v} rings) :
    (ShortComplex.mk (ModuleInverseLimit.inverseLimitToProduct rings system) (delta rings system)
      (inverseLimitToProduct_delta rings system)).Exact :=
  ShortComplex.exact_of_f_is_kernel _ (inverseLimitToProduct_isKernel rings system)

private theorem inverseLimitToProduct_delta_shortExact_of_epi (rings : ℕᵒᵖ ⥤ RingCat.{u})
    (system : PresheafOfModules.{v} rings) [Epi (delta rings system)] :
    (ShortComplex.mk (ModuleInverseLimit.inverseLimitToProduct rings system) (delta rings system)
      (inverseLimitToProduct_delta rings system)).ShortExact := by
  have := inverseLimitToProduct_mono rings system
  exact ⟨inverseLimitToProduct_delta_exact rings system⟩

private theorem inverseLimitToProduct_delta_shortExact_of_model
    (rings : ℕᵒᵖ ⥤ RingCat.{u}) (system : PresheafOfModules.{v} rings)
    (derivedFunctor : DerivedCategory (PresheafOfModules.{v} rings) ⥤
      DerivedCategory (ModuleCat.{v} (limit rings : RingCat.{u})))
    (homologyOneZero : IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{v} (limit rings : RingCat.{u})) 1).obj
        (derivedFunctor.obj
          ((DerivedCategory.singleFunctor (PresheafOfModules.{v} rings) 0).obj system))))
    (complex : CochainComplex (ModuleCat.{v} (limit rings : RingCat.{u})) ℤ)
    (degreeZeroIso : complex.X 0 ≅ product rings system)
    (degreeOneIso : complex.X 1 ≅ product rings system)
    (supported : ∀ degree : ℤ, degree ≠ 0 → degree ≠ 1 → IsZero (complex.X degree))
    (differential : degreeZeroIso.inv ≫ complex.d 0 1 ≫ degreeOneIso.hom = delta rings system)
    (model : Nonempty (derivedFunctor.obj
      ((DerivedCategory.singleFunctor (PresheafOfModules.{v} rings) 0).obj system) ≅
        DerivedCategory.Q.obj complex)) :
    (ShortComplex.mk (ModuleInverseLimit.inverseLimitToProduct rings system) (delta rings system)
      (inverseLimitToProduct_delta rings system)).ShortExact := by
  obtain ⟨modelIso⟩ := model
  have derivedHomologyZero : IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{v} (limit rings : RingCat.{u})) 1).obj (DerivedCategory.Q.obj complex)) :=
    homologyOneZero.of_iso ((DerivedCategory.homologyFunctor
      (ModuleCat.{v} (limit rings : RingCat.{u})) 1).mapIso modelIso.symm)
  have homologyZero : IsZero (complex.homology 1) :=
    (Iso.isZero_iff ((DerivedCategory.homologyFunctorFactors
      (ModuleCat.{v} (limit rings : RingCat.{u})) 1).app complex)).1 derivedHomologyZero
  have exactAtOne : complex.ExactAt 1 :=
    (complex.exactAt_iff_isZero_homology 1).2 homologyZero
  have shortExact : (complex.sc' 0 1 2).Exact :=
    (HomologicalComplex.exactAt_iff' complex 0 1 2 (by simp) (by simp)).1 exactAtOne
  have outgoingZero : (complex.sc' 0 1 2).g = 0 :=
    (supported 2 (by decide) (by decide)).eq_of_tgt _ _
  have : Epi (complex.d 0 1) := shortExact.epi_f outgoingZero
  have : Epi (delta rings system) := by
    rw [← differential]
    infer_instance
  exact inverseLimitToProduct_delta_shortExact_of_epi rings system


end ModuleInverseLimit.Naturality

namespace ModuleInverseLimit

private theorem inverseLimit_unbounded_shortExact_of_homology_one_zero
    (rings : ℕᵒᵖ ⥤ RingCat.{u})
    (derivedFunctor : DerivedCategory (PresheafOfModules.{v} rings) ⥤
      DerivedCategory (ModuleCat.{v} (limit rings : RingCat.{u})))
    (unit : (inverseLimit rings).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ derivedFunctor)
    [derivedFunctor.IsRightDerivedFunctor unit
      (HomotopyCategory.quasiIso (PresheafOfModules.{v} rings) (ComplexShape.up ℤ))]
    (system : PresheafOfModules.{v} rings)
    (homologyOneZero : IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{v} (limit rings : RingCat.{u})) 1).obj
        (derivedFunctor.obj
          ((DerivedCategory.singleFunctor (PresheafOfModules.{v} rings) 0).obj system)))) :
    ∃ zero : inverseLimitToProduct rings system ≫ productDelta rings system = 0,
      (ShortComplex.mk (inverseLimitToProduct rings system) (productDelta rings system)
        zero).ShortExact := by
  obtain ⟨complex, zeroIso, oneIso, supported, differential, model⟩ :=
    inverseLimit_unbounded_twoTerm_model_data rings derivedFunctor unit system
  exact ⟨ModuleInverseLimit.Naturality.inverseLimitToProduct_delta rings system,
    ModuleInverseLimit.Naturality.inverseLimitToProduct_delta_shortExact_of_model rings system
      derivedFunctor homologyOneZero complex zeroIso oneIso supported differential model⟩

private theorem finiteDifference_map_shortExact_of_epi
    (rings : ℕᵒᵖ ⥤ RingCat.{u}) (system : PresheafOfModules.{v} rings)
    [Epi (productDelta rings system)] :
    ((ShortComplex.mk (prefixUnitMap rings system) (finiteDifference rings system)
      (prefixUnitMap_finiteDifference rings system)).map (inverseLimit rings)).ShortExact := by
  let sequence := ShortComplex.mk (prefixUnitMap rings system) (finiteDifference rings system)
    (prefixUnitMap_finiteDifference rings system)
  have shortExact := finiteDifference_shortExact rings system
  have : Mono sequence.f := shortExact.mono_f
  have compositionEpi : Epi ((prefixLimitIso rings system).inv ≫
      (inverseLimit rings).map (finiteDifference rings system) ≫
        (shortPrefixLimitIso rings system).hom) := by
    rw [finiteDifference_limit_eq_delta]
    infer_instance
  have : Epi ((inverseLimit rings).map sequence.g) :=
    (epi_comp_iff_of_isIso _ (shortPrefixLimitIso rings system).hom).1
      (epi_of_epi (prefixLimitIso rings system).inv _)
  exact {
    exact := shortExact.exact.map_of_mono_of_preservesKernel (inverseLimit rings)
      inferInstance inferInstance
    mono_f := by
      change Mono ((inverseLimit rings).map sequence.f)
      infer_instance
    epi_g := by
      change Epi ((inverseLimit rings).map sequence.g)
      infer_instance }

private theorem finiteResolution_isStrictlyGE (rings : ℕᵒᵖ ⥤ RingCat.{u})
    (system : PresheafOfModules.{v} rings) : (finiteResolution rings system).IsStrictlyGE 0 := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro degree below
  exact HomologicalComplex.isZero_double_X _ _ degree (by omega) (by omega)

private theorem sourceAcyclicSystem_of_delta_epi
    (rings : ℕᵒᵖ ⥤ RingCat.{u}) (system : PresheafOfModules.{v} rings)
    [Epi (productDelta rings system)] : sourceAcyclicSystem rings system := by
  obtain ⟨pointwise, _, _⟩ :=
    CategoryTheory.Functor.hasRightDerivedFunctor_of_enough_source_acyclic_objects
    (inverseLimit.{u, v} rings) (inverseLimit_enough_source_acyclic rings)
  let := pointwise
  let original := (inverseLimit rings).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh
  let derivedFunctor := original.totalRightDerived DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso (PresheafOfModules.{v} rings))
  let unit := original.totalRightDerivedUnit DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso (PresheafOfModules.{v} rings))
  let resolution : HomotopyCategory.Plus (PresheafOfModules.{v} rings) :=
    ⟨(HomotopyCategory.quotient _ _).obj (finiteResolution rings system),
      (HomotopyCategory.plus_quotient_obj_iff _).2 ⟨0, finiteResolution_isStrictlyGE rings system⟩⟩
  let comparison :
      (HomotopyCategory.Plus.singleFunctor (PresheafOfModules.{v} rings) 0).obj system ⟶
        resolution :=
    ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map (finiteResolutionUnit rings system))
  have := finiteResolutionUnit_quasiIso rings system
  have : QuasiIso (((inverseLimit rings).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (finiteResolutionUnit rings system)) :=
    Stacks.DoubleResolution.map_shortExactResolutionUnit_quasiIso (inverseLimit rings) _
      (finiteDifference_map_shortExact_of_epi rings system)
  have : IsIso (original.map comparison) := by
    suffices IsIso (DerivedCategory.Plus.ι.map (original.map comparison)) from
      isIso_of_reflects_iso _ DerivedCategory.Plus.ι
    change IsIso (DerivedCategory.Qh.map
      (((inverseLimit rings).mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((HomotopyCategory.quotient _ _).map (finiteResolutionUnit rings system))))
    exact (NatIso.isIso_map_iff
      (Functor.isoWhiskerRight
        (Functor.mapHomotopyCategoryFactors (inverseLimit rings) (ComplexShape.up ℤ))
          DerivedCategory.Qh ≪≫
        Functor.isoWhiskerLeft ((inverseLimit rings).mapHomologicalComplex (ComplexShape.up ℤ))
          (DerivedCategory.quotientCompQhIso (ModuleCat.{v} (limit rings : RingCat.{u}))))
      (finiteResolutionUnit rings system)).2
        (show IsIso (DerivedCategory.Q.map
          (((inverseLimit rings).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (finiteResolutionUnit rings system))) from inferInstance)
  have : IsIso (unit.app resolution) :=
    (CategoryTheory.Functor.isIso_unit_and_isGE_of_enough_source_acyclic_objects
      (inverseLimit.{u, v} rings)
      (inverseLimit_enough_source_acyclic rings) derivedFunctor unit).1 resolution
        (finiteResolution_source_acyclic_terms rings system)
  have : IsIso (unit.app
      ((HomotopyCategory.Plus.singleFunctor (PresheafOfModules.{v} rings) 0).obj system) ≫
        (DerivedCategory.Plus.Qh ⋙ derivedFunctor).map comparison) := by
    rw [← unit.naturality comparison]
    infer_instance
  have : IsIso (DerivedCategory.Plus.Qh.map comparison) := by
    suffices IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map comparison)) from
      isIso_of_reflects_iso _ DerivedCategory.Plus.ι
    change IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ _).map (finiteResolutionUnit rings system)))
    exact (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso (PresheafOfModules.{v} rings))
      (finiteResolutionUnit rings system)).2 inferInstance
  have : IsIso ((DerivedCategory.Plus.Qh ⋙ derivedFunctor).map comparison) := by
    change IsIso (derivedFunctor.map (DerivedCategory.Plus.Qh.map comparison))
    infer_instance
  apply (CategoryTheory.Functor.computesRightDerived_iff_isIso_unit_of_enough_source_acyclic_objects
    (inverseLimit.{u, v} rings) (inverseLimit_enough_source_acyclic rings) derivedFunctor unit _).2
  exact IsIso.of_isIso_comp_right _ ((DerivedCategory.Plus.Qh ⋙ derivedFunctor).map comparison)


private theorem sourceAcyclicSystem_of_homology_one_zero
    (rings : ℕᵒᵖ ⥤ RingCat.{u})
    (derivedFunctor : DerivedCategory (PresheafOfModules.{v} rings) ⥤
      DerivedCategory (ModuleCat.{v} (limit rings : RingCat.{u})))
    (unit : (inverseLimit rings).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ derivedFunctor)
    [derivedFunctor.IsRightDerivedFunctor unit
      (HomotopyCategory.quasiIso (PresheafOfModules.{v} rings) (ComplexShape.up ℤ))]
    (system : PresheafOfModules.{v} rings)
    (homologyOneZero : IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{v} (limit rings : RingCat.{u})) 1).obj
        (derivedFunctor.obj
          ((DerivedCategory.singleFunctor (PresheafOfModules.{v} rings) 0).obj system)))) :
    sourceAcyclicSystem rings system := by
  obtain ⟨zero, shortExact⟩ := inverseLimit_unbounded_shortExact_of_homology_one_zero
    rings derivedFunctor unit system homologyOneZero
  have : Epi (productDelta rings system) := shortExact.epi_g
  exact sourceAcyclicSystem_of_delta_epi rings system

private theorem inverseLimit_unbounded_termwise_computation
    (rings : ℕᵒᵖ ⥤ RingCat.{u})
    (derivedFunctor : DerivedCategory (PresheafOfModules.{v} rings) ⥤
      DerivedCategory (ModuleCat.{v} (limit rings : RingCat.{u})))
    (unit : (inverseLimit rings).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ derivedFunctor)
    [derivedFunctor.IsRightDerivedFunctor unit
      (HomotopyCategory.quasiIso (PresheafOfModules.{v} rings) (ComplexShape.up ℤ))]
    (complex : CochainComplex (PresheafOfModules.{v} rings) ℤ)
    (homologyOneZero : ∀ degree : ℤ, IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{v} (limit rings : RingCat.{u})) 1).obj
        (derivedFunctor.obj ((DerivedCategory.singleFunctor (PresheafOfModules.{v} rings) 0).obj
          (complex.X degree))))) :
    Nonempty (derivedFunctor.obj (DerivedCategory.Q.obj complex) ≅
      DerivedCategory.Q.obj
        (((inverseLimit rings).mapHomologicalComplex (ComplexShape.up ℤ)).obj complex)) := by
  have := (inverseLimit_unbounded_controls rings derivedFunctor unit).2.2 complex
    (fun degree => sourceAcyclicSystem_of_homology_one_zero rings derivedFunctor unit
      (complex.X degree) (homologyOneZero degree))
  exact inverseLimit_termwise_model_of_unit rings derivedFunctor unit complex


/-- **Stacks 091D.** For modules over an inverse system of rings, the inverse-limit functor has
a right derived functor on the unbounded derived category. Higher derived limits vanish above
degree one; the derived limit of a module system is represented by the two-term product complex
with differential `(x_n) ↦ (x_n - f_{n+1}(x_{n+1}))`; Mittag--Leffler systems are right
acyclic; every complex has a quasi-isomorphic complex of right-acyclic terms; and a termwise
right-acyclic complex computes its derived limit by taking inverse limits termwise. For each
right-acyclic system, the canonical limit cone and product differential form a natural short
exact sequence. -/
@[stacks 091D]
public theorem inverseLimit_hasRightDerivedFunctor_and_computations
    (rings : ℕᵒᵖ ⥤ RingCat.{u}) :
    let baseRing := limit rings
    let functor : PresheafOfModules.{v} rings ⥤ ModuleCat.{v} baseRing := inverseLimit rings
    let productFamily (system : PresheafOfModules.{v} rings) : ModuleCat.{v} baseRing :=
      ∏ᶜ fun n : ℕ ↦ (moduleDiagram rings system).obj (Opposite.op n)
    let shift (system : PresheafOfModules.{v} rings) : productFamily system ⟶ productFamily system
      := Pi.lift fun n ↦
      Pi.π (fun n : ℕ ↦ (moduleDiagram rings system).obj (Opposite.op n)) (n + 1) ≫
        (moduleDiagram rings system).map (homOfLE (Nat.le_succ n)).op
    let delta (system : PresheafOfModules.{v} rings) : productFamily system ⟶ productFamily system
      := 𝟙 (productFamily system) - shift system
    ∃ (additive : functor.Additive),
      letI := additive
      ∃ (derivedFunctor : DerivedCategory (PresheafOfModules.{v} rings) ⥤
            DerivedCategory (ModuleCat.{v} baseRing))
          (unit : functor.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
            DerivedCategory.Qh ⋙ derivedFunctor),
          derivedFunctor.IsRightDerivedFunctor unit
              (HomotopyCategory.quasiIso (PresheafOfModules.{v} rings) (ComplexShape.up ℤ)) ∧
          (∀ (system : PresheafOfModules.{v} rings) (degree : ℤ), 1 < degree →
            IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} baseRing) degree).obj
              (derivedFunctor.obj ((DerivedCategory.singleFunctor (PresheafOfModules.{v} rings)
                0).obj system)))) ∧
          (∀ system : PresheafOfModules.{v} rings, ∃ (complex : CochainComplex (ModuleCat.{v}
            baseRing) ℤ)
              (zeroIso : complex.X 0 ≅ productFamily system) (oneIso : complex.X 1 ≅ productFamily
                system),
            (∀ index : ℤ, index ≠ 0 → index ≠ 1 → IsZero (complex.X index)) ∧
            zeroIso.inv ≫ complex.d 0 1 ≫ oneIso.hom = delta system ∧
            Nonempty (derivedFunctor.obj
              ((DerivedCategory.singleFunctor (PresheafOfModules.{v} rings) 0).obj system) ≅
                DerivedCategory.Q.obj complex)) ∧
          (∀ system : PresheafOfModules.{v} rings, (system.presheaf ⋙ forget Ab).IsMittagLeffler →
            IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} baseRing) 1).obj
              (derivedFunctor.obj ((DerivedCategory.singleFunctor (PresheafOfModules.{v} rings)
                0).obj system)))) ∧
          (∀ system : PresheafOfModules.{v} rings,
            IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} baseRing) 1).obj
              (derivedFunctor.obj ((DerivedCategory.singleFunctor (PresheafOfModules.{v} rings)
                0).obj system))) →
            ∃ zeroComposition : inverseLimitToProduct rings system ≫ delta system = 0,
              (ShortComplex.mk (inverseLimitToProduct rings system) (delta system)
                zeroComposition).ShortExact) ∧
          (∀ {system targetSystem : PresheafOfModules.{v} rings} (morphism : system ⟶ targetSystem),
            inverseLimitToProduct rings system ≫ productMap rings morphism =
              functor.map morphism ≫ inverseLimitToProduct rings targetSystem ∧
            delta system ≫ productMap rings morphism = productMap rings morphism ≫ delta
              targetSystem) ∧
          (∀ complex : CochainComplex (PresheafOfModules.{v} rings) ℤ,
            ∃ (replacement : CochainComplex (PresheafOfModules.{v} rings) ℤ) (morphism : complex ⟶
              replacement) (_ : QuasiIso morphism),
              ∀ degree : ℤ, IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} baseRing) 1).obj
                (derivedFunctor.obj
                  ((DerivedCategory.singleFunctor (PresheafOfModules.{v} rings) 0).obj
                    (replacement.X degree))))) ∧
          ∀ complex : CochainComplex (PresheafOfModules.{v} rings) ℤ,
            (∀ degree : ℤ, IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} baseRing) 1).obj
              (derivedFunctor.obj
                ((DerivedCategory.singleFunctor (PresheafOfModules.{v} rings) 0).obj (complex.X
                  degree))))) →
            Nonempty (derivedFunctor.obj (DerivedCategory.Q.obj complex) ≅
              DerivedCategory.Q.obj
                ((functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj complex)) := by
  dsimp only
  refine ⟨inferInstance, ?_⟩
  have := inverseLimit_unbounded_exists.{u, v} rings
  let original := (inverseLimit.{u, v} rings).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh
  let weakEquivalences := HomotopyCategory.quasiIso (PresheafOfModules.{v} rings) (ComplexShape.up
    ℤ)
  let derivedFunctor := original.totalRightDerived DerivedCategory.Qh weakEquivalences
  let unit := original.totalRightDerivedUnit DerivedCategory.Qh weakEquivalences
  refine ⟨derivedFunctor, unit, inferInstance,
    (inverseLimit_unbounded_controls rings derivedFunctor unit).1,
    inverseLimit_unbounded_twoTerm_model_data rings derivedFunctor unit,
    inverseLimit_unbounded_ml_homology_one rings derivedFunctor unit,
    inverseLimit_unbounded_shortExact_of_homology_one_zero rings derivedFunctor unit,
    ?_, inverseLimit_unbounded_replacements rings derivedFunctor unit,
    inverseLimit_unbounded_termwise_computation rings derivedFunctor unit⟩
  intro source target morphism
  exact ⟨ModuleInverseLimit.Naturality.inverseLimitToProduct_naturality rings morphism,
    ModuleInverseLimit.Naturality.delta_naturality rings morphism⟩


end ModuleInverseLimit

end

end

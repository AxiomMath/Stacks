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
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleInverseLimitFunctor.Existence
import all StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleInverseLimitFunctor.MittagLefflerPrefix
import all StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleInverseLimitFunctor.Existence

/-!
# The two-term product model of the derived inverse limit

Finite prefix systems and their limits, the finite-difference resolution of a module system,
and the identification of the derived inverse limit of a module system with the two-term
product complex with differential `1 - shift`. Part of `ModuleInverseLimitFunctor`.
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

namespace ModuleInverseLimit

@[expose] noncomputable section

open Limits Opposite

universe ringLevel moduleLevel

public abbrev termProduct (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel})
    (system : PresheafOfModules.{moduleLevel} rings) :=
  ∏ᶜ fun index : ℕ => (moduleDiagram rings system).obj (op index)

/-- Restricting the projection of a limit ring element along `stage ⟶ op n` gives its projection. -/
private theorem limit_π_map_eq
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (stage : ℕᵒᵖ) (n : ℕ) (h : n ≤ stage.unop)
    (scalar : (limit rings : RingCat.{ringLevel})) :
    (rings.map (homOfLE h).op) ((limit.π rings stage).hom scalar) =
      (limit.π rings (op n)).hom scalar :=
  ConcreteCategory.congr_hom (limit.w rings (homOfLE h).op) scalar

/-- A transition map along `homOfLE (le_refl n)` is the identity. -/
private theorem map_homOfLE_op_refl_apply
    {rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}} (system : PresheafOfModules.{moduleLevel} rings)
    {n : ℕ} (h : n ≤ n) (value : system.obj (op n)) :
    system.map (homOfLE h).op value = value := by
  rw [show (homOfLE h).op = 𝟙 (op n) from Subsingleton.elim _ _, system.map_id]
  rfl

/-- Transition maps along `homOfLE` compose. -/
private theorem map_homOfLE_op_comp_apply
    {rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}} (system : PresheafOfModules.{moduleLevel} rings)
    {a b c : ℕ} (h₁ : a ≤ b) (h₂ : b ≤ c) (h₃ : a ≤ c) (value : system.obj (op c)) :
    system.map (homOfLE h₃).op value =
      system.map (homOfLE h₁).op (system.map (homOfLE h₂).op value) :=
  (system.congr_map_apply (show (homOfLE h₃).op = (homOfLE h₂).op ≫ (homOfLE h₁).op from
    Subsingleton.elim _ _) value).trans (system.map_comp_apply _ _ value)

private theorem prefixRestricted_smul
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings)
    (stage : ℕᵒᵖ) (scalar : (limit rings : RingCat.{ringLevel}))
    (values : (moduleDiagram rings (prefixSystem rings system)).obj stage)
    (index : Fin (stage.unop + 1)) :
    ((((moduleDiagram rings (prefixSystem rings system)).obj stage).smul scalar).asHom.hom
      values) index =
      (((moduleDiagram rings system).obj (op index.val)).smul scalar).asHom.hom (values index) := by
  change (rings.map (homOfLE (Nat.le_of_lt_succ index.isLt)).op)
      ((limit.π rings stage).hom scalar) • values index =
    ((limit.π rings (op index.val)).hom scalar) • values index
  rw [limit_π_map_eq]

private def prefixRestrictedEvaluation
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings)
    (stage : ℕᵒᵖ) (index : Fin (stage.unop + 1)) :
    (moduleDiagram rings (prefixSystem rings system)).obj stage ⟶
      (moduleDiagram rings system).obj (op index.val) := by
  letI : Module (limit rings : RingCat.{ringLevel})
      ((prefixSystem rings system).obj stage) :=
    ((moduleDiagram rings (prefixSystem rings system)).obj stage).isModule
  letI : Module (limit rings : RingCat.{ringLevel}) (system.obj (op index.val)) :=
    ((moduleDiagram rings system).obj (op index.val)).isModule
  exact ModuleCat.ofHom
    { toFun := fun values => values index
      map_add' := fun _ _ => rfl
      map_smul' := fun scalar values => prefixRestricted_smul rings system stage scalar values index
        }

private def prefixLimitCone
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings) :
    Cone (moduleDiagram rings (prefixSystem rings system)) where
  pt := termProduct rings system
  π :=
    { app := fun stage => by
        letI : Module (limit rings : RingCat.{ringLevel})
            ((prefixSystem rings system).obj stage) :=
          ((moduleDiagram rings (prefixSystem rings system)).obj stage).isModule
        exact ModuleCat.ofHom
          { toFun := fun values index =>
              Pi.π (fun index : ℕ => (moduleDiagram rings system).obj (op index)) index.val values
            map_add' := by
              intro first second
              funext index
              exact map_add _ first second
            map_smul' := by
              intro scalar values
              funext index
              change (Pi.π (fun index : ℕ => (moduleDiagram rings system).obj (op index))
                  index.val) (scalar • values) =
                ((((moduleDiagram rings (prefixSystem rings system)).obj stage).smul
                  scalar).asHom.hom
                  (fun index => Pi.π (fun index : ℕ =>
                    (moduleDiagram rings system).obj (op index)) index.val values)) index
              rw [prefixRestricted_smul]
              exact map_smul _ scalar values }
      naturality := by
        intro source target morphism
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro values
        funext index
        rfl }

private theorem prefixLimitCone_projection
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings)
    (stage : ℕᵒᵖ) (index : Fin (stage.unop + 1)) :
    (prefixLimitCone rings system).π.app stage ≫
      prefixRestrictedEvaluation rings system stage index =
        Pi.π (fun index : ℕ => (moduleDiagram rings system).obj (op index)) index.val := by
  apply ModuleCat.hom_ext
  rfl

private def prefixLimitConeIsLimit
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings) :
    IsLimit (prefixLimitCone rings system) where
  lift cone := Pi.lift fun index => cone.π.app (op index) ≫
    prefixRestrictedEvaluation rings system (op index) ⟨index, Nat.lt_succ_self index⟩
  fac cone stage := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro values
    funext index
    change Pi.π (fun index : ℕ => (moduleDiagram rings system).obj (op index)) index.val
        ((Pi.lift fun coordinate => cone.π.app (op coordinate) ≫
          prefixRestrictedEvaluation rings system (op coordinate)
            ⟨coordinate, Nat.lt_succ_self coordinate⟩) values) = cone.π.app stage values index
    rw [← ConcreteCategory.comp_apply, Pi.lift_comp_π]
    change cone.π.app (op index.val) values ⟨index.val, Nat.lt_succ_self index.val⟩ =
      cone.π.app stage values index
    have compatible := ConcreteCategory.congr_hom
      (cone.w (homOfLE (Nat.le_of_lt_succ index.isLt)).op) values
    exact (congrFun compatible ⟨index.val, Nat.lt_succ_self index.val⟩).symm
  uniq cone arrow factors := by
    apply Pi.hom_ext
    intro index
    have projected := congrArg (fun component => component ≫
      prefixRestrictedEvaluation rings system (op index) ⟨index, Nat.lt_succ_self index⟩)
        (factors (op index))
    rw [Pi.lift_comp_π]
    rw [Category.assoc, prefixLimitCone_projection] at projected
    exact projected

private def prefixLimitIso
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings) :
    (inverseLimit rings).obj (prefixSystem rings system) ≅ termProduct rings system :=
  limit.isoLimitCone ⟨prefixLimitCone rings system, prefixLimitConeIsLimit rings system⟩

private theorem prefixLimitIso_inv_projection
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings)
    (stage : ℕᵒᵖ) :
    (prefixLimitIso rings system).inv ≫
      limit.π (moduleDiagram rings (prefixSystem rings system)) stage =
        (prefixLimitCone rings system).π.app stage :=
  limit.isoLimitCone_inv_π _ _

private theorem prefixLimitIso_hom_projection
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings)
    (index : ℕ) :
    (prefixLimitIso rings system).hom ≫
      Pi.π (fun index : ℕ => (moduleDiagram rings system).obj (op index)) index =
        limit.π (moduleDiagram rings (prefixSystem rings system)) (op index) ≫
          prefixRestrictedEvaluation rings system (op index) ⟨index, Nat.lt_succ_self index⟩ := by
  rw [← cancel_epi (prefixLimitIso rings system).inv, Iso.inv_hom_id_assoc,
    ← Category.assoc, prefixLimitIso_inv_projection, prefixLimitCone_projection]

private theorem prefixUnitMap_restricted_last
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings)
    (index : ℕ) :
    (moduleDiagramMap rings (prefixUnitMap rings system)).app (op index) ≫
      prefixRestrictedEvaluation rings system (op index) ⟨index, Nat.lt_succ_self index⟩ =
        𝟙 ((moduleDiagram rings system).obj (op index)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro value
  change system.map (homOfLE (le_refl index)).op value = value
  exact map_homOfLE_op_refl_apply system _ value

private theorem prefixLimitIso_identifies_unit
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings) :
    (inverseLimit rings).map (prefixUnitMap rings system) ≫ (prefixLimitIso rings system).hom =
      inverseLimitToProduct rings system := by
  apply Pi.hom_ext
  intro index
  rw [Category.assoc, prefixLimitIso_hom_projection, ← Category.assoc,
    inverseLimit_map_π, Category.assoc, prefixUnitMap_restricted_last, Category.comp_id]
  exact (Pi.lift_comp_π (fun index : ℕ =>
    limit.π (moduleDiagram rings system) (op index)) index).symm

private instance shortPrefixComponentModule
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings)
    (stage : ℕ) (index : Fin stage) :
    Module (rings.obj (op stage)) (system.obj (op index.val)) :=
  Module.compHom _ (rings.map (homOfLE (Nat.le_of_lt index.isLt)).op).hom

private abbrev shortPrefixObj
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings)
    (stage : ℕ) : ModuleCat.{moduleLevel} (rings.obj (op stage)) :=
  ModuleCat.of _ ((index : Fin stage) → system.obj (op index.val))

private def shortPrefixMap
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings)
    {source target : ℕᵒᵖ} (transition : source ⟶ target) :
    shortPrefixObj rings system source.unop ⟶
      (ModuleCat.restrictScalars (rings.map transition).hom).obj
        (shortPrefixObj rings system target.unop) := by
  letI : Module (rings.obj source) (shortPrefixObj rings system source.unop) :=
    (shortPrefixObj rings system source.unop).isModule
  letI : Module (rings.obj target) (shortPrefixObj rings system target.unop) :=
    (shortPrefixObj rings system target.unop).isModule
  letI : Module (rings.obj source) (shortPrefixObj rings system target.unop) :=
    Module.compHom _ (rings.map transition).hom
  exact ModuleCat.ofHom
    { toFun := fun values index => values ⟨index.val, by
        have order := leOfHom transition.unop
        omega⟩
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro scalar values
        funext index
        change (rings.map (homOfLE (by
          have order := leOfHom transition.unop
          omega : index.val ≤ source.unop)).op) scalar •
            (values ⟨index.val, by have order := leOfHom transition.unop; omega⟩) =
            (rings.map (homOfLE (Nat.le_of_lt index.isLt)).op)
              ((rings.map transition) scalar) •
                (values ⟨index.val, by have order := leOfHom transition.unop; omega⟩)
        have factor : (homOfLE (by
            have order := leOfHom transition.unop
            omega : index.val ≤ source.unop)).op =
            transition ≫ (homOfLE (Nat.le_of_lt index.isLt)).op := Subsingleton.elim _ _
        rw [factor, rings.map_comp]
        rfl }

private def shortPrefixSystem
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings) :
    PresheafOfModules.{moduleLevel} rings where
  obj stage := shortPrefixObj rings system stage.unop
  map transition := shortPrefixMap rings system transition
  map_id stage := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro values
    funext index
    rfl
  map_comp first second := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro values
    funext index
    rfl

private theorem shortPrefixSystem_isMittagLeffler
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings) :
    ((shortPrefixSystem rings system).presheaf ⋙ forget Ab).IsMittagLeffler := by
  apply Functor.isMittagLeffler_of_surjective
  intro source target transition values
  refine ⟨fun index => if bound : index.val < target.unop then
    values ⟨index.val, bound⟩ else 0, ?_⟩
  funext index
  change (if bound : index.val < target.unop then values ⟨index.val, bound⟩ else 0) = values index
  simp [index.isLt]

private def transitionAddHom
    {rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}} (system : PresheafOfModules.{moduleLevel} rings)
    {source target : ℕᵒᵖ} (transition : source ⟶ target) :
    system.obj source →+ system.obj target where
  toFun value := system.map transition value
  map_zero' := map_zero _
  map_add' := map_add _

private theorem transitionAddHom_smul
    {rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}} (system : PresheafOfModules.{moduleLevel} rings)
    {source target : ℕᵒᵖ} (transition : source ⟶ target)
    (scalar : rings.obj source) (value : system.obj source) :
    transitionAddHom system transition (scalar • value) =
      (rings.map transition) scalar • transitionAddHom system transition value :=
  system.map_smul transition scalar value

private def finiteDifference
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings) :
    prefixSystem rings system ⟶ shortPrefixSystem rings system where
  app stage := by
    letI : Module (rings.obj stage) (prefixObj rings system stage.unop) :=
      (prefixObj rings system stage.unop).isModule
    letI : Module (rings.obj stage) (shortPrefixObj rings system stage.unop) :=
      (shortPrefixObj rings system stage.unop).isModule
    exact ModuleCat.ofHom
      { toFun := fun values index =>
          (values ⟨index.val, by omega⟩ : system.obj (op index.val)) -
            (transitionAddHom system (homOfLE (Nat.le_succ index.val)).op
              (values ⟨index.val + 1, by omega⟩) : system.obj (op index.val))
        map_add' := by
          intro first second
          funext index
          change ((first ⟨index.val, Nat.lt_succ_of_lt index.isLt⟩ : system.obj (op index.val)) +
              second ⟨index.val, Nat.lt_succ_of_lt index.isLt⟩) -
            (transitionAddHom system (homOfLE (Nat.le_succ index.val)).op
              ((first ⟨index.val + 1, Nat.succ_lt_succ index.isLt⟩ : system.obj (op (index.val +
                1))) +
                second ⟨index.val + 1, Nat.succ_lt_succ index.isLt⟩) : system.obj (op index.val)) =
                  _
          rw [map_add]
          dsimp only [Pi.add_apply]
          abel
        map_smul' := by
          intro scalar values
          funext index
          change (rings.map (homOfLE (Nat.le_of_lt index.isLt)).op) scalar •
              (values ⟨index.val, by omega⟩ : system.obj (op index.val)) -
            (transitionAddHom system (homOfLE (Nat.le_succ index.val)).op
              ((rings.map (homOfLE (Nat.le_of_lt_succ index.succ.isLt)).op) scalar •
                (values ⟨index.val + 1, by omega⟩ : system.obj (op (index.val + 1)))) :
                  system.obj (op index.val)) =
            (rings.map (homOfLE (Nat.le_of_lt index.isLt)).op) scalar •
              ((values ⟨index.val, by omega⟩ : system.obj (op index.val)) -
                (transitionAddHom system (homOfLE (Nat.le_succ index.val)).op
                  (values ⟨index.val + 1, by omega⟩) : system.obj (op index.val)))
          rw [transitionAddHom_smul, smul_sub]
          have factor : (homOfLE (Nat.le_of_lt index.isLt)).op =
              (homOfLE (Nat.le_of_lt_succ index.succ.isLt)).op ≫
                (homOfLE (Nat.le_succ index.val)).op := Subsingleton.elim _ _
          rw [factor, rings.map_comp]
          rfl }
  naturality transition := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro values
    funext index
    rfl

private theorem prefixUnitMap_finiteDifference
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings) :
    prefixUnitMap rings system ≫ finiteDifference rings system = 0 := by
  ext stage value
  funext index
  change transitionAddHom system (homOfLE (Nat.le_of_lt index.isLt)).op value -
    transitionAddHom system (homOfLE (Nat.le_succ index.val)).op
      (transitionAddHom system (homOfLE (Nat.le_of_lt_succ index.succ.isLt)).op value) = 0
  rw [sub_eq_zero]
  change system.map (homOfLE (Nat.le_of_lt index.isLt)).op value =
    system.map (homOfLE (Nat.le_succ index.val)).op
      (system.map (homOfLE (Nat.le_of_lt_succ index.succ.isLt)).op value)
  exact map_homOfLE_op_comp_apply system _ _ _ value

private theorem finiteDifference_app_surjective
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings)
    (stage : ℕᵒᵖ) : Function.Surjective ((finiteDifference rings system).app stage) := by
  intro target
  let values : (index : Fin (stage.unop + 1)) → system.obj (op index.val) :=
    Fin.reverseInduction
      (motive := fun index : Fin (stage.unop + 1) => system.obj (op index.val))
      0 (fun index value => target index +
        transitionAddHom system (homOfLE (Nat.le_succ index.val)).op value)
  refine ⟨values, ?_⟩
  funext index
  change values ⟨index.val, Nat.lt_succ_of_lt index.isLt⟩ -
    transitionAddHom system (homOfLE (Nat.le_succ index.val)).op (values index.succ) = target index
  rw [sub_eq_iff_eq_add]
  exact Fin.reverseInduction_castSucc index

private theorem finiteDifference_kernel_lifts
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings)
    (stage : ℕᵒᵖ) (values : (prefixSystem rings system).obj stage)
    (annihilates : (finiteDifference rings system).app stage values = 0) :
    ∃ value : system.obj stage, (prefixUnitMap rings system).app stage value = values := by
  let value : system.obj stage := values (Fin.last stage.unop)
  have coordinates : ∀ index : Fin (stage.unop + 1),
      transitionAddHom system (homOfLE (Nat.le_of_lt_succ index.isLt)).op value = values index := by
    intro index
    refine Fin.reverseInduction ?_ ?_ index
    · exact map_homOfLE_op_refl_apply system _ value
    · intro index inductionHypothesis
      have differenceZero := congrFun annihilates index
      change values ⟨index.val, Nat.lt_succ_of_lt index.isLt⟩ -
        transitionAddHom system (homOfLE (Nat.le_succ index.val)).op (values index.succ) = 0
          at differenceZero
      rw [show transitionAddHom system (homOfLE (Nat.le_of_lt_succ index.castSucc.isLt)).op value =
          transitionAddHom system (homOfLE (Nat.le_succ index.val)).op
            (transitionAddHom system (homOfLE (Nat.le_of_lt_succ index.succ.isLt)).op value) from
        map_homOfLE_op_comp_apply system _ _ _ value, inductionHypothesis]
      exact (sub_eq_zero.mp differenceZero).symm
  exact ⟨value, funext coordinates⟩

private theorem finiteDifference_shortExact
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings) :
    (ShortComplex.mk (prefixUnitMap rings system) (finiteDifference rings system)
      (prefixUnitMap_finiteDifference rings system)).ShortExact := by
  let sequence := ShortComplex.mk (prefixUnitMap rings system) (finiteDifference rings system)
    (prefixUnitMap_finiteDifference rings system)
  have pointwise (stage : ℕᵒᵖ) :
      (sequence.map (PresheafOfModules.evaluation rings stage)).Exact :=
    (sequence.map (PresheafOfModules.evaluation rings stage)).moduleCat_exact_iff.mpr
      (finiteDifference_kernel_lifts rings system stage)
  have : Mono sequence.f := prefixUnitMap_mono rings system
  have : Epi sequence.g :=
    PresheafOfModules.epi_of_surjective (finiteDifference_app_surjective rings system)
  refine ⟨?_⟩
  change sequence.Exact
  apply sequence.exact_iff_isZero_homology.mpr
  apply (IsZero.iff_id_eq_zero _).mpr
  ext stage value
  have homologyZero : IsZero ((PresheafOfModules.evaluation rings stage).obj sequence.homology) :=
    ((sequence.map (PresheafOfModules.evaluation rings stage)).exact_iff_isZero_homology.mp
      (pointwise stage)).of_iso
        (sequence.mapHomologyIso (PresheafOfModules.evaluation rings stage)).symm
  exact ConcreteCategory.congr_hom (homologyZero.eq_of_src (𝟙 _) 0) value

private theorem shortPrefixRestricted_smul
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings)
    (stage : ℕᵒᵖ) (scalar : (limit rings : RingCat.{ringLevel}))
    (values : (moduleDiagram rings (shortPrefixSystem rings system)).obj stage)
    (index : Fin stage.unop) :
    ((((moduleDiagram rings (shortPrefixSystem rings system)).obj stage).smul scalar).asHom.hom
      values) index =
      (((moduleDiagram rings system).obj (op index.val)).smul scalar).asHom.hom (values index) := by
  change (rings.map (homOfLE (Nat.le_of_lt index.isLt)).op)
      ((limit.π rings stage).hom scalar) • values index =
    ((limit.π rings (op index.val)).hom scalar) • values index
  rw [limit_π_map_eq]

private def shortPrefixRestrictedEvaluation
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings)
    (stage : ℕᵒᵖ) (index : Fin stage.unop) :
    (moduleDiagram rings (shortPrefixSystem rings system)).obj stage ⟶
      (moduleDiagram rings system).obj (op index.val) := by
  letI : Module (limit rings : RingCat.{ringLevel})
      ((shortPrefixSystem rings system).obj stage) :=
    ((moduleDiagram rings (shortPrefixSystem rings system)).obj stage).isModule
  letI : Module (limit rings : RingCat.{ringLevel}) (system.obj (op index.val)) :=
    ((moduleDiagram rings system).obj (op index.val)).isModule
  exact ModuleCat.ofHom
    { toFun := fun values => values index
      map_add' := fun _ _ => rfl
      map_smul' := fun scalar values => shortPrefixRestricted_smul rings system stage scalar values
        index }

private def shortPrefixLimitCone
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings) :
    Cone (moduleDiagram rings (shortPrefixSystem rings system)) where
  pt := termProduct rings system
  π :=
    { app := fun stage => by
        letI : Module (limit rings : RingCat.{ringLevel})
            ((shortPrefixSystem rings system).obj stage) :=
          ((moduleDiagram rings (shortPrefixSystem rings system)).obj stage).isModule
        exact ModuleCat.ofHom
          { toFun := fun values index =>
              Pi.π (fun index : ℕ => (moduleDiagram rings system).obj (op index)) index.val values
            map_add' := by
              intro first second
              funext index
              exact map_add _ first second
            map_smul' := by
              intro scalar values
              funext index
              change (Pi.π (fun index : ℕ => (moduleDiagram rings system).obj (op index))
                  index.val) (scalar • values) =
                ((((moduleDiagram rings (shortPrefixSystem rings system)).obj stage).smul
                  scalar).asHom.hom
                  (fun index => Pi.π (fun index : ℕ =>
                    (moduleDiagram rings system).obj (op index)) index.val values)) index
              rw [shortPrefixRestricted_smul]
              exact map_smul _ scalar values }
      naturality := by
        intro source target morphism
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro values
        funext index
        rfl }

private theorem shortPrefixLimitCone_projection
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings)
    (stage : ℕᵒᵖ) (index : Fin stage.unop) :
    (shortPrefixLimitCone rings system).π.app stage ≫
      shortPrefixRestrictedEvaluation rings system stage index =
        Pi.π (fun index : ℕ => (moduleDiagram rings system).obj (op index)) index.val := by
  apply ModuleCat.hom_ext
  rfl

private def shortPrefixLimitConeIsLimit
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings) :
    IsLimit (shortPrefixLimitCone rings system) where
  lift cone := Pi.lift fun index => cone.π.app (op (index + 1)) ≫
    shortPrefixRestrictedEvaluation rings system (op (index + 1)) ⟨index, Nat.lt_succ_self index⟩
  fac cone stage := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro values
    funext index
    change Pi.π (fun index : ℕ => (moduleDiagram rings system).obj (op index)) index.val
        ((Pi.lift fun coordinate => cone.π.app (op (coordinate + 1)) ≫
          shortPrefixRestrictedEvaluation rings system (op (coordinate + 1))
            ⟨coordinate, Nat.lt_succ_self coordinate⟩) values) = cone.π.app stage values index
    rw [← ConcreteCategory.comp_apply, Pi.lift_comp_π]
    change cone.π.app (op (index.val + 1)) values ⟨index.val, Nat.lt_succ_self index.val⟩ =
      cone.π.app stage values index
    have compatible := ConcreteCategory.congr_hom
      (cone.w (homOfLE (Nat.succ_le_of_lt index.isLt)).op) values
    exact (congrFun compatible ⟨index.val, Nat.lt_succ_self index.val⟩).symm
  uniq cone arrow factors := by
    apply Pi.hom_ext
    intro index
    have projected := congrArg (fun component => component ≫
      shortPrefixRestrictedEvaluation rings system (op (index + 1)) ⟨index, Nat.lt_succ_self index⟩)
        (factors (op (index + 1)))
    rw [Pi.lift_comp_π]
    rw [Category.assoc, shortPrefixLimitCone_projection] at projected
    exact projected

private def shortPrefixLimitIso
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings) :
    (inverseLimit rings).obj (shortPrefixSystem rings system) ≅ termProduct rings system :=
  limit.isoLimitCone ⟨shortPrefixLimitCone rings system, shortPrefixLimitConeIsLimit rings system⟩

private theorem shortPrefixLimitIso_inv_projection
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings)
    (stage : ℕᵒᵖ) :
    (shortPrefixLimitIso rings system).inv ≫
      limit.π (moduleDiagram rings (shortPrefixSystem rings system)) stage =
        (shortPrefixLimitCone rings system).π.app stage :=
  limit.isoLimitCone_inv_π _ _

private theorem shortPrefixLimitIso_hom_projection
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings)
    (index : ℕ) :
    (shortPrefixLimitIso rings system).hom ≫
      Pi.π (fun index : ℕ => (moduleDiagram rings system).obj (op index)) index =
        limit.π (moduleDiagram rings (shortPrefixSystem rings system)) (op (index + 1)) ≫
          shortPrefixRestrictedEvaluation rings system (op (index + 1)) ⟨index, Nat.lt_succ_self
            index⟩ := by
  rw [← cancel_epi (shortPrefixLimitIso rings system).inv, Iso.inv_hom_id_assoc,
    ← Category.assoc, shortPrefixLimitIso_inv_projection, shortPrefixLimitCone_projection]

public def productDelta
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings) :
    termProduct rings system ⟶ termProduct rings system :=
  𝟙 _ - Pi.lift (fun index =>
    Pi.π (fun index : ℕ => (moduleDiagram rings system).obj (op index)) (index + 1) ≫
      (moduleDiagram rings system).map (homOfLE (Nat.le_succ index)).op)

private theorem finiteDifference_limit_eq_delta
    (rings : ℕᵒᵖ ⥤ RingCat.{ringLevel}) (system : PresheafOfModules.{moduleLevel} rings) :
    (prefixLimitIso rings system).inv ≫ (inverseLimit rings).map (finiteDifference rings system) ≫
      (shortPrefixLimitIso rings system).hom = productDelta rings system := by
  apply Pi.hom_ext
  intro index
  rw [Category.assoc, Category.assoc, shortPrefixLimitIso_hom_projection]
  rw [← Category.assoc ((inverseLimit rings).map (finiteDifference rings system))
    (limit.π (moduleDiagram rings (shortPrefixSystem rings system)) (op (index + 1))) _,
    inverseLimit_map_π]
  rw [Category.assoc, ← Category.assoc (prefixLimitIso rings system).inv
    (limit.π (moduleDiagram rings (prefixSystem rings system)) (op (index + 1))) _,
    prefixLimitIso_inv_projection]
  simp only [productDelta, Preadditive.sub_comp, Category.id_comp, Pi.lift_comp_π]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro value
  rfl

private abbrev finiteResolution (rings : ℕᵒᵖ ⥤ RingCat.{u})
    (system : PresheafOfModules.{v} rings) : CochainComplex (PresheafOfModules.{v} rings) ℤ :=
  HomologicalComplex.double (finiteDifference rings system)
    (show (ComplexShape.up ℤ).Rel 0 1 by rfl)

private abbrev finiteResolutionUnit (rings : ℕᵒᵖ ⥤ RingCat.{u})
    (system : PresheafOfModules.{v} rings) :
    (CochainComplex.singleFunctor (PresheafOfModules.{v} rings) 0).obj system ⟶
      finiteResolution rings system :=
  Stacks.DoubleResolution.shortExactResolutionUnit (ShortComplex.mk (prefixUnitMap rings system)
    (finiteDifference rings system) (prefixUnitMap_finiteDifference rings system))

private theorem finiteResolutionUnit_quasiIso (rings : ℕᵒᵖ ⥤ RingCat.{u})
    (system : PresheafOfModules.{v} rings) : QuasiIso (finiteResolutionUnit rings system) :=
  Stacks.DoubleResolution.shortExactResolutionUnit_quasiIso _
    (finiteDifference_shortExact rings system)

private theorem finiteResolution_source_acyclic_terms (rings : ℕᵒᵖ ⥤ RingCat.{u})
    (system : PresheafOfModules.{v} rings) (degree : ℤ) :
    sourceAcyclicSystem rings ((finiteResolution rings system).X degree) := by
  by_cases isZeroDegree : degree = 0
  · subst degree
    exact mittagLeffler_computes_source rings _
      (presheaf_mittagLeffler_of_epi
        (HomologicalComplex.doubleXIso₀ (finiteDifference rings system) (by rfl)).inv
        (prefixSystem_isMittagLeffler rings system))
  · by_cases isOneDegree : degree = 1
    · subst degree
      exact mittagLeffler_computes_source rings _
        (presheaf_mittagLeffler_of_epi
          (HomologicalComplex.doubleXIso₁ (finiteDifference rings system) (by rfl)
            (by norm_num)).inv
          (shortPrefixSystem_isMittagLeffler rings system))
    · exact sourceAcyclicSystem_of_isZero rings _
        (HomologicalComplex.isZero_double_X _ _ degree isZeroDegree isOneDegree)

private abbrev productDeltaComplex (rings : ℕᵒᵖ ⥤ RingCat.{u})
    (system : PresheafOfModules.{v} rings) :
    CochainComplex (ModuleCat.{v} (limit rings : RingCat.{u})) ℤ :=
  HomologicalComplex.double (productDelta rings system)
    (show (ComplexShape.up ℤ).Rel 0 1 by rfl)

private def finiteResolutionLimitIso (rings : ℕᵒᵖ ⥤ RingCat.{u})
    (system : PresheafOfModules.{v} rings) :
    ((inverseLimit rings).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (finiteResolution rings system) ≅ productDeltaComplex rings system := by
  let functor := inverseLimit rings
  refine Stacks.DoubleResolution.isoDoubleOfSupport _ (productDelta rings system)
    (functor.mapIso (HomologicalComplex.doubleXIso₀ (finiteDifference rings system) (by rfl)) ≪≫
      prefixLimitIso rings system)
    (functor.mapIso (HomologicalComplex.doubleXIso₁ (finiteDifference rings system) (by rfl)
      (by norm_num)) ≪≫ shortPrefixLimitIso rings system) ?_ ?_
  · intro degree isZeroDegree isOneDegree
    exact functor.map_isZero
      (HomologicalComplex.isZero_double_X _ _ degree isZeroDegree isOneDegree)
  · change (prefixLimitIso rings system).inv ≫ functor.map _ ≫ functor.map _ ≫
      (functor.map _ ≫ (shortPrefixLimitIso rings system).hom) = _
    simp only [← Functor.map_comp_assoc]
    rw [HomologicalComplex.double_d _ _ (by norm_num)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    exact finiteDifference_limit_eq_delta rings system

private theorem inverseLimit_termwise_model_of_unit
    (rings : ℕᵒᵖ ⥤ RingCat.{u})
    (derivedFunctor : DerivedCategory (PresheafOfModules.{v} rings) ⥤
      DerivedCategory (ModuleCat.{v} (limit rings : RingCat.{u})))
    (unit : (inverseLimit rings).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ derivedFunctor)
    (complex : CochainComplex (PresheafOfModules.{v} rings) ℤ)
    [IsIso (unit.app ((HomotopyCategory.quotient (PresheafOfModules.{v} rings)
      (ComplexShape.up ℤ)).obj complex))] :
    Nonempty (derivedFunctor.obj (DerivedCategory.Q.obj complex) ≅
      DerivedCategory.Q.obj
        (((inverseLimit rings).mapHomologicalComplex (ComplexShape.up ℤ)).obj complex)) := by
  let inputIso := (DerivedCategory.quotientCompQhIso (PresheafOfModules.{v} rings)).app complex
  let outputIso := DerivedCategory.Qh.mapIso
      ((Functor.mapHomotopyCategoryFactors (inverseLimit rings) (ComplexShape.up ℤ)).app complex) ≪≫
    (DerivedCategory.quotientCompQhIso (ModuleCat.{v} (limit rings : RingCat.{u}))).app _
  exact ⟨(derivedFunctor.mapIso inputIso).symm ≪≫
    (asIso (unit.app ((HomotopyCategory.quotient (PresheafOfModules.{v} rings)
      (ComplexShape.up ℤ)).obj complex))).symm ≪≫ outputIso⟩

private theorem inverseLimit_unbounded_twoTerm_model
    (rings : ℕᵒᵖ ⥤ RingCat.{u})
    (derivedFunctor : DerivedCategory (PresheafOfModules.{v} rings) ⥤
      DerivedCategory (ModuleCat.{v} (limit rings : RingCat.{u})))
    (unit : (inverseLimit rings).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ derivedFunctor)
    [derivedFunctor.IsRightDerivedFunctor unit
      (HomotopyCategory.quasiIso (PresheafOfModules.{v} rings) (ComplexShape.up ℤ))]
    (system : PresheafOfModules.{v} rings) :
    Nonempty (derivedFunctor.obj
      ((DerivedCategory.singleFunctor (PresheafOfModules.{v} rings) 0).obj system) ≅
        DerivedCategory.Q.obj (productDeltaComplex rings system)) := by
  have := finiteResolutionUnit_quasiIso rings system
  have := (inverseLimit_unbounded_controls rings derivedFunctor unit).2.2
    (finiteResolution rings system) (finiteResolution_source_acyclic_terms rings system)
  obtain ⟨comparison⟩ := inverseLimit_termwise_model_of_unit rings derivedFunctor unit
    (finiteResolution rings system)
  exact ⟨derivedFunctor.mapIso (asIso (DerivedCategory.Q.map (finiteResolutionUnit rings system)))
    ≪≫
    comparison ≪≫ DerivedCategory.Q.mapIso (finiteResolutionLimitIso rings system)⟩


public theorem inverseLimit_unbounded_twoTerm_model_data
    (rings : ℕᵒᵖ ⥤ RingCat.{u})
    (derivedFunctor : DerivedCategory (PresheafOfModules.{v} rings) ⥤
      DerivedCategory (ModuleCat.{v} (limit rings : RingCat.{u})))
    (unit : (inverseLimit rings).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ derivedFunctor)
    [derivedFunctor.IsRightDerivedFunctor unit
      (HomotopyCategory.quasiIso (PresheafOfModules.{v} rings) (ComplexShape.up ℤ))]
    (system : PresheafOfModules.{v} rings) :
    ∃ (complex : CochainComplex (ModuleCat.{v} (limit rings : RingCat.{u})) ℤ)
      (zeroIso : complex.X 0 ≅ termProduct rings system)
      (oneIso : complex.X 1 ≅ termProduct rings system),
      (∀ degree : ℤ, degree ≠ 0 → degree ≠ 1 → IsZero (complex.X degree)) ∧
      zeroIso.inv ≫ complex.d 0 1 ≫ oneIso.hom = productDelta rings system ∧
      Nonempty (derivedFunctor.obj
        ((DerivedCategory.singleFunctor (PresheafOfModules.{v} rings) 0).obj system) ≅
          DerivedCategory.Q.obj complex) := by
  refine ⟨productDeltaComplex rings system,
    HomologicalComplex.doubleXIso₀ (productDelta rings system) (by rfl),
    HomologicalComplex.doubleXIso₁ (productDelta rings system) (by rfl) (by norm_num),
    fun degree nonzero nonone => HomologicalComplex.isZero_double_X _ _ degree nonzero nonone,
    ?_, inverseLimit_unbounded_twoTerm_model rings derivedFunctor unit system⟩
  rw [HomologicalComplex.double_d (productDelta rings system) (by rfl) (by norm_num)]
  simp


end

end ModuleInverseLimit

end

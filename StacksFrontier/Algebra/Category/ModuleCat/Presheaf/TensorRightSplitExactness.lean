module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.FreeSplitUniverse
public import StacksFrontier.Algebra.Category.ModuleCat.TensorRightSplitUniverse
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactness

/-!
# Exactness of the objectwise tensor product of presheaves of modules, at split universes

`Stacks.tensorRight`, the objectwise tensor product of presheaves of modules, is
already universe-polymorphic: it sends `PresheafOfModules.{z₁} (ringPresheaf O)`
to `PresheafOfModules.{max z₁ z} (ringPresheaf O)` with the ring universe `w`
independent of both. Its *exactness* properties, however, were available only at
module universe `w`, because the sectionwise argument went through
`MonoidalCategory (ModuleCat.{m} R)`, which Mathlib states only for a ring
carrier `R : Type m`.

This file reruns that sectionwise argument through
`ModuleCat.tensorRightSplit`, where the ring universe and the module universe are
independent, and so obtains both halves at module universe `max t w` over a ring
presheaf in `CommRingCat.{w}`.

## Main results

* `Stacks.preservesColimitsOfSize_tensorRight_split`: tensoring presheaves of
  modules on the right preserves all colimits, at module universe `max t w`.
* `Stacks.preservesFiniteLimits_tensorRight_of_flat_obj_split`: tensoring on the
  right with an objectwise flat presheaf of modules is left exact, at module
  universe `max t w`.
* `Stacks.epi_fromFreeCoverSplit` and
  `Stacks.preservesFiniteLimits_tensorRight_freeCoverSplit`: **Stacks 03EW for
  presheaves of modules** at module universe `max t w` — every presheaf of
  modules is the target of an epimorphism from one whose tensor functor is
  exact.

## Implementation notes

Both proofs are the ones in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SheafFlatCover.lean` with
`MonoidalCategory.tensorRight` replaced by `ModuleCat.tensorRightSplit`. The
replacement is defeq on objects and on morphisms — `LinearMap.rTensor M f` is by
definition `TensorProduct.map f LinearMap.id`, which is what `Stacks.tensorRight`
uses — so the colimit and limit cones produced by the sectionwise functor are
literally the ones the goal asks for, exactly as before. What changes is only
which instance supplies the preservation: the tensor-hom adjunction and
`Module.Flat.rTensor_exact` at split universes rather than Mathlib's monoidal
closed structure and `Module.Flat.iff_preservesFiniteLimits_tensorRight`.

At `t := w` these specialise to `Stacks.preservesColimitsOfSize_tensorRight` and
`Stacks.preservesFiniteLimits_tensorRight_of_flat_obj`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open TensorProduct

universe v u w t

namespace Stacks

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- **Tensoring presheaves of modules on the right preserves colimits**, with the
module universe `max t w` independent of the ring universe `w`. Colimits of
presheaves of modules are computed sectionwise, and sectionwise this is
`ModuleCat.tensorRightSplit`, a left adjoint. -/
instance preservesColimitsOfSize_tensorRight_split
    (F : PresheafOfModules.{max t w} (ringPresheaf O)) :
    PreservesColimitsOfSize.{max t w, max t w}
      (tensorRight F : PresheafOfModules.{max t w} (ringPresheaf O) ⥤ _) where
  preservesColimitsOfShape := ⟨⟨fun hc ↦ ⟨by
    refine PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun X ↦ ?_)
    exact isColimitOfPreserves (ModuleCat.tensorRightSplit
      (show ModuleCat.{max t w} ((ringPresheaf O).obj X) from F.obj X))
      (isColimitOfPreserves (PresheafOfModules.evaluation _ X) hc)⟩⟩⟩

/-- Tensoring presheaves of modules on the right preserves finite colimits, with the module
universe `max t w` independent of the ring universe `w`. -/
instance preservesFiniteColimits_tensorRight_split
    (F : PresheafOfModules.{max t w} (ringPresheaf O)) :
    PreservesFiniteColimits
      (tensorRight F : PresheafOfModules.{max t w} (ringPresheaf O) ⥤ _) :=
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- **Tensoring on the right with an objectwise flat presheaf of modules is left
exact**, with the module universe `max t w` independent of the ring universe `w`.
Limits of presheaves of modules are computed sectionwise, so this reduces to
flatness of each module of sections. -/
lemma preservesFiniteLimits_tensorRight_of_flat_obj_split
    (N : PresheafOfModules.{max t w} (ringPresheaf O))
    (hN : ∀ X : Cᵒᵖ, Module.Flat ((ringPresheaf O).obj X) (N.obj X)) :
    PreservesFiniteLimits
      (tensorRight N : PresheafOfModules.{max t w} (ringPresheaf O) ⥤ _) := by
  refine ⟨fun D _ _ ↦ ⟨⟨fun hc ↦ ⟨?_⟩⟩⟩⟩
  refine PresheafOfModules.evaluationJointlyReflectsLimits _ _ fun X ↦ ?_
  let M : ModuleCat.{max t w} ((ringPresheaf O).obj X) := N.obj X
  have := hN X
  have := ModuleCat.preservesFiniteLimits_tensorRightSplit M
  exact isLimitOfPreserves (ModuleCat.tensorRightSplit M)
    (isLimitOfPreserves (PresheafOfModules.evaluation _ X) hc)

section FreeCover

variable (M : PresheafOfModules.{max t w} (ringPresheaf O))

/-- The free presheaf of modules on the underlying presheaf of sets of `M`, at
module universe `max t w` over a ring presheaf in `CommRingCat.{w}`. It is
objectwise free, hence objectwise flat, and it maps onto `M`. -/
noncomputable abbrev freeCoverSplit : PresheafOfModules.{max t w} (ringPresheaf O) :=
  PresheafOfModules.freeSplitObj (M.presheaf ⋙ forget _)

/-- The canonical surjection from the free presheaf of modules on the sections of
`M`, at split universes. -/
noncomputable def fromFreeCoverSplit : freeCoverSplit M ⟶ M :=
  PresheafOfModules.freeSplitObjDesc (fun _ x ↦ x) (fun _ _ ↦ rfl)

/-- The map `fromFreeCoverSplit M` sends the basis element of a section `m` of `M` to `m`. -/
@[simp]
lemma fromFreeCoverSplit_app_freeSplitObjMk (X : Cᵒᵖ) (m : M.obj X) :
    (fromFreeCoverSplit M).app X
        (PresheafOfModules.freeSplitObjMk (ringPresheaf O) (M.presheaf ⋙ forget _) m) = m :=
  ModuleCat.freeSplitDesc_apply _ m

/-- The canonical map `fromFreeCoverSplit M` from the free cover onto `M` is an epimorphism. -/
instance epi_fromFreeCoverSplit : Epi (fromFreeCoverSplit M) :=
  PresheafOfModules.epi_of_surjective fun _ m ↦
    ⟨_, fromFreeCoverSplit_app_freeSplitObjMk M _ m⟩

/-- Each module of sections of the free cover `freeCoverSplit M` is flat. -/
lemma flat_freeCoverSplit_obj (X : Cᵒᵖ) :
    Module.Flat ((ringPresheaf O).obj X) ((freeCoverSplit M).obj X) := by
  change Module.Flat ((ringPresheaf O).obj X)
    ((M.presheaf ⋙ forget _).obj X →₀ (ringPresheaf O).obj X)
  infer_instance

/-- **Stacks 03EW for presheaves of modules, at split universes.** Tensoring on
the right with the free cover of `M` is left exact. -/
lemma preservesFiniteLimits_tensorRight_freeCoverSplit :
    PreservesFiniteLimits
      (tensorRight (freeCoverSplit M) : PresheafOfModules.{max t w} (ringPresheaf O) ⥤ _) :=
  preservesFiniteLimits_tensorRight_of_flat_obj_split _ (flat_freeCoverSplit_obj M)

end FreeCover

end Stacks

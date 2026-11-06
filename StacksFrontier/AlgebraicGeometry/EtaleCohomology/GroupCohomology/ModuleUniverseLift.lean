module

public import Mathlib.Algebra.Module.ULift
public import Mathlib.Topology.LocallyConstant.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DiscreteModules
import StacksCore.Tactic.StacksAttribute

/-!
# Raising the coefficient universe of an `R`-`G`-module

For an `R`-`G`-module `M` in `Stacks.Injectives.ContinuousModule.{t, u, w} R G`, the
`R`-`G`-module `ULift M` has the raised carrier and the raised action, and lies in
`Stacks.Injectives.ContinuousModule.{t, u, max w s} R G`: it is again discrete with continuous
action.

## Main definitions

* `Stacks.GroupCohomology.representationOfModule`: the representation of `G` on the underlying
  module of an `R`-`G`-module.
* `Stacks.GroupCohomology.uliftRepresentation`: a representation on the raised carrier.
* `Stacks.GroupCohomology.uliftContinuousModule`: the `R`-`G`-module `ULift M`.

## Main results

* `Stacks.GroupCohomology.isLocallyConstant_ρ_apply`: the orbit map of an element of an
  `R`-`G`-module is locally constant.
* `Stacks.GroupCohomology.uliftContinuousModule_ρ_hom`: the raised action acts on `ULift.up` by
  the original action.

## References

* [Stacks Project, Tag 04JP](https://stacks.math.columbia.edu/tag/04JP): the `R`-`G`-modules.
* [Stacks Project, Tag 04JR](https://stacks.math.columbia.edu/tag/04JR): the cohomology groups
  whose coefficient universe this is about.
-/

@[expose] public noncomputable section

open CategoryTheory

open scoped Stacks.DiscreteModuleTopology

universe t s u w

namespace Stacks.GroupCohomology

/-! ### The representation underlying an `R`-`G`-module -/

section Underlying

variable {R : Type t} [Ring R] {G : Type u} [Group G] [TopologicalSpace G]

/-- The representation of `G` on the underlying module of an `R`-`G`-module. -/
def representationOfModule (N : Stacks.Injectives.ContinuousModule.{t, u, w} R G) :
    Representation R G N.obj.obj.V :=
  (ModuleCat.endRingEquiv N.obj.obj.V).toMonoidHom.comp N.obj.obj.ρ

/-- `representationOfModule N` acts by the action of `N`. -/
@[simp] theorem representationOfModule_apply
    (N : Stacks.Injectives.ContinuousModule.{t, u, w} R G) (g : G) (x : N.obj.obj.V) :
    representationOfModule N g x = (N.obj.obj.ρ g).asHom.hom x := rfl

variable [IsTopologicalGroup G]

/-- **The orbit map of an element of an `R`-`G`-module is locally constant.** -/
theorem isLocallyConstant_ρ_apply (N : Stacks.Injectives.ContinuousModule.{t, u, w} R G)
    (z : N.obj.obj.V) : IsLocallyConstant fun g : G ↦ (N.obj.obj.ρ g).asHom.hom z := by
  intro s
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun h : G ↦ g⁻¹ * h) ⁻¹' {k : G | (N.obj.obj.ρ k).asHom.hom z = z}, fun h hh ↦ ?_,
    (isOpen_stabilizer R G N z).preimage (by fun_prop), ?_⟩
  · simp only [Set.mem_preimage, Set.mem_setOf_eq] at hh
    have hmul : (N.obj.obj.ρ (g * (g⁻¹ * h))).asHom.hom z =
        (N.obj.obj.ρ g).asHom.hom ((N.obj.obj.ρ (g⁻¹ * h)).asHom.hom z) := by rw [map_mul]; rfl
    rw [mul_inv_cancel_left, hh] at hmul
    exact Set.mem_preimage.mpr (hmul ▸ hg)
  · simp only [Set.mem_preimage, Set.mem_setOf_eq, inv_mul_cancel]
    rw [map_one]; rfl

end Underlying

/-! ### The raised representation -/

/-- **A representation of `G` on `V`, read on the raised carrier `ULift V`.** -/
def uliftRepresentation.{t', u', w', s'} {R : Type t'} [Ring R] {G : Type u'} [Group G]
    {V : Type w'} [AddCommGroup V] [Module R V] (ρ : Representation R G V) :
    Representation R G (ULift.{s'} V) where
  toFun g :=
    { toFun x := ULift.up (ρ g x.down)
      map_add' x y := by
        refine ULift.down_injective ?_
        change ρ g (x.down + y.down) = ρ g x.down + ρ g y.down
        rw [map_add]
      map_smul' c x := by
        refine ULift.down_injective ?_
        change ρ g (c • x.down) = c • ρ g x.down
        rw [map_smul] }
  map_one' := by
    refine LinearMap.ext fun x ↦ ULift.down_injective ?_
    change ρ 1 x.down = x.down
    rw [map_one]; rfl
  map_mul' g h := by
    refine LinearMap.ext fun x ↦ ULift.down_injective ?_
    change ρ (g * h) x.down = ρ g (ρ h x.down)
    rw [map_mul]; rfl

/-- The raised representation acts on `ULift.up x` by the original action on `x`. -/
@[simp] theorem uliftRepresentation_apply.{t', u', w', s'} {R : Type t'} [Ring R] {G : Type u'}
    [Group G] {V : Type w'} [AddCommGroup V] [Module R V] (ρ : Representation R G V) (g : G)
    (x : V) : uliftRepresentation.{t', u', w', s'} ρ g (ULift.up x) = ULift.up (ρ g x) := rfl

/-- The raised representation read through `ULift.down`. -/
@[simp] theorem uliftRepresentation_apply_down.{t', u', w', s'} {R : Type t'} [Ring R]
    {G : Type u'} [Group G] {V : Type w'} [AddCommGroup V] [Module R V]
    (ρ : Representation R G V) (g : G) (x : ULift.{s'} V) :
    (uliftRepresentation.{t', u', w', s'} ρ g x).down = ρ g x.down := rfl

/-! ### The raised `R`-`G`-module -/

/-- **An `R`-`G`-module with its coefficient universe raised.** The carrier is `ULift M` and the
action is the original one. -/
def uliftContinuousModule.{t', u', w', s'} {R : Type t'} [Ring R] {G : Type u'} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (N : Stacks.Injectives.ContinuousModule.{t', u', w'} R G) :
    Stacks.Injectives.ContinuousModule.{t', u', max w' s'} R G :=
  ofRepresentation (uliftRepresentation.{t', u', w', s'} (representationOfModule N))
    (by
      rw [isContinuous_actionOfRepresentation_iff]
      intro x
      have hset :
          {g : G | uliftRepresentation.{t', u', w', s'} (representationOfModule N) g x = x} =
          {g : G | (N.obj.obj.ρ g).asHom.hom x.down = x.down} := by
        ext g
        exact ⟨fun h ↦ congrArg ULift.down h, fun h ↦ congrArg ULift.up h⟩
      rw [hset]
      exact isOpen_stabilizer R G N x.down)

/-- The raised action acts on `ULift.up` by the original action. -/
@[simp] theorem uliftContinuousModule_ρ_hom.{t', u', w', s'} {R : Type t'} [Ring R]
    {G : Type u'} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (N : Stacks.Injectives.ContinuousModule.{t', u', w'} R G) (g : G) (x : N.obj.obj.V) :
    ((uliftContinuousModule.{t', u', w', s'} N).obj.obj.ρ g).asHom.hom (ULift.up x) =
      ULift.up ((N.obj.obj.ρ g).asHom.hom x) := rfl

/-- The raised action read through `ULift.down`. -/
@[simp] theorem uliftContinuousModule_ρ_hom_down.{t', u', w', s'} {R : Type t'} [Ring R]
    {G : Type u'} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (N : Stacks.Injectives.ContinuousModule.{t', u', w'} R G) (g : G)
    (x : (uliftContinuousModule.{t', u', w', s'} N).obj.obj.V) :
    (((uliftContinuousModule.{t', u', w', s'} N).obj.obj.ρ g).asHom.hom x).down =
      (N.obj.obj.ρ g).asHom.hom x.down := rfl

end Stacks.GroupCohomology

end

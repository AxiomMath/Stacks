module

public import Mathlib.Algebra.Module.ULift
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import StacksFrontier.AlgebraicGeometry.GradedLocalization.ModuleMaps

/-!
# Universe lifting of a grading

A family of additive subgroups `𝒜 : ι → σ` of an additive group `A` transports along
`ULift.down : ULift A → A` to a family of additive subgroups of `ULift A`. This file records that
transport and checks that it preserves the three structures a graded ring and a graded module
carry: a direct-sum decomposition, a graded-ring structure, and the compatibility of a graded
action.

## Main definitions

* `Stacks.GradedModule.uliftGrading`: the grading transported to a larger universe.

## Main results

* `Stacks.GradedModule.uliftGradingDecomposition`: universe lifting preserves a direct-sum
  decomposition.
* `Stacks.GradedModule.uliftGradingGradedRing`: universe lifting preserves a graded-ring
  structure.
* `Stacks.GradedModule.uliftGradingGradedSMul`: universe lifting preserves the compatibility of
  a graded action.

## Implementation notes

The lifted pieces are `AddSubgroup (ULift A)` rather than a copy of `σ`, since there is no
reason for the original `SetLike` carrier to have a universe-lifted analogue. Membership is
literally membership of the underlying element, so each lifted piece is additively isomorphic to
the original one by `ULift.up`, and the decomposition is transported along the induced
isomorphism of direct sums together with `AddEquiv.ulift`.

The grading action of `ℕ` degrees on `ℤ` degrees that `SetLike.GradedSMul` needs is the scoped
instance `Stacks.GradedLocalization.instVAddNatInt`; open that namespace to use
`uliftGradingGradedSMul`.

## References

* [Stacks Project, Tag 01MB](https://stacks.math.columbia.edu/tag/01MB)
-/

@[expose] public section

open DirectSum

namespace Stacks.GradedModule

open Stacks.GradedLocalization

universe u v w t r

/-- Transport a grading to a larger universe using the canonical map `ULift.down`. -/
public def uliftGrading {A : Type u} [AddCommGroup A] {ι : Type r}
    {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) :
    ι → AddSubgroup (ULift.{v} A) := fun i =>
  { carrier := {a | a.down ∈ 𝒜 i}
    zero_mem' := zero_mem _
    add_mem' := fun ha hb => add_mem ha hb
    neg_mem' := fun ha => neg_mem ha }

/-- Universe lifting preserves the direct-sum decomposition. -/
public noncomputable instance uliftGradingDecomposition {A : Type u} [AddCommGroup A]
    {ι : Type r} [DecidableEq ι] {σ : Type w} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ι → σ) [Decomposition 𝒜] :
    Decomposition (uliftGrading.{u, v} 𝒜) := by
  let e (i : ι) : 𝒜 i ≃+ uliftGrading.{u, v} 𝒜 i :=
    { toFun := fun a => ⟨ULift.up a.1, a.2⟩
      invFun := fun a => ⟨a.1.down, a.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  let E := (AddEquiv.ulift : ULift.{v} A ≃+ A).trans
    ((decomposeAddEquiv 𝒜).trans (congrAddEquiv e))
  have hE : (DirectSum.coeAddMonoidHom (uliftGrading.{u, v} 𝒜)).comp E.toAddMonoidHom =
      AddMonoidHom.id _ := by
    have hmap : (DirectSum.coeAddMonoidHom (uliftGrading.{u, v} 𝒜)).comp
        (congrAddEquiv e).toAddMonoidHom =
        (AddEquiv.ulift : ULift.{v} A ≃+ A).symm.toAddMonoidHom.comp
          (DirectSum.coeAddMonoidHom 𝒜) := by
      refine DirectSum.addHom_ext fun i a => ?_
      change DirectSum.coeAddMonoidHom (uliftGrading.{u, v} 𝒜)
        (DirectSum.map (fun j => (e j).toAddMonoidHom) (DirectSum.of _ i a)) =
        ULift.up (DirectSum.coeAddMonoidHom 𝒜 (DirectSum.of _ i a))
      simp only [DirectSum.map_of, DirectSum.coeAddMonoidHom_of]
      rfl
    refine AddMonoidHom.ext fun a => ?_
    change DirectSum.coeAddMonoidHom (uliftGrading.{u, v} 𝒜)
      (congrAddEquiv e (decomposeAddEquiv 𝒜 a.down)) = a
    exact (DFunLike.congr_fun hmap _).trans
      (congrArg ULift.up ((decomposeAddEquiv 𝒜).left_inv a.down))
  exact Decomposition.ofAddHom (ℳ := uliftGrading.{u, v} 𝒜) E.toAddMonoidHom hE (by
    refine AddMonoidHom.ext fun a => E.symm.injective ?_
    simpa using DFunLike.congr_fun hE (E.symm a))

/-- Universe lifting preserves the graded ring structure. -/
public noncomputable instance uliftGradingGradedRing {S : Type u} [CommRing S]
    {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
    (𝒮 : ℕ → σ) [GradedRing 𝒮] : GradedRing (uliftGrading.{u, v} 𝒮) where
  one_mem := SetLike.GradedOne.one_mem (A := 𝒮)
  mul_mem := fun _ _ _ _ ha hb => SetLike.GradedMul.mul_mem (A := 𝒮) ha hb

/-- The lifted scalar action respects the lifted gradings. -/
public instance uliftGradingGradedSMul {S : Type u} {M : Type v}
    [CommRing S] [AddCommGroup M] [Module S M]
    {σ : Type w} {τ : Type t} [SetLike σ S] [AddSubgroupClass σ S]
    [SetLike τ M] [AddSubgroupClass τ M]
    (𝒮 : ℕ → σ) (𝒨 : ℤ → τ) [SetLike.GradedSMul 𝒮 𝒨] :
    SetLike.GradedSMul (uliftGrading.{u, v} 𝒮) (uliftGrading.{v, u} 𝒨) where
  smul_mem := fun _ _ _ _ ha hb => SetLike.GradedSMul.smul_mem (A := 𝒮) (B := 𝒨) ha hb

end Stacks.GradedModule

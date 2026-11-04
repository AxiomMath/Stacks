module

public import StacksFrontier.CategoryTheory.Trace.Preliminaries.DiagonalAction

/-!
# Equivariant endomorphisms of a tensor product with diagonal action

An endomorphism of the module attached to a representation that is linear over the group
algebra is the same thing as a coefficient-linear endomorphism commuting with the group
action.  Two such endomorphisms, one over a commutative ring `A` and one over an
`A`-algebra `Λ`, tensor to an endomorphism of the tensor product carrying the diagonal
action.

## Main definitions

* `groupAlgebraEnd_restrictScalars` restricts a group-algebra-linear endomorphism to the
  coefficient ring.
* `groupLinearMapAsEnd` bundles an equivariant coefficient-linear endomorphism as a
  group-algebra endomorphism.
* `diagonalTensorEndomorphism` is the tensor product of two equivariant endomorphisms,
  acting on the tensor product with diagonal group action.

## Main results

* `groupAlgebraEnd_commutes`: a group-algebra-linear endomorphism commutes with the
  represented group action.

## References

* [Stacks Project, Tag 03UA](https://stacks.math.columbia.edu/tag/03UA)
-/

@[expose] public noncomputable section

open scoped MonoidAlgebra

open Stacks.Trace.Representation

universe uA uΛ uG uP uM

namespace Stacks.Trace

/-- The module of a representation over a ring is an additive group. -/
instance Representation.asModuleNC.addCommGroup
    {k : Type*} {G : Type*} {V : Type*} [Ring k] [Monoid G]
    [AddCommMonoid V] [Module k V] (ρ : _root_.Representation k G V) :
    AddCommGroup (asModuleNC ρ) := Module.addCommMonoidToAddCommGroup k

/-- Restriction of an equivariant endomorphism from the group algebra to its coefficient
ring. -/
def groupAlgebraEnd_restrictScalars
    {k : Type*} {G : Type*} {V : Type*} [Semiring k] [Monoid G]
    [AddCommMonoid V] [Module k V] (ρ : _root_.Representation k G V)
    (f : Module.End k[G] (asModuleNC ρ)) : Module.End k V :=
  { f with
    map_smul' := by
      intro a x
      have h := f.map_smul (MonoidAlgebra.single 1 a) (show asModuleNC ρ from x)
      rw [single_smul_asModuleNC ρ a 1, single_smul_asModuleNC ρ a 1, map_one ρ] at h
      change f (a • x) = a • f x at h
      exact h }

/-- A group-algebra-linear endomorphism commutes with the represented group action. -/
lemma groupAlgebraEnd_commutes
    {k : Type*} {G : Type*} {V : Type*} [Semiring k] [Monoid G]
    [AddCommMonoid V] [Module k V] (ρ : _root_.Representation k G V)
    (f : Module.End k[G] (asModuleNC ρ)) (g : G) (x : V) :
    f (ρ g x) = ρ g (f x) := by
  have h := f.map_smul (MonoidAlgebra.single g (1 : k) : k[G]) (show asModuleNC ρ from x)
  rw [single_smul_asModuleNC, single_smul_asModuleNC] at h
  simpa using h

/-- Bundle an equivariant coefficient-linear endomorphism as a group-algebra endomorphism. -/
def groupLinearMapAsEnd
    {k : Type*} {G : Type*} {V : Type*} [Semiring k] [Monoid G]
    [AddCommMonoid V] [Module k V] (ρ : _root_.Representation k G V)
    (f : asModuleNC ρ →ₗ[k] asModuleNC ρ)
    (hf : ∀ g x, f (ρ g x) = ρ g (f x)) :
    Module.End k[G] (asModuleNC ρ) :=
  { f with map_smul' := map_smul_asModuleNC ρ ρ f hf }

/-- The tensor product endomorphism on the tensor product carrying the diagonal action. -/
def diagonalTensorEndomorphism
    {A : Type uA} {Λ : Type uΛ} {G : Type uG} {P : Type uP} {M : Type uM}
    [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P]
    [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
    (ρ : _root_.Representation A G P) (σ : _root_.Representation Λ G M)
    (u : Module.End A[G] (asModuleNC ρ))
    (v : Module.End Λ[G] (asModuleNC σ)) :
    { f : Module.End Λ[G] (asModuleNC (tprodAlgebra ρ σ)) //
      ∀ (p : P) (m : M), f (p ⊗ₜ[A] m) =
        (show P from u p) ⊗ₜ[A] (show M from v m) } := by
  let τ := Representation.tprodAlgebraReversed ρ σ
  let f0 : TensorProduct A M P →ₗ[Λ] TensorProduct A M P :=
    TensorProduct.AlgebraTensorModule.map (groupAlgebraEnd_restrictScalars σ v)
      (groupAlgebraEnd_restrictScalars ρ u)
  let eNC : asModuleNC τ ≃ₗ[Λ] TensorProduct A M P := {
    toFun := id
    invFun := id
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  let fΛ : asModuleNC τ →ₗ[Λ] asModuleNC τ :=
    eNC.symm.toLinearMap.comp (f0.comp eNC.toLinearMap)
  have hf0 : ∀ g z, f0 (τ g z) = τ g (f0 z) := by
    intro g z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul m p =>
        change f0 ((σ g m) ⊗ₜ[A] (ρ g p)) =
          (σ g (v m)) ⊗ₜ[A] (ρ g (u p))
        simp only [f0, TensorProduct.AlgebraTensorModule.map_tmul]
        have hv : groupAlgebraEnd_restrictScalars σ v (σ g m) =
            σ g (show M from v (show asModuleNC σ from m)) :=
          groupAlgebraEnd_commutes σ v g (show asModuleNC σ from m)
        have hu : groupAlgebraEnd_restrictScalars ρ u (ρ g p) =
            ρ g (show P from u (show asModuleNC ρ from p)) :=
          groupAlgebraEnd_commutes ρ u g (show asModuleNC ρ from p)
        rw [hv, hu]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hf : ∀ g z, fΛ (τ g z) = τ g (fΛ z) := fun g z => eNC.injective (hf0 g (eNC z))
  let fG : Module.End Λ[G] (asModuleNC τ) := groupLinearMapAsEnd τ fΛ hf
  let e := Representation.tprodAlgebraCommModuleEquiv ρ σ
  let f : Module.End Λ[G] (asModuleNC (tprodAlgebra ρ σ)) :=
    e.symm.toLinearMap.comp (fG.comp e.toLinearMap)
  refine ⟨f, fun p m => ?_⟩
  change e.symm (fG (e (p ⊗ₜ[A] m))) =
    (show P from u p) ⊗ₜ[A] (show M from v m)
  rw [Representation.tprodAlgebraCommModuleEquiv_apply_tmul]
  change e.symm (eNC.symm (f0 (eNC (m ⊗ₜ[A] p)))) =
    (show P from u p) ⊗ₜ[A] (show M from v m)
  simp only [eNC]
  rfl
end Stacks.Trace

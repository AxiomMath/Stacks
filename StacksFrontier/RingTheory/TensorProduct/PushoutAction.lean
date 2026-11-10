module

public import Mathlib.RingTheory.IsTensorProduct

/-!
# Modules over a pushout of rings as modules with a commuting action

Let `T = S ⊗_A R` be a pushout of commutative rings and let `M` be an `S`-module together with
a ring map `ρ : R → End_S(M)` which on `A` is the action of `A` through `S`.  The two actions of
`S` and of `R` on `M` commute, so `M` is a `T`-module, and `M` is recovered from its base change
`T ⊗_S M` as the quotient by the relations

`t ⊗ ρ(r) m = (r t) ⊗ m`, for `r ∈ R`.

## Main definitions

* `Algebra.IsPushout.actionHom`: the action `T → End_S(M)` assembled from the actions of `S`
  and `R`.
* `Algebra.IsPushout.actionLift`: the action map `T ⊗_S M → M`, `t ⊗ m ↦ t • m`.
* `Algebra.IsPushout.relationMap`: for `r ∈ R`, the `T`-linear endomorphism
  `t ⊗ m ↦ t ⊗ ρ(r) m - (r t) ⊗ m` of `T ⊗_S M`, whose ranges are the relations.

## Main results

* `Algebra.IsPushout.actionLift_tmul_one`: `actionLift (1 ⊗ m) = m`.
* `Algebra.IsPushout.actionLift_relationMap`: the action map kills every relation.
* `Algebra.IsPushout.sub_tmul_actionLift_mem`: every element `z` of `T ⊗_S M` differs from
  `1 ⊗ actionLift z` by a sum of relations.
-/

@[expose] public noncomputable section

open TensorProduct

namespace Algebra.IsPushout

variable {A S R T : Type*} [CommRing A] [CommRing S] [CommRing R] [CommRing T]
  [Algebra A S] [Algebra A R] [Algebra A T] [Algebra S T] [Algebra R T]
  [IsScalarTower A S T] [IsScalarTower A R T] [Algebra.IsPushout A S R T]
  {M : Type*} [AddCommGroup M] [Module S M]
  (ρ : R →+* Module.End S M)
  (hρ : ∀ a : A, ρ (algebraMap A R a) = algebraMap S (Module.End S M) (algebraMap A S a))

/-- The `A`-algebra structure on `End_S(M)` through `S`. -/
@[reducible] def endAlgebra : Algebra A (Module.End S M) :=
  ((algebraMap S (Module.End S M)).comp (algebraMap A S)).toAlgebra' fun a f => by
    ext m
    exact (f.map_smul (algebraMap A S a) m).symm

/-- The action of `S` on `M`, as a map of `A`-algebras. -/
def leftActionAlgHom :
    letI := endAlgebra (A := A) (S := S) (M := M)
    S →ₐ[A] Module.End S M :=
  letI := endAlgebra (A := A) (S := S) (M := M)
  AlgHom.mk (algebraMap S (Module.End S M)) fun _ => rfl

include hρ in
/-- The action `ρ` of `R` on `M`, as a map of `A`-algebras. -/
def rightActionAlgHom :
    letI := endAlgebra (A := A) (S := S) (M := M)
    R →ₐ[A] Module.End S M :=
  letI := endAlgebra (A := A) (S := S) (M := M)
  AlgHom.mk ρ fun a => hρ a

include hρ in
/-- The action of `T = S ⊗_A R` on `M` assembled from the action of `S` and the commuting action
`ρ` of `R`. -/
def actionHom : T →+* Module.End S M :=
  letI := endAlgebra (A := A) (S := S) (M := M)
  (Algebra.pushoutDesc T (leftActionAlgHom (A := A)) (rightActionAlgHom ρ hρ)
    (fun s r => by
      ext m
      exact ((ρ r).map_smul s m).symm)).toRingHom

/-- On the image of `S` in `T`, the action of `T` on `M` is the action of `S`. -/
theorem actionHom_algebraMap_left (s : S) :
    actionHom ρ hρ (algebraMap S T s) = algebraMap S (Module.End S M) s := by
  let := endAlgebra (A := A) (S := S) (M := M)
  exact Algebra.pushoutDesc_left _ _ _ _ s

/-- On the image of `R` in `T`, the action of `T` on `M` is `ρ`. -/
theorem actionHom_algebraMap_right (r : R) :
    actionHom ρ hρ (algebraMap R T r) = ρ r := by
  let := endAlgebra (A := A) (S := S) (M := M)
  exact Algebra.pushoutDesc_right _ _ _ _ r

/-- The action of `T` on `M`, as an `S`-linear map into `End_S(M)`. -/
def actionLinearMap : T →ₗ[S] Module.End S M where
  toFun t := actionHom ρ hρ t
  map_add' t t' := by rw [map_add]
  map_smul' s t := by
    rw [Algebra.smul_def, map_mul, actionHom_algebraMap_left]
    ext m
    rfl

/-- The action map `T ⊗_S M → M`, `t ⊗ m ↦ t • m`. -/
def actionLift : T ⊗[S] M →ₗ[S] M :=
  _root_.TensorProduct.lift (actionLinearMap ρ hρ)

/-- The action map sends `t ⊗ m` to `t • m`. -/
@[simp]
theorem actionLift_tmul (t : T) (m : M) : actionLift ρ hρ (t ⊗ₜ m) = actionHom ρ hρ t m :=
  rfl

/-- The action map sends `1 ⊗ m` to `m`. -/
theorem actionLift_tmul_one (m : M) : actionLift ρ hρ ((1 : T) ⊗ₜ m) = m := by
  rw [actionLift_tmul, map_one]
  rfl

variable (T) in
/-- For `r ∈ R`, the `T`-linear endomorphism `t ⊗ m ↦ t ⊗ ρ(r) m - (r t) ⊗ m` of `T ⊗_S M`; its
range consists of the relations identifying `M` with a quotient of `T ⊗_S M`. -/
def relationMap (r : R) : T ⊗[S] M →ₗ[T] T ⊗[S] M :=
  (ρ r).baseChange T - algebraMap R T r • LinearMap.id

/-- The relation map for `r` sends `t ⊗ m` to `t ⊗ ρ(r) m - (r t) ⊗ m`. -/
theorem relationMap_tmul (r : R) (t : T) (m : M) :
    relationMap T ρ r (t ⊗ₜ m) = t ⊗ₜ ρ r m - (algebraMap R T r * t) ⊗ₜ m := by
  simp [relationMap, LinearMap.baseChange_tmul, _root_.TensorProduct.smul_tmul', Algebra.smul_def]

/-- **The action map kills every relation.** -/
theorem actionLift_relationMap (r : R) (z : T ⊗[S] M) :
    actionLift ρ hρ (relationMap T ρ r z) = 0 := by
  induction z using _root_.TensorProduct.inductionOn with
  | tmul t m =>
    rw [relationMap_tmul, map_sub, actionLift_tmul, actionLift_tmul, map_mul,
      actionHom_algebraMap_right, sub_eq_zero, ← actionHom_algebraMap_right (T := T) ρ hρ r,
      ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]
  | add z w hz hw => rw [map_add, map_add, hz, hw, add_zero]

variable (T) in
/-- The submodule of relations: the join of the ranges of the relation maps. -/
def relations : Submodule T (T ⊗[S] M) :=
  ⨆ r : R, LinearMap.range (relationMap T ρ r)

variable (T) in
/-- Every value of a relation map is a relation. -/
theorem relationMap_mem_relations (r : R) (z : T ⊗[S] M) :
    relationMap T ρ r z ∈ relations T ρ :=
  Submodule.mem_iSup_of_mem r ⟨z, rfl⟩

/-- **The action map kills the relations.** -/
theorem relations_le_ker_actionLift :
    (relations T ρ).restrictScalars S ≤ LinearMap.ker (actionLift ρ hρ) := by
  intro z hz
  change z ∈ relations T ρ at hz
  refine Submodule.iSup_induction (motive := fun x => x ∈ LinearMap.ker (actionLift ρ hρ))
    (fun r => LinearMap.range (relationMap T ρ r)) hz ?_ ?_ ?_
  · rintro r _ ⟨w, rfl⟩
    exact actionLift_relationMap ρ hρ r w
  · exact (LinearMap.ker (actionLift ρ hρ)).zero_mem
  · intro x y hx hy
    exact (LinearMap.ker (actionLift ρ hρ)).add_mem hx hy

/-- Membership of a difference in a submodule is additive. -/
private theorem add_sub_add_mem {X : Type*} [AddCommGroup X] {N : AddSubgroup X} {a b c d : X}
    (h₁ : a - c ∈ N) (h₂ : b - d ∈ N) : a + b - (c + d) ∈ N := by
  rw [add_sub_add_comm]
  exact N.add_mem h₁ h₂

include hρ in
/-- For `t ∈ T` and `m ∈ M`, the element `t ⊗ m - 1 ⊗ (t • m)` of `T ⊗_S M` is a relation. -/
theorem tmul_sub_one_tmul_mem (t : T) (m : M) :
    t ⊗ₜ m - (1 : T) ⊗ₜ actionHom ρ hρ t m ∈ relations T ρ := by
  obtain ⟨z, rfl⟩ := (Algebra.IsPushout.equiv A S R T).surjective t
  induction z using _root_.TensorProduct.inductionOn generalizing m with
  | tmul s r =>
    rw [Algebra.IsPushout.equiv_tmul, map_mul, actionHom_algebraMap_left,
      actionHom_algebraMap_right]
    have h1 : (algebraMap S T s * algebraMap R T r) ⊗ₜ[S] m =
        algebraMap R T r • ((1 : T) ⊗ₜ[S] (s • m)) := by
      rw [_root_.TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← _root_.TensorProduct.smul_tmul,
        Algebra.smul_def]
    have h2 : relationMap T ρ r ((1 : T) ⊗ₜ[S] (s • m)) =
        (1 : T) ⊗ₜ[S] ρ r (s • m) - algebraMap R T r • ((1 : T) ⊗ₜ[S] (s • m)) := by
      rw [relationMap_tmul, mul_one, _root_.TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h3 : (algebraMap S (Module.End S M) s * ρ r) m = ρ r (s • m) := by
      change s • ρ r m = ρ r (s • m)
      rw [map_smul]
    rw [h1, h3]
    rw [← neg_mem_iff, neg_sub, ← h2]
    exact relationMap_mem_relations T ρ r _
  | add z w hz hw =>
    rw [map_add, map_add, _root_.TensorProduct.add_tmul, LinearMap.add_apply,
      _root_.TensorProduct.tmul_add]
    exact add_sub_add_mem (N := (relations T ρ).toAddSubgroup) (hz m) (hw m)

/-- **Every element of `T ⊗_S M` differs from `1 ⊗ (its action)` by a sum of relations.** -/
theorem sub_tmul_actionLift_mem (z : T ⊗[S] M) :
    z - (1 : T) ⊗ₜ actionLift ρ hρ z ∈ relations T ρ := by
  induction z using _root_.TensorProduct.inductionOn with
  | tmul t m => exact tmul_sub_one_tmul_mem ρ hρ t m
  | add z w hz hw =>
    rw [map_add, _root_.TensorProduct.tmul_add]
    exact add_sub_add_mem (N := (relations T ρ).toAddSubgroup) hz hw

end Algebra.IsPushout

end

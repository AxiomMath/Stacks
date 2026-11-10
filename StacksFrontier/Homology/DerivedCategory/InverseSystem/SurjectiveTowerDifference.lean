module

public import Mathlib.Algebra.Group.Basic

/-!
# Surjectivity of the difference map of a surjective tower of abelian groups

Let `M` be a tower of abelian groups with transition maps `t n : M (n + 1) → M n`. If every
transition map is surjective, then the difference map `x ↦ fun n ↦ x n - t n (x (n + 1))` on the
product of the terms is surjective: a preimage is built upwards, one transition map at a time.
-/

namespace Stacks.InverseSystem

universe u

/-- The difference map of a tower of abelian groups whose transition maps are all surjective is
surjective on the product of the terms. -/
public theorem surjective_pi_sub_shift
    {M : ℕ → Type u} [∀ n, AddCommGroup (M n)]
    (t : ∀ n, M (n + 1) → M n) (ht : ∀ n, Function.Surjective (t n)) :
    Function.Surjective (fun x : ∀ n, M n ↦ fun n ↦ x n - t n (x (n + 1))) := by
  classical
  intro y
  let x : ∀ n, M n := fun n ↦ Nat.rec (0 : M 0)
    (fun n z ↦ (ht n (z - y n)).choose) n
  refine ⟨x, funext fun n ↦ ?_⟩
  have hn : t n (x (n + 1)) = x n - y n := (ht n (x n - y n)).choose_spec
  change x n - t n (x (n + 1)) = y n
  rw [hn, sub_sub_cancel]

end Stacks.InverseSystem

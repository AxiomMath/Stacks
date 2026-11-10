module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SectionsColimitDescent
public import Mathlib.LinearAlgebra.TensorProduct.DirectLimit

/-!
# Extension of scalars along a filtered colimit of modules, elementwise

Let `G_i → G` be a filtered colimit of `R`-modules, in the elementwise form
`Stacks.IsStagesColimit`, and let `M` be an `R`-module. Then `G_i ⊗_R M → G ⊗_R M` is a filtered
colimit: the tensor product commutes with filtered colimits.

## Main results

* `Stacks.LimitHomDescent.isStagesColimit_rTensor`: the statement.
-/

@[expose] public section

open TensorProduct

universe u v

namespace Stacks.LimitHomDescent

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [IsDirected J (· ≤ ·)]
  [Nonempty J] [DecidableEq J]
  {G : J → Type u} [∀ j, AddCommGroup (G j)] [∀ j, Module R (G j)]
  (f : ∀ i j, i ≤ j → G i →ₗ[R] G j) {T : Type u} [AddCommGroup T] [Module R T]
  (ι : ∀ j, G j →ₗ[R] T)
  (hrefl : ∀ i (x : G i), f i i le_rfl x = x)
  (hcomp : ∀ i j k (h : i ≤ j) (h' : j ≤ k) (x : G i), f j k h' (f i j h x) = f i k (h.trans h') x)

omit [DecidableEq J] in
include hrefl hcomp in
/-- **The tensor product commutes with filtered colimits**, elementwise. -/
theorem isStagesColimit_rTensor
    (hG : Stacks.IsStagesColimit (fun i j h x => f i j h x) (fun j x => ι j x))
    (M : Type u) [AddCommGroup M] [Module R M] :
    Stacks.IsStagesColimit (fun i j h x => (f i j h).rTensor M x)
      (fun j x => (ι j).rTensor M x) := by
  classical
  have : DirectedSystem G (fun i j h => f i j h) :=
    ⟨fun i x => hrefl i x, fun k j i h h' x => hcomp i j k h h' x⟩
  let Φ : Module.DirectLimit G f →ₗ[R] T :=
    Module.DirectLimit.lift R J G f ι (fun i j h x => hG.ι_trans i j h x)
  have hΦ : Function.Bijective Φ := by
    constructor
    · intro z w hzw
      obtain ⟨i, x, y, rfl, rfl⟩ := Module.DirectLimit.exists_of₂ z w
      simp only [Φ, Module.DirectLimit.lift_of] at hzw
      obtain ⟨j, hij, hj⟩ := hG.exists_trans_eq i x y hzw
      rw [← Module.DirectLimit.of_f (hij := hij), ← Module.DirectLimit.of_f (hij := hij)]
      exact congrArg _ hj
    · intro t
      obtain ⟨i, x, hx⟩ := hG.exists_stage t
      exact ⟨Module.DirectLimit.of R J G f i x, by simp only [Φ, Module.DirectLimit.lift_of, hx]⟩
  let eΦ : Module.DirectLimit G f ≃ₗ[R] T := LinearEquiv.ofBijective Φ hΦ
  let E : Module.DirectLimit G f ⊗[R] M ≃ₗ[R] Module.DirectLimit (G · ⊗[R] M)
      (fun i j h => (f i j h).rTensor M) := directLimitLeft f M
  have hcompat : ∀ i (y : G i ⊗[R] M),
      (ι i).rTensor M y = eΦ.toLinearMap.rTensor M (E.symm
        (Module.DirectLimit.of R J (G · ⊗[R] M) (fun i j h => (f i j h).rTensor M) i y)) := by
    intro i y
    induction y using TensorProduct.inductionOn with
    | tmul x m =>
      simp only [E, directLimitLeft_symm_of_tmul, LinearMap.rTensor_tmul, LinearEquiv.coe_coe]
      congr 1
      exact (Module.DirectLimit.lift_of (G := G) (f := f) ι
        (fun i j h x => hG.ι_trans i j h x) x).symm
    | add y y' hy hy' => simp only [map_add, hy, hy']
  refine ⟨fun i j h y => ?_, fun t => ?_, fun i y y' hyy => ?_⟩
  · rw [hcompat, hcompat, Module.DirectLimit.of_f]
  · obtain ⟨z, rfl⟩ := (LinearEquiv.rTensor M eΦ).surjective t
    obtain ⟨i, y, hy⟩ := Module.DirectLimit.exists_of (E z)
    refine ⟨i, y, ?_⟩
    rw [hcompat, hy, LinearEquiv.symm_apply_apply]
    rfl
  · rw [hcompat, hcompat] at hyy
    exact Module.DirectLimit.exists_eq_of_of_eq
      (E.symm.injective ((LinearEquiv.rTensor M eΦ).injective hyy))

end Stacks.LimitHomDescent

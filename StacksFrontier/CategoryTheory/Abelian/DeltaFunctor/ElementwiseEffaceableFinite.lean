module

public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.ElementwiseEffaceable

/-!
# Effacing all of a finite cohomology module at once

If a δ-functor `F` with values in modules is elementwise effaceable, every class of `Fⁿ⁺¹(X)` is
killed by some monomorphism out of `X`. When `Fⁿ⁺¹(X)` is finite, one monomorphism kills all of
them: kill one class, push the remaining ones forward, and compose.

## Main results

* `CategoryTheory.DeltaFunctor.ElementwiseEffaceable.exists_mono_map_eq_zero_of_finite`.
-/

@[expose] public section

universe w v u u'

namespace CategoryTheory.DeltaFunctor.ElementwiseEffaceable

variable {A : Type u} [Category.{v} A] [Abelian A] {R : Type u'} [Ring R]
  {F : DeltaFunctor A (ModuleCat.{w} R)} [F.ElementwiseEffaceable]

/-- A monomorphism out of `X` killing every class of a finite set in `Fⁿ⁺¹(X)`. -/
theorem exists_mono_map_eq_zero_of_finset {X : A} {n : ℕ}
    (s : Finset ((F.functor (n + 1)).obj X)) :
    ∃ (I : A) (ι : X ⟶ I), Mono ι ∧ ∀ x ∈ s, (F.functor (n + 1)).map ι x = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨X, 𝟙 X, inferInstance, fun x hx ↦ absurd hx (Finset.notMem_empty x)⟩
  | insert x s _ ih =>
    obtain ⟨I, ι, hι, hs⟩ := ih
    obtain ⟨I', ι', hι', hx⟩ := ElementwiseEffaceable.exists_mono ((F.functor (n + 1)).map ι x)
    refine ⟨I', ι ≫ ι', mono_comp _ _, fun y hy ↦ ?_⟩
    rw [Functor.map_comp, ModuleCat.comp_apply]
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hx
    · rw [hs y hy, map_zero]

/-- **One monomorphism kills a finite `Fⁿ⁺¹(X)`.** -/
theorem exists_mono_map_eq_zero_of_finite (X : A) (n : ℕ)
    [Finite ((F.functor (n + 1)).obj X)] :
    ∃ (I : A) (ι : X ⟶ I), Mono ι ∧ (F.functor (n + 1)).map ι = 0 := by
  let := Fintype.ofFinite ((F.functor (n + 1)).obj X)
  obtain ⟨I, ι, hι, h⟩ := exists_mono_map_eq_zero_of_finset (F := F) (X := X) (n := n) Finset.univ
  exact ⟨I, ι, hι, ModuleCat.hom_ext (LinearMap.ext fun x ↦ (h x (Finset.mem_univ x)).trans rfl)⟩

end CategoryTheory.DeltaFunctor.ElementwiseEffaceable

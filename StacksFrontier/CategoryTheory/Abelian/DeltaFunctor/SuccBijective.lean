module

public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.ElementwiseEffaceable

/-!
# Bijectivity of a morphism of δ-functors, one degree at a time

Let `γ : F ⟶ G` be a morphism of cohomological δ-functors with values in modules. If `γ` is
bijective in degree `n` and both `F` and `G` are effaced class by class in degree `n + 1` (every
class of `Fⁿ⁺¹(X)`, resp. `Gⁿ⁺¹(X)`, is killed by some monomorphism out of `X`), then `γ` is
bijective in degree `n + 1`. This is the five lemma along the sequence `X → I → I/X` of an
effacing monomorphism; it needs effaceability only in the one degree, which is what makes it
usable before the full universality of `G` is known.

## Main results

* `CategoryTheory.DeltaFunctor.bijective_app_succ` — the induction step.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u u'

namespace CategoryTheory.DeltaFunctor

variable {A : Type u} [Category.{v} A] [Abelian A] {R : Type u'} [Ring R]
  {F G : DeltaFunctor A (ModuleCat.{w} R)}

/-- **Bijectivity passes from degree `n` to degree `n + 1`** when both δ-functors are effaced
class by class in degree `n + 1`. -/
theorem bijective_app_succ (γ : F ⟶ G) (n : ℕ)
    (hn : ∀ X, Function.Bijective ((γ.app n).app X))
    (hF : ∀ (X : A) (x : (F.functor (n + 1)).obj X),
      ∃ (I : A) (ι : X ⟶ I), Mono ι ∧ (F.functor (n + 1)).map ι x = 0)
    (hG : ∀ (X : A) (x : (G.functor (n + 1)).obj X),
      ∃ (I : A) (ι : X ⟶ I), Mono ι ∧ (G.functor (n + 1)).map ι x = 0)
    (X : A) : Function.Bijective ((γ.app (n + 1)).app X) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨I, ι, hι, hzι⟩ := hF X z
    let S := ElementwiseEffaceable.effSeq ι
    have hS := ElementwiseEffaceable.shortExact_effSeq ι
    obtain ⟨y, rfl⟩ := ElementwiseEffaceable.exists_δ_eq hS z hzι
    have hγy : G.δ hS n ((γ.app n).app S.X₃ y) = 0 :=
      (ConcreteCategory.congr_hom (γ.comm hS n) y).trans hz
    obtain ⟨w', hw'⟩ := (ShortComplex.moduleCat_exact_iff _).1 (G.exact_δ₁ hS n) _ hγy
    obtain ⟨w, rfl⟩ := (hn S.X₂).2 w'
    have hyw : (F.functor n).map S.g w = y :=
      (hn S.X₃).1 ((ConcreteCategory.congr_hom ((γ.app n).naturality S.g) w).trans hw')
    rw [← hyw, ← ConcreteCategory.comp_apply, F.map_g_δ]
    rfl
  · intro x
    obtain ⟨I, ι, hι, hxι⟩ := hG X x
    let S := ElementwiseEffaceable.effSeq ι
    have hS := ElementwiseEffaceable.shortExact_effSeq ι
    obtain ⟨y, rfl⟩ := ElementwiseEffaceable.exists_δ_eq hS x hxι
    obtain ⟨y', rfl⟩ := (hn S.X₃).2 y
    exact ⟨F.δ hS n y', (ConcreteCategory.congr_hom (γ.comm hS n) y').symm⟩

end CategoryTheory.DeltaFunctor

end

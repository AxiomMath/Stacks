module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.MapAlongCorepresentation
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# `Ext` along an exact functor and a corepresenting morphism, with acyclic images of injectives

Let `R : A ⥤ B` be an exact functor of abelian categories, `A` having enough injectives, and let
`u : Y ⟶ R X` be such that `f ↦ u ≫ R f` is a bijection `(X ⟶ M) ≃ (Y ⟶ R M)` for every `M`.
If `Ext^{n+1}(Y, R I)` vanishes for every injective `I` of `A`, then the comparison
`Stacks.Cohomology.ExtComparison.extMapAlong` (apply `R`, precompose with `u`) is bijective in
every degree.

This is `Stacks.Cohomology.ExtComparison.extMapAlong_bijective` with the hypothesis that `R`
preserves injective objects replaced by the only consequence the dimension shifting uses. It
applies to restriction of scalars along a surjection of rings, which does not preserve injective
objects, but carries them to objects without higher cohomology.

## Main results

* `Stacks.Cohomology.ExtComparison.extMapAlong_bijective_of_subsingleton`: the comparison is
  bijective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe w w' vA vB uA uB

namespace Stacks.Cohomology.ExtComparison

variable {A : Type uA} [Category.{vA} A] [Abelian A] {B : Type uB} [Category.{vB} B] [Abelian B]
  (R : A ⥤ B) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [HasExt.{w} A] [HasExt.{w'} B]

/-- **The comparison along a corepresenting morphism is bijective when `R` carries injective
objects to objects without higher `Ext` from `Y`.** If `R` is exact, `A` has enough injectives,
`f ↦ u ≫ R f` is bijective on morphisms out of `X`, and `Ext^{n+1}(Y, R I) = 0` for every
injective `I`, then `Ext^n(X, M) ⟶ Ext^n(Y, R M)` is bijective for every `M` and `n`. -/
theorem extMapAlong_bijective_of_subsingleton [EnoughInjectives A] {X : A} {Y : B}
    (u : Y ⟶ R.obj X) (hu : ∀ M : A, Function.Bijective (fun f : X ⟶ M => u ≫ R.map f))
    (hI : ∀ (I : A) [Injective I] (n : ℕ), Subsingleton (Ext.{w'} Y (R.obj I) (n + 1)))
    (M : A) (n : ℕ) : Function.Bijective (extMapAlong.{w, w'} R u M n) := by
  induction n generalizing M with
  | zero =>
    have he : (extMapAlong.{w, w'} R u M 0 : _ → _) ∘ Ext.mk₀ =
        Ext.mk₀ ∘ (fun f : X ⟶ M => u ≫ R.map f) := funext (extMapAlong_mk₀ R u)
    refine (Function.Bijective.of_comp_iff _ (Ext.mk₀_bijective X M)).mp ?_
    rw [he]
    exact (Ext.mk₀_bijective Y (R.obj M)).comp (hu M)
  | succ n hn =>
    let I : InjectivePresentation M := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    have : Injective S.X₂ := I.injective
    have := Ext.subsingleton_of_injective X S.X₂ n
    have := hI S.X₂ n
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (extMapAlong.{w, w'} R u S.X₂ n) (extMapAlong.{w, w'} R u S.X₃ n)
      (extMapAlong.{w, w'} R u S.X₁ (n + 1))
      (by ext e; exact (extMapAlong_comp_mk₀ R u S.g e).symm)
      (by ext e; exact (extMapAlong_comp_extClass R u hS e).symm)
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' X hS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' Y (hS.map_of_exact R) n (n + 1) rfl))
      (hn _).surjective (hn _)
      (fun x₁ => Ext.covariant_sequence_exact₁ _ hS x₁ (by subsingleton) rfl)
      (fun y₁ => Ext.covariant_sequence_exact₁ _ (hS.map_of_exact R) y₁
        (Subsingleton.elim (α := Ext.{w'} Y (R.obj S.X₂) (n + 1)) _ _) rfl)

end Stacks.Cohomology.ExtComparison

end

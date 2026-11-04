module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective

/-!
# `Ext` along an exact functor and a corepresenting morphism

Let `R : A ⥤ B` be an exact functor of abelian categories which preserves injective objects, with
`A` having enough injectives. Let `X : A`, `Y : B` and `u : Y ⟶ R X` be such that
`f ↦ u ≫ R f` is a bijection `(X ⟶ M) ≃ (Y ⟶ R M)` for every `M`. Then applying `R` to an
extension class and precomposing with `u` gives a bijection `Ext^n(X, M) ≃ Ext^n(Y, R M)` in every
degree.

The map is built from `CategoryTheory.Abelian.Ext.mapExactFunctor`, so it is compatible with the
composition of `Ext` on both sides. This is what makes it natural in the *first* variable as well
as in the second, which the comparisons through derived functors do not give for free: a
cohomology presheaf is `Ext` out of a varying object, and its restriction maps are precomposition.

## Main definitions

* `Stacks.Cohomology.ExtComparison.extMapAlong`: the comparison map.

## Main results

* `Stacks.Cohomology.ExtComparison.extMapAlong_bijective`: the comparison is bijective.
* `Stacks.Cohomology.ExtComparison.extMapAlong_mk₀_comp`: the comparison commutes with
  precomposition by a morphism of the first variable, given a commuting square of corepresenting
  morphisms.

## Implementation notes

The bijectivity is the dimension shifting argument of
`CategoryTheory.Functor.mapExt_bijective_of_preservesInjectiveObjects`, which is the case
`u = 𝟙` of a fully faithful `R`; the five lemma applies to the covariant long exact sequences of
an injective presentation of `M` and of its image under `R`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe w w' vA vB uA uB

namespace Stacks.Cohomology.ExtComparison

variable {A : Type uA} [Category.{vA} A] [Abelian A] {B : Type uB} [Category.{vB} B] [Abelian B]
  (R : A ⥤ B) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [HasExt.{w} A] [HasExt.{w'} B]

/-- **The comparison `Ext^n(X, M) ⟶ Ext^n(Y, R M)` along `u : Y ⟶ R X`.** Apply the exact
functor `R` to an extension class and precompose with `u`. -/
def extMapAlong {X : A} {Y : B} (u : Y ⟶ R.obj X) (M : A) (n : ℕ) :
    Ext.{w} X M n →+ Ext.{w'} Y (R.obj M) n :=
  ((Ext.mk₀ u).precomp (R.obj M) (zero_add n)).comp (R.mapExtAddHom X M n)

/-- The comparison along `u` sends `e` to the composition of `Ext.mk₀ u` with the image of `e`
under `R`. -/
theorem extMapAlong_apply {X : A} {Y : B} (u : Y ⟶ R.obj X) {M : A} {n : ℕ}
    (e : Ext.{w} X M n) :
    extMapAlong.{w, w'} R u M n e = (Ext.mk₀ u).comp (e.mapExactFunctor R) (zero_add n) :=
  rfl

/-- **The comparison commutes with precomposition in the first variable.** If `u₁ ≫ R z = y ≫ u₂`
then the comparisons along `u₁` and `u₂` intertwine precomposition by `z` and by `y`. -/
theorem extMapAlong_mk₀_comp {X₁ X₂ : A} {Y₁ Y₂ : B} (u₁ : Y₁ ⟶ R.obj X₁)
    (u₂ : Y₂ ⟶ R.obj X₂) (z : X₁ ⟶ X₂) (y : Y₁ ⟶ Y₂) (h : u₁ ≫ R.map z = y ≫ u₂) {M : A}
    {n : ℕ} (e : Ext.{w} X₂ M n) :
    extMapAlong.{w, w'} R u₁ M n ((Ext.mk₀ z).comp e (zero_add n)) =
      (Ext.mk₀ y).comp (extMapAlong.{w, w'} R u₂ M n e) (zero_add n) := by
  simp only [extMapAlong_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.mk₀_comp_mk₀_assoc, h]

/-- **The comparison commutes with postcomposition by a morphism in the second variable.** -/
theorem extMapAlong_comp_mk₀ {X : A} {Y : B} (u : Y ⟶ R.obj X) {M M' : A} (g : M ⟶ M')
    {n : ℕ} (e : Ext.{w} X M n) :
    extMapAlong.{w, w'} R u M' n (e.comp (Ext.mk₀ g) (add_zero n)) =
      (extMapAlong.{w, w'} R u M n e).comp (Ext.mk₀ (R.map g)) (add_zero n) := by
  simp only [extMapAlong_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero]

/-- **The comparison commutes with the connecting map of a short exact sequence** in the second
variable. -/
theorem extMapAlong_comp_extClass {X : A} {Y : B} (u : Y ⟶ R.obj X) {S : ShortComplex A}
    (hS : S.ShortExact) {n : ℕ} (e : Ext.{w} X S.X₃ n) :
    extMapAlong.{w, w'} R u S.X₁ (n + 1) (e.comp hS.extClass rfl) =
      (extMapAlong.{w, w'} R u S.X₃ n e).comp (hS.map_of_exact R).extClass rfl := by
  simp only [extMapAlong_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  exact (Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)).symm

/-- In degree `0`, the comparison along `u` sends the class of `f : X ⟶ M` to the class of
`u ≫ R.map f`. -/
theorem extMapAlong_mk₀ {X : A} {Y : B} (u : Y ⟶ R.obj X) {M : A} (f : X ⟶ M) :
    extMapAlong.{w, w'} R u M 0 (Ext.mk₀ f) = Ext.mk₀ (u ≫ R.map f) := by
  simp only [extMapAlong_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]

/-- **The comparison along a corepresenting morphism is bijective.** If `R` is exact and preserves
injective objects, `A` has enough injectives, and `f ↦ u ≫ R f` is bijective on morphisms out of
`X`, then `Ext^n(X, M) ⟶ Ext^n(Y, R M)` is bijective for every `M` and `n`. -/
theorem extMapAlong_bijective [EnoughInjectives A] [R.PreservesInjectiveObjects] {X : A} {Y : B}
    (u : Y ⟶ R.obj X) (hu : ∀ M : A, Function.Bijective (fun f : X ⟶ M => u ≫ R.map f))
    (M : A) (n : ℕ) : Function.Bijective (extMapAlong.{w, w'} R u M n) := by
  induction n generalizing M with
  | zero =>
    have he : (extMapAlong.{w, w'} R u M 0 : _ → _) ∘ Ext.mk₀ =
        Ext.mk₀ ∘ (fun f : X ⟶ M => u ≫ R.map f) :=
      funext fun f => extMapAlong_mk₀ R u f
    refine (Function.Bijective.of_comp_iff _ (Ext.mk₀_bijective X M)).mp ?_
    rw [he]
    exact (Ext.mk₀_bijective Y (R.obj M)).comp (hu M)
  | succ n hn =>
    let I : InjectivePresentation M := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    have : Injective (S.map R).X₂ := Functor.PreservesInjectiveObjects.injective_obj I.injective
    have := Ext.subsingleton_of_injective X S.X₂ n
    have := Ext.subsingleton_of_injective Y (S.map R).X₂ n
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
      (fun y₁ => Ext.covariant_sequence_exact₁ _ (hS.map_of_exact R) y₁ (by subsingleton) rfl)

end Stacks.Cohomology.ExtComparison

end

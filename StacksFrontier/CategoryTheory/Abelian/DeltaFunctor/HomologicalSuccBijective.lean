module

public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.HomologicalUniversal
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Bijectivity of a morphism of homological δ-functors, degree by degree

Let `γ : T ⟶ H` be a morphism of homological δ-functors with values in modules. If `γₙ` is
bijective on every object and both `T` and `H` are coeffaceable in degree `n + 1`, then `γₙ₊₁`
is bijective on every object: coeffacing `X` for `T` by `P₁ ⟶ X` and then `P₁` for `H` by
`P₂ ⟶ P₁`, the composite `π : P₂ ⟶ X` is killed by `Tₙ₊₁` and by `Hₙ₊₁`, so both connecting maps
of `0 → ker π → P₂ → X → 0` identify `Tₙ₊₁(X)` and `Hₙ₊₁(X)` with the kernels of `Tₙ(ker π ⟶ P₂)`
and `Hₙ(ker π ⟶ P₂)`, which `γₙ` matches. This is the homological form of
`CategoryTheory.DeltaFunctor.bijective_app_succ`.

## Main results

* `Stacks.CategoryHomology.HomologicalDeltaFunctor.bijective_app_succ`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w w'

namespace Stacks.CategoryHomology.HomologicalDeltaFunctor

variable {A : Type u} [Category.{v} A] [Abelian A] {R : Type w} [Ring R]
  {T H : HomologicalDeltaFunctor A (ModuleCat.{w'} R)}

/-- **`γₙ₊₁` is bijective** if `γₙ` is and both δ-functors are coeffaceable in degree `n + 1`. -/
theorem bijective_app_succ (γ : T ⟶ H) (n : ℕ)
    (hn : ∀ X, Function.Bijective ((γ.app n).app X))
    (hT : ∀ X, Nonempty (T.Coeffacement X n)) (hH : ∀ X, Nonempty (H.Coeffacement X n)) (X : A) :
    Function.Bijective ((γ.app (n + 1)).app X) := by
  obtain ⟨cT⟩ := hT X
  obtain ⟨cH⟩ := hH cT.P
  let π : cH.P ⟶ X := cH.π ≫ cT.π
  have : Epi π := epi_comp _ _
  have hπT : (T.functor (n + 1)).map π = 0 := by
    rw [Functor.map_comp, cT.map_π, comp_zero]
  have hπH : (H.functor (n + 1)).map π = 0 := by
    rw [Functor.map_comp, cH.map_π, zero_comp]
  let S := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel S (kernelIsKernel π))
      (inferInstanceAs (Mono (kernel.ι π))) (inferInstanceAs (Epi π))
  have hinj : ∀ (F : HomologicalDeltaFunctor A (ModuleCat.{w'} R)),
      (F.functor (n + 1)).map π = 0 → Function.Injective (F.δ hS n).hom := by
    intro F hF
    exact (ModuleCat.mono_iff_injective _).1 ((F.exact_δ₁ hS n).mono_g hF)
  have hcomm : ∀ x, (γ.app n).app S.X₁ ((T.δ hS n) x) = (H.δ hS n) ((γ.app (n + 1)).app X x) :=
    fun x ↦ congrArg (fun φ ↦ ModuleCat.Hom.hom φ x) (γ.comm hS n)
  refine ⟨fun a b hab ↦ hinj T hπT ((hn S.X₁).1 (by rw [hcomm, hcomm, hab])), fun h ↦ ?_⟩
  obtain ⟨z, hz⟩ := (hn S.X₁).2 ((H.δ hS n) h)
  have hfz : ((T.functor n).map S.f) z = 0 := by
    apply (hn S.X₂).1
    have := congrArg (fun φ ↦ ModuleCat.Hom.hom φ z) ((γ.app n).naturality S.f)
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at this
    rw [this, hz, map_zero, ← ModuleCat.comp_apply, H.δ_map_f hS n]
    rfl
  obtain ⟨x, hx⟩ := (ShortComplex.moduleCat_exact_iff_ker_sub_range _).1 (T.exact_δ₂ hS n) hfz
  refine ⟨x, hinj H hπH ?_⟩
  rw [← hcomm]
  exact (congrArg _ hx).trans hz

end Stacks.CategoryHomology.HomologicalDeltaFunctor

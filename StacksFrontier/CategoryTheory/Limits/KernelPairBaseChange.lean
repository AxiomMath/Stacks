module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Base change of a kernel pair

Let `s, t : R ⟶ U` be a kernel pair of `u : U ⟶ Y` and let `g : Y' ⟶ Y`. If `U'` is the fibre
product of `u` and `g`, and `R'` is the fibre product of `s ≫ u` and `g`, with two morphisms
`s', t' : R' ⟶ U'` lying over `s` and `t`, then `s', t'` is a kernel pair of `U' ⟶ Y'`.

## Main results

* `CategoryTheory.IsPullback.of_isPullback_kernelPair`: the base changed pair is a kernel pair.
-/

@[expose] public section

namespace CategoryTheory.IsPullback

open Limits

variable {C : Type*} [Category* C]

/-- **The base change of a kernel pair is a kernel pair.** -/
theorem of_isPullback_kernelPair {R U Y R' U' Y' : C} {s t : R ⟶ U} {u : U ⟶ Y}
    (hk : IsPullback s t u u) {σ : U' ⟶ U} {u' : U' ⟶ Y'} {g : Y' ⟶ Y}
    (hU : IsPullback σ u' u g) {ρ : R' ⟶ R} {s' t' : R' ⟶ U'} (hs : s' ≫ σ = ρ ≫ s)
    (ht : t' ≫ σ = ρ ≫ t) (hst : s' ≫ u' = t' ≫ u')
    (hR : IsPullback ρ (s' ≫ u') (s ≫ u) g) : IsPullback s' t' u' u' := by
  have key : ∀ {W : C} (x y : W ⟶ U'), x ≫ u' = y ≫ u' → (x ≫ σ) ≫ u = (y ≫ σ) ≫ u :=
    fun x y h => by rw [Category.assoc, hU.w, ← Category.assoc, h, Category.assoc,
      ← hU.w, Category.assoc]
  refine IsPullback.of_isLimit' ⟨hst⟩ (PullbackCone.IsLimit.mk _
    (fun c => hR.lift (hk.lift (c.fst ≫ σ) (c.snd ≫ σ) (key _ _ c.condition)) (c.fst ≫ u')
      (by rw [hk.lift_fst_assoc, Category.assoc, hU.w, Category.assoc]))
    (fun c => ?_) (fun c => ?_) (fun c m h₁ h₂ => ?_))
  · apply hU.hom_ext
    · rw [Category.assoc, hs, hR.lift_fst_assoc, hk.lift_fst]
    · rw [Category.assoc, hR.lift_snd]
  · apply hU.hom_ext
    · rw [Category.assoc, ht, hR.lift_fst_assoc, hk.lift_snd]
    · rw [Category.assoc, ← hst, hR.lift_snd, c.condition]
  · apply hR.hom_ext
    · rw [hR.lift_fst]
      apply hk.hom_ext
      · rw [hk.lift_fst, Category.assoc, ← hs, ← Category.assoc]
        exact congrArg (· ≫ σ) h₁
      · rw [hk.lift_snd, Category.assoc, ← ht, ← Category.assoc]
        exact congrArg (· ≫ σ) h₂
    · rw [hR.lift_snd, ← Category.assoc]
      exact congrArg (· ≫ u') h₁

end CategoryTheory.IsPullback

end

module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# `R`-linearity of a total right derived functor

Mathlib carries `R`-linearity of a functor across a localization
(`CategoryTheory.Localization.functor_linear_iff`), but that asks for a
`CategoryTheory.Localization.Lifting`, that is for the comparison `L ⋙ G ≅ F` to be an
isomorphism. For a *derived* functor the comparison `α : F ⟶ L ⋙ RF` is an isomorphism only
when `F` already inverts `W` — for an exact functor, in the homological setting — so
`R`-linearity does not transport to `RF` that way. Mathlib's other route, through
`CategoryTheory.Functor.mapDerivedCategory`, is likewise available only for an exact functor,
and `Stacks.DerivedLinear.rightDerived_linear` is about the classical right derived functors
`CategoryTheory.Functor.rightDerived` of an additive functor between abelian categories, not
about a total right derived functor along a localization.

This file carries it across by the universal property of `RF` instead: the two natural
endomorphisms of `RF` given by `RF.map (r • 𝟙 -)` and by `r • 𝟙` agree after restriction along
`L`, hence agree, which is exactly `R`-linearity of `RF` by
`CategoryTheory.Functor.linear_iff`. No exactness and no resolution hypothesis is involved.

## Main results

* `CategoryTheory.Functor.linear_of_isRightDerivedFunctor` — a total right derived functor of an
  `R`-linear functor along an `R`-linear localization functor is `R`-linear.
-/

@[expose] public section

namespace CategoryTheory

/-- **The total right derived functor of an `R`-linear functor is `R`-linear.**

Let `L : C ⥤ D` be a localization functor for `W` which is itself `R`-linear, and let
`α : F ⟶ L ⋙ RF` exhibit `RF` as a right derived functor of an `R`-linear `F`. The two natural
endomorphisms `r • 𝟙` and `RF.map (r • 𝟙 -)` of `RF` become equal after restricting along `L`,
because `L` and `F` are `R`-linear and `α` is natural; so they are equal, which is
`R`-linearity of `RF`. -/
theorem Functor.linear_of_isRightDerivedFunctor (R : Type*) [Ring R]
    {C D H : Type*} [Category* C] [Category* D] [Category* H]
    [Preadditive C] [Preadditive D] [Preadditive H]
    [CategoryTheory.Linear R C] [CategoryTheory.Linear R D] [CategoryTheory.Linear R H]
    {L : C ⥤ D} (W : MorphismProperty C) [L.IsLocalization W] [Functor.Linear R L]
    {F : C ⥤ H} (RF : D ⥤ H) (α : F ⟶ L ⋙ RF) [RF.IsRightDerivedFunctor α W]
    [Functor.Linear R F] : Functor.Linear R RF := by
  rw [Functor.linear_iff]
  intro Y r
  let γ₁ : RF ⟶ RF :=
    { app Z := RF.map (r • 𝟙 Z)
      naturality Z Z' g := by
        rw [← RF.map_comp, ← RF.map_comp]
        congr 1
        simp [Linear.smul_comp, Linear.comp_smul] }
  let γ₂ : RF ⟶ RF :=
    { app Z := r • 𝟙 (RF.obj Z)
      naturality Z Z' g := by simp [Linear.smul_comp, Linear.comp_smul] }
  have hcomp : α ≫ Functor.whiskerLeft L γ₁ = α ≫ Functor.whiskerLeft L γ₂ := by
    ext Z
    have h₁ : RF.map (r • 𝟙 (L.obj Z)) = (L ⋙ RF).map (r • 𝟙 Z) := by
      rw [Functor.comp_map, L.map_smul, L.map_id]
    have h₂ : α.app Z ≫ (L ⋙ RF).map (r • 𝟙 Z) = r • α.app Z := by
      rw [← α.naturality (r • 𝟙 Z), F.map_smul, F.map_id, Linear.smul_comp, Category.id_comp]
    change α.app Z ≫ RF.map (r • 𝟙 (L.obj Z)) = α.app Z ≫ (r • 𝟙 (RF.obj (L.obj Z)))
    rw [h₁, h₂]
    simp
  exact NatTrans.congr_app (RF.rightDerived_ext α W RF γ₁ γ₂ hcomp) Y

end CategoryTheory

end

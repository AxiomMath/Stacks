module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Right derived functors of linear functors are linear

Let `L : C ⥤ D` be an `R`-linear localization functor and `F : C ⥤ H` an `R`-linear functor.
Every right derived functor `RF : D ⥤ H` of `F` along `L` is `R`-linear: the two natural
endomorphisms `RF(r • 𝟙)` and `r • 𝟙` of `RF` agree after composition with the unit
`F ⟶ L ⋙ RF`, because `L` and `F` are linear, and a natural transformation out of a right
derived functor is determined by that composite.

## Main results

* `CategoryTheory.Functor.IsRightDerivedFunctor.linear` — a right derived functor of an
  `R`-linear functor along an `R`-linear localization is `R`-linear.
-/

@[expose] public section

namespace CategoryTheory.Functor.IsRightDerivedFunctor

variable (R : Type*) [Ring R] {C D H : Type*} [Category* C] [Category* D] [Category* H]
  [Preadditive C] [Preadditive D] [Preadditive H] [CategoryTheory.Linear R C]
  [CategoryTheory.Linear R D] [CategoryTheory.Linear R H]
  {L : C ⥤ D} [L.Linear R] {F : C ⥤ H} [F.Linear R]
  (RF : D ⥤ H) (α : F ⟶ L ⋙ RF) (W : MorphismProperty C) [L.IsLocalization W]
  [RF.IsRightDerivedFunctor α W]

include α W in
/-- **A right derived functor of an `R`-linear functor is `R`-linear.** -/
theorem linear : Functor.Linear R RF := by
  rw [Functor.linear_iff]
  intro X r
  let γ₁ : RF ⟶ RF := Functor.whiskerRight (r • 𝟙 (𝟭 D)) RF
  let γ₂ : RF ⟶ RF := r • 𝟙 RF
  have h : γ₁ = γ₂ := by
    refine rightDerived_ext RF α W RF γ₁ γ₂ ?_
    ext Y
    have hL : r • 𝟙 (L.obj Y) = L.map (r • 𝟙 Y) := by rw [L.map_smul, L.map_id]
    have hF : F.map (r • 𝟙 Y) = r • 𝟙 (F.obj Y) := by rw [F.map_smul, F.map_id]
    have hnat := α.naturality (r • 𝟙 Y)
    simp only [Functor.comp_map] at hnat
    simp only [γ₁, γ₂, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      NatTrans.app_smul, NatTrans.id_app, Functor.id_obj, hL, ← hnat, hF,
      CategoryTheory.Linear.smul_comp, CategoryTheory.Linear.comp_smul, Category.id_comp,
      Category.comp_id]
    exact congrArg (r • ·) (Category.comp_id (α.app Y)).symm
  simpa [γ₁, γ₂] using congrArg (fun γ : RF ⟶ RF ↦ γ.app X) h

end CategoryTheory.Functor.IsRightDerivedFunctor

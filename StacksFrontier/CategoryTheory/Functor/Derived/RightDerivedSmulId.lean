module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# A right derived functor sends a scalar multiple of an identity to that multiple

Let `C`, `D`, `H` be `R`-linear categories, `L : C ⥤ D` an `R`-linear localization functor and
`RF : D ⥤ H` a right derived functor of an `R`-linear functor `F : C ⥤ H` along `L`. Then
`RF` sends `r • 𝟙 X` to `r • 𝟙 (RF X)` for every object `X` of `D` and every `r ∈ R`, although
`RF` is not assumed to be linear: both `X ↦ RF(r • 𝟙 X)` and `r • 𝟙 RF` are natural
transformations `RF ⟶ RF`, they agree after precomposition with the unit `F ⟶ L ⋙ RF` because
`F` and `L` are linear, and natural transformations out of a right derived functor are determined
by that precomposition.

For derived global sections `RΓ(X, -)` of a ringed space this says that multiplication by a
global function on a complex induces multiplication by it on `RΓ(X, -)` and on its cohomology.

## Main results

* `CategoryTheory.Functor.rightDerived_map_smul_id`: `RF.map (r • 𝟙 X) = r • 𝟙 (RF.obj X)`.
-/

@[expose] public section

namespace CategoryTheory.Functor

variable {C D H : Type*} [Category* C] [Category* D] [Category* H]
  [Preadditive C] [Preadditive D] [Preadditive H] {R : Type*} [Semiring R]
  [CategoryTheory.Linear R C] [CategoryTheory.Linear R D] [CategoryTheory.Linear R H]

/-- **A right derived functor sends `r • 𝟙` to `r • 𝟙`**, for a right derived functor of a
linear functor along a linear localization functor. -/
theorem rightDerived_map_smul_id (RF : D ⥤ H) {F : C ⥤ H} {L : C ⥤ D} (α : F ⟶ L ⋙ RF)
    (W : MorphismProperty C) [L.IsLocalization W] [RF.IsRightDerivedFunctor α W]
    [F.Linear R] [L.Linear R] (r : R) (X : D) :
    RF.map (r • 𝟙 X) = r • 𝟙 (RF.obj X) := by
  let γ : RF ⟶ RF :=
    { app := fun Y => RF.map (r • 𝟙 Y)
      naturality := fun Y Z g => by
        rw [← RF.map_comp, ← RF.map_comp, CategoryTheory.Linear.comp_smul,
          CategoryTheory.Linear.smul_comp, Category.comp_id, Category.id_comp] }
  have h : γ = r • 𝟙 RF := by
    refine RF.rightDerived_ext α W RF γ (r • 𝟙 RF) ?_
    ext Y
    show α.app Y ≫ RF.map (r • 𝟙 (L.obj Y)) = α.app Y ≫ (r • 𝟙 (RF.obj (L.obj Y)))
    calc α.app Y ≫ RF.map (r • 𝟙 (L.obj Y)) = α.app Y ≫ (L ⋙ RF).map (r • 𝟙 Y) := by
          rw [← L.map_id, ← L.map_smul]
          rfl
      _ = F.map (r • 𝟙 Y) ≫ α.app Y := (α.naturality _).symm
      _ = α.app Y ≫ (r • 𝟙 (RF.obj (L.obj Y))) := by
          rw [F.map_smul, F.map_id, CategoryTheory.Linear.smul_comp,
            CategoryTheory.Linear.comp_smul, Category.id_comp]
          exact congrArg (r • ·) (Category.comp_id (α.app Y)).symm
  exact NatTrans.congr_app h X

end CategoryTheory.Functor

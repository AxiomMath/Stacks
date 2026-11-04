module

public import Mathlib.CategoryTheory.GuitartExact.KanExtension

/-!
# The base change of a right Kan extension along a `2`-square, read at an object

Let `w : CategoryTheory.TwoSquare T L R B` be a square of functors

```
  C₁ --T--> C₂
  |          |
  L          R
  v          v
  C₃ --B--> C₄
```

commuting up to a `2`-cell `T ⋙ R ⟶ L ⋙ B`, and `CategoryTheory.TwoSquare.ranBaseChange` the
induced comparison

`Ran_B(-) ∘ R ⟶ Ran_T((-) ∘ L)`

of functors `(C₃ ⥤ D) ⥤ (C₂ ⥤ D)`. This file computes the comparison, with no exactness
hypothesis on the square: after whiskering with `T` and the counit of `Ran_T`, and at an object
`X` of `C₂` followed by a projection of the limit computing `Ran_T((-) ∘ L)` at `X`.

## Main results

* `CategoryTheory.TwoSquare.ranBaseChange_app_app_ranCounit`: the comparison at `T Y` followed
  by the counit of `Ran_T` is the `2`-cell of the square at `Y` followed by the counit of `Ran_B`.
* `CategoryTheory.TwoSquare.ranBaseChange_app_app_comp_π`: the comparison at an object `X` of
  `C₂`, followed by the projection at a structured arrow `X ⟶ T Y`, is the map of `Ran_B` along
  `R X ⟶ R (T Y) ⟶ B (L Y)` followed by the counit of `Ran_B`.
* `CategoryTheory.Functor.ran_obj_obj_hom_ext`: two maps into a pointwise right Kan extension
  at an object agree as soon as they agree after restricting along each structured arrow over
  that object and taking the counit.
-/

@[expose] public section

namespace CategoryTheory

open Category Functor Limits

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄} {D : Type u₅}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
  [Category.{v₅} D]

namespace Functor

/-- Two maps into a pointwise right Kan extension at an object `X` agree as soon as they agree
after restricting along every structured arrow over `X` and taking the counit. -/
theorem ran_obj_obj_hom_ext (T : C₁ ⥤ C₂) [∀ F : C₁ ⥤ D, T.HasRightKanExtension F]
    (F : C₁ ⥤ D) [T.HasPointwiseRightKanExtension F] (X : C₂) {Z : D}
    {f g : Z ⟶ (T.ran.obj F).obj X}
    (h : ∀ e : StructuredArrow X T,
      f ≫ (T.ran.obj F).map e.hom ≫ (T.ranCounit.app F).app e.right =
        g ≫ (T.ran.obj F).map e.hom ≫ (T.ranCounit.app F).app e.right) :
    f = g := by
  rw [← cancel_mono (T.ranObjObjIsoLimit F X).hom]
  refine limit.hom_ext fun e ↦ ?_
  rw [assoc, assoc, ranObjObjIsoLimit_hom_π]
  exact h e

end Functor

namespace TwoSquare

variable {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄} (w : TwoSquare T L R B)
  [∀ F : C₁ ⥤ D, T.HasRightKanExtension F] [∀ F : C₃ ⥤ D, B.HasRightKanExtension F]

/-- The base change of a right Kan extension along a `2`-square at `T Y`, followed by the counit
of `Ran_T` at `Y`, is the `2`-cell of the square at `Y` followed by the counit of `Ran_B`. -/
theorem ranBaseChange_app_app_ranCounit (F : C₃ ⥤ D) (Y : C₁) :
    (w.ranBaseChange.app F).app (T.obj Y) ≫ (T.ranCounit.app (L ⋙ F)).app Y =
      (B.ran.obj F).map (w.natTrans.app Y) ≫ (B.ranCounit.app F).app (L.obj Y) := by
  have h : ((T.ranAdjunction D).homEquiv _ _).symm (w.ranBaseChange.app F) =
      ((Functor.RightExtension.mk (B.ran.obj F) (B.ranCounit.app F)).compTwoSquare w).hom := by
    rw [ranBaseChange_app, Equiv.symm_apply_apply]
  rw [Adjunction.homEquiv_counit, Functor.ranAdjunction_counit] at h
  refine (NatTrans.congr_app h Y).trans ?_
  simp

/-- The base change at an object `X` of `C₂`, followed by the projection at a structured arrow
`d : X ⟶ T Y` of the limit computing `Ran_T` at `X`, is the map of `Ran_B` along the composite
`R X ⟶ R (T Y) ⟶ B (L Y)` followed by the counit of `Ran_B` at `L Y`. -/
theorem ranBaseChange_app_app_comp_π (F : C₃ ⥤ D)
    [T.HasPointwiseRightKanExtension (L ⋙ F)] (X : C₂) (d : StructuredArrow X T) :
    (w.ranBaseChange.app F).app X ≫
        (T.ranObjObjIsoLimit (L ⋙ F) X).hom ≫ limit.π _ d =
      (B.ran.obj F).map (R.map d.hom ≫ w.natTrans.app d.right) ≫
        (B.ranCounit.app F).app (L.obj d.right) := by
  have hn : (w.ranBaseChange.app F).app X ≫ (T.ran.obj (L ⋙ F)).map d.hom =
      (B.ran.obj F).map (R.map d.hom) ≫ (w.ranBaseChange.app F).app (T.obj d.right) :=
    ((w.ranBaseChange.app F).naturality d.hom).symm
  rw [Functor.ranObjObjIsoLimit_hom_π, ← Category.assoc, hn, Category.assoc,
    ranBaseChange_app_app_ranCounit]
  simp

end TwoSquare

end CategoryTheory

end

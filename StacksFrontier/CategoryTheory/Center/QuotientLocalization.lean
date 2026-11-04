module

public import Mathlib.CategoryTheory.Center.Localization
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Quotient.Preadditive

/-!
# The center of a quotient category, and centers under a left derived functor

An element `z` of the center of a category `C` (an endomorphism of the identity functor)
descends to the center of a quotient category of `C`, and, through
`CategoryTheory.CatCenter.localization`, to the center of a localization of `C`.

If a total left derived functor `LF : D ⥤ H` of `F : C ⥤ H` along a localization `L : C ⥤ D`
is given, and `F` carries `z` to an element `w` of the center of `H` (that is
`F.map (z.app X) = w.app (F.obj X)` for all `X`), then `LF` carries the localization of `z` to
`w` as well: both are natural endomorphisms of `LF`, and they agree after the counit.

## Main definitions

* `CategoryTheory.CatCenter.quotient`: the descent of an element of the center to a quotient
  category.
* `CategoryTheory.CatCenter.quotientRingHom`: the descent as a ring morphism.

## Main results

* `CategoryTheory.CatCenter.map_localization_app_of_isLeftDerivedFunctor`: a left derived functor
  carries the localization of an element of the center to the element its underived functor
  carries it to.
-/

@[expose] public section

namespace CategoryTheory.CatCenter

universe v₁ v₂ v₃ u₁ u₂ u₃

section Quotient

variable {C : Type u₁} [Category.{v₁} C] (r : HomRel C) [Congruence r]

/-- An element of the center of `C` induces an element of the center of the quotient category
`C/r`: its component at the class of `X` is the class of its component at `X`. -/
def quotient (z : CatCenter C) : CatCenter (CategoryTheory.Quotient r) where
  app X := (Quotient.functor r).map (z.app X.as)
  naturality := by
    rintro ⟨X⟩ ⟨Y⟩ f
    obtain ⟨f, rfl⟩ := (Quotient.functor r).map_surjective f
    simpa only [Functor.id_obj, Functor.id_map, Functor.map_comp] using
      congrArg (Quotient.functor r).map (z.naturality f)

omit [Congruence r] in
/-- The component of `CategoryTheory.CatCenter.quotient r z` at the class of `X` is the class of
the component of `z` at `X`. -/
@[simp]
lemma quotient_app (z : CatCenter C) (X : C) :
    (z.quotient r).app ((Quotient.functor r).obj X) = (Quotient.functor r).map (z.app X) :=
  rfl

variable [Preadditive C] [Preadditive (CategoryTheory.Quotient r)]
  [(Quotient.functor r).Additive]

/-- The descent of elements of the center to a quotient category, as a morphism of rings. -/
def quotientRingHom : CatCenter C →+* CatCenter (CategoryTheory.Quotient r) where
  toFun := quotient r
  map_one' := ext _ _ fun X => (Quotient.functor r).map_id X.as
  map_mul' z w := ext _ _ fun X => (Quotient.functor r).map_comp (w.app X.as) (z.app X.as)
  map_zero' := ext _ _ fun X => (Quotient.functor r).map_zero X.as X.as
  map_add' z w := ext _ _ fun X => (Quotient.functor r).map_add (f := z.app X.as) (g := w.app X.as)

omit [Congruence r] in
/-- The underlying function of `CategoryTheory.CatCenter.quotientRingHom r` is
`CategoryTheory.CatCenter.quotient r`. -/
@[simp]
lemma quotientRingHom_apply (z : CatCenter C) : quotientRingHom r z = z.quotient r := rfl

end Quotient

section Derived

variable {C : Type u₁} {D : Type u₂} {H : Type u₃} [Category.{v₁} C] [Category.{v₂} D]
  [Category.{v₃} H] (LF : D ⥤ H) {F : C ⥤ H} {L : C ⥤ D} (α : L ⋙ LF ⟶ F)
  (W : MorphismProperty C) [L.IsLocalization W] [LF.IsLeftDerivedFunctor α W]

include α

/-- **A left derived functor respects the center.** If `F` carries `z` (in the center of `C`) to
`w` (in the center of `H`), then its total left derived functor `LF` carries the localization of
`z` to `w`. -/
theorem map_localization_app_of_isLeftDerivedFunctor (z : CatCenter C) (w : CatCenter H)
    (hF : ∀ X : C, F.map (z.app X) = w.app (F.obj X)) (Y : D) :
    LF.map ((z.localization L W).app Y) = w.app (LF.obj Y) := by
  let γ₁ : LF ⟶ LF :=
    { app Y := LF.map ((z.localization L W).app Y)
      naturality Y Y' f := by
        simpa only [Functor.id_obj, Functor.id_map, Functor.map_comp] using
          congrArg LF.map ((z.localization L W).naturality f) }
  let γ₂ : LF ⟶ LF :=
    { app Y := w.app (LF.obj Y)
      naturality Y Y' f := w.naturality (LF.map f) }
  have hγ : γ₁ = γ₂ := by
    refine LF.leftDerived_ext α W LF γ₁ γ₂ (NatTrans.ext (funext fun X => ?_))
    change LF.map ((z.localization L W).app (L.obj X)) ≫ α.app X =
      w.app (LF.obj (L.obj X)) ≫ α.app X
    rw [localization_app]
    have h1 := α.naturality (z.app X)
    have h2 := w.naturality (α.app X)
    simp only [Functor.comp_obj, Functor.comp_map] at h1 h2
    rw [h1, hF, ← h2]
  exact NatTrans.congr_app hγ Y

end Derived

end CategoryTheory.CatCenter

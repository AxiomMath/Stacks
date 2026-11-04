module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite

/-!
# A property of the diagonal of a presheaf on a big fppf site

If the fibre product of any two representable presheaves over a presheaf has a representable
morphism to their product with a given property, then the diagonal of the presheaf has that
property.

## Main results

* `AlgebraicGeometry.Space.presheaf_diagonal` is the representable-property criterion for the
  diagonal of a presheaf.

## Implementation notes

The hypothesis specifies a representing object for each pairwise fibre product, and tests the
property only on its canonical morphism to the product over the base. The conclusion uses
`CategoryTheory.MorphismProperty.presheaf`, so it both asserts representability of the
diagonal and tests the property after every representable base change; both come out of the
same representing object, pulled back along the diagonal of the base.

## References

* [Stacks Project, Tag 0CB7](https://stacks.math.columbia.edu/tag/0CB7)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-- If `yoneda W` is the fibre product of the two components of `g : yoneda U ⟶ F ⨯ F` via
`f : W ⟶ U ⨯ U`, then `yoneda` carries the pullback of `f` along `diag U` to the pullback of
`diag F` along `g`. -/
theorem isPullback_yoneda_pullback_diag.{u₁, v₁} {C : Type u₁} [Category.{v₁} C]
    {F : Cᵒᵖ ⥤ Type v₁} {U W : C} [HasBinaryProduct U U] (g : yoneda.obj U ⟶ F ⨯ F) (f : W ⟶ U ⨯ U)
    [HasPullback f (Limits.diag U)]
    (hW : IsPullback (yoneda.map (f ≫ prod.fst)) (yoneda.map (f ≫ prod.snd))
      (g ≫ prod.fst) (g ≫ prod.snd)) :
    IsPullback (yoneda.map (pullback.snd f (Limits.diag U)) ≫ g ≫ prod.fst)
      (yoneda.map (pullback.snd f (Limits.diag U))) (diag F) g := by
  have hX := (IsPullback.of_hasPullback f (diag U)).map yoneda
  have hq : ∀ k : U ⨯ U ⟶ U, Limits.diag U ≫ k = 𝟙 U →
      yoneda.map (pullback.fst f (diag U)) ≫ yoneda.map (f ≫ k) =
        yoneda.map (pullback.snd f (diag U)) := fun k hk => by
    rw [← Functor.map_comp, pullback.condition_assoc, hk, Category.comp_id]
  have hq₁ := hq prod.fst (by simp)
  have hq₂ := hq prod.snd (by simp)
  have hr : yoneda.map (pullback.snd f (diag U)) ≫ g ≫ prod.fst =
      yoneda.map (pullback.snd f (diag U)) ≫ g ≫ prod.snd := by
    rw [← reassoc_of% hq₁, ← reassoc_of% hq₂]
    exact _ ≫= hW.w
  refine IsPullback.mk' (by apply Limits.prod.hom_ext <;> simp [hr]) ?_ ?_
  · intro Z k l _ hk₂
    exact hX.hom_ext (hW.hom_ext (by simp only [Category.assoc, hq₁, hk₂])
      (by simp only [Category.assoc, hq₂, hk₂])) hk₂
  · intro Z z t hzt
    have hα : z = t ≫ g ≫ prod.fst := by simpa using hzt =≫ prod.fst
    have hβ : z = t ≫ g ≫ prod.snd := by simpa using hzt =≫ prod.snd
    obtain ⟨w, hw₁, hw₂⟩ := hW.exists_lift t t (hα.symm.trans hβ)
    have hw : w ≫ yoneda.map f = t ≫ yoneda.map (Limits.diag U) := by
      ext V x
      show w.app V x ≫ f = t.app V x ≫ Limits.diag U
      apply Limits.prod.hom_ext
      · simpa using congrArg (fun φ => φ x) (congr_app hw₁ V)
      · simpa using congrArg (fun φ => φ x) (congr_app hw₂ V)
    exact ⟨hX.lift w t hw, by simp [hα], hX.lift_snd w t hw⟩

/-- A property of all pairwise fibre products of representables over a presheaf passes to its
diagonal. -/
@[stacks 0CB7]
theorem presheaf_diagonal (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (h : ∀ (U V : BigFppfOver B S hS) (a : F.obj (op U)) (b : F.obj (op V)),
      ∃ (W : BigFppfOver B S hS)
        (i : yoneda.obj W ≅ pullback (yonedaEquiv.symm a) (yonedaEquiv.symm b))
        (f : W ⟶ U ⨯ V),
        yoneda.map (f ≫ prod.fst) =
          i.hom ≫ pullback.fst (yonedaEquiv.symm a) (yonedaEquiv.symm b) ∧
        yoneda.map (f ≫ prod.snd) =
          i.hom ≫ pullback.snd (yonedaEquiv.symm a) (yonedaEquiv.symm b) ∧
        P ((BigFppfOver.toScheme B S hS).map f)) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (diag F) := by
  let T := BigFppfOver.toScheme B S hS
  apply MorphismProperty.relative.of_exists (F := yoneda) (P := P.inverseImage T)
  intro U g
  let a := yonedaEquiv (g ≫ Limits.prod.fst)
  let b := yonedaEquiv (g ≫ Limits.prod.snd)
  have hα : yonedaEquiv.symm a = g ≫ Limits.prod.fst := by simp [a]
  have hβ : yonedaEquiv.symm b = g ≫ Limits.prod.snd := by simp [b]
  obtain ⟨W, i, f, hf₁, hf₂, hP⟩ := h U U a b
  refine ⟨_, _, _, isPullback_yoneda_pullback_diag g f ?_,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := P)
      ((IsPullback.of_hasPullback f (Limits.diag U)).map T) hP⟩
  rw [hf₁, hf₂, ← hα, ← hβ]
  exact IsPullback.of_iso_pullback
    ⟨by rw [Category.assoc, Category.assoc, pullback.condition]⟩ i rfl rfl

end AlgebraicGeometry.Space

end

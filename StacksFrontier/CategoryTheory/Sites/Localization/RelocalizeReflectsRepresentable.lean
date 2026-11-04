module

public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRepresentable

/-!
# Relocalization reflects representable presheaves

Let `C` be a category and let `f : V ⟶ U` be a morphism of `C`.  The presheaf level lower shriek
of the relocalization functor `j = Over.map f : C/V ⥤ C/U` of Stacks 03EH is
`CategoryTheory.OverShriek.relocalizePresheafFunctor f`, written `Λ` here.  It carries the
representable presheaf `h_Z` to `h_{j Z}` (`CategoryTheory.OverShriek.relocalizeYonedaIso`), and
`j Z` has the same underlying object of `C` as `Z`.

This file proves the converse: if `Λ G` is represented by an object `T` of `C/U`, then `G` is
represented by an object `T'` of `C/V` with the same underlying object of `C`.

## Main results

* `CategoryTheory.OverShriek.reflectsIsomorphisms_relocalizePresheafFunctor`: `Λ` reflects
  isomorphisms.
* `CategoryTheory.OverShriek.exists_left_eq_nonempty_iso_yoneda`: `Λ` reflects representable
  presheaves, with the same underlying object.

## References

* [Stacks Project, Tag 03EH](https://stacks.math.columbia.edu/tag/03EH)
* [Stacks Project, Tag 03I4](https://stacks.math.columbia.edu/tag/03I4)
-/

@[expose] public section

open CategoryTheory Opposite

universe v u

namespace CategoryTheory.OverShriek

variable {C : Type u} [Category.{v} C] {U V : C} (f : V ⟶ U)

/-- The presheaf level lower shriek `Λ = relocalizePresheafFunctor f` of the relocalization
functor reflects isomorphisms. -/
instance reflectsIsomorphisms_relocalizePresheafFunctor :
    (relocalizePresheafFunctor f).ReflectsIsomorphisms := by
  have : (Over.map (yoneda.map f) ⋙ Over.forget (yoneda.obj U)).ReflectsIsomorphisms := by
    rw [Over.mapForget_eq]
    infer_instance
  have : (Over.map (yoneda.map f)).ReflectsIsomorphisms :=
    reflectsIsomorphisms_of_comp _ (Over.forget (yoneda.obj U))
  change (presheafFunctorToOver ⋙ Over.map (yoneda.map f) ⋙
    fiberFunctor (𝟙 (yoneda.obj U))).ReflectsIsomorphisms
  infer_instance

/-- **`Λ` reflects representable presheaves, with the same underlying object.**  If `Λ G` is
represented by `T : C/U`, then `G` is represented by an object `T'` of `C/V` with
`T'.left = T.left`. -/
theorem exists_left_eq_nonempty_iso_yoneda {G : (Over V)ᵒᵖ ⥤ Type v} {T : Over U}
    (e : (relocalizePresheafFunctor f).obj G ≅ yoneda.obj T) :
    ∃ T' : Over V, T'.left = T.left ∧ Nonempty (G ≅ yoneda.obj T') := by
  obtain ⟨ψ, h, σ, hσ⟩ := exists_eq_relocalizeYonedaFactorIso_comp f e.inv
  have hΛ : (relocalizePresheafFunctor f).map σ =
      (relocalizeYonedaFactorIso f h).inv ≫ e.inv := by
    rw [hσ, Iso.inv_hom_id_assoc]
  have : IsIso ((relocalizePresheafFunctor f).map σ) := by
    rw [hΛ]
    infer_instance
  have : IsIso σ := isIso_of_reflects_iso σ (relocalizePresheafFunctor f)
  exact ⟨Over.mk ψ, rfl, ⟨(asIso σ).symm⟩⟩

end CategoryTheory.OverShriek

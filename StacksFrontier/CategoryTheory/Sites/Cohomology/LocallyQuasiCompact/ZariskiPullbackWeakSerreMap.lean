module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiPullbackWeakSerre

/-!
# The image of a weak Serre class under a fully faithful exact left adjoint

This file continues the module
`StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiPullbackWeakSerre`,
generalizing `CategoryTheory.ObjectProperty.isWeakSerreClass_map_top` from the whole category to
a weak Serre class of it.

## Main results

* `CategoryTheory.ObjectProperty.isWeakSerreClass_map` — the image of a weak Serre class under a
  fully faithful exact left adjoint with an exact right adjoint is a weak Serre class.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace CategoryTheory.ObjectProperty

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- A five term sequence is exact as a `CategoryTheory.ComposableArrows` as soon as it is exact
at each of its three inner objects. (The private lemma of the same name in
`StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiPullbackWeakSerre`.) -/
private theorem exact_mk₄ {X₀ X₁ X₂ X₃ X₄ : C}
    {f₀ : X₀ ⟶ X₁} {f₁ : X₁ ⟶ X₂} {f₂ : X₂ ⟶ X₃} {f₃ : X₃ ⟶ X₄}
    {w₀ : f₀ ≫ f₁ = 0} {w₁ : f₁ ≫ f₂ = 0} {w₂ : f₂ ≫ f₃ = 0}
    (e₀ : (ShortComplex.mk f₀ f₁ w₀).Exact) (e₁ : (ShortComplex.mk f₁ f₂ w₁).Exact)
    (e₂ : (ShortComplex.mk f₂ f₃ w₂).Exact) :
    (ComposableArrows.mk₄ f₀ f₁ f₂ f₃).Exact :=
  ComposableArrows.exact_of_δ₀ (ComposableArrows.exact₂_mk _ w₀ e₀)
    (ComposableArrows.exact_of_δ₀ (ComposableArrows.exact₂_mk _ w₁ e₁)
      (ComposableArrows.exact₂_mk _ w₂ e₂))

omit [Abelian C] [Abelian D] in
/-- An object lies in the image of `P` under a fully faithful left adjoint exactly when the right
adjoint carries it into `P` and the counit is invertible there. -/
theorem prop_map_iff_of_adjunction {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [L.Full] [L.Faithful]
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] (Y : D) :
    (P.map L) Y ↔ P (R.obj Y) ∧ IsIso (adj.counit.app Y) := by
  constructor
  · rintro ⟨A, hA, ⟨e⟩⟩
    exact ⟨P.prop_of_iso (asIso (adj.unit.app A) ≪≫ R.mapIso e) hA,
      adj.isIso_counit_app_iff_mem_essImage.2 ⟨A, ⟨e⟩⟩⟩
  · rintro ⟨hR, hc⟩
    exact ⟨R.obj Y, hR, ⟨asIso (adj.counit.app Y)⟩⟩

omit [Abelian C] [Abelian D] in
/-- The counit of an adjunction is invertible at an object exactly when that object lies in the
image of the whole category under the left adjoint. -/
theorem isIso_counit_app_iff_prop_top_map {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [L.Full] [L.Faithful] (Y : D) :
    IsIso (adj.counit.app Y) ↔ ((⊤ : ObjectProperty C).map L) Y := by
  rw [prop_map_iff, adj.isIso_counit_app_iff_mem_essImage]
  exact ⟨fun ⟨A, h⟩ => ⟨A, trivial, h⟩, fun ⟨A, _, h⟩ => ⟨A, h⟩⟩

/-- **The image of a weak Serre class under a fully faithful exact left adjoint with an exact
right adjoint is a weak Serre class.** This generalizes `isWeakSerreClass_map_top` from the whole
category to a weak Serre class `P` of it.

An object `Y` lies in the image exactly when `R Y` lies in `P` and the counit is invertible at `Y`.
For a five term exact sequence whose four outer terms lie in the image, the first condition holds
at the middle term because `R` carries the sequence to a five term exact sequence of `C` whose
four outer terms lie in `P`, and the second holds by the five lemma, exactly as in
`isWeakSerreClass_map_top`. -/
theorem isWeakSerreClass_map {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [L.Full] [L.Faithful] [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (P : ObjectProperty C) [P.IsWeakSerreClass] :
    (P.map L).IsWeakSerreClass := by
  have := isWeakSerreClass_map_top adj
  refine (isWeakSerreClass_iff_prop_obj₂_of_exact _).2 ⟨?_, ?_⟩
  · obtain ⟨X, hX⟩ := P.exists_prop_of_isWeakSerreClass
    exact ⟨L.obj X, X, hX, ⟨Iso.refl _⟩⟩
  intro S hS h₀ h₁ h₃ h₄
  simp only [prop_map_iff_of_adjunction adj P, isIso_counit_app_iff_prop_top_map adj]
    at h₀ h₁ h₃ h₄ ⊢
  exact ⟨P.prop_obj₂_of_exact (ComposableArrows.mk₄ (R.map (S.map' 0 1)) (R.map (S.map' 1 2))
      (R.map (S.map' 2 3)) (R.map (S.map' 3 4)))
      (exact_mk₄ ((hS.exact' 0 1 2).map R) ((hS.exact' 1 2 3).map R) ((hS.exact' 2 3 4).map R))
      h₀.1 h₁.1 h₃.1 h₄.1,
    ((⊤ : ObjectProperty C).map L).prop_obj₂_of_exact S hS h₀.2 h₁.2 h₃.2 h₄.2⟩

end CategoryTheory.ObjectProperty

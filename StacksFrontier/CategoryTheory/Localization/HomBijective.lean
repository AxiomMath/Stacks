module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions

/-!
# Bijectivity of the maps a localization functor induces on Hom types

A localization functor `L : A ⥤ B` at a class `W` admitting a right calculus of fractions
induces a bijection on a Hom type as soon as every `W`-morphism into the source can be
refined to one along which precomposition is bijective. The two auxiliary statements say
when precomposition itself is bijective: along a morphism that `L` inverts, and across an
adjunction.

## Main results

* `Stacks.Localization.localization_map_bijective_of_refinements`
* `Stacks.Localization.precomp_bijective_of_localization`
* `Stacks.Localization.adjunction_precomp_bijective`
-/

@[expose] public section

open CategoryTheory

namespace Stacks.Localization

/-- A localization functor at a class with a right calculus of fractions is bijective on
`X ⟶ Y` once every `W`-morphism `s` into `X` admits a `W`-refinement `t` along which
precomposition with `t ≫ s` is bijective. -/
lemma localization_map_bijective_of_refinements
    {A B : Type*} [Category A] [Category B]
    (W : MorphismProperty A) [W.HasRightCalculusOfFractions]
    (L : A ⥤ B) [L.IsLocalization W] (X Y : A)
    (h : ∀ (Z : A) (s : Z ⟶ X), W s →
      ∃ (Z' : A) (t : Z' ⟶ Z), W t ∧
        Function.Bijective (fun a : X ⟶ Y => (t ≫ s) ≫ a)) :
    Function.Bijective (L.map : (X ⟶ Y) → (L.obj X ⟶ L.obj Y)) := by
  constructor
  · intro a b hab
    obtain ⟨Z, s, hs, hsab⟩ := (W.map_eq_iff_precomp L a b).mp hab
    obtain ⟨Z', t, ht, hb⟩ := h Z s hs
    apply hb.injective
    simpa only [Category.assoc] using congrArg (fun k => t ≫ k) hsab
  · intro f
    obtain ⟨q, rfl⟩ := Localization.exists_rightFraction L W f
    obtain ⟨Z', t, ht, hb⟩ := h _ q.s q.hs
    obtain ⟨a, ha⟩ := hb.surjective (t ≫ q.f)
    refine ⟨a, ?_⟩
    have : IsIso (L.map t) := Localization.inverts L W t ht
    apply (cancel_epi (L.map t ≫ L.map q.s)).mp
    simp only [Category.assoc]
    rw [q.map_s_comp_map]
    simp only [← L.map_comp]
    exact congrArg L.map (by simpa only [Category.assoc] using ha)

/-- Precomposition with `s : X ⟶ Y` is bijective on morphisms to `Z` when a functor `L`
inverting `s` is bijective on both `X ⟶ Z` and `Y ⟶ Z`. -/
lemma precomp_bijective_of_localization
    {A B : Type*} [Category A] [Category B] (L : A ⥤ B)
    {X Y Z : A} (s : X ⟶ Y) [IsIso (L.map s)]
    (hX : Function.Bijective (L.map : (X ⟶ Z) → _))
    (hY : Function.Bijective (L.map : (Y ⟶ Z) → _)) :
    Function.Bijective (fun a : Y ⟶ Z => s ≫ a) := by
  constructor
  · intro a b hab
    apply hY.injective
    apply (cancel_epi (L.map s)).mp
    simpa only [← L.map_comp] using congrArg L.map hab
  · intro b
    obtain ⟨a, ha⟩ := hY.surjective (inv (L.map s) ≫ L.map b)
    refine ⟨a, hX.injective ?_⟩
    simp only [L.map_comp, ha, IsIso.hom_inv_id_assoc]

/-- Across an adjunction `F ⊣ G`, precomposition with `s` on morphisms to `G.obj I` is
bijective as soon as precomposition with `F.map s` on morphisms to `I` is. -/
lemma adjunction_precomp_bijective
    {A B : Type*} [Category A] [Category B] {F : A ⥤ B} {G : B ⥤ A}
    (adj : F ⊣ G) {X Y : A} (s : X ⟶ Y) (I : B)
    (h : Function.Bijective (fun a : F.obj Y ⟶ I => F.map s ≫ a)) :
    Function.Bijective (fun a : Y ⟶ G.obj I => s ≫ a) := by
  constructor
  · intro a b hab
    apply (adj.homEquiv Y I).symm.injective
    apply h.injective
    simpa only [← adj.homEquiv_naturality_left_symm] using
      congrArg (adj.homEquiv X I).symm hab
  · intro b
    obtain ⟨a, ha⟩ := h.surjective ((adj.homEquiv X I).symm b)
    refine ⟨adj.homEquiv Y I a, ?_⟩
    simpa only [adj.homEquiv_naturality_left, Equiv.apply_symm_apply] using
      congrArg (adj.homEquiv X I) ha

end Stacks.Localization

end

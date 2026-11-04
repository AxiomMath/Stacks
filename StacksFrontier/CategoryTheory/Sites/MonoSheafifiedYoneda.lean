module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.CategoryTheory.Sites.Density
import StacksCore.Tactic.StacksAttribute

/-! # Monomorphisms of sheafified representables

A morphism `g : X₁ ⟶ X₂` of a site induces a morphism `h_g^# : h_{X₁}^# ⟶ h_{X₂}^#` of
sheafified representables. If it is a monomorphism, as Stacks 0EVY assumes, then for any two
morphisms `a, b : Y ⟶ X₁` with `a ≫ g = b ≫ g`, the sieve of morphisms equalizing `a` and `b` is
a covering sieve: `yoneda.map g` is locally injective
(`CategoryTheory.Presheaf.IsLocallyInjective`).

## Main results

* `CategoryTheory.Sheaf.injective_hom_app_of_mono`: a monomorphism of sheaves of sets is
  injective on sections.
* `CategoryTheory.Sheaf.isLocallyInjective_yoneda_map`: local injectivity descends from the
  universe-raising Yoneda embedding to the Yoneda embedding.
* `CategoryTheory.Sheaf.isLocallyInjective_yoneda_map_of_mono`: the hypothesis of Stacks 0EVY
  in its elementary form.

## Implementation notes

The conclusion is stated for `yoneda` rather than `uliftYoneda`, so that it does not involve
the sheaf universe `max u v`.

## References

* [Stacks Project, Tag 0EVY](https://stacks.math.columbia.edu/tag/0EVY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf

universe u v t

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- A monomorphism of sheaves of sets is injective on sections: by Yoneda's lemma for sheaves
a section of `F` over `X` is a morphism `h_X^# ⟶ F`, and postcomposition with a monomorphism
is injective. -/
lemma injective_hom_app_of_mono [HasWeakSheafify J (Type max u v)]
    {F₁ F₂ : Sheaf J (Type max u v)} (φ : F₁ ⟶ F₂) [Mono φ] (X : Cᵒᵖ) :
    Function.Injective (φ.hom.app X) := by
  intro x y hxy
  have key : (sectionEquiv J (X := X.unop) (F := F₁)).symm x ≫ φ =
      (sectionEquiv J (X := X.unop) (F := F₁)).symm y ≫ φ := by
    apply (sectionEquiv J (X := X.unop) (F := F₂)).injective
    rwa [sectionEquiv_comp, sectionEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact (sectionEquiv J (X := X.unop) (F := F₁)).symm.injective ((cancel_mono φ).1 key)

/-- Local injectivity descends from the universe-raising Yoneda embedding to the Yoneda
embedding: the two equalizer sieves of a pair of morphisms of the site agree, because `ULift.up`
is injective. -/
lemma isLocallyInjective_yoneda_map {X₁ X₂ : C} (g : X₁ ⟶ X₂)
    (h : Presheaf.IsLocallyInjective J (uliftYoneda.{t}.map g)) :
    Presheaf.IsLocallyInjective J (yoneda.map g) := by
  refine ⟨fun {Y} a b hab ↦ ?_⟩
  refine J.superset_covering (fun Z f hf ↦ ?_)
    (h.equalizerSieve_mem (ULift.up a) (ULift.up b) (congrArg ULift.up hab))
  exact congrArg ULift.down hf

/-- **The monomorphism hypothesis of Stacks 0EVY in elementary form.** If `h_g^#` is a
monomorphism of sheafified representables, then precomposition with `g` is locally injective
on the representable presheaves: whenever `a ≫ g = b ≫ g`, the morphisms equalizing `a` and
`b` form a covering sieve. -/
lemma isLocallyInjective_yoneda_map_of_mono [HasWeakSheafify J (Type max u v)]
    {X₁ X₂ : C} (g : X₁ ⟶ X₂) (hg : Mono ((sheafifiedYoneda J).map g)) :
    Presheaf.IsLocallyInjective J (yoneda.map g) := by
  have h1 : Presheaf.IsLocallyInjective J
      ((sheafToPresheaf J (Type max u v)).map ((sheafifiedYoneda J).map g)) :=
    Presheaf.isLocallyInjective_of_injective _ _
      (fun X ↦ injective_hom_app_of_mono J ((sheafifiedYoneda J).map g) X)
  exact isLocallyInjective_yoneda_map.{u, v, u} J g
    ((Presheaf.isLocallyInjective_presheafToSheaf_map_iff _ _).1 h1)

end CategoryTheory.Sheaf

end

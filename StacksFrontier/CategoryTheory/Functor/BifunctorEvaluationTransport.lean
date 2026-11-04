module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Products.Basic

/-!
# Transporting an evaluation along an equivalence of categories

Let `T : C ⥤ C ⥤ C` be a bifunctor and `ev : T(I, K) ⟶ L` a morphism such that every morphism
`T(W, K) ⟶ L` factors uniquely as `T(g, K) ≫ ev` with `g : W ⟶ I`: `(I, ev)` is an internal
Hom from `K` to `L` for `T`, in the sense of the universal property alone (the hypothesis shape
of `CategoryTheory.MonoidalCategory.isIso_of_tensorHomBijective_map`, written with the
bifunctor in place of a monoidal structure). This file records three ways of producing new
internal Homs from old ones:

* along an equivalence of categories `E : C ≌ D` carrying `T` to a bifunctor on `D` up to a
  natural isomorphism, `(E I, τ⁻¹ ≫ E ev)` is an internal Hom from `E K` to `E L`;
* along a natural isomorphism of bifunctors;
* along isomorphisms of the source and of the target.

## Main results

* `CategoryTheory.bijective_map_app_comp_transport_equivalence`
* `CategoryTheory.bijective_map_app_comp_natIso`
* `CategoryTheory.bijective_map_app_comp_congr`
-/

@[expose] public section

namespace CategoryTheory

open scoped CategoryTheory.Prod

variable {C D : Type*} [Category C] [Category D]

/-- Precomposition with an isomorphism is bijective. -/
private theorem bijective_comp_left_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] (Z : C) :
    Function.Bijective fun x : Y ⟶ Z => f ≫ x :=
  ⟨fun a b hab => by simpa using congrArg (inv f ≫ ·) hab,
    fun y => ⟨inv f ≫ y, by simp⟩⟩

/-- Postcomposition with an isomorphism is bijective. -/
private theorem bijective_comp_right_of_isIso {Y Z : C} (g : Y ⟶ Z) [IsIso g] (X : C) :
    Function.Bijective fun x : X ⟶ Y => x ≫ g :=
  ⟨fun a b hab => by simpa using congrArg (· ≫ inv g) hab,
    fun y => ⟨y ≫ inv g, by simp⟩⟩

/-- **An internal Hom transported along an equivalence of categories.** If `E : C ≌ D` carries
the bifunctor `TC` to `TD` by `τ`, and `(I, ev)` is an internal Hom from `K` to `L` for `TC`,
then `(E I, τ⁻¹ ≫ E ev)` is an internal Hom from `E K` to `E L` for `TD`. -/
theorem bijective_map_app_comp_transport_equivalence (E : C ≌ D) (TC : C ⥤ C ⥤ C)
    (TD : D ⥤ D ⥤ D)
    (τ : Functor.uncurry.obj TC ⋙ E.functor ≅
      E.functor.prod E.functor ⋙ Functor.uncurry.obj TD)
    {K L I : C} (ev : (TC.obj I).obj K ⟶ L)
    (h : ∀ W : C, Function.Bijective fun g : W ⟶ I => (TC.map g).app K ≫ ev) (W' : D) :
    Function.Bijective fun g : W' ⟶ E.functor.obj I =>
      (TD.map g).app (E.functor.obj K) ≫ τ.inv.app (I, K) ≫ E.functor.map ev := by
  let u : E.functor.obj (E.inverse.obj W') ≅ W' := E.counitIso.app W'
  let c : (TD.obj W').obj (E.functor.obj K) ⟶ E.functor.obj ((TC.obj (E.inverse.obj W')).obj K) :=
    (TD.map u.inv).app (E.functor.obj K) ≫ τ.inv.app (E.inverse.obj W', K)
  have hc : IsIso c := by
    dsimp only [c]
    infer_instance
  have key : (fun g : W' ⟶ E.functor.obj I =>
      (TD.map g).app (E.functor.obj K) ≫ τ.inv.app (I, K) ≫ E.functor.map ev) =
      (fun x => c ≫ E.functor.map x) ∘ (fun g₀ => (TC.map g₀).app K ≫ ev) ∘
        (fun g => E.fullyFaithfulFunctor.preimage (u.hom ≫ g)) := by
    funext g
    have hτ := τ.inv.naturality (E.fullyFaithfulFunctor.preimage (u.hom ≫ g) ×ₘ 𝟙 K)
    have hC : (Functor.uncurry.obj TC).map (E.fullyFaithfulFunctor.preimage (u.hom ≫ g) ×ₘ 𝟙 K) =
        (TC.map (E.fullyFaithfulFunctor.preimage (u.hom ≫ g))).app K := by simp
    have hD : (Functor.uncurry.obj TD).map
        (E.functor.map (E.fullyFaithfulFunctor.preimage (u.hom ≫ g)) ×ₘ 𝟙 (E.functor.obj K)) =
        (TD.map (E.functor.map (E.fullyFaithfulFunctor.preimage (u.hom ≫ g)))).app
          (E.functor.obj K) := by simp
    simp only [Functor.comp_map, Functor.prod_map, Functor.map_id] at hτ
    rw [hC, hD, Functor.FullyFaithful.map_preimage] at hτ
    simp only [Function.comp_apply, c, Functor.map_comp, Category.assoc]
    rw [← reassoc_of% hτ, ← NatTrans.comp_app_assoc, ← Functor.map_comp, Iso.inv_hom_id_assoc]
  rw [key]
  refine Function.Bijective.comp ?_ (Function.Bijective.comp (h _) ?_)
  · exact (bijective_comp_left_of_isIso c _).comp (E.fullyFaithfulFunctor.map_bijective _ _)
  · exact E.fullyFaithfulFunctor.homEquiv.symm.bijective.comp (bijective_comp_left_of_isIso u.hom _)

/-- **An internal Hom transported along a natural isomorphism of bifunctors.** -/
theorem bijective_map_app_comp_natIso {T T' : C ⥤ C ⥤ C} (κ : T ≅ T') {K L I : C}
    (ev : (T'.obj I).obj K ⟶ L)
    (h : ∀ W : C, Function.Bijective fun g : W ⟶ I => (T'.map g).app K ≫ ev) (W : C) :
    Function.Bijective fun g : W ⟶ I =>
      (T.map g).app K ≫ (κ.hom.app I).app K ≫ ev := by
  have key : (fun g : W ⟶ I => (T.map g).app K ≫ (κ.hom.app I).app K ≫ ev) =
      (fun x => (κ.hom.app W).app K ≫ x) ∘ (fun g : W ⟶ I => (T'.map g).app K ≫ ev) := by
    funext g
    simp only [Function.comp_apply, ← Category.assoc, ← NatTrans.comp_app, ← κ.hom.naturality]
  rw [key]
  exact (bijective_comp_left_of_isIso _ _).comp (h W)

/-- **An internal Hom transported along isomorphisms of its source and its target.** -/
theorem bijective_map_app_comp_congr (T : C ⥤ C ⥤ C) {K₁ K₂ L₁ L₂ I : C} (a : K₂ ≅ K₁)
    (b : L₁ ≅ L₂) (ev : (T.obj I).obj K₁ ⟶ L₁)
    (h : ∀ W : C, Function.Bijective fun g : W ⟶ I => (T.map g).app K₁ ≫ ev) (W : C) :
    Function.Bijective fun g : W ⟶ I =>
      (T.map g).app K₂ ≫ (T.obj I).map a.hom ≫ ev ≫ b.hom := by
  have key : (fun g : W ⟶ I => (T.map g).app K₂ ≫ (T.obj I).map a.hom ≫ ev ≫ b.hom) =
      (fun x => (T.obj W).map a.hom ≫ x) ∘ (fun x => x ≫ b.hom) ∘
        (fun g : W ⟶ I => (T.map g).app K₁ ≫ ev) := by
    funext g
    simp only [Function.comp_apply, ← Category.assoc, NatTrans.naturality]
  rw [key]
  exact (bijective_comp_left_of_isIso _ _).comp
    ((bijective_comp_right_of_isIso _ _).comp (h W))

end CategoryTheory

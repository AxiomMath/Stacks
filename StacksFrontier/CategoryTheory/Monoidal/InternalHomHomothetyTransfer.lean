module

public import StacksFrontier.CategoryTheory.Monoidal.InternalHomUnitHomothety

/-!
# Carrying the homothety of an internal hom along a functor

Let `C` and `D` be monoidal categories and `R : C ⥤ D` a functor equipped with

* a comparison `c A B : R(A ⊗ B) ≅ R A ⊗ R B`, natural in its first variable, and
* a comparison `u : R(𝟙_ C) ≅ 𝟙_ D`

which satisfy the **left unitality** identity

`u⁻¹ ▷ R K ≫ c(𝟙_ C, K)⁻¹ ≫ R(λ_ K) = λ_(R K)`,

that is, the left-unitor law of a monoidal functor written for the pair `(c, u)` at the one
object `K`. Let `e : A ⊗ K ⟶ K` be a morphism and `a : 𝟙_ C ⟶ A` the *homothety* of the pair,
the morphism with `a ▷ K ≫ e = λ_ K`.

This file proves that `R a` is an isomorphism as soon as, on the other side,

* `e' : A' ⊗ R K ⟶ R K` exhibits `A'` as an internal hom from `R K` to `R K` — every
  `Z ⟶ A'` is `x ▷ R K ≫ e'` for exactly one `x` —
* some isomorphism `t : R A ≅ A'` has `t ▷ R K ≫ e' = c(A, K)⁻¹ ≫ R e`, and
* `A'` is isomorphic to `𝟙_ D` as an object.

Nothing about sheaves, sites or derived categories enters: this is the formal half of the
passage from a local computation of an internal hom to invertibility of a global homothety,
with each of the three comparisons appearing as a parameter rather than as a monoidal structure
on `R`. Stating it this way is what lets it be read at a comparison `c` built independently of
any monoidal structure on `R`, which is the situation for restriction to a localized site.

## Main results

* `CategoryTheory.MonoidalCategory.isIso_map_of_whiskerRight_comp_eq_leftUnitor_of_iso_tensorUnit`
  — **`R a` is an isomorphism**, under the hypotheses above.

## Implementation notes

The proof is three rewrites. The composite `u⁻¹ ≫ R a ≫ t : 𝟙_ D ⟶ A'` has
`(u⁻¹ ≫ R a ≫ t) ▷ R K ≫ e' = λ_(R K)`: whiskering is functorial, `t ▷ R K ≫ e'` is
`c(A, K)⁻¹ ≫ R e` by hypothesis, the naturality of `c` in its first variable moves `R a ▷ R K`
past `c(A, K)⁻¹` into `R(a ▷ K)`, the defining equation of the homothety replaces
`a ▷ K ≫ e` by `λ_ K`, and left unitality finishes. So
`CategoryTheory.MonoidalCategory.isIso_of_whiskerRight_comp_eq_leftUnitor_of_iso_tensorUnit`
applies to that composite, and `u` and `t` being isomorphisms carries invertibility back to
`R a`.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.MonoidalCategory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D] (R : C ⥤ D)
  (c : ∀ A B : C, R.obj (A ⊗ B) ≅ R.obj A ⊗ R.obj B) (u : R.obj (𝟙_ C) ≅ 𝟙_ D)

/-- **The image of a homothety under a functor carrying tensor products and the unit, from an
object computation on the other side.**

Let `R : C ⥤ D` come with comparisons `c A B : R(A ⊗ B) ≅ R A ⊗ R B` and `u : R(𝟙_ C) ≅ 𝟙_ D`
satisfying the left-unitor law `hu` at `K`, let `a : 𝟙_ C ⟶ A` satisfy `a ▷ K ≫ e = λ_ K`,
and suppose that in `D`

* `e' : A' ⊗ R K ⟶ R K` exhibits `A'` as an internal hom from `R K` to `R K`,
* `t : R A ⟶ A'` is an isomorphism with `t ▷ R K ≫ e' = c(A, K)⁻¹ ≫ R e`, and
* `A' ≅ 𝟙_ D`.

Then `R a` is an isomorphism. -/
theorem isIso_map_of_whiskerRight_comp_eq_leftUnitor_of_iso_tensorUnit
    (hc : ∀ {A A' : C} (f : A ⟶ A') (B : C),
      R.map (f ▷ B) ≫ (c A' B).hom = (c A B).hom ≫ R.map f ▷ R.obj B)
    {K : C}
    (hu : u.inv ▷ R.obj K ≫ (c (𝟙_ C) K).inv ≫ R.map (λ_ K).hom = (λ_ (R.obj K)).hom)
    {A : C} (e : A ⊗ K ⟶ K) {a : 𝟙_ C ⟶ A} (ha : a ▷ K ≫ e = (λ_ K).hom)
    {A' : D} (e' : A' ⊗ R.obj K ⟶ R.obj K)
    (he' : ∀ Z : D, Function.Bijective fun x : Z ⟶ A' => x ▷ R.obj K ≫ e')
    (t : R.obj A ⟶ A') [IsIso t]
    (ht : t ▷ R.obj K ≫ e' = (c A K).inv ≫ R.map e)
    (ψ : A' ≅ 𝟙_ D) :
    IsIso (R.map a) := by
  have h1 : R.map a ▷ R.obj K ≫ (c A K).inv = (c (𝟙_ C) K).inv ≫ R.map (a ▷ K) := by
    rw [Iso.comp_inv_eq, Category.assoc, hc a K, Iso.inv_hom_id_assoc]
  have key : (u.inv ≫ R.map a ≫ t) ▷ R.obj K ≫ e' = (λ_ (R.obj K)).hom := by
    rw [comp_whiskerRight, comp_whiskerRight, Category.assoc, Category.assoc, ht,
      reassoc_of% h1, ← R.map_comp, ha, hu]
  have : IsIso (u.inv ≫ R.map a ≫ t) :=
    isIso_of_whiskerRight_comp_eq_leftUnitor_of_iso_tensorUnit e' he' key ψ
  have hfac : R.map a = u.hom ≫ (u.inv ≫ R.map a ≫ t) ≫ inv t := by simp
  rw [hfac]
  infer_instance

end CategoryTheory.MonoidalCategory

end

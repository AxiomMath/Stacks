module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategory
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Defs

/-!
# Categorical moduli spaces

Let `f : 𝒳 ⟶ Y` be a 1-morphism from a category fibred in groupoids over the big fppf site
of `S` — in particular from an algebraic stack — to the category attached to an algebraic
space `Y`. Then `f` is a *categorical moduli space* when every 1-morphism from `𝒳` to an
algebraic space factors through `f`, up to an invertible 2-morphism, by a unique morphism of
algebraic spaces, and a *uniform* one when that persists after every flat base change. Both
notions have a relative form in which the target spaces are restricted to a full subcategory of
the category of algebraic spaces over `S`, given by a predicate on its objects.

## Main definitions

* `AlgebraicGeometry.Stack.IsCategoricalModuliSpace`: `f` is a categorical moduli space.
* `AlgebraicGeometry.Stack.IsUniformCategoricalModuliSpace`: `f` is a uniform categorical moduli
  space.
* `AlgebraicGeometry.Stack.IsCategoricalModuliSpaceIn`: `f` is a categorical moduli space in a
  full subcategory of algebraic spaces.
* `AlgebraicGeometry.Stack.IsUniformCategoricalModuliSpaceIn`: `f` is a uniform categorical
  moduli space in a full subcategory of algebraic spaces.

## Main results

* `AlgebraicGeometry.Stack.eq_of_isCategoricalModuliSpace`: the factoring morphism of algebraic
  spaces is unique.
* `AlgebraicGeometry.Stack.categoricalFactorization_comp`: the factorization of a 1-morphism and
  that of its restriction along a base change agree.
* `AlgebraicGeometry.Stack.isCategoricalModuliSpace_of_isTwoFibreProduct`: being a categorical
  moduli space does not depend on the chosen 2-fibre product presenting the base change.

## References

* [Stacks Project, Tag 0DUG](https://stacks.math.columbia.edu/tag/0DUG)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A 1-morphism from a category fibred in groupoids to the
category attached to an algebraic space `Y` is a *categorical moduli space* when every
1-morphism to the category attached to an algebraic space `W` factors through it by a unique
morphism `Y ⟶ W` of algebraic spaces, the factorization holding up to an invertible
2-morphism. -/
@[stacks 0DUG "part (1)"]
abbrev IsCategoricalModuliSpace
    {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (Y : AlgebraicSpaces B S hS)
    (f : 𝒳 ⟶ fibredCategory B S hS Y.obj) : Prop :=
  ∀ (W : AlgebraicSpaces B S hS)
    (g : 𝒳 ⟶ fibredCategory B S hS W.obj),
      ∃! h : Y ⟶ W,
        Nonempty (f ≫ (associatedMap B S hS h.hom).1 ≅ g)

/-- A categorical moduli space is *uniform* when every base change of it along a flat morphism
of algebraic spaces, given by any 2-fibre product of the cospan, is again a categorical moduli
space. -/
@[stacks 0DUG "part (2)"]
abbrev IsUniformCategoricalModuliSpace
    {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (Y : AlgebraicSpaces B S hS)
    (f : 𝒳 ⟶ fibredCategory B S hS Y.obj) : Prop :=
  ∀ (Y' : AlgebraicSpaces B S hS) (a : Y' ⟶ Y),
    Space.IsFlat B S hS a.hom →
      ∀ (P : Bicategory.TwoCommSq (associatedMap B S hS a.hom).1 f),
        Bicategory.IsTwoFibreProduct P →
          IsCategoricalModuliSpace B S hS Y' P.fst

/-- The universal factorization property with the target algebraic spaces restricted to the full
subcategory selected by the object predicate `C`, which `Y` is required to meet. -/
@[stacks 0DUG "part (3)"]
abbrev IsCategoricalModuliSpaceIn
    (C : AlgebraicSpaces B S hS → Prop)
    {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (Y : AlgebraicSpaces B S hS)
    (f : 𝒳 ⟶ fibredCategory B S hS Y.obj) : Prop :=
  C Y ∧
    ∀ (W : AlgebraicSpaces B S hS), C W →
      ∀ (g : 𝒳 ⟶ fibredCategory B S hS W.obj),
        ∃! h : Y ⟶ W,
          Nonempty (f ≫ (associatedMap B S hS h.hom).1 ≅ g)

/-- A categorical moduli space in the full subcategory selected by
`C` is *uniform in* `C` when its base change along every flat morphism of that subcategory is
again a categorical moduli space in `C`. -/
@[stacks 0DUG "part (4)"]
abbrev IsUniformCategoricalModuliSpaceIn
    (C : AlgebraicSpaces B S hS → Prop)
    {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (Y : AlgebraicSpaces B S hS)
    (f : 𝒳 ⟶ fibredCategory B S hS Y.obj) : Prop :=
  C Y ∧
    ∀ (Y' : AlgebraicSpaces B S hS), C Y' →
      ∀ (a : Y' ⟶ Y), Space.IsFlat B S hS a.hom →
        ∀ (P : Bicategory.TwoCommSq (associatedMap B S hS a.hom).1 f),
          Bicategory.IsTwoFibreProduct P →
            IsCategoricalModuliSpaceIn B S hS C Y' P.fst

/-! ### Consequences of the universal property -/

section Uniqueness

variable {𝒳 𝒳' 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-- Composing a 2-isomorphism `A ≅ N ≫ B` with a factorization `B ≫ k ≅ G` gives
`A ≫ k ≅ N ≫ G`. -/
private theorem nonempty_iso_comp_of_iso {𝒜 ℬ 𝒞 𝒟 : CatFiberedInGroupoids.{u, u, u + 1, u + 1}
      (BigFppfOver B S hS)} {A : 𝒜 ⟶ 𝒞} {N : 𝒜 ⟶ ℬ} {X : ℬ ⟶ 𝒞} {k : 𝒞 ⟶ 𝒟} {G : ℬ ⟶ 𝒟}
    (e : A ≅ N ≫ X) (hk : Nonempty (X ≫ k ≅ G)) : Nonempty (A ≫ k ≅ N ≫ G) :=
  hk.elim fun hk ↦ ⟨Bicategory.whiskerRightIso e k ≪≫ Bicategory.whiskerLeftIso N hk⟩

/-- The morphism of algebraic spaces through which a 1-morphism factors through a categorical
moduli space is unique. -/
theorem eq_of_isCategoricalModuliSpace {Y W : AlgebraicSpaces B S hS}
    {f : 𝒳 ⟶ fibredCategory B S hS Y.obj}
    (hf : IsCategoricalModuliSpace B S hS Y f)
    (g : 𝒳 ⟶ fibredCategory B S hS W.obj) (h₁ h₂ : Y ⟶ W)
    (η₁ : Nonempty (f ≫ (associatedMap B S hS h₁.hom).1 ≅ g))
    (η₂ : Nonempty (f ≫ (associatedMap B S hS h₂.hom).1 ≅ g)) : h₁ = h₂ := by
  obtain ⟨h, -, hu⟩ := hf W g
  exact (hu h₁ η₁).trans (hu h₂ η₂).symm

/-- The factorizations of a 1-morphism and of its restriction along a base change agree.
Suppose `f' : 𝒳' ⟶ Y'` is a categorical moduli space sitting over `f : 𝒳 ⟶ Y` along
`r : Y' ⟶ Y` and `N : 𝒳' ⟶ 𝒳`, and that `g : 𝒳 ⟶ W` restricts to `g' : 𝒳' ⟶ W`. Then the
morphism `Y' ⟶ W` factoring `g'` is the restriction along `r` of any morphism `Y ⟶ W` factoring
`g`. -/
theorem categoricalFactorization_comp {Y Y' W : AlgebraicSpaces B S hS}
    {f : 𝒳 ⟶ fibredCategory B S hS Y.obj} {f' : 𝒳' ⟶ fibredCategory B S hS Y'.obj}
    (hf' : IsCategoricalModuliSpace B S hS Y' f')
    (r : Y' ⟶ Y) (N : 𝒳' ⟶ 𝒳)
    (g : 𝒳 ⟶ fibredCategory B S hS W.obj) (g' : 𝒳' ⟶ fibredCategory B S hS W.obj)
    (e : f' ≫ (associatedMap B S hS r.hom).1 ≅ N ≫ f) (eg : N ≫ g ≅ g')
    (k : Y ⟶ W) (k' : Y' ⟶ W)
    (hk : Nonempty (f ≫ (associatedMap B S hS k.hom).1 ≅ g))
    (hk' : Nonempty (f' ≫ (associatedMap B S hS k'.hom).1 ≅ g')) : r ≫ k = k' := by
  refine eq_of_isCategoricalModuliSpace B S hS hf' g' _ _ ?_ hk'
  change Nonempty (f' ≫ (associatedMap B S hS (r.hom ≫ k.hom)).1 ≅ g')
  rw [associatedMap_comp]
  exact (nonempty_iso_comp_of_iso B S hS e hk).map (· ≪≫ eg)

/-- Being a categorical moduli space does not depend on the chosen 2-fibre product: if one
2-fibre product of a cospan whose first leg is attached to an algebraic space `Y` has first
projection a categorical moduli space of `Y`, so does every other. -/
theorem isCategoricalModuliSpace_of_isTwoFibreProduct {Y : AlgebraicSpaces B S hS}
    {a : fibredCategory B S hS Y.obj ⟶ 𝒵} {f : 𝒳 ⟶ 𝒵} {P Q : Bicategory.TwoCommSq a f}
    (hP : Bicategory.IsTwoFibreProduct P) (hQ : Bicategory.IsTwoFibreProduct Q)
    (hc : IsCategoricalModuliSpace B S hS Y Q.fst) :
    IsCategoricalModuliSpace B S hS Y P.fst := by
  classical
  let L := Bicategory.twoFibreProductPreHom hQ P
  let M := Bicategory.twoFibreProductPreHom hP Q
  obtain ⟨e, -⟩ := Bicategory.twoFibreProductPreHom_rel hP (L.comp M) (.id P)
  intro W g
  obtain ⟨k, ⟨hk⟩, hu⟩ := hc W (M.hom ≫ g)
  exact ⟨k, (nonempty_iso_comp_of_iso B S hS L.isoFst ⟨hk⟩).map
      (· ≪≫ Bicategory.whiskerRightIso e g ≪≫ Bicategory.leftUnitor g),
    fun k' hk' ↦ hu k' (nonempty_iso_comp_of_iso B S hS M.isoFst hk')⟩

end Uniqueness

end AlgebraicGeometry.Stack

end

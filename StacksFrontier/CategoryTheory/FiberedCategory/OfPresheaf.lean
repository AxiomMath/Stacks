module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.CategoryTheory.FiberedCategory.Grothendieck

import StacksCore.Tactic.StacksAttribute

/-!
# The fibred category attached to a presheaf of categories

Let `𝒞` be a category and let `F : 𝒞ᵒᵖ ⥤ Cat` be a presheaf of categories, written `f^* = F(f)`
for `f : V ⟶ U`. Stacks 02XV builds from `F` a fibred category `p_F : 𝒮_F ⥤ 𝒞`: the objects of
`𝒮_F` are the pairs `(U, x)` with `U` an object of `𝒞` and `x` an object of `F(U)`; a morphism
`(V, y) ⟶ (U, x)` is a pair `(f, φ)` with `f : V ⟶ U` and `φ : y ⟶ f^* x`, so that
`Mor((V, y), (U, x))` is the disjoint union over `f` of `Mor_{F(V)}(y, f^* x)`; the composite of
`(g, ψ)` with `(f, φ)` is `(f ∘ g, g^*(φ) ∘ ψ)`; and `p_F` sends `(U, x)` to `U`. That `p_F` is a
fibred category is witnessed by the strongly cartesian lift
`(f, 𝟙 (f^* x)) : (V, f^* x) ⟶ (U, x)` of `f : V ⟶ U`.

## Main definitions

* `CategoryTheory.presheafOfCategories`: the category `𝒮_F` together with `p_F`, as an object of
  the 2-category of categories over `𝒞`.

## Main results

* `CategoryTheory.PresheafOfCategories.objEquiv`,
  `CategoryTheory.PresheafOfCategories.homEquiv` and
  `CategoryTheory.PresheafOfCategories.comp_fiber`: the objects, the morphisms and the composition
  of `𝒮_F` are the source's;
* `CategoryTheory.PresheafOfCategories.isFibered`: `p_F` is a fibred category.

That `(f, 𝟙 (f^* x))` is a strongly cartesian lift of `f` — the source's claim that a morphism
`h` with `f ∘ h = g` determines one and only one lift `(h, ν)` of a given `(g, ψ)` — is Mathlib's
`Pseudofunctor.CoGrothendieck.isStronglyCartesian_homCartesianLift`, recorded with
`add_to_stacks` below.

## Implementation notes

`𝒮_F` is Mathlib's `CategoryTheory.Pseudofunctor.CoGrothendieck`, written `∫ᶜ`, applied to the
pseudofunctor `F.toPseudofunctor'`. Mathlib's construction takes a pseudofunctor
`LocallyDiscrete 𝒞ᵒᵖ ⥤ᵖ Cat` and inserts the coherence isomorphisms `mapId` and `mapComp` at the
places where the source uses `g^* ∘ f^* = (f ∘ g)^*` on the nose. A functor into the 2-category of
categories in the sense of Stacks 003N is an ordinary functor into the strict bicategory `Cat`, and
for such a functor those coherence isomorphisms are `eqToIso`; `comp_fiber` below records that the
second component of the composition of `∫ᶜ F.toPseudofunctor'` is then literally the source's
`g^*(φ) ∘ ψ`, transported along `g^*(f^* x) = (f ∘ g)^* x`. Its first component is `f ∘ g` by
Mathlib's `Pseudofunctor.CoGrothendieck.categoryStruct_comp_base`, and `p_F` sends `(U, x)` to `U`
and `(f, φ)` to `f` by `Pseudofunctor.CoGrothendieck.forget_obj` and `forget_map`.

`Functor.toPseudofunctor'` is a plain `def`, so a goal mentioning both an object of `F(U)` and an
object of `F.toPseudofunctor'.obj ⟨op U⟩` is not type-correct at `implicit` transparency and
`rw`/`simp` refuse it; the two are unfolded locally below.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

open Opposite Pseudofunctor
open scoped Pseudofunctor.CoGrothendieck

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]

-- The construction itself is Mathlib's; what follows only wraps it as an object over `𝒞`
-- and checks it carries the source's objects, morphisms and composition.
add_to_stacks 02XV "the category `𝒮_F`" CategoryTheory.Pseudofunctor.CoGrothendieck
add_to_sga "4 XVII 2.2.12" CategoryTheory.Pseudofunctor.CoGrothendieck
add_to_stacks 02XV "the projection `p_F`" CategoryTheory.Pseudofunctor.CoGrothendieck.forget
add_to_sga "4 I 8.3.2" "more general" CategoryTheory.Pseudofunctor.CoGrothendieck.forget
add_to_stacks 02XV "`p_F` is a fibred category"
  CategoryTheory.Pseudofunctor.CoGrothendieck.instIsFiberedForget
add_to_sga "4 VI 6.1.3" "Fiberedness clause"
  CategoryTheory.Pseudofunctor.CoGrothendieck.instIsFiberedForget
add_to_sga "4 VI 7.1.4" "partial" CategoryTheory.Pseudofunctor.CoGrothendieck.instIsFiberedForget
add_to_sga "4 XVII 2.2.12" "partial" CategoryTheory.Pseudofunctor.CoGrothendieck.instIsFiberedForget
add_to_stacks 02XV "the strongly cartesian lift of `f`"
  CategoryTheory.Pseudofunctor.CoGrothendieck.isStronglyCartesian_homCartesianLift

/-- **Stacks 02XV.**
The category `𝒮_F` attached to a presheaf of categories `F : 𝒞ᵒᵖ ⥤ Cat`, together with its
projection `p_F : 𝒮_F ⥤ 𝒞`, as an object of the 2-category of categories over `𝒞`. -/
@[stacks 02XV]
abbrev presheafOfCategories (F : 𝒞ᵒᵖ ⥤ Cat.{v₂, u₂}) : BasedCategory 𝒞 :=
  BasedCategory.ofFunctor (Pseudofunctor.CoGrothendieck.forget F.toPseudofunctor')

namespace PresheafOfCategories

attribute [local implicit_reducible] Functor.toPseudofunctor'
  pseudofunctorOfIsLocallyDiscrete Quiver.Hom.toLoc

variable (F : 𝒞ᵒᵖ ⥤ Cat.{v₂, u₂})

/-- The strict compatibility `g^*(f^* x) = (f ∘ g)^* x` of the pullback functors of a presheaf of
categories, which is what makes the composition law of `𝒮_F` type-check. -/
lemma pullback_comp_obj {W V U : 𝒞} (g : W ⟶ V) (f : V ⟶ U) (x : F.obj (op U)) :
    (F.map g.op).toFunctor.obj ((F.map f.op).toFunctor.obj x) =
      (F.map (g ≫ f).op).toFunctor.obj x := by
  rw [op_comp, F.map_comp, Cat.Hom.comp_toFunctor]
  rfl

/-- **Stacks 02XV.**
`Ob(𝒮_F) = {(U, x) | U ∈ Ob(𝒞), x ∈ Ob(F(U))}`. -/
@[stacks 02XV]
def objEquiv : ∫ᶜ F.toPseudofunctor' ≃ Σ U : 𝒞, F.obj (op U) where
  toFun X := ⟨X.base, X.fiber⟩
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Stacks 02XV.**
`Mor_{𝒮_F}((V, y), (U, x))` is the disjoint union over `f : V ⟶ U` of `Mor_{F(V)}(y, f^* x)`. -/
@[stacks 02XV]
def homEquiv (X Y : ∫ᶜ F.toPseudofunctor') :
    (X ⟶ Y) ≃ Σ f : X.base ⟶ Y.base, (X.fiber ⟶ (F.map f.op).toFunctor.obj Y.fiber) where
  toFun u := ⟨u.base, u.fiber⟩
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Stacks 02XV.**
The composition of `𝒮_F` is the source's: the composite of `ψ : z ⟶ g^* y` with `φ : y ⟶ f^* x` is
`g^*(φ) ∘ ψ`, read as a morphism `z ⟶ (f ∘ g)^* x` through `pullback_comp_obj`. -/
@[stacks 02XV]
lemma comp_fiber {X Y Z : ∫ᶜ F.toPseudofunctor'} (u : X ⟶ Y) (v : Y ⟶ Z) :
    (u ≫ v).fiber = u.fiber ≫ (F.map u.base.op).toFunctor.map v.fiber ≫
      eqToHom (pullback_comp_obj F u.base v.base Z.fiber) := by
  simp only [Pseudofunctor.CoGrothendieck.categoryStruct_comp_fiber,
    Functor.toPseudofunctor'_mapComp, eqToIso.inv, Cat.eqToHom_app]
  rfl

/-- **Stacks 02XV.**
The projection `p_F : 𝒮_F ⥤ 𝒞` is a fibred category.

This bridge is load-bearing: instance resolution does not see Mathlib's
`CoGrothendieck.instIsFiberedForget` through `BasedCategory.ofFunctor`'s projection, so
`infer_instance` fails on this goal without it. -/
@[stacks 02XV, sga "4 VI 6.1.3" "strict functor case"]
instance isFibered : (presheafOfCategories F).p.IsFibered :=
  inferInstanceAs (Pseudofunctor.CoGrothendieck.forget F.toPseudofunctor').IsFibered

end PresheafOfCategories

end CategoryTheory

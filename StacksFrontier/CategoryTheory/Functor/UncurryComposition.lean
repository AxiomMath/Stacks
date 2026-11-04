module

public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Whiskering

/-!
# Uncurrying a bifunctor composed on either side

A bifunctor is written here in the curried form `H : C₁ ⥤ C₂ ⥤ D`, and composing a functor
`G : D ⥤ E` after it, or functors `P` and `Q` before it in the two variables, is done by
whiskering: `H ⋙ (whiskeringRight _ _ _).obj G` and `P ⋙ H ⋙ (whiskeringLeft _ _ _).obj Q`.
Uncurried, those two composites are the ones written on pairs: `Functor.uncurry.obj H ⋙ G` and
`P.prod Q ⋙ Functor.uncurry.obj H`.

## Main definitions

* `CategoryTheory.Functor.uncurryCompRightIso`: `(H ⋙ G)ᵘ ≅ Hᵘ ⋙ G` for a functor composed
  after a bifunctor.

## Main results

* `CategoryTheory.Functor.uncurry_whiskeringLeft_comp`: `(P ⋙ H ⋙ Q)ᵘ = P.prod Q ⋙ Hᵘ` for
  functors composed before a bifunctor in its two variables.

## Implementation notes

The right-hand composition is *not* an equality of functors on morphisms: uncurrying `H`
followed by `G` sends `(f, g)` to `G((H f)_{-} ≫ (H _)g)`, while `Hᵘ ⋙ G` sends it to
`G((H f)_{-}) ≫ G((H _)g)`, and the two agree only by functoriality of `G`. So it is given as
an isomorphism with identity components rather than as an equality.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

variable {B₁ : Type u₁} [Category.{v₁} B₁] {B₂ : Type u₂} [Category.{v₂} B₂]
  {C₁ : Type u₃} [Category.{v₃} C₁] {C₂ : Type u₄} [Category.{v₄} C₂]
  {D : Type u₅} [Category.{v₅} D]

/-- **Uncurrying commutes with composing a functor after a bifunctor**: the bifunctor
`(X, Y) ↦ G (H X Y)` is `Hᵘ` followed by `G`, by an isomorphism whose components are
identities. -/
def uncurryCompRightIso {E : Type*} [Category E] (H : C₁ ⥤ C₂ ⥤ D) (G : D ⥤ E) :
    uncurry.obj (H ⋙ (whiskeringRight C₂ D E).obj G) ≅ uncurry.obj H ⋙ G :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ by simp [uncurry]

/-- **Uncurrying commutes with composing functors before a bifunctor**: the bifunctor
`(X, Y) ↦ H (P X) (Q Y)` is the product functor `P × Q` followed by `Hᵘ`. -/
theorem uncurry_whiskeringLeft_comp (H : C₁ ⥤ C₂ ⥤ D) (P : B₁ ⥤ C₁) (Q : B₂ ⥤ C₂) :
    uncurry.obj (P ⋙ H ⋙ (whiskeringLeft B₂ C₂ D).obj Q) = P.prod Q ⋙ uncurry.obj H :=
  rfl

end CategoryTheory.Functor

end

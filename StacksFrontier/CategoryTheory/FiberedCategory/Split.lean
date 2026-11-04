module

public import StacksFrontier.CategoryTheory.FiberedCategory.OfPresheaf
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoOver

/-!
# Split fibred categories

Let `𝒞` be a category. A presheaf of categories `F : 𝒞ᵒᵖ ⥤ Cat` gives rise to a fibred category
`p_F : 𝒮_F ⥤ 𝒞` by the Grothendieck construction (Stacks 02XV,
`CategoryTheory.presheafOfCategories`), and a fibred category is *split* (Stacks 02XW) when it is
isomorphic over `𝒞` — isomorphic, not merely equivalent — to one of these.

## Main definitions

* `CategoryTheory.Functor.IsSplitFibered`: Stacks 02XW.

## Implementation notes

The objects of `𝒮_F` are pairs `(U, x)` with `U` an object of `𝒞` and `x` an object of `F(U)`, so
they live in the universe `max u₁ u₂` for `F : 𝒞ᵒᵖ ⥤ Cat.{v₂, u₂}` and `𝒞 : Type u₁`. The
existential below quantifies over `F : 𝒞ᵒᵖ ⥤ Cat.{v₂, u₂}` with `v₂`, `u₂` the universes of the
category `𝒮` being tested for splitness, which is the choice that makes the two sides comparable
in the intended case `u₁ ≤ u₂`; note that an *isomorphism* over `𝒞`, unlike an equivalence,
forces the object types of the two sides to be in bijection, so no generality is lost by tying
the universe of `F` to that of `𝒮`.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮]

/-- **Stacks 02XW.**
A *split fibred category* over `𝒞` is a fibred category `p : 𝒮 ⥤ 𝒞` that is isomorphic over `𝒞`
to the fibred category `𝒮_F` attached to some presheaf of categories `F : 𝒞ᵒᵖ ⥤ Cat`
(Stacks 02XV). The source is explicit that isomorphism over `𝒞`, and not merely equivalence over
`𝒞`, is meant. -/
@[stacks 02XW]
def Functor.IsSplitFibered (p : 𝒮 ⥤ 𝒞) : Prop :=
  p.IsFibered ∧ ∃ F : 𝒞ᵒᵖ ⥤ Cat.{v₂, u₂},
    (BasedCategory.ofFunctor p).IsoOver (presheafOfCategories F)

/-- A split fibred category is a fibred category. -/
lemma Functor.IsSplitFibered.isFibered {p : 𝒮 ⥤ 𝒞} (h : p.IsSplitFibered) : p.IsFibered :=
  h.1

/-- The category over `𝒞` attached to a presheaf of categories `F : 𝒞ᵒᵖ ⥤ Cat` is split: it is
isomorphic over `𝒞` to itself. This says the notion of Stacks 02XW is not vacuous. -/
lemma Functor.isSplitFibered_presheafOfCategories
    (F : 𝒞ᵒᵖ ⥤ Cat.{max v₁ v₂, max u₁ u₂}) : (presheafOfCategories F).p.IsSplitFibered :=
  ⟨inferInstance, F, .refl _⟩

end CategoryTheory

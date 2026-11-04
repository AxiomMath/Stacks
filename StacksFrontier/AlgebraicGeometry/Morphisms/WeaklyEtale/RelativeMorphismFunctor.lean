module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import StacksCore.Tactic.StacksAttribute

/-!
# The relative morphism functor

For two schemes `Z` and `X` over a scheme `S`, the relative morphism functor `Mor_S(Z, X)` sends
a scheme `T` over `S` to the set of morphisms `T ×_S Z ⟶ T ×_S X` over `T`, equivalently to the
set of morphisms `T ×_S Z ⟶ X` over `S`.

## Main definitions

* `AlgebraicGeometry.relativeHom` is the relative morphism functor `Mor_S(Z, X)` on the opposite
  of the category of schemes over `S`.
* `AlgebraicGeometry.relativeHomObjEquivOverBase` identifies its two descriptions: morphisms
  `T ×_S Z ⟶ X` over `S` and morphisms `T ×_S Z ⟶ T ×_S X` over `T`.

## Implementation notes

Products in the slice category over `S` are fibre products over `S`, so the functor is the Yoneda
functor of `X` precomposed with the opposite of the product-with-`Z` functor; the universal
properties of the two products supply functoriality. The factors are written in the order
`Z ⨯ T` rather than `T ⨯ Z`; the two objects agree up to `CategoryTheory.Limits.prod.symmetry`.
The identification of a morphism `T ×_S Z ⟶ X` over `S` with a morphism `T ×_S Z ⟶ T ×_S X` over
`T` is the adjunction `Over.forget T ⊣ Over.star T` taken in the category of schemes over `S`.

## References

* [Stacks Project, Tag 0BL2](https://stacks.math.columbia.edu/tag/0BL2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

/-- The relative morphism functor `Mor_S(Z, X)` of two schemes `Z` and `X` over `S`: it sends a
scheme `T` over `S` to the set of morphisms `T ×_S Z ⟶ X` over `S`, and a morphism `T' ⟶ T` over
`S` to the operation of base change along it. -/
@[stacks 0BL2]
noncomputable def relativeHom (Z X : Over S) : (Over S)ᵒᵖ ⥤ Type u :=
  (prod.functor.obj Z).op ⋙ yoneda.obj X

/-- An element of `Mor_S(Z, X)(T)` is a morphism `T ×_S Z ⟶ X` over `S`. -/
@[simp]
lemma relativeHom_obj (Z X : Over S) (T : (Over S)ᵒᵖ) :
    (relativeHom Z X).obj T = (Z ⨯ T.unop ⟶ X) :=
  rfl

/-- The functor `Mor_S(Z, X)` acts on morphisms of schemes over `S` by base change: it
precomposes a morphism out of a fibre product with the induced morphism of fibre products. -/
@[simp]
lemma relativeHom_map (Z X : Over S) {T T' : (Over S)ᵒᵖ} (h : T ⟶ T')
    (b : (relativeHom Z X).obj T) :
    (relativeHom Z X).map h b = prod.map (𝟙 Z) h.unop ≫ b :=
  rfl

/-- The object `T ×_S Z` of the category of schemes over `T`, via its second projection. -/
noncomputable abbrev prodOverBase (Z T : Over S) : Over T :=
  Over.mk (prod.snd : Z ⨯ T ⟶ T)

/-- The two descriptions of an element of `Mor_S(Z, X)(T)` agree: a morphism `T ×_S Z ⟶ X` over
`S` is the same thing as a morphism `T ×_S Z ⟶ T ×_S X` over `T`. This is the adjunction
`Over.forget T ⊣ Over.star T` in the category of schemes over `S`. -/
noncomputable def relativeHomObjEquivOverBase (Z X T : Over S) :
    (relativeHom Z X).obj (op T) ≃ (prodOverBase Z T ⟶ (Over.star T).obj X) :=
  (Over.forgetAdjStar T).homEquiv (prodOverBase Z T) X

/-- A morphism `T ×_S Z ⟶ T ×_S X` over `T` is turned into a morphism `T ×_S Z ⟶ X` over `S` by
composing with the projection to `X`. -/
lemma relativeHomObjEquivOverBase_symm_apply (Z X T : Over S)
    (c : prodOverBase Z T ⟶ (Over.star T).obj X) :
    (relativeHomObjEquivOverBase Z X T).symm c = c.left ≫ prod.snd :=
  rfl

end AlgebraicGeometry

end

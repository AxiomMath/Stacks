module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.CospanReindex

/-!
# Reading a pre-morphism of squares across a reindexing of the second cospan leg

`CategoryTheory.Bicategory.TwoCommSq.reindexSnd` moves a 2-commutative square (**Stacks 003O**)
over a cospan `(f, g)` to one over `(f, g')` along an invertible 2-morphism `θ : g ≅ g'`, and
`CategoryTheory.Bicategory.isTwoFibreProduct_reindexSnd` says that a 2-fibre product
(**Stacks 003Q**) stays one. What
`StacksFrontier.CategoryTheory.TwoFibreProduct.CospanReindex` supplies at the level of
*pre-morphisms* is only the first-leg form,
`CategoryTheory.Bicategory.TwoCommSq.PreHom.reindexFst`: the terminality transport for the second
leg goes through `CategoryTheory.Bicategory.TwoCommSq.swap`, which needs nothing about individual
pre-morphisms.

A consumer that has a pre-morphism in hand and has to keep its underlying 1-morphism — because
that 1-morphism is what carries a property across the reindexing — needs the second-leg form.
This file supplies it.

## Main definitions

* `CategoryTheory.Bicategory.TwoCommSq.PreHom.reindexSnd`: a pre-morphism
  `T.reindexSnd θ.symm ⟶ S` over `(f, g)`, read as a pre-morphism `T ⟶ S.reindexSnd θ` over
  `(f, g')`.

## Implementation notes

As with the first leg, reindexing changes neither the apex nor the two projections of a square,
so the underlying 1-morphism and the two comparison 2-isomorphisms are unchanged and only the
Stacks 003O compatibility square is re-proved. That re-proof is not repeated here: it is the
first-leg one conjugated by `CategoryTheory.Bicategory.TwoCommSq.PreHom.swap`, exactly as
`CategoryTheory.Bicategory.TwoCommSq.reindexSnd` is defined from
`CategoryTheory.Bicategory.TwoCommSq.reindexFst`. The conjugation type-checks because
`CategoryTheory.Bicategory.TwoCommSq.swap_swap` holds by `rfl`.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Bicategory

universe w v u

variable {A : Type u} [Bicategory.{w, v} A]

variable {X Y Z : A} {f : X ⟶ Z} {g g' : Y ⟶ Z}

/-- A pre-morphism of 2-commutative squares `T.reindexSnd θ.symm ⟶ S` over `(f, g)`, read as a
pre-morphism `T ⟶ S.reindexSnd θ` over `(f, g')`. The underlying 1-morphism and the two
comparison 2-isomorphisms are unchanged; only the compatibility square is re-proved, and that
re-proof is `CategoryTheory.Bicategory.TwoCommSq.PreHom.reindexFst` conjugated by
`CategoryTheory.Bicategory.TwoCommSq.PreHom.swap`. -/
def TwoCommSq.PreHom.reindexSnd (θ : g ≅ g') {T : TwoCommSq f g'} {S : TwoCommSq f g}
    (m : TwoCommSq.PreHom (T.reindexSnd θ.symm) S) : TwoCommSq.PreHom T (S.reindexSnd θ) :=
  (TwoCommSq.PreHom.reindexFst (T := T.swap) (S := S.swap) θ m.swap).swap

/-- Reindexing the second cospan leg leaves the underlying 1-morphism of a pre-morphism of
2-commutative squares alone. -/
@[simp]
theorem TwoCommSq.PreHom.reindexSnd_hom (θ : g ≅ g') {T : TwoCommSq f g'} {S : TwoCommSq f g}
    (m : TwoCommSq.PreHom (T.reindexSnd θ.symm) S) : (m.reindexSnd θ).hom = m.hom :=
  rfl

end CategoryTheory.Bicategory

end

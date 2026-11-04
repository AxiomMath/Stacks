module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.Defs

/-!
# Exchanging the two legs of a 2-commutative square (Stacks 003O, 003Q)

A 2-commutative square over a cospan `f : x ⟶ z`, `g : y ⟶ z` in a bicategory
(`CategoryTheory.Bicategory.TwoCommSq`, **Stacks 003O**) has the same data as a 2-commutative
square over the cospan read in the other order, with its two projections and the filler
exchanged. The exchange is an isomorphism of the categories of 2-commutative squares of
Stacks 003O — it is involutive on the nose, on objects, on pre-morphisms and on the morphisms of
the quotient category — so it carries 2-fibre products (**Stacks 003Q**) to 2-fibre products.

## Main definitions

* `CategoryTheory.Bicategory.TwoCommSq.swap`: the square over the reversed cospan.
* `CategoryTheory.Bicategory.TwoCommSq.PreHom.swap` and
  `CategoryTheory.Bicategory.TwoCommSq.swapHom`: the exchange on pre-morphisms and on the
  morphisms of the category of Stacks 003O, each involutive on the nose
  (`CategoryTheory.Bicategory.TwoCommSq.swap_swap`,
  `CategoryTheory.Bicategory.TwoCommSq.swapHom_swapHom`).

## Main results

* `CategoryTheory.Bicategory.isTwoFibreProduct_swap`: a swapped 2-fibre product is a 2-fibre
  product.

## Implementation notes

`TwoCommSq.swap` is marked `@[implicit_reducible]`: the compatibility square of Stacks 003O for
the swapped pre-morphism is typed through the projections of the swapped square, and without
that attribute the goal is not type-correct at the `implicit` transparency level at which Lean
checks implicit arguments.

Involutivity holds by `rfl` at every level — on squares, on pre-morphisms and hence on the
morphisms of the quotient category — because a swapped square is a structure literal whose fields
are the given ones permuted.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

/-- The 2-commutative square over the reversed cospan carried by a 2-commutative square over
`(f, g)`: the same apex, the two projections exchanged, and the filler inverted. -/
@[implicit_reducible]
def TwoCommSq.swap (T : TwoCommSq f g) : TwoCommSq g f where
  pt := T.pt
  fst := T.snd
  snd := T.fst
  iso := T.iso.symm

/-- Exchanging the legs twice is the identity on 2-commutative squares. -/
theorem TwoCommSq.swap_swap (T : TwoCommSq f g) : T.swap.swap = T := rfl

/-- **The compatibility square of Stacks 003O for the exchanged pre-morphism.** It is the given
compatibility square solved for the inverted filler: the filler of the target square is
invertible, so whiskering it by the underlying 1-morphism is too. -/
theorem TwoCommSq.PreHom.swap_compat {T S : TwoCommSq f g}
    (a : TwoCommSq.PreHom T S) :
    T.iso.inv ≫ (a.isoFst.hom ▷ f) ≫ (α_ a.hom S.fst f).hom
      = (a.isoSnd.hom ▷ g) ≫ (α_ a.hom S.snd g).hom ≫ (a.hom ◁ S.iso.inv) := by
  rw [Iso.inv_comp_eq, reassoc_of% a.compat, ← whiskerLeft_comp, Iso.hom_inv_id,
    whiskerLeft_id, Category.comp_id]

/-- A pre-morphism of 2-commutative squares (**Stacks 003O**) read on the reversed cospan: the
same 1-morphism with its two comparison 2-cells exchanged. -/
@[implicit_reducible]
def TwoCommSq.PreHom.swap {T S : TwoCommSq f g} (a : TwoCommSq.PreHom T S) :
    TwoCommSq.PreHom T.swap S.swap where
  hom := a.hom
  isoFst := a.isoSnd
  isoSnd := a.isoFst
  compat := TwoCommSq.PreHom.swap_compat a

/-- The exchange on the morphisms of the category of 2-commutative squares of **Stacks 003O**:
pre-morphisms modulo the 2-cell equivalence, whose mediating 2-cell is unchanged. -/
def TwoCommSq.swapHom {T S : TwoCommSq f g} (m : T ⟶ S) : T.swap ⟶ S.swap :=
  Quotient.map TwoCommSq.PreHom.swap
    (fun _ _ hm => by obtain ⟨θ, h1, h2⟩ := hm; exact ⟨θ, h2, h1⟩) m

/-- Exchanging the legs twice is the identity on the morphisms of the category of Stacks 003O. -/
theorem TwoCommSq.swapHom_swapHom {T S : TwoCommSq f g} (m : T ⟶ S) :
    TwoCommSq.swapHom (TwoCommSq.swapHom m) = m := by
  induction m using Quotient.ind with | _ a => rfl

/-- **A swapped 2-fibre product is a 2-fibre product (Stacks 003Q).** Exchanging the two legs is
an involutive isomorphism of the categories of 2-commutative squares of Stacks 003O over the two
orderings of the cospan, so it carries the terminal object to the terminal object. -/
noncomputable def isTwoFibreProduct_swap {P : TwoCommSq f g} (hP : IsTwoFibreProduct P) :
    IsTwoFibreProduct P.swap := by
  refine IsTerminal.ofUniqueHom (fun T => TwoCommSq.swapHom (hP.from T.swap)) ?_
  intro T m
  rw [← TwoCommSq.swapHom_swapHom m,
    hP.hom_ext (TwoCommSq.swapHom m) (hP.from T.swap)]

end CategoryTheory.Bicategory

end

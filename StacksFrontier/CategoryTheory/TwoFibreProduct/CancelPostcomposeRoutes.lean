module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.CancelFstPostcompose

/-!
# The last leg of each of the two cancellation routes into a 2-fibre product (Stacks 003O, 02XD)

Fix a cospan `bb' : 𝒱' ⟶ 𝒴`, `bb : 𝒱 ⟶ 𝒴` of categories fibred in groupoids. A cancellation of
**Stacks 02XD** applied to the canonical 2-fibre product `𝒱' ×_𝒴 𝒱` along a 1-morphism `cc`, read
back over the cospan `(bb', bb)` by changing its second leg along the cancellation's own
comparison 2-cell (`CategoryTheory.Bicategory.TwoCommSq.postcomposeSnd`), carries a pre-morphism
of Stacks 003O to `𝒱' ×_𝒴 𝒱` itself, given by the outer projection. This file provides that
pre-morphism for each of the two cancellations — the second-factor one and the first-factor one —
and the two filler identities and one filler agreement they need.

They are the final leg of each of the two routes a chase comparing two 1-morphisms into
`𝒱' ×_𝒴 𝒱` composes: the preceding legs are
`CategoryTheory.CatFiberedInGroupoids.cancelFstPostcomposePreHom` and
`CategoryTheory.Bicategory.TwoCommSq.PreHom.postcomposeSnd`.

## Main definitions

* `CategoryTheory.CatFiberedInGroupoids.cancelSndPostcomposeSndPreHom`: the pre-morphism for the
  second-factor cancellation.
* `CategoryTheory.CatFiberedInGroupoids.cancelFstPostcomposeSndPreHom`: the pre-morphism for the
  first-factor cancellation, whose two legs have to be exchanged to read over `(bb', bb)`.

## Main results

* `CategoryTheory.CatFiberedInGroupoids.postcomposeSnd_iso_hom_strict`,
  `CategoryTheory.CatFiberedInGroupoids.cancelSndSquare_iso_hom`,
  `CategoryTheory.CatFiberedInGroupoids.cancelFstSquare_iso_inv`: the three fillers used here, as
  composites of whiskerings with no associator in them.
* `CategoryTheory.CatFiberedInGroupoids.swap_postcompose_iso_hom`: exchanging the legs of a square
  read over a postcomposed cospan and reading the exchanged square over the exchanged postcomposed
  cospan give the *same filler*, not merely 2-isomorphic ones.

## Implementation notes

The compatibility square of Stacks 003O for each pre-morphism is, after the filler identities are
substituted, two cancellations of an invertible 2-cell against its inverse together with one
identity 2-cell that a left-whiskered identity leaves behind. None of that can be done by `rw` or
`simp` in place: in this strict 2-category two consecutive factors of such a composite are typed
through different bracketings of one and the same 1-morphism, so the composite is not type-correct
at the `implicit` transparency level at which Lean checks the implicit arguments of a motive. The
remedy is the one `StacksFrontier.CategoryTheory.TwoFibreProduct.CancelFstPostcompose` records: name
the bookkeeping in a plain category with abstract objects and *apply* it, application checking up
to definitional equality, where the bracketing is free. `cancel_tail_two`, `cancel_head_two` and
`id_chain6` are those lemmas; each is one `rw` or `simp` line over an abstract category.

`swap_postcompose_iso_hom` is the other half of
`CategoryTheory.Bicategory.TwoCommSq.swap_postcompose`, which gives the equality of the two
squares. The equality is not definitional, so a pre-morphism out of one of them is not a
pre-morphism out of the other; but the two squares have the same apex and the same two legs *on
the nose*, so the only field of a pre-morphism that has to be re-proved is its compatibility
square, and the filler agreement here is exactly what re-proves it — with no transport, which
would leave the underlying 1-morphism unreadable.

No `@[stacks]` attribute: nothing here asserts a sentence of Stacks 003O or 02XD, these being
comparisons between objects those tags provide, and the `02XD` tag stays on
`CategoryTheory.Limits.CategoricalPullback.assocComp` in
`StacksFrontier.CategoryTheory.TwoFibreProduct.Cancellation`.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits

namespace CategoryTheory.CatFiberedInGroupoids

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
  {𝒰 𝒱 𝒱' 𝒜 𝒞 𝒳 𝒴 :
    CatFiberedInGroupoids.{v₁, max v₁ v₂, u₁, max (max u₁ u₂) (max v₁ v₂)} C}

/-! ### Fillers, with the associators gone -/

/-- **The filler of a square read over a cospan with only its second leg changed, without its
associator.** In the strict 2-category of categories fibred in groupoids the associator of
`CategoryTheory.Bicategory.TwoCommSq.postcomposeSnd` is an identity 2-cell, and this is the filler
with it cancelled: the given filler followed by the inverse of the cospan's comparison 2-cell,
whiskered by the second leg. -/
theorem postcomposeSnd_iso_hom_strict {F : 𝒱' ⟶ 𝒴} {G : 𝒰 ⟶ 𝒴}
    (Z : Bicategory.TwoCommSq F G) {q : 𝒱 ⟶ 𝒴} (τ : 𝒰 ⟶ 𝒱) (δ : τ ≫ q ≅ G) :
    (Z.postcomposeSnd τ δ).iso.hom = Z.iso.hom ≫ (Z.snd ◁ δ.inv) := by
  exact congrArg (fun t => Z.iso.hom ≫ t) (Category.comp_id (Z.snd ◁ δ.inv))

/-- **The filler of the second-factor cancellation of Stacks 02XD, as a composite of three
whiskerings.** This is `CategoryTheory.CatFiberedInGroupoids.cancelSndSquare_iso` read on the
`hom` component, with the three associators that the strict 2-category makes identities already
cancelled. It is the `hom` companion of
`CategoryTheory.CatFiberedInGroupoids.cancelSndSquare_iso_inv`. -/
theorem cancelSndSquare_iso_hom (g : 𝒱' ⟶ 𝒴) (f : 𝒱 ⟶ 𝒴) (c : 𝒰 ⟶ 𝒱) (G : 𝒰 ⟶ 𝒴)
    (θ : c ≫ f ≅ G) :
    (cancelSndSquare.{v₁, v₂, u₁, u₂} g f c G θ).iso.hom
      = ((twoFibreProductSquare.{v₁, v₂, u₁, u₂}
            (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).snd c).fst
            ◁ (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).iso.hom)
        ≫ ((twoFibreProductSquare.{v₁, v₂, u₁, u₂}
            (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).snd c).iso.hom ▷ f)
        ≫ ((twoFibreProductSquare.{v₁, v₂, u₁, u₂}
            (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).snd c).snd ◁ θ.hom) := rfl

/-- **The inverse filler of the first-factor cancellation of Stacks 02XD, as a composite of three
whiskerings.** The `inv` companion of
`CategoryTheory.CatFiberedInGroupoids.cancelFstSquare_iso_hom`, which is the direction a consumer
reading the square through `CategoryTheory.Bicategory.TwoCommSq.swap` needs. -/
theorem cancelFstSquare_iso_inv (g : 𝒱' ⟶ 𝒴) (f : 𝒱 ⟶ 𝒴) (c : 𝒰 ⟶ 𝒱') (G : 𝒰 ⟶ 𝒴)
    (θ : c ≫ g ≅ G) :
    (cancelFstSquare.{v₁, v₂, u₁, u₂} g f c G θ).iso.inv
      = (((twoFibreProductSquare.{v₁, v₂, u₁, u₂}
            (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).fst c).snd ◁ θ.inv)
          ≫ ((twoFibreProductSquare.{v₁, v₂, u₁, u₂}
            (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).fst c).iso.inv ▷ g))
        ≫ ((twoFibreProductSquare.{v₁, v₂, u₁, u₂}
            (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).fst c).fst
            ◁ (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).iso.hom) := rfl

/-! ### Bookkeeping, named in a plain category -/

/-- Cancelling the last two factors of a five-term composite against the two before them, and the
identity the strict bicategory's unitors leave at the front. Stated for an abstract category so
that the associativity rearrangement is available to `rw`, which it is not inside a composite of
whiskerings. -/
private theorem cancel_tail_two {D : Type*} [Category D] {X0 X1 X2 X3 : D}
    (a : X0 ⟶ X1) (b : X1 ⟶ X2) (c : X2 ⟶ X3) (c' : X3 ⟶ X2) (b' : X2 ⟶ X1) (i : X0 ⟶ X0)
    (hi : i = 𝟙 X0) (hc : c ≫ c' = 𝟙 X2) (hb : b ≫ b' = 𝟙 X1) :
    ((a ≫ b ≫ c) ≫ c') ≫ b' = i ≫ a := by
  rw [hi, Category.id_comp]
  have h : (b ≫ c) ≫ c' ≫ b' = 𝟙 X1 := by
    rw [Category.assoc b c (c' ≫ b'), ← Category.assoc c c' b', hc, Category.id_comp, hb]
  rw [Category.assoc (a ≫ b ≫ c) c' b', Category.assoc a (b ≫ c) (c' ≫ b'), h,
    Category.comp_id]

/-- Cancelling the first factor of a composite against the one after it, and the identity at the
end. Stated for an abstract category for the same reason as `cancel_tail_two`. -/
private theorem cancel_head_two {D : Type*} [Category D] {X0 X1 X2 X3 : D}
    (a : X0 ⟶ X1) (a' : X1 ⟶ X0) (b : X0 ⟶ X2) (c : X2 ⟶ X3) (i : X3 ⟶ X3)
    (hi : i = 𝟙 X3) (ha : a ≫ a' = 𝟙 X0) :
    (a ≫ ((a' ≫ b) ≫ c)) ≫ i = b ≫ c := by
  rw [hi, Category.comp_id, Category.assoc a' b c, ← Category.assoc a a' (b ≫ c), ha,
    Category.id_comp]

/-- Removing the four identities that a strict bicategory's associators leave in a composite of
three factors. Stated for an abstract category for the same reason as `cancel_tail_two`. -/
private theorem id_chain6 {D : Type*} [Category D] {X0 X1 X2 X3 : D}
    (a : X0 ⟶ X1) (b : X1 ⟶ X2) (c : X2 ⟶ X3) :
    (((((𝟙 X0 ≫ a) ≫ 𝟙 X1) ≫ b) ≫ 𝟙 X2) ≫ c) ≫ 𝟙 X3 = a ≫ b ≫ c := by simp

/-! ### The two squares over a postcomposed cospan agree on the nose -/

/-- **Exchanging the legs of a square read over a postcomposed cospan gives the same filler as
reading the exchanged square over the exchanged postcomposed cospan.**
`CategoryTheory.Bicategory.TwoCommSq.swap_postcompose` says the two squares are equal; the two
have the same apex and the same two legs definitionally, so this identity of fillers is the whole
of that equality, in the form that lets a pre-morphism out of one be rebuilt as a pre-morphism out
of the other without transporting it. -/
theorem swap_postcompose_iso_hom {F : 𝒰 ⟶ 𝒳} {G : 𝒱 ⟶ 𝒳} (Z : Bicategory.TwoCommSq F G)
    (f : 𝒳 ⟶ 𝒴) {p : 𝒜 ⟶ 𝒴} {q : 𝒞 ⟶ 𝒴} (σ : 𝒰 ⟶ 𝒜) (τ : 𝒱 ⟶ 𝒞)
    (ε : σ ≫ p ≅ F ≫ f) (δ : τ ≫ q ≅ G ≫ f) :
    (Z.postcompose f σ τ ε δ).swap.iso.hom = (Z.swap.postcompose f τ σ δ ε).iso.hom := by
  rw [postcompose_iso_hom_strict.{v₁, v₂, u₁, u₂} Z.swap f τ σ δ ε]
  change (((((𝟙 _ ≫ (Z.snd ◁ δ.hom)) ≫ 𝟙 _) ≫ (Z.iso.inv ▷ f)) ≫ 𝟙 _)
      ≫ (Z.fst ◁ ε.inv)) ≫ 𝟙 _ = _
  exact id_chain6 _ _ _

/-! ### The two pre-morphisms -/

/-- **The second-factor cancellation of Stacks 02XD, read back over its own cospan, maps to the
canonical 2-fibre product (Stacks 003O).** Take the canonical square `𝒱' ×_𝒴 𝒱`, cancel its second
factor along `cc : 𝒰 ⟶ 𝒱` as in Stacks 02XD — giving a square over `(bb', GG)` with apex
`(𝒱' ×_𝒴 𝒱) ×_𝒱 𝒰` — and read that back over `(bb', bb)` by changing its second leg along `θ`.
The outer projection is then a pre-morphism to `𝒱' ×_𝒴 𝒱` itself, with its first comparison 2-cell
an identity and its second the inverse filler of the outer product.

The underlying 1-morphism is the outer projection on the nose, which is what a chase needs when
that projection carries a property of its own. -/
def cancelSndPostcomposeSndPreHom (bb' : 𝒱' ⟶ 𝒴) (bb : 𝒱 ⟶ 𝒴) (cc : 𝒰 ⟶ 𝒱) (GG : 𝒰 ⟶ 𝒴)
    (θ : cc ≫ bb ≅ GG) :
    Bicategory.TwoCommSq.PreHom
      ((cancelSndSquare.{v₁, v₂, u₁, u₂} bb' bb cc GG θ).postcomposeSnd cc θ)
      (twoFibreProductSquare.{v₁, v₂, u₁, u₂} bb' bb) :=
  preHomOfStrict.{v₁, v₂, u₁, u₂}
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
      (twoFibreProductSquare.{v₁, v₂, u₁, u₂} bb' bb).snd cc).fst
    (Iso.refl _)
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
      (twoFibreProductSquare.{v₁, v₂, u₁, u₂} bb' bb).snd cc).iso.symm
    (by
      rw [postcomposeSnd_iso_hom_strict.{v₁, v₂, u₁, u₂},
        cancelSndSquare_iso_hom.{v₁, v₂, u₁, u₂}]
      exact cancel_tail_two _ _ _ _ _ _
        ((congrArg (fun t => t ▷ bb') (Iso.refl_hom _)).trans (id_whiskerRight _ _))
        (Bicategory.whiskerLeftIso
          (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
            (twoFibreProductSquare.{v₁, v₂, u₁, u₂} bb' bb).snd cc).snd θ).hom_inv_id
        (Bicategory.whiskerRightIso
          (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
            (twoFibreProductSquare.{v₁, v₂, u₁, u₂} bb' bb).snd cc).iso bb).hom_inv_id)

/-- **The first-factor cancellation of Stacks 02XD, read back over its own cospan and with its
legs exchanged, maps to the canonical 2-fibre product (Stacks 003O).** The companion of
`CategoryTheory.CatFiberedInGroupoids.cancelSndPostcomposeSndPreHom`: the first-factor
cancellation along `cc : 𝒰 ⟶ 𝒱'` has apex `(𝒱' ×_𝒴 𝒱) ×_{𝒱'} 𝒰` and lies over `(bb, GG)`, so
reading it back over its own cospan gives a square over `(bb, bb')` and the two legs have to be
exchanged. The two comparison 2-cells are therefore the other way round: the first is the inverse
filler of the outer product and the second is an identity. -/
def cancelFstPostcomposeSndPreHom (bb' : 𝒱' ⟶ 𝒴) (bb : 𝒱 ⟶ 𝒴) (cc : 𝒰 ⟶ 𝒱') (GG : 𝒰 ⟶ 𝒴)
    (θ : cc ≫ bb' ≅ GG) :
    Bicategory.TwoCommSq.PreHom
      ((cancelFstSquare.{v₁, v₂, u₁, u₂} bb' bb cc GG θ).postcomposeSnd cc θ).swap
      (twoFibreProductSquare.{v₁, v₂, u₁, u₂} bb' bb) :=
  preHomOfStrict.{v₁, v₂, u₁, u₂}
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
      (twoFibreProductSquare.{v₁, v₂, u₁, u₂} bb' bb).fst cc).fst
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
      (twoFibreProductSquare.{v₁, v₂, u₁, u₂} bb' bb).fst cc).iso.symm
    (Iso.refl _)
    (by
      rw [postcomposeSnd_swap_iso_hom.{v₁, v₂, u₁, u₂},
        cancelFstSquare_iso_inv.{v₁, v₂, u₁, u₂}]
      exact cancel_head_two _ _ _ _ _
        ((congrArg (fun t => t ▷ bb) (Iso.refl_hom _)).trans (id_whiskerRight _ _))
        (Bicategory.whiskerLeftIso
          (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
            (twoFibreProductSquare.{v₁, v₂, u₁, u₂} bb' bb).fst cc).snd θ).hom_inv_id)

end CategoryTheory.CatFiberedInGroupoids

end

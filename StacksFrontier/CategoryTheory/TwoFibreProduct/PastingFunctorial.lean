module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting

/-!
# Functoriality of pasting along the first projection

Pasting a 2-commutative square `P` over a cospan `(g, f)` with a square over the inner cospan
`(k, P.fst)` is a construction on the inner square
(`CategoryTheory.Bicategory.TwoCommSq.pasteFst`), and this file records that it is functorial in
it: a pre-morphism of inner squares induces a pre-morphism of the outer rectangles, with the same
underlying 1-morphism.

This is the first-projection counterpart of
`CategoryTheory.Bicategory.TwoCommSq.PreHom.paste`, and it is what a base-change argument needs:
a comparison 1-morphism into a 2-fibre product of the inner cospan is, unchanged, a comparison
into a 2-fibre product of the composed cospan.

## Main definitions

* `CategoryTheory.Bicategory.pasteFstOuterPreHom`: the canonical pre-morphism of a pasted
  rectangle, reassociated over the outer cospan, onto the square it was pasted with.
* `CategoryTheory.Bicategory.TwoCommSq.PreHom.pasteFst`: the induced pre-morphism of outer
  rectangles.

## Main results

* `CategoryTheory.Bicategory.TwoCommSq.PreHom.pasteFst_hom`: the induced pre-morphism has the
  same underlying 1-morphism.
-/

@[expose] public section

namespace CategoryTheory.Bicategory

universe w v u

variable {A : Type u} [Bicategory.{w, v} A]

variable {X Y Z T : A} {g : Z ⟶ Y} {f : X ⟶ Y}

/-- Cancelling an associator against its inverse across an identity whiskering, at the
bracketing in which the filler of a pasted rectangle presents it. -/
private theorem assoc_inv_id_whiskerRight_assoc {W X' Y' Z' : A} (m : W ⟶ X') (n : X' ⟶ Y')
    (r : Y' ⟶ Z') {F G H : W ⟶ Z'} (x : F ⟶ G) (y : G ⟶ H) (z : H ⟶ m ≫ n ≫ r) :
    (x ≫ y ≫ z ≫ (α_ m n r).inv) ≫ (𝟙 (m ≫ n) ▷ r) ≫ (α_ m n r).hom = x ≫ y ≫ z := by
  rw [id_whiskerRight, Category.id_comp, Category.assoc, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

-- the compatibility square is stated against the projections of `pasteFst`, whose filler is a
-- composite of five structural 2-cells; without the local attribute the goal is not type-correct
-- at `implicit` transparency and neither `simp` nor `rw` fires on it
attribute [local implicit_reducible] TwoCommSq.pasteFst in
/-- **The canonical pre-morphism of a pasted rectangle onto the square it was pasted with.** The
rectangle `P.pasteFst D`, read over the cospan `(g, f)` by composing its first projection with
`k`, maps to `P` by the inner square's second projection, the comparison against `P.fst` being
the inner square's own filler. -/
def pasteFstOuterPreHom (P : TwoCommSq g f) {k : T ⟶ Z} (D : TwoCommSq k P.fst) :
    TwoCommSq.PreHom (pasteOuterSq k (P.pasteFst D)) P where
  hom := D.snd
  isoFst := D.iso
  isoSnd := Iso.refl _
  compat := by
    dsimp [pasteOuterSq, TwoCommSq.pasteFst]
    rw [Iso.hom_inv_id_assoc]
    simp only [whiskerRightIso_hom, whiskerLeftIso_hom]
    exact assoc_inv_id_whiskerRight_assoc D.snd P.snd f (D.iso.hom ▷ g)
      (α_ D.snd P.fst g).hom (D.snd ◁ P.iso.hom)

/-- **Pasting along the first projection is functorial in the inner square.** A pre-morphism of
squares over the inner cospan `(k, P.fst)` induces one of the rectangles pasted onto `P`, over
the cospan `(k ≫ g, f)`. -/
def TwoCommSq.PreHom.pasteFst (P : TwoCommSq g f) {k : T ⟶ Z} {D Q : TwoCommSq k P.fst}
    (m : TwoCommSq.PreHom D Q) :
    TwoCommSq.PreHom (P.pasteFst D) (P.pasteFst Q) :=
  pasteFstPreHom P Q (pasteFstOuterPreHom P D) m

/-- The pre-morphism of outer rectangles induced by a pre-morphism of inner squares has the same
underlying 1-morphism. -/
theorem TwoCommSq.PreHom.pasteFst_hom (P : TwoCommSq g f) {k : T ⟶ Z} {D Q : TwoCommSq k P.fst}
    (m : TwoCommSq.PreHom D Q) : (TwoCommSq.PreHom.pasteFst P m).hom = m.hom := rfl

end CategoryTheory.Bicategory

end

module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting

/-!
# Functoriality of reading a square over a composed cospan over the outer one

`CategoryTheory.Bicategory.pasteOuterSq k S` reads a 2-commutative square `S` over the cospan
`(k ≫ g, f)` as a square over `(g, f)`, by composing its first leg with `k`. This file records
that the operation is functorial on pre-morphisms: a pre-morphism of squares over `(k ≫ g, f)`
induces one of the reassociated squares, with the same underlying 1-morphism.

It is the first-leg counterpart of
`CategoryTheory.Bicategory.TwoCommSq.PreHom.postcomposeSnd`, and it is what lets a comparison
1-morphism into a rectangle pasted along the first projection be pushed down to the square it was
pasted onto: composed with `CategoryTheory.Bicategory.pasteFstOuterPreHom` it turns a
pre-morphism `S₁ ⟶ P.pasteFst Q` into a pre-morphism `pasteOuterSq k S₁ ⟶ P`.

## Main definitions

* `CategoryTheory.Bicategory.TwoCommSq.PreHom.pasteOuter`: the induced pre-morphism.

## Main results

* `CategoryTheory.Bicategory.TwoCommSq.PreHom.pasteOuter_hom`: it has the same underlying
  1-morphism.

## Implementation notes

The compatibility square of **Stacks 003O** is proved from an auxiliary identity in which every
2-cell is abstract, exactly as in `StacksFrontier/CategoryTheory/TwoFibreProduct/Pasting.lean`: with
the structure projections of `pasteOuterSq` in the way neither `bicategory` nor `simp` can be
pointed at the goal, whereas the abstract identity is one rewrite by the given compatibility
square followed by coherence.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
-/

@[expose] public section

namespace CategoryTheory.Bicategory

universe w v u

variable {A : Type u} [Bicategory.{w, v} A]

/-- The compatibility square of Stacks 003O for the reassociation of a pre-morphism along the
first leg, with every 2-cell abstract. -/
private theorem pasteOuter_compat_aux {w₁ w₂ tt xx yy zz : A}
    (p : w₁ ⟶ w₂) (a₁ : w₁ ⟶ tt) (b₁ : w₁ ⟶ xx) (a₂ : w₂ ⟶ tt) (b₂ : w₂ ⟶ xx)
    (kk : tt ⟶ yy) (gg : yy ⟶ zz) (ff : xx ⟶ zz)
    (σ₁ : a₁ ≫ (kk ≫ gg) ⟶ b₁ ≫ ff) (σ₂ : a₂ ≫ (kk ≫ gg) ⟶ b₂ ≫ ff)
    (φ : a₁ ⟶ p ≫ a₂) (ψ : b₁ ⟶ p ≫ b₂)
    (hu : σ₁ ≫ (ψ ▷ ff) ≫ (α_ p b₂ ff).hom =
      (φ ▷ (kk ≫ gg)) ≫ (α_ p a₂ (kk ≫ gg)).hom ≫ (p ◁ σ₂)) :
    (α_ a₁ kk gg).hom ≫ σ₁ ≫ (ψ ▷ ff) ≫ (α_ p b₂ ff).hom =
      (((φ ▷ kk) ≫ (α_ p a₂ kk).hom) ▷ gg) ≫ (α_ p (a₂ ≫ kk) gg).hom ≫
        (p ◁ ((α_ a₂ kk gg).hom ≫ σ₂)) := by
  rw [hu]
  bicategory

variable {X Y Z T : A} {g : Z ⟶ Y} {f : X ⟶ Y}

/-- **Reading a square over a composed cospan over the outer cospan is functorial.** A
pre-morphism of squares over `(k ≫ g, f)` induces one of the squares over `(g, f)` obtained by
composing the first leg with `k`, with the same underlying 1-morphism: its first comparison
2-cell is the given one whiskered by `k` and reassociated, and its second is the given one
unchanged. **Stacks 003O.** -/
def TwoCommSq.PreHom.pasteOuter {k : T ⟶ Z} {S₁ S₂ : TwoCommSq (k ≫ g) f}
    (u : TwoCommSq.PreHom S₁ S₂) :
    TwoCommSq.PreHom (pasteOuterSq k S₁) (pasteOuterSq k S₂) where
  hom := u.hom
  isoFst := whiskerRightIso u.isoFst k ≪≫ α_ u.hom S₂.fst k
  isoSnd := u.isoSnd
  compat := by
    dsimp [pasteOuterSq]
    simp only [whiskerRightIso_hom, Category.assoc]
    exact pasteOuter_compat_aux u.hom S₁.fst S₁.snd S₂.fst S₂.snd k g f S₁.iso.hom S₂.iso.hom
      u.isoFst.hom u.isoSnd.hom u.compat

/-- The reassociated pre-morphism has the same underlying 1-morphism. -/
theorem TwoCommSq.PreHom.pasteOuter_hom {k : T ⟶ Z} {S₁ S₂ : TwoCommSq (k ≫ g) f}
    (u : TwoCommSq.PreHom S₁ S₂) : (TwoCommSq.PreHom.pasteOuter u).hom = u.hom := rfl

end CategoryTheory.Bicategory

end

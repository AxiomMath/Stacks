module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.Defs

/-!
# Changing only the second leg of the cospan of a 2-commutative square (Stacks 003O)

A 2-commutative square over a cospan `F : 𝒰 ⟶ 𝒳`, `G : 𝒱 ⟶ 𝒳` in a bicategory
(`CategoryTheory.Bicategory.TwoCommSq`, **Stacks 003O**) can be read over the cospan
`F`, `q : 𝒞 ⟶ 𝒳` as soon as the second leg is compared with `q`: a 1-morphism `τ : 𝒱 ⟶ 𝒞`
together with an invertible 2-cell `τ ≫ q ≅ G`. The new square has the same apex and the same
first leg, its second leg composed with `τ`, and the given filler conjugated by that 2-cell.

This is the special case of `CategoryTheory.Bicategory.TwoCommSq.postcompose` in which the
comparison of the targets and the comparison on the first side are both identities — and it is
*not* definitionally that case, because the general construction leaves the legs composed with
identity 1-morphisms behind. Those identity factors are half the bulk of every compatibility
square a consumer then has to prove, which is why the special case is worth having: the
compatibility square of Stacks 003O for the induced pre-morphism needs the exchange law **once**
here, against twice for `TwoCommSq.postcompose`.

## Main definitions

* `CategoryTheory.Bicategory.TwoCommSq.postcomposeSnd`: the square read over the new cospan.
* `CategoryTheory.Bicategory.TwoCommSq.PreHom.postcomposeSnd`: the induced pre-morphism.

## Main results

* `CategoryTheory.Bicategory.TwoCommSq.postcomposeSnd_iso_hom`: the filler of the new square.

## Implementation notes

`TwoCommSq.postcomposeSnd` is marked `@[implicit_reducible]` for the reason recorded in
`StacksFrontier.CategoryTheory.TwoFibreProduct.Swap` and in
`StacksFrontier.CategoryTheory.TwoFibreProduct.PostcomposeCospan` for their own constructions: the
compatibility square of Stacks 003O for the induced pre-morphism is typed through the new
square's apex and projections, and without that attribute the goal is not type-correct at the
`implicit` transparency level at which Lean checks implicit arguments. Without the attribute,
`rw` fails to find the given compatibility square in the goal, reporting that the
target is not type-correct under the `implicit` transparency level.

The compatibility square needs the exchange law once, to move the comparison 2-cell of the
cospan past the pre-morphism's own comparison on the second leg, and the `bicategory` tactic does
not perform that move. So the proof is one instance of
`CategoryTheory.Bicategory.whisker_exchange_assoc`, the given compatibility square reassociated,
and two coherence identities that `bicategory` does close.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B]
variable {𝒰 𝒱 𝒳 𝒞 : B} {F : 𝒰 ⟶ 𝒳} {G : 𝒱 ⟶ 𝒳}

/-- **A 2-commutative square read over a cospan with only the second leg changed.** Let `Z` be a
2-commutative square over the cospan `(F, G)` (**Stacks 003O**) and compare its second leg with
`q : 𝒞 ⟶ 𝒳`: a 1-morphism `τ : 𝒱 ⟶ 𝒞` and an invertible 2-cell `δ : τ ≫ q ≅ G`. Then `Z` becomes
a square over `(F, q)`, with the same apex, the same first leg, its second leg composed with `τ`,
and the filler of `Z` conjugated by `δ`. -/
@[implicit_reducible]
def TwoCommSq.postcomposeSnd (Z : TwoCommSq F G) {q : 𝒞 ⟶ 𝒳} (τ : 𝒱 ⟶ 𝒞) (δ : τ ≫ q ≅ G) :
    TwoCommSq F q where
  pt := Z.pt
  fst := Z.fst
  snd := Z.snd ≫ τ
  iso := Z.iso ≪≫ whiskerLeftIso Z.snd δ.symm ≪≫ (α_ Z.snd τ q).symm

/-- The filler of a square read over a cospan with only the second leg changed: the given filler,
the comparison 2-cell of the cospan whiskered by the second leg, and one associator.

It holds by `rfl`, but it is stated because `simp` on its own does not unfold the `hom`
projection of the `whiskerLeftIso` in the definition — the same reason
`CategoryTheory.Bicategory.TwoCommSq.precompose_iso_hom` is stated in
`StacksFrontier.CategoryTheory.TwoFibreProduct.JointlyFaithful`. -/
theorem TwoCommSq.postcomposeSnd_iso_hom (Z : TwoCommSq F G) {q : 𝒞 ⟶ 𝒳} (τ : 𝒱 ⟶ 𝒞)
    (δ : τ ≫ q ≅ G) :
    (Z.postcomposeSnd τ δ).iso.hom
      = Z.iso.hom ≫ (Z.snd ◁ δ.inv) ≫ (α_ Z.snd τ q).inv := rfl

/-- **A pre-morphism of 2-commutative squares read over a cospan with only the second leg
changed.** The same 1-morphism, with its first comparison 2-cell of Stacks 003O unchanged and its
second whiskered by `τ`.

This is the point of `CategoryTheory.Bicategory.TwoCommSq.postcomposeSnd`: the compatibility
square of Stacks 003O is proved here once, so a consumer composing pre-morphisms across this
change of cospan never proves one by hand. -/
def TwoCommSq.PreHom.postcomposeSnd {Z₁ Z₂ : TwoCommSq F G} (u : TwoCommSq.PreHom Z₁ Z₂)
    {q : 𝒞 ⟶ 𝒳} (τ : 𝒱 ⟶ 𝒞) (δ : τ ≫ q ≅ G) :
    TwoCommSq.PreHom (Z₁.postcomposeSnd τ δ) (Z₂.postcomposeSnd τ δ) where
  hom := u.hom
  isoFst := u.isoFst
  isoSnd := whiskerRightIso u.isoSnd τ ≪≫ α_ u.hom Z₂.snd τ
  compat := by
    dsimp [TwoCommSq.postcomposeSnd]
    simp only [Iso.symm_hom, whiskerLeftIso_hom, whiskerRightIso_hom, Category.assoc,
      comp_whiskerRight, whiskerLeft_comp]
    rw [← reassoc_of% u.compat]
    rw [show (α_ Z₁.snd τ q).inv ≫ u.isoSnd.hom ▷ τ ▷ q ≫ (α_ u.hom Z₂.snd τ).hom ▷ q ≫
          (α_ u.hom (Z₂.snd ≫ τ) q).hom
        = u.isoSnd.hom ▷ (τ ≫ q) ≫ (α_ u.hom Z₂.snd (τ ≫ q)).hom ≫
          u.hom ◁ (α_ Z₂.snd τ q).inv from by bicategory]
    rw [whisker_exchange_assoc u.isoSnd.hom δ.inv]
    bicategory

end CategoryTheory.Bicategory

end

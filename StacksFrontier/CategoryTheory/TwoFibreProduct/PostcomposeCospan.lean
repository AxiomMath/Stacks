module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.Defs
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# Reading a 2-commutative square over a postcomposed cospan

A 2-commutative square over a cospan `F : 𝒰 ⟶ 𝒳`, `G : 𝒱 ⟶ 𝒳` in a bicategory
(`CategoryTheory.Bicategory.TwoCommSq`, Stacks 003O) can be read as a square over a *different*
cospan `p : 𝒜 ⟶ 𝒴`, `q : ℬ ⟶ 𝒴` as soon as the two cospans are compared: a 1-morphism
`f : 𝒳 ⟶ 𝒴` of the targets together with `σ : 𝒰 ⟶ 𝒜`, `τ : 𝒱 ⟶ ℬ` and invertible 2-cells
`σ ≫ p ≅ F ≫ f`, `τ ≫ q ≅ G ≫ f`. The new square has the same apex and its legs composed with
`σ` and `τ`; its filler is the given one conjugated by the two comparison 2-cells. A pre-morphism
of squares over `(F, G)` becomes one over `(p, q)` with its two comparison 2-cells whiskered.

## Main definitions

* `CategoryTheory.Bicategory.TwoCommSq.postcompose`: the square read over the new cospan.
* `CategoryTheory.Bicategory.TwoCommSq.PreHom.postcompose`: the induced pre-morphism.

## Main results

* `CategoryTheory.Bicategory.TwoCommSq.swap_postcompose`: the construction commutes with
  exchanging the two legs (`CategoryTheory.Bicategory.TwoCommSq.swap`).

## Implementation notes

`TwoCommSq.postcompose` is marked `@[implicit_reducible]`: without it `simp` reports *no progress*
on the compatibility square of the induced pre-morphism, a goal that is not type-correct at the
`implicit` transparency level.

The `bicategory` tactic does not apply the exchange law, so the compatibility square is proved by
two rewrites with `CategoryTheory.Bicategory.whisker_exchange_assoc` before `bicategory` closes it.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B]

/-! ### Three coherence identities -/

/-- Whiskering a 2-cell by a composite, read through the associators. -/
private theorem associator_inv_whiskerRight_whiskerRight {t s 𝒱 𝒞 𝒴 : B} (vv : t ⟶ s)
    (y₁ : t ⟶ 𝒱) (y₂ : s ⟶ 𝒱) (τ : 𝒱 ⟶ 𝒞) (q : 𝒞 ⟶ 𝒴) (as : y₁ ⟶ vv ≫ y₂) :
    (α_ y₁ τ q).inv ≫ as ▷ τ ▷ q ≫ (α_ vv y₂ τ).hom ▷ q ≫ (α_ vv (y₂ ≫ τ) q).hom
      = as ▷ (τ ≫ q) ≫ (α_ vv y₂ (τ ≫ q)).hom ≫ vv ◁ (α_ y₂ τ q).inv := by
  bicategory

/-- Whiskering a 2-cell by a composite 1-morphism, read through the associators. -/
private theorem associator_whiskerRight_comp {t s 𝒱 𝒳 𝒴 : B} (vv : t ⟶ s)
    (y₁ : t ⟶ 𝒱) (y₂ : s ⟶ 𝒱) (G : 𝒱 ⟶ 𝒳) (f : 𝒳 ⟶ 𝒴) (as : y₁ ⟶ vv ≫ y₂) :
    (α_ y₁ G f).hom ≫ as ▷ (G ≫ f) = (as ▷ G) ▷ f ≫ (α_ (vv ≫ y₂) G f).hom := by
  bicategory

/-- Whiskering a 2-cell by a composite 1-morphism, read through the inverse associators. -/
private theorem associator_inv_whiskerRight_comp {t s 𝒰 𝒳 𝒴 : B} (vv : t ⟶ s)
    (x₁ : t ⟶ 𝒰) (x₂ : s ⟶ 𝒰) (F : 𝒰 ⟶ 𝒳) (f : 𝒳 ⟶ 𝒴) (af : x₁ ⟶ vv ≫ x₂) :
    (α_ x₁ F f).inv ≫ (af ▷ F) ▷ f = af ▷ (F ≫ f) ≫ (α_ (vv ≫ x₂) F f).inv := by
  bicategory

/-! ### The square and the pre-morphism over the new cospan -/

variable {𝒰 𝒱 𝒳 𝒴 𝒜 𝒞 : B} {F : 𝒰 ⟶ 𝒳} {G : 𝒱 ⟶ 𝒳}

/-- **A 2-commutative square read over a postcomposed cospan.** Let `Z` be a 2-commutative square
over the cospan `(F, G)` with target `𝒳` and compare that cospan with one `(p, q)` with target
`𝒴`: a 1-morphism `f : 𝒳 ⟶ 𝒴`, 1-morphisms `σ`, `τ` on the two sides, and invertible 2-cells
`ε : σ ≫ p ≅ F ≫ f`, `δ : τ ≫ q ≅ G ≫ f`. Then `Z` becomes a square over `(p, q)`, with the same
apex, its legs composed with `σ` and `τ`, and the filler of `Z` whiskered by `f` and conjugated by
`ε` and `δ`. -/
@[implicit_reducible]
def TwoCommSq.postcompose (Z : TwoCommSq F G) (f : 𝒳 ⟶ 𝒴) {p : 𝒜 ⟶ 𝒴} {q : 𝒞 ⟶ 𝒴}
    (σ : 𝒰 ⟶ 𝒜) (τ : 𝒱 ⟶ 𝒞) (ε : σ ≫ p ≅ F ≫ f) (δ : τ ≫ q ≅ G ≫ f) :
    TwoCommSq p q where
  pt := Z.pt
  fst := Z.fst ≫ σ
  snd := Z.snd ≫ τ
  iso := α_ Z.fst σ p ≪≫ whiskerLeftIso Z.fst ε ≪≫ (α_ Z.fst F f).symm ≪≫
    whiskerRightIso Z.iso f ≪≫ α_ Z.snd G f ≪≫ whiskerLeftIso Z.snd δ.symm ≪≫
    (α_ Z.snd τ q).symm

/-- **A pre-morphism of 2-commutative squares read over a postcomposed cospan.** The same
1-morphism, with each comparison 2-cell of Stacks 003O whiskered by the corresponding leg of the
comparison of cospans. -/
def TwoCommSq.PreHom.postcompose {Z₁ Z₂ : TwoCommSq F G} (u : TwoCommSq.PreHom Z₁ Z₂)
    (f : 𝒳 ⟶ 𝒴) {p : 𝒜 ⟶ 𝒴} {q : 𝒞 ⟶ 𝒴}
    (σ : 𝒰 ⟶ 𝒜) (τ : 𝒱 ⟶ 𝒞) (ε : σ ≫ p ≅ F ≫ f) (δ : τ ≫ q ≅ G ≫ f) :
    TwoCommSq.PreHom (Z₁.postcompose f σ τ ε δ) (Z₂.postcompose f σ τ ε δ) where
  hom := u.hom
  isoFst := whiskerRightIso u.isoFst σ ≪≫ α_ u.hom Z₂.fst σ
  isoSnd := whiskerRightIso u.isoSnd τ ≪≫ α_ u.hom Z₂.snd τ
  compat := by
    dsimp [TwoCommSq.postcompose]
    simp only [Iso.symm_hom, whiskerLeftIso_hom, whiskerRightIso_hom, Category.assoc,
      comp_whiskerRight, whiskerLeft_comp]
    rw [associator_inv_whiskerRight_whiskerRight u.hom Z₁.snd Z₂.snd τ q u.isoSnd.hom,
      whisker_exchange_assoc u.isoSnd.hom δ.inv,
      reassoc_of% (associator_whiskerRight_comp u.hom Z₁.snd Z₂.snd G f u.isoSnd.hom),
      ← reassoc_of% (comp_whiskerRight Z₁.iso.hom (u.isoSnd.hom ▷ G) f),
      show Z₁.iso.hom ≫ u.isoSnd.hom ▷ G
          = (u.isoFst.hom ▷ F ≫ (α_ u.hom Z₂.fst F).hom ≫ u.hom ◁ Z₂.iso.hom)
            ≫ (α_ u.hom Z₂.snd G).inv from by rw [← u.compat]; simp]
    simp only [comp_whiskerRight, Category.assoc]
    rw [reassoc_of% (associator_inv_whiskerRight_comp u.hom Z₁.fst Z₂.fst F f u.isoFst.hom),
      whisker_exchange_assoc u.isoFst.hom ε.hom]
    bicategory

/-- **Reading a square over a postcomposed cospan commutes with exchanging its two legs.** -/
theorem TwoCommSq.swap_postcompose (Z : TwoCommSq F G) (f : 𝒳 ⟶ 𝒴) {p : 𝒜 ⟶ 𝒴} {q : 𝒞 ⟶ 𝒴}
    (σ : 𝒰 ⟶ 𝒜) (τ : 𝒱 ⟶ 𝒞) (ε : σ ≫ p ≅ F ≫ f) (δ : τ ≫ q ≅ G ≫ f) :
    (Z.postcompose f σ τ ε δ).swap = Z.swap.postcompose f τ σ δ ε := by
  dsimp only [TwoCommSq.swap, TwoCommSq.postcompose]
  congr 1
  apply Iso.ext
  simp

end CategoryTheory.Bicategory

end

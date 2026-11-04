module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CancelSndTwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFirstFactor

/-!
# Cancelling the first factor of an iterated 2-fibre product (Stacks 02XD)

Fix a base category `C` and a cospan `g : 𝒵 ⟶ 𝒴`, `f : 𝒳 ⟶ 𝒴` of categories fibred in groupoids
over `C`, together with `c : 𝒰 ⟶ 𝒵` and a 1-morphism `G : 𝒰 ⟶ 𝒴` identified with `c ≫ g` by an
invertible 2-cell `θ`. The canonical 2-fibre product squares of Stacks 003Q give the iterated
apex `(𝒵 ×_𝒴 𝒳) ×_𝒵 𝒰`, and this file exhibits that one apex as a 2-fibre product of the cospan
`(f, G)`:

```text
(𝒵 ×_𝒴 𝒳) ×_𝒵 𝒰  ≃  𝒳 ×_𝒴 𝒰
```

This is the companion of
`CategoryTheory.CatFiberedInGroupoids.isTwoFibreProduct_cancelSndSquare`, which cancels the
*second* factor of the inner product. The two are not interchangeable: the iterated apex
`(𝒵 ×_𝒴 𝒳) ×_𝒳 𝒰` of that file and the apex `(𝒵 ×_𝒴 𝒳) ×_𝒵 𝒰` of this one are different
categories, so a consumer which forms the outer product over the *first* projection of the inner
square — as the étale-smooth analogue of Stacks 06FM does, where the comparison into the fibre
product of the final diagram is a base change of the comparison of the *given* diagram — cannot
use the second-factor statement at all.

## Main definitions

* `CategoryTheory.CatFiberedInGroupoids.cancelFstSquare`: the iterated 2-fibre product, read as a
  2-commutative square over the cospan `(f, G)`.

## Main results

* `CategoryTheory.CatFiberedInGroupoids.isTwoFibreProduct_cancelFstSquare`: that square is a
  2-fibre product.

## Implementation notes

Nothing is re-proved. The whole content is that exchanging the two factors of the inner product,
`CategoryTheory.TwoFibreProductOver.swap`, carries the first projection to the second one *on the
nose*, so changing the first factor of the outer product along it —
`CategoryTheory.TwoFibreProductOver.precomposeFst` — is an equivalence over `C` from this file's
apex to the apex of the second-factor cancellation of the exchanged cospan, strictly compatible
with both outer projections and with the composite to `𝒳`. The comparison is therefore a
pre-morphism of 2-commutative squares with *identity* comparison 2-cells, and
`CategoryTheory.Bicategory.isTwoFibreProduct_of_isEquivalence_to` transports terminality along
it.

The filler is defined as the filler of the second-factor cancellation read through the
comparison, for the reason recorded in
`StacksFrontier.CategoryTheory.TwoFibreProduct.CancelSndTwoFibreProduct`: written that way the two
legs it compares are definitionally the composites of the comparison with the legs of that
square, so the Stacks 003O compatibility square holds with identity comparison 2-cells.

No `@[stacks 02XD]` attribute: that tag stays on
`CategoryTheory.Limits.CategoricalPullback.assocComp` in
`StacksFrontier.CategoryTheory.TwoFibreProduct.Cancellation`, as the records of
`StacksFrontier.CategoryTheory.TwoFibreProduct.OverDiagonalBaseChange` and
`StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalSquare` already rule.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.CatFiberedInGroupoids

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
  {𝒵 𝒳 𝒴 𝒰 : CatFiberedInGroupoids.{v₁, max v₁ v₂, u₁, max (max u₁ u₂) (max v₁ v₂)} C}

section

variable (g : 𝒵 ⟶ 𝒴) (f : 𝒳 ⟶ 𝒴) (c : 𝒰 ⟶ 𝒵) (G : 𝒰 ⟶ 𝒴) (θ : c ≫ g ≅ G)

/-- The comparison functor of the first-factor cancellation: changing the first factor of the
outer product along the exchange of the two factors of the inner one. -/
def cancelFstFunctor :
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).fst c).pt.val.obj ⥤
      (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂} f g).snd c).pt.val.obj :=
  TwoFibreProductOver.precomposeFst
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).pt.val.p
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂} f g).pt.val.p 𝒰.val.p 𝒵.val.p
    (TwoFibreProductOver.snd 𝒳.val.p 𝒵.val.p 𝒴.val.p f.hom.toFunctor g.hom.toFunctor)
    c.hom.toFunctor
    (TwoFibreProductOver.swap 𝒵.val.p 𝒳.val.p 𝒴.val.p g.hom.toFunctor f.hom.toFunctor)
    (TwoFibreProductOver.swap_comp_structureFunctor ..)

/-- `CategoryTheory.CatFiberedInGroupoids.cancelFstFunctor` is an equivalence of categories: the
exchange of the two factors of the inner product is one, and changing the first factor of a
2-fibre product over `C` along an equivalence over `C` is one. -/
theorem isEquivalence_cancelFstFunctor :
    (cancelFstFunctor.{v₁, v₂, u₁, u₂} g f c).IsEquivalence := by
  have hsw : (TwoFibreProductOver.swap 𝒵.val.p 𝒳.val.p 𝒴.val.p g.hom.toFunctor
      f.hom.toFunctor).IsEquivalence := inferInstance
  exact TwoFibreProductOver.isEquivalence_precomposeFst
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).pt.val.p
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂} f g).pt.val.p 𝒰.val.p 𝒵.val.p
    (TwoFibreProductOver.snd 𝒳.val.p 𝒵.val.p 𝒴.val.p f.hom.toFunctor g.hom.toFunctor)
    c.hom.toFunctor
    (TwoFibreProductOver.swap 𝒵.val.p 𝒳.val.p 𝒴.val.p g.hom.toFunctor f.hom.toFunctor)
    (TwoFibreProductOver.swap_comp_structureFunctor ..)
    𝒰.isFiberedInGroupoids
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).pt.isFiberedInGroupoids
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂} f g).pt.isFiberedInGroupoids
    hsw TwoFibreProductOver.snd_comp_eq

/-- The comparison 1-morphism of the first-factor cancellation, read in the 2-category of
categories fibred in groupoids:
`(𝒵 ×_𝒴 𝒳) ×_𝒵 𝒰 ⟶ (𝒳 ×_𝒴 𝒵) ×_𝒵 𝒰`. -/
def cancelFstMor :
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).fst c).pt ⟶
      (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂} f g).snd c).pt :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := cancelFstFunctor.{v₁, v₂, u₁, u₂} g f c
      w := TwoFibreProductOver.precomposeFst_comp_structureFunctor .. }

/-- The cospan `(f, G)` read on the iterated 2-fibre product `(𝒵 ×_𝒴 𝒳) ×_𝒵 𝒰`: the projection
to `𝒳` is the composite of the outer projection with the *second* projection of the inner square,
and the projection to `𝒰` is the outer one.

The filler is the filler of the second-factor cancellation of the exchanged cospan read through
the comparison `CategoryTheory.CatFiberedInGroupoids.cancelFstMor`. -/
def cancelFstSquare : Bicategory.TwoCommSq f G where
  pt := (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).fst c).pt
  fst := (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
      (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).fst c).fst ≫
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).snd
  snd := (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).fst c).snd
  iso := Bicategory.whiskerLeftIso (cancelFstMor.{v₁, v₂, u₁, u₂} g f c)
    (cancelSndSquare.{v₁, v₂, u₁, u₂} f g c G θ).iso

/-- The comparison, as a pre-morphism of 2-commutative squares over the cospan `(f, G)`. Both
comparison 2-cells are identities, by the nose-compatibility of
`CategoryTheory.TwoFibreProductOver.precomposeFst` with the outer projections and of
`CategoryTheory.TwoFibreProductOver.swap` with the two inner ones. -/
def cancelFstPreHom :
    Bicategory.TwoCommSq.PreHom (cancelFstSquare.{v₁, v₂, u₁, u₂} g f c G θ)
      (cancelSndSquare.{v₁, v₂, u₁, u₂} f g c G θ) where
  hom := cancelFstMor.{v₁, v₂, u₁, u₂} g f c
  isoFst := Iso.refl _
  isoSnd := Iso.refl _
  compat := by
    apply Bicategory.InducedBicategory.hom₂_ext
    apply BasedNatTrans.ext
    ext P
    change (cancelSndSquare.{v₁, v₂, u₁, u₂} f g c G θ).iso.hom.hom.toNatTrans.app
          ((cancelFstFunctor.{v₁, v₂, u₁, u₂} g f c).obj P) ≫
        G.hom.toFunctor.map (𝟙 _) ≫ 𝟙 _
      = f.hom.toFunctor.map (𝟙 _) ≫ 𝟙 _ ≫
        (cancelSndSquare.{v₁, v₂, u₁, u₂} f g c G θ).iso.hom.hom.toNatTrans.app
          ((cancelFstFunctor.{v₁, v₂, u₁, u₂} g f c).obj P)
    exact map_id_comp_id_eq f.hom.toFunctor G.hom.toFunctor _

/-- **The first-factor cancellation as a statement about 2-fibre products.** The iterated
2-fibre product `(𝒵 ×_𝒴 𝒳) ×_𝒵 𝒰`, with the composite of its outer projection and the second
projection of the inner square to `𝒳` and its own outer projection to `𝒰`, is a 2-fibre product
of the cospan `f : 𝒳 ⟶ 𝒴`, `G : 𝒰 ⟶ 𝒴`. -/
noncomputable def isTwoFibreProduct_cancelFstSquare :
    Bicategory.IsTwoFibreProduct (cancelFstSquare.{v₁, v₂, u₁, u₂} g f c G θ) :=
  Bicategory.isTwoFibreProduct_of_isEquivalence_to
    (isTwoFibreProduct_cancelSndSquare.{v₁, v₂, u₁, u₂} f g c G θ)
    (cancelFstPreHom.{v₁, v₂, u₁, u₂} g f c G θ)
    (isEquivalence_cancelFstFunctor.{v₁, v₂, u₁, u₂} g f c)

end

end CategoryTheory.CatFiberedInGroupoids

end

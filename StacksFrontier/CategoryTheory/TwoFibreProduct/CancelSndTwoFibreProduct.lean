module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverCancelSndInverse

/-!
# An iterated 2-fibre product is a 2-fibre product of the outer cospan (Stacks 02XD)

Fix a base category `C` and a cospan `g : 𝒵 ⟶ 𝒴`, `f : 𝒳 ⟶ 𝒴` of categories fibred in groupoids
over `C`, together with `c : 𝒰 ⟶ 𝒳` and a 1-morphism `G : 𝒰 ⟶ 𝒴` identified with `c ≫ f` by an
invertible 2-cell `θ`. The canonical 2-fibre product squares of Stacks 003Q
(`CategoryTheory.CatFiberedInGroupoids.twoFibreProductSquare`) give the iterated apex
`(𝒵 ×_𝒴 𝒳) ×_𝒳 𝒰`, and this file exhibits that one apex as a 2-fibre product of the *outer*
cospan `(g, G)` as well:

```text
(𝒵 ×_𝒴 𝒳) ×_𝒳 𝒰  ≃  𝒵 ×_𝒴 𝒰
```

This is **Stacks 02XD** read as a statement about 2-fibre products rather than about apexes. The
difference matters, and it is the whole point of the file. The comparison functor
`CategoryTheory.TwoFibreProductOver.cancelSnd` and its quasi-inverse identify the two apexes as
categories over `C`; that identification says nothing about the two projections, so it cannot be
used to recognise a projection of one apex as a base change. Here the conclusion is
`CategoryTheory.Bicategory.IsTwoFibreProduct` of the one apex over the outer cospan, so Stacks
045B, 045C and 0300 — every statement whose hypothesis is "this square is a 2-fibre product" —
apply to the iterated apex with its outer projections directly.

## Main definitions

* `CategoryTheory.CatFiberedInGroupoids.cancelSndSquare`: the iterated 2-fibre product, read as a
  2-commutative square over the outer cospan `(g, G)`.

## Main results

* `CategoryTheory.CatFiberedInGroupoids.isTwoFibreProduct_cancelSndSquare`: that square is a
  2-fibre product.

## Implementation notes

The proof transports terminality along an isomorphism in the category of 2-commutative squares of
Stacks 003O, whose morphisms are pre-morphisms modulo the 2-cell equivalence. One half of the
isomorphism is free: both composites into the canonical square `𝒵 ×_𝒴 𝒰` agree because that
square is terminal. The other half is the unit of the cancellation equivalence, and the two
conditions of the 2-cell equivalence hold because that unit is an identity along both
projections — `CategoryTheory.TwoFibreProductOver.cancelSndUnitIso_hom_app_a_a` and
`CategoryTheory.TwoFibreProductOver.cancelSndUnitIso_hom_app_b`.

Both comparison 2-cells of both pre-morphisms are identities, by the four strict compatibilities
`CategoryTheory.TwoFibreProductOver.cancelSnd_comp_fst`, `cancelSnd_comp_snd`,
`cancelSndInv_comp_fst_comp_fst` and `cancelSndInv_comp_snd`. That is why the compatibility
square of Stacks 003O reduces, in both cases, to the componentwise statement that the 2-cell of
the iterated square is the 2-cell of the canonical one read through the comparison; in the
2-category of categories fibred in groupoids the associators and unitors are identities on the
nose, since `CategoryTheory.BasedCategory` is a strict bicategory whose associator and unitors are
literally `CategoryTheory.BasedNatIso.id`.

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

variable (g : 𝒵 ⟶ 𝒴) (f : 𝒳 ⟶ 𝒴) (c : 𝒰 ⟶ 𝒳) (G : 𝒰 ⟶ 𝒴) (θ : c ≫ f ≅ G)

/-- The comparison 1-morphism of Stacks 02XD, read in the 2-category of categories fibred in
groupoids: `(𝒵 ×_𝒴 𝒳) ×_𝒳 𝒰 ⟶ 𝒵 ×_𝒴 𝒰`. -/
def cancelSndMor :
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).snd c).pt ⟶
      (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g G).pt :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.cancelSnd 𝒵.val.p 𝒳.val.p 𝒴.val.p 𝒰.val.p
        g.hom.toFunctor f.hom.toFunctor c.hom.toFunctor G.hom.toFunctor f.hom.w
        (underlyingIso θ) (fun u => θ.hom.hom.isHomLift' u)
      w := TwoFibreProductOver.cancelSnd_comp_structureFunctor .. }

/-- The quasi-inverse comparison 1-morphism of Stacks 02XD, read in the 2-category of categories
fibred in groupoids: `𝒵 ×_𝒴 𝒰 ⟶ (𝒵 ×_𝒴 𝒳) ×_𝒳 𝒰`. -/
def cancelSndInvMor :
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g G).pt ⟶
      (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).snd c).pt :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.cancelSndInv 𝒵.val.p 𝒳.val.p 𝒴.val.p 𝒰.val.p
        g.hom.toFunctor f.hom.toFunctor c.hom.toFunctor G.hom.toFunctor c.hom.w
        (underlyingIso θ) (fun u => θ.hom.hom.isHomLift' u)
      w := TwoFibreProductOver.cancelSndInv_comp_structureFunctor .. }

/-- The outer cospan `(g, G)` read on the iterated 2-fibre product `(𝒵 ×_𝒴 𝒳) ×_𝒳 𝒰`: the
projection to `𝒵` is the composite of the two projections and the projection to `𝒰` is the outer
one.

The filler is the filler of the canonical square `𝒵 ×_𝒴 𝒰` read through the comparison
`CategoryTheory.CatFiberedInGroupoids.cancelSndMor`. That is the same 2-cell as the one assembled
from the two fillers and from `θ` — at an object `((U, z, x, ψ), u, φ)` both are
`θ_u ∘ f(φ) ∘ ψ` — and it is written this way because the two legs it compares are then
*definitionally* the composites of the comparison with the legs of the canonical square, which is
what makes the compatibility square of Stacks 003O hold for the comparison with identity
comparison 2-cells. -/
def cancelSndSquare : Bicategory.TwoCommSq g G where
  pt := (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).snd c).pt
  fst := (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
      (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).snd c).fst ≫
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).fst
  snd := (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).snd c).snd
  iso := Bicategory.whiskerLeftIso (cancelSndMor.{v₁, v₂, u₁, u₂} g f c G θ)
    (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g G).iso

/-- The comparison, as a pre-morphism of 2-commutative squares over the outer cospan. Both
comparison 2-cells are identities, by
`CategoryTheory.TwoFibreProductOver.cancelSnd_comp_fst` and
`CategoryTheory.TwoFibreProductOver.cancelSnd_comp_snd`. -/
def cancelSndPreHom :
    Bicategory.TwoCommSq.PreHom (cancelSndSquare.{v₁, v₂, u₁, u₂} g f c G θ)
      (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g G) where
  hom := cancelSndMor.{v₁, v₂, u₁, u₂} g f c G θ
  isoFst := Iso.refl _
  isoSnd := Iso.refl _
  compat := by
    apply Bicategory.InducedBicategory.hom₂_ext
    apply BasedNatTrans.ext
    ext P
    exact map_id_comp_id_eq g.hom.toFunctor G.hom.toFunctor _

/-- The quasi-inverse comparison, as a pre-morphism of 2-commutative squares over the outer
cospan. Both comparison 2-cells are identities, by
`CategoryTheory.TwoFibreProductOver.cancelSndInv_comp_fst_comp_fst` and
`CategoryTheory.TwoFibreProductOver.cancelSndInv_comp_snd`, and the two fillers agree by
`CategoryTheory.TwoFibreProductOver.cancelSndObj_cancelSndInvObj_iso_hom`. -/
def cancelSndInvPreHom :
    Bicategory.TwoCommSq.PreHom (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g G)
      (cancelSndSquare.{v₁, v₂, u₁, u₂} g f c G θ) where
  hom := cancelSndInvMor.{v₁, v₂, u₁, u₂} g f c G θ
  isoFst := Iso.refl _
  isoSnd := Iso.refl _
  compat := by
    apply Bicategory.InducedBicategory.hom₂_ext
    apply BasedNatTrans.ext
    ext Q
    exact map_id_comp_id_eq_of_eq g.hom.toFunctor G.hom.toFunctor
      (TwoFibreProductOver.cancelSndObj_cancelSndInvObj_iso_hom 𝒵.val.p 𝒳.val.p 𝒴.val.p 𝒰.val.p
        g.hom.toFunctor f.hom.toFunctor c.hom.toFunctor G.hom.toFunctor f.hom.w c.hom.w
        (underlyingIso θ) (fun u => θ.hom.hom.isHomLift' u) Q).symm

/-- The unit of the cancellation equivalence, as a 2-isomorphism of the 2-category of categories
fibred in groupoids. -/
noncomputable def cancelSndUnitTwoIso :
    cancelSndMor.{v₁, v₂, u₁, u₂} g f c G θ ≫ cancelSndInvMor.{v₁, v₂, u₁, u₂} g f c G θ ≅
      𝟙 (twoFibreProductSquare.{v₁, v₂, u₁, u₂}
        (twoFibreProductSquare.{v₁, v₂, u₁, u₂} g f).snd c).pt :=
  Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso
    (TwoFibreProductOver.cancelSndUnitIso 𝒵.val.p 𝒳.val.p 𝒴.val.p 𝒰.val.p
      g.hom.toFunctor f.hom.toFunctor c.hom.toFunctor G.hom.toFunctor f.hom.w c.hom.w
      (underlyingIso θ) (fun u => θ.hom.hom.isHomLift' u))
    (fun P => TwoFibreProductOver.cancelSndUnitIso_hom_app_isHomLift 𝒵.val.p 𝒳.val.p 𝒴.val.p
      𝒰.val.p g.hom.toFunctor f.hom.toFunctor c.hom.toFunctor G.hom.toFunctor f.hom.w c.hom.w
      (underlyingIso θ) (fun u => θ.hom.hom.isHomLift' u) P))

/-- The canonical 2-fibre product `𝒵 ×_𝒴 𝒰` and the iterated one `(𝒵 ×_𝒴 𝒳) ×_𝒳 𝒰` are
isomorphic as objects of the category of 2-commutative squares over `(g, G)`. One of the two
identities is free, both composites into `𝒵 ×_𝒴 𝒰` agreeing because that square is terminal; the
other is the unit of the cancellation equivalence. -/
noncomputable def cancelSndSquareIso :
    twoFibreProductSquare.{v₁, v₂, u₁, u₂} g G ≅ cancelSndSquare.{v₁, v₂, u₁, u₂} g f c G θ where
  hom := _root_.Quotient.mk _ (cancelSndInvPreHom.{v₁, v₂, u₁, u₂} g f c G θ)
  inv := _root_.Quotient.mk _ (cancelSndPreHom.{v₁, v₂, u₁, u₂} g f c G θ)
  hom_inv_id :=
    (isTwoFibreProduct_twoFibreProductSquare.{v₁, v₂, u₁, u₂} g G).hom_ext _ _
  inv_hom_id := by
    refine _root_.Quotient.sound ⟨cancelSndUnitTwoIso.{v₁, v₂, u₁, u₂} g f c G θ, ?_, ?_⟩ <;>
    · apply Bicategory.InducedBicategory.hom₂_ext
      apply BasedNatTrans.ext
      ext P
      change (𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _) ≫ 𝟙 _ = 𝟙 _
      simp

/-- **Stacks 02XD as a statement about 2-fibre products.** The iterated 2-fibre product
`(𝒵 ×_𝒴 𝒳) ×_𝒳 𝒰`, with the composite of its two projections to `𝒵` and its own projection to
`𝒰`, is a 2-fibre product of the outer cospan `g : 𝒵 ⟶ 𝒴`, `G : 𝒰 ⟶ 𝒴`.

Deliberately untagged: the `02XD` tag stays on
`CategoryTheory.Limits.CategoricalPullback.assocComp` in
`StacksFrontier.CategoryTheory.TwoFibreProduct.Cancellation`, as the records of
`StacksFrontier.CategoryTheory.TwoFibreProduct.OverDiagonalBaseChange` and
`StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalSquare` already rule. -/
noncomputable def isTwoFibreProduct_cancelSndSquare :
    Bicategory.IsTwoFibreProduct (cancelSndSquare.{v₁, v₂, u₁, u₂} g f c G θ) :=
  IsTerminal.ofIso (isTwoFibreProduct_twoFibreProductSquare.{v₁, v₂, u₁, u₂} g G)
    (cancelSndSquareIso.{v₁, v₂, u₁, u₂} g f c G θ)

end

end CategoryTheory.CatFiberedInGroupoids

end

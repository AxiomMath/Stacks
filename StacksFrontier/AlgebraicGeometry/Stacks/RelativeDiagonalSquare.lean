module

public import StacksFrontier.AlgebraicGeometry.Stacks.ProductMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonal
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverProdDiagonal

/-!
# The 2-fibre product as a base change of the diagonal (Stacks 02XE, over the site)

Let `S` be a scheme contained in a big fppf site `B` and let `𝒯₁`, `𝒯₂`, `𝒳` be categories
fibred in groupoids over the big fppf site of `S`, with 1-morphisms `x : 𝒯₁ ⟶ 𝒳` and
`y : 𝒯₂ ⟶ 𝒳`. Stacks 02XE identifies the 2-fibre product `𝒯₁ ×_𝒳 𝒯₂` with the 2-fibre product
of the cospan

```text
x × y : 𝒯₁ × 𝒯₂ ⟶ 𝒳 × 𝒳,        Δ : 𝒳 ⟶ 𝒳 × 𝒳.
```

This file exhibits the 2-commutative square over that cospan whose apex is
`AlgebraicGeometry.Stack.twoFibreProduct` and proves that it is a 2-fibre product in the sense
of `CategoryTheory.Bicategory.IsTwoFibreProduct`, i.e. a terminal object of the category of
2-commutative squares over the cospan (Stacks 003O, 003Q). Its mathematical content — the
mediating 1-morphism, its compatibility and its uniqueness — is
`StacksFrontier.CategoryTheory.TwoFibreProduct.OverProdDiagonal`, stated for categories over an
arbitrary base; this file is the bicategorical packaging.

The point of the square is Stacks 0302: in it the projection `𝒯₁ ×_𝒳 𝒯₂ ⟶ 𝒯₁ × 𝒯₂` is a base
change of the diagonal of `𝒳`, so it is representable by algebraic spaces whenever the diagonal
is — which is condition (1) of Stacks 045G, the second clause of being an algebraic stack. With
`x = y = f : 𝒳 ⟶ 𝒴` this is the input the *relative* half of Stacks 050Q needs.

The absolute version of Stacks 02XE, for Mathlib's
`CategoryTheory.Limits.CategoricalPullback` (Stacks 003R), is in
`StacksFrontier.CategoryTheory.TwoFibreProduct.Diagonal` and does **not** give this one: the
comparison isomorphism of an object is arbitrary there and vertical here, and the two notions
are inequivalent. The `@[stacks 02XE]` tag therefore stays on the absolute version, as the
`02XC`/`02XD` tags stay on `StacksFrontier.CategoryTheory.TwoFibreProduct.Associativity` and
`.Cancellation` while their over-the-base forms live untagged in
`StacksFrontier.CategoryTheory.TwoFibreProduct.OverComposable` and `.OverComparison`.

## Main definitions

* `CategoryTheory.CatFiberedInGroupoids.productMap`: the product
  `x × y : 𝒯₁ × 𝒯₂ ⟶ 𝒳₁ × 𝒳₂` of two 1-morphisms, with independent targets.
* `AlgebraicGeometry.Stack.relativeDiagonalSquare`: the 2-commutative square.
* `AlgebraicGeometry.Stack.relativeDiagonalLift` and
  `AlgebraicGeometry.Stack.relativeDiagonalLiftCone`: the mediating 1-morphism and the
  morphism of squares it carries.

## Main results

* `AlgebraicGeometry.Stack.isTwoFibreProduct_relativeDiagonalSquare`: the square is a 2-fibre
  product.
* `AlgebraicGeometry.Stack.relativeDiagonalLiftCone_rel`: the mediating morphism of squares is
  the only one.

## Implementation notes

The universes are the saturated ones that Stacks 0302 is stated at,
`CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}`: the apex of a 2-fibre
product has object universe `max (u + 1) w v` and morphism universe `max u v`, so only at those
values are the apex, the two products `𝒯₁ × 𝒯₂`, `𝒳 × 𝒳` and the three given categories all
objects of one 2-category. `AlgebraicGeometry.Stack.twoFibreProduct`, which allows independent
universes, lands in exactly that tuple when its three arguments do.

`CategoryTheory.CatFiberedInGroupoids.productMap` is the product of two 1-morphisms with
**independent targets**, which is the shape Stacks 0303 needs; Stacks 02XE uses only its
common-target case, and that is the case the square below is built from.

## References

* [Stacks Project, Tag 02XE](https://stacks.math.columbia.edu/tag/02XE)
* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 0302](https://stacks.math.columbia.edu/tag/0302)
* [Stacks Project, Tag 050Q](https://stacks.math.columbia.edu/tag/050Q)
-/

@[expose] public section

open CategoryTheory


namespace AlgebraicGeometry.Stack

open CategoryTheory

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒯₁ 𝒯₂ 𝒳 : CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}
    (BigFppfOver B S hS)) (x : 𝒯₁ ⟶ 𝒳) (y : 𝒯₂ ⟶ 𝒳)

/-- **The over-the-site form of Stacks 02XE.** The 2-commutative square

```text
  𝒯₁ ×_𝒳 𝒯₂ ⟶ 𝒯₁ × 𝒯₂
      |            |
      |            | x × y
      v            v
      𝒳     ⟶    𝒳 × 𝒳
            Δ
```

of categories fibred in groupoids over the big fppf site of `S`, whose apex is the 2-fibre
product `AlgebraicGeometry.Stack.twoFibreProduct` of `x` and `y`. Its first projection is the
forgetful 1-morphism `(U, t₁, t₂, φ) ↦ (t₁, t₂)` to the product, its second projection is
`(U, t₁, t₂, φ) ↦ y t₂`, and the 2-cell filling it has components `(φ, 𝟙)`. -/
noncomputable def relativeDiagonalSquare :
    Bicategory.TwoCommSq (CatFiberedInGroupoids.productMap x y) (diagonal B S hS 𝒳) where
  pt := twoFibreProduct B S hS 𝒳 𝒯₁ 𝒯₂ x.hom y.hom
  fst := Bicategory.InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.toProduct 𝒯₁.val.p 𝒯₂.val.p 𝒳.val.p x.hom.toFunctor
        y.hom.toFunctor
      w := TwoFibreProductOver.toProduct_comp_structureFunctor .. }
  snd := Bicategory.InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.snd 𝒯₁.val.p 𝒯₂.val.p 𝒳.val.p x.hom.toFunctor
        y.hom.toFunctor ⋙ y.hom.toFunctor
      w := by
        have h : TwoFibreProductOver.snd 𝒯₁.val.p 𝒯₂.val.p 𝒳.val.p x.hom.toFunctor
              y.hom.toFunctor ⋙ (y.hom.toFunctor ⋙ 𝒳.val.p) =
            TwoFibreProductOver.structureFunctor 𝒯₁.val.p 𝒯₂.val.p 𝒳.val.p x.hom.toFunctor
              y.hom.toFunctor := by
          rw [y.hom.w, TwoFibreProductOver.snd_comp_eq]
        exact h }
  iso := Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso
    (TwoFibreProductOver.toProductDiagonalIso x.hom.toFunctor y.hom.toFunctor x.hom.w y.hom.w)
    (fun P => TwoFibreProductOver.structureFunctor_isHomLift _ (𝟙 P.base) P.vertical))

variable (T : Bicategory.TwoCommSq (CatFiberedInGroupoids.productMap x y) (diagonal B S hS 𝒳))

/-- The mediating 1-morphism from a 2-commutative square `T` over the same cospan into the apex
`𝒯₁ ×_𝒳 𝒯₂` of `relativeDiagonalSquare`: on an object `s` of `T` it is
`(p s, (T.fst s).x, (T.fst s).y, φ)`, with `φ` read off the two components of the 2-cell of
`T`. -/
noncomputable def relativeDiagonalLift :
    T.pt ⟶ (relativeDiagonalSquare B S hS 𝒯₁ 𝒯₂ 𝒳 x y).pt :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.coneLift x.hom.w y.hom.w T.pt.val.p T.fst.hom.toFunctor
        T.snd.hom.toFunctor (CatFiberedInGroupoids.underlyingIso T.iso) T.fst.hom.w
        (fun s => T.iso.hom.hom.isHomLift' s)
      w := TwoFibreProductOver.coneLift_comp_structureFunctor .. }

/-- `relativeDiagonalLift` as a morphism of 2-commutative squares in the sense of
Stacks 003O: its two comparison 2-isomorphisms and their compatibility square. -/
noncomputable def relativeDiagonalLiftCone :
    Bicategory.TwoCommSq.PreHom T (relativeDiagonalSquare B S hS 𝒯₁ 𝒯₂ 𝒳 x y) where
  hom := relativeDiagonalLift B S hS 𝒯₁ 𝒯₂ 𝒳 x y T
  isoFst := Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso
    (TwoFibreProductOver.coneLiftProductIso x.hom.w y.hom.w T.pt.val.p T.fst.hom.toFunctor
      T.snd.hom.toFunctor (CatFiberedInGroupoids.underlyingIso T.iso) T.fst.hom.w
      (fun s => T.iso.hom.hom.isHomLift' s))
    (fun s => TwoFibreProductOver.coneLiftProductIso_hom_app_isHomLift x.hom.w y.hom.w
      T.pt.val.p T.fst.hom.toFunctor T.snd.hom.toFunctor
      (CatFiberedInGroupoids.underlyingIso T.iso) T.fst.hom.w
      (fun s => T.iso.hom.hom.isHomLift' s) s))
  isoSnd := Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso
    (TwoFibreProductOver.coneLiftBaseIso x.hom.w y.hom.w T.pt.val.p T.fst.hom.toFunctor
      T.snd.hom.toFunctor (CatFiberedInGroupoids.underlyingIso T.iso) T.fst.hom.w
      (fun s => T.iso.hom.hom.isHomLift' s))
    (fun s => TwoFibreProductOver.coneLiftBaseIso_hom_app_isHomLift x.hom.w y.hom.w
      T.pt.val.p T.fst.hom.toFunctor T.snd.hom.toFunctor
      (CatFiberedInGroupoids.underlyingIso T.iso) T.fst.hom.w
      (fun s => T.iso.hom.hom.isHomLift' s) s))
  compat := Bicategory.InducedBicategory.hom₂_ext (BasedNatTrans.ext _ _ (NatTrans.ext (funext
    (fun s => TwoFibreProductOver.coneCompat_id x.hom.w y.hom.w T.pt.val.p T.fst.hom.toFunctor
      T.snd.hom.toFunctor (CatFiberedInGroupoids.underlyingIso T.iso) T.fst.hom.w
      (fun s => T.iso.hom.hom.isHomLift' s) s))))

variable (a : Bicategory.TwoCommSq.PreHom T (relativeDiagonalSquare B S hS 𝒯₁ 𝒯₂ 𝒳 x y))

/-- Uniqueness of the mediating morphism of 2-commutative squares: any other one is related to
`relativeDiagonalLiftCone` by the 2-cell equivalence of Stacks 003O, so the two agree in the
category `CategoryTheory.Bicategory.TwoCommSq`. -/
lemma relativeDiagonalLiftCone_rel :
    Bicategory.TwoCommSq.PreHom.Rel a (relativeDiagonalLiftCone B S hS 𝒯₁ 𝒯₂ 𝒳 x y T) := by
  have hid : ∀ s, (CatFiberedInGroupoids.underlyingIso T.iso).hom.app s ≫
      (TwoFibreProductOver.diagonal (Functor.comp_id 𝒳.val.p)).map
        ((CatFiberedInGroupoids.underlyingIso a.isoSnd).hom.app s) ≫ 𝟙 _ =
      (TwoFibreProductOver.prodMap x.hom.toFunctor y.hom.toFunctor x.hom.w y.hom.w).map
          ((CatFiberedInGroupoids.underlyingIso a.isoFst).hom.app s) ≫ 𝟙 _ ≫
        (TwoFibreProductOver.toProductDiagonalIso x.hom.toFunctor y.hom.toFunctor x.hom.w
          y.hom.w).hom.app (a.hom.hom.toFunctor.obj s) :=
    fun s => congrArg (fun b => b.hom.app s) a.compat
  refine ⟨Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso
    (TwoFibreProductOver.coneLiftIso x.hom.w y.hom.w T.pt.val.p T.fst.hom.toFunctor
      T.snd.hom.toFunctor (CatFiberedInGroupoids.underlyingIso T.iso) T.fst.hom.w
      (fun s => T.iso.hom.hom.isHomLift' s) a.hom.hom.toFunctor
      (CatFiberedInGroupoids.underlyingIso a.isoFst) (fun s => a.isoFst.hom.hom.isHomLift' s)
      (CatFiberedInGroupoids.underlyingIso a.isoSnd) hid)
    fun s => TwoFibreProductOver.coneLiftIso_hom_app_isHomLift (hc := hid) ..), ?_, ?_⟩
  all_goals
    refine Bicategory.InducedBicategory.hom₂_ext (BasedNatTrans.ext _ _ (NatTrans.ext (funext
      fun s => ?_)))
  · exact TwoFibreProductOver.coneRelFst
      (hA := T.fst.hom.w) (ht := fun s => by exact T.iso.hom.hom.isHomLift' s)
      (hiFst := fun s => by exact a.isoFst.hom.hom.isHomLift' s) (hc := hid) ..
  · exact TwoFibreProductOver.coneRelSnd
      (hA := T.fst.hom.w) (ht := fun s => by exact T.iso.hom.hom.isHomLift' s)
      (hiFst := fun s => by exact a.isoFst.hom.hom.isHomLift' s) (hc := hid) ..

/-- **The over-the-site form of Stacks 02XE.** `relativeDiagonalSquare` is a 2-fibre product
in the 2-category of categories fibred in groupoids over the big fppf site of `S`: the 2-fibre
product `𝒯₁ ×_𝒳 𝒯₂` is the 2-fibre product of `x × y : 𝒯₁ × 𝒯₂ ⟶ 𝒳 × 𝒳` and the diagonal
`Δ : 𝒳 ⟶ 𝒳 × 𝒳`.

Together with Stacks 0302
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_baseChange`) this makes the
projection `𝒯₁ ×_𝒳 𝒯₂ ⟶ 𝒯₁ × 𝒯₂` representable by algebraic spaces as soon as the diagonal of
`𝒳` is. -/
noncomputable def isTwoFibreProduct_relativeDiagonalSquare :
    Bicategory.IsTwoFibreProduct (relativeDiagonalSquare B S hS 𝒯₁ 𝒯₂ 𝒳 x y) := by
  refine CategoryTheory.Limits.IsTerminal.ofUniqueHom
    (fun T => _root_.Quotient.mk _ (relativeDiagonalLiftCone B S hS 𝒯₁ 𝒯₂ 𝒳 x y T)) ?_
  intro T a
  induction a using _root_.Quotient.inductionOn with
  | h a => exact _root_.Quotient.sound (relativeDiagonalLiftCone_rel B S hS 𝒯₁ 𝒯₂ 𝒳 x y T a)

end AlgebraicGeometry.Stack

end

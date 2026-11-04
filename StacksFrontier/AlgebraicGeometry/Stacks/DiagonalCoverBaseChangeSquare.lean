module

public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalBaseChangeSquare
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverDiagonalCoverBaseChange

/-!
# `r × r` is a base change of `r`, over the big fppf site

Let `f : 𝒳 ⟶ 𝒴` and `g : 𝒴' ⟶ 𝒴` be 1-morphisms of algebraic stacks over `S`, write
`𝒰 = 𝒳 ×_{f, 𝒴, g} 𝒴'` for the 2-fibre product of Stacks 04T2 and `r : 𝒰 ⟶ 𝒳` for its first
projection. The 1-morphism

```text
r × r : 𝒰 ×_{𝒴'} 𝒰 ⟶ 𝒳 ×_𝒴 𝒳
```

(`AlgebraicGeometry.Stack.diagonalMapDiag`) exhibits `Δ_{f'}` as a base change of `Δ_f`
(`AlgebraicGeometry.Stack.diagonalBaseChangeSquare`). This file identifies `r × r` itself, by
exhibiting the 2-commutative square

```text
            r × r
 𝒰 ×_{𝒴'} 𝒰  ----->  𝒳 ×_𝒴 𝒳
    |                   |
pr₁ |                   | pr₁
    v                   v
    𝒰  ------r------>  𝒳
```

as a 2-fibre product. So **`r × r` is a base change of `r`**, and since `r` is itself a base
change of `g`, every property of 1-morphisms stable under base change that `g` has — in
particular representability by algebraic spaces (**Stacks 0302**) and the relative properties of
**Stacks 03YK** (**Stacks 045C**) — is inherited by `r × r`.

This is an input to **Stacks 06TZ**: the quasi-DM, DM and
quasi-separated conditions of Stacks 04YW descend along `r × r` by `@[stacks 045D]`
`AlgebraicGeometry.Stack.hasRelativeProperty_of_baseChange` applied at
`AlgebraicGeometry.Stack.diagonalBaseChangeSquare`, given the local essential surjectivity of
`r × r`, which a cover transports along a base change.

## Main definitions

* `AlgebraicGeometry.Stack.diagonalCoverMor`: the comparison 1-morphism from `𝒰 ×_{𝒴'} 𝒰` into
  the canonical 2-fibre product of the cospan `(pr₁, r)`.
* `AlgebraicGeometry.Stack.diagonalCoverSquare`: the square displayed above.

## Main results

* `AlgebraicGeometry.Stack.isTwoFibreProduct_diagonalCoverSquare`: that square is a 2-fibre
  product, so `r × r` is a base change of `r`.

## Implementation notes

The mathematical content is `CategoryTheory.TwoFibreProductOver.coverComparison` and its
equivalence, over an arbitrary base category; this file is the bicategorical packaging.

Both comparison 2-cells of `AlgebraicGeometry.Stack.diagonalCoverPreHom` are **identities**,
because the comparison functor composed with the two projections of the canonical 2-fibre product
is `r × r` and the first projection of `𝒰 ×_{𝒴'} 𝒰` on the nose
(`CategoryTheory.TwoFibreProductOver.coverComparison_comp_fst` and `_comp_snd` are both `rfl`).
The Stacks 003O compatibility square then reduces to
`CategoryTheory.CatFiberedInGroupoids.map_id_comp_id_eq`, and the filler of the square is the
filler of the canonical one read through the comparison so that the two legs it compares are
*definitionally* those composites.

No declaration here carries a `@[stacks]` attribute. The statement is a 2-fibre product
recognition for an iterated 2-fibre product in the (2,1)-category of categories fibred in
groupoids, of the same kind as Stacks 02XC/02XD/04S7 but not any one of those three statements,
whose tags are on the absolute forms `CategoryTheory.Limits.CategoricalPullback.assoc`,
`CategoryTheory.Limits.CategoricalPullback.assocComp` and
`CategoryTheory.Limits.CategoricalPullback.pr₀₂`.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 045D](https://stacks.math.columbia.edu/tag/045D)
* [Stacks Project, Tag 06TZ](https://stacks.math.columbia.edu/tag/06TZ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {𝒳 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}

/-- The first projection `pr₁ : 𝒳 ×_𝒴 𝒳 ⟶ 𝒳`, read in the 2-category of categories fibred in
groupoids over the big fppf site of `S`: the first leg of the cospan of which `r × r` is a base
change. -/
noncomputable abbrev diagonalProdFst (f : 𝒳 ⟶ 𝒴) :
    twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom ⟶ 𝒳.val :=
  (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom f.hom).fst

/-- The first projection `pr₁ : 𝒰 ×_{𝒴'} 𝒰 ⟶ 𝒰` of the self-product of the base change over
`𝒴'`, read in the 2-category of categories fibred in groupoids. -/
noncomputable abbrev diagonalSelfProdFst (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴) :
    twoFibreProduct B S hS 𝒴'.val
        (twoFibreProductAlgebraicStack B S hS f g).val
        (twoFibreProductAlgebraicStack B S hS f g).val
        (twoFibreProductSquareAlgebraicStacks B S hS f g).snd.hom.hom
        (twoFibreProductSquareAlgebraicStacks B S hS f g).snd.hom.hom ⟶
      (twoFibreProductAlgebraicStack B S hS f g).val :=
  (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
    (twoFibreProductSquareAlgebraicStacks B S hS f g).snd.hom
    (twoFibreProductSquareAlgebraicStacks B S hS f g).snd.hom).fst

/-- The comparison 1-morphism `𝒰 ×_{𝒴'} 𝒰 ⟶ (𝒳 ×_𝒴 𝒳) ×_𝒳 𝒰` into the canonical 2-fibre product
of the cospan `(pr₁, r)`, read in the 2-category of categories fibred in groupoids over the big
fppf site of `S`. -/
noncomputable def diagonalCoverMor (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴) :
    twoFibreProduct B S hS 𝒴'.val
        (twoFibreProductAlgebraicStack B S hS f g).val
        (twoFibreProductAlgebraicStack B S hS f g).val
        (twoFibreProductSquareAlgebraicStacks B S hS f g).snd.hom.hom
        (twoFibreProductSquareAlgebraicStacks B S hS f g).snd.hom.hom ⟶
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (diagonalProdFst B S hS f)
        (twoFibreProductSquareAlgebraicStacks B S hS f g).fst.hom).pt :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.coverComparison
        (p𝒳 := 𝒳.val.val.p) (p𝒱 := 𝒴'.val.val.p) (p𝒴 := 𝒴.val.val.p)
        (h := f.hom.hom.toFunctor) (s := g.hom.hom.toFunctor)
        (CatFiberedInGroupoids.homFunctor_comp_p g.hom)
      w := TwoFibreProductOver.coverComparison_comp_structureFunctor .. }

/-- **The square exhibiting `r × r` as a base change of `r`.** With `𝒰 = 𝒳 ×_{f, 𝒴, g} 𝒴'` and
`r : 𝒰 ⟶ 𝒳` its first projection, this is the 2-commutative square whose apex is
`𝒰 ×_{𝒴'} 𝒰`, whose first leg is `r × r = AlgebraicGeometry.Stack.diagonalMapDiag`, whose second
leg is the first projection of `𝒰 ×_{𝒴'} 𝒰`, and whose cospan is `(pr₁, r)`.

The filler is the filler of the canonical square of that cospan read through
`AlgebraicGeometry.Stack.diagonalCoverMor`, so that the two legs it compares are definitionally
the composites of the comparison with the legs of the canonical square. -/
noncomputable def diagonalCoverSquare (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴) :
    Bicategory.TwoCommSq (diagonalProdFst B S hS f)
      (twoFibreProductSquareAlgebraicStacks B S hS f g).fst.hom where
  pt := twoFibreProduct B S hS 𝒴'.val
    (twoFibreProductAlgebraicStack B S hS f g).val
    (twoFibreProductAlgebraicStack B S hS f g).val
    (twoFibreProductSquareAlgebraicStacks B S hS f g).snd.hom.hom
    (twoFibreProductSquareAlgebraicStacks B S hS f g).snd.hom.hom
  fst := diagonalMapDiag B S hS f g
  snd := diagonalSelfProdFst B S hS f g
  iso := Bicategory.whiskerLeftIso (diagonalCoverMor B S hS f g)
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (diagonalProdFst B S hS f)
      (twoFibreProductSquareAlgebraicStacks B S hS f g).fst.hom).iso

/-- The comparison, as a pre-morphism of 2-commutative squares over the cospan `(pr₁, r)`. Both
comparison 2-cells are identities, by
`CategoryTheory.TwoFibreProductOver.coverComparison_comp_fst` and `_comp_snd`. -/
noncomputable def diagonalCoverPreHom (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴) :
    Bicategory.TwoCommSq.PreHom (diagonalCoverSquare B S hS f g)
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (diagonalProdFst B S hS f)
        (twoFibreProductSquareAlgebraicStacks B S hS f g).fst.hom) where
  hom := diagonalCoverMor B S hS f g
  isoFst := Iso.refl _
  isoSnd := Iso.refl _
  compat := by
    apply Bicategory.InducedBicategory.hom₂_ext
    apply BasedNatTrans.ext
    ext P
    change (diagonalCoverSquare B S hS f g).iso.hom.hom.toNatTrans.app P ≫
        (twoFibreProductSquareAlgebraicStacks B S hS f g).fst.hom.hom.toFunctor.map (𝟙 _) ≫
          𝟙 _ =
      (diagonalProdFst B S hS f).hom.toFunctor.map (𝟙 _) ≫ 𝟙 _ ≫
        (diagonalCoverSquare B S hS f g).iso.hom.hom.toNatTrans.app P
    exact CatFiberedInGroupoids.map_id_comp_id_eq
      (diagonalProdFst B S hS f).hom.toFunctor
      (twoFibreProductSquareAlgebraicStacks B S hS f g).fst.hom.hom.toFunctor
      ((diagonalCoverSquare B S hS f g).iso.hom.hom.toNatTrans.app P)

/-- **`r × r` is a base change of `r`.** The square
`AlgebraicGeometry.Stack.diagonalCoverSquare` is a 2-fibre product of the cospan `(pr₁, r)`: the
canonical square of that cospan is one unconditionally, the pre-morphism into it is the
comparison of `CategoryTheory.TwoFibreProductOver.coverComparison`, and that comparison is an
equivalence of categories. -/
noncomputable def isTwoFibreProduct_diagonalCoverSquare (f : 𝒳 ⟶ 𝒴) (g : 𝒴' ⟶ 𝒴) :
    Bicategory.IsTwoFibreProduct (diagonalCoverSquare B S hS f g) :=
  Bicategory.isTwoFibreProduct_of_isEquivalence_to
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      (diagonalProdFst B S hS f)
      (twoFibreProductSquareAlgebraicStacks B S hS f g).fst.hom)
    (diagonalCoverPreHom B S hS f g)
    (TwoFibreProductOver.isEquivalence_coverComparison
      (p𝒳 := 𝒳.val.val.p) (p𝒱 := 𝒴'.val.val.p) (p𝒴 := 𝒴.val.val.p)
      (h := f.hom.hom.toFunctor) (s := g.hom.hom.toFunctor)
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p g.hom))

end AlgebraicGeometry.Stack

end

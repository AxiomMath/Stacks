module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.MonomorphismEquivalentConditions
public import StacksFrontier.CategoryTheory.TwoFibreProduct.PrecomposeLegs

/-!
# The diagonal square of a monomorphism of algebraic stacks (Stacks 0CBB)

Let `f : 𝒳 ⟶ 𝒳'` and `g : 𝒳' ⟶ 𝒴` be 1-morphisms of algebraic stacks over `S`. **Stacks 0CBB**
says that if `f` is a monomorphism then the canonical square

```text
  𝒳  --Δ_{𝒳/𝒴}-->  𝒳 ×_𝒴 𝒳
  |                     |
 f|                     | f × f
  v                     v
  𝒳' --Δ_{𝒳'/𝒴}--> 𝒳' ×_𝒴 𝒳'
```

is a fibre product square, i.e. a 2-fibre product in the 2-category of algebraic stacks over
`(Sch/S)_fppf` (Stacks 03YP).

## Main definitions

* `AlgebraicGeometry.Stack.monomorphismDiagonalSquare`: the square above, in the 2-category of
  algebraic stacks. Its legs are the relative diagonal of `f ≫ g`
  (`AlgebraicGeometry.Stack.relativeDiagonalAlgebraicStacks`) and `f`, and its cospan is the
  1-morphism `f × f` of Stacks 04Z1 (`AlgebraicGeometry.Stack.comparisonCospanRight`) together with
  the relative diagonal of `g`.

## Main results

* `AlgebraicGeometry.Stack.isTwoFibreProduct_monomorphismDiagonalSquare`: **Stacks 0CBB**.

## Implementation notes

The proof is the source's, in its two steps. By **Stacks 04ZZ** the relative diagonal
`Δ_{𝒳/𝒳'} : 𝒳 ⟶ 𝒳 ×_{𝒳'} 𝒳` of the monomorphism `f` is an equivalence, which is the source's
`𝒳 = 𝒳 ×_{𝒳'} 𝒳`: this is the implication (1) ⟹ (3) of
`AlgebraicGeometry.Stack.AlgebraicStacks.isMonomorphism_tfae_of_bootstrap`, taken through the two
implications it is assembled from,
`AlgebraicGeometry.Stack.AlgebraicStacks.full_and_faithful_homFunctor_of_isMonomorphism`
((1) ⟹ (2)) and `CategoryTheory.TwoFibreProductOver.full_and_faithful_iff_isEquivalence_diagonal`
((2) ⟺ (3)). By **Stacks 04Z1** over the big fppf site
(`AlgebraicGeometry.Stack.isTwoFibreProduct_comparisonSquare`) the square

```text
  𝒳 ×_{𝒳'} 𝒳  --i-->  𝒳 ×_𝒴 𝒳
       |                  |
       v                  v
       𝒳'  --Δ_{𝒳'/𝒴}--> 𝒳' ×_𝒴 𝒳'
```

is 2-cartesian. The square of 0CBB is that square precomposed with `Δ_{𝒳/𝒳'}`: the composite
`Δ_{𝒳/𝒳'} ≫ i` is `Δ_{𝒳/𝒴}` (`AlgebraicGeometry.Stack.relativeDiagonal_comp`), and the composite
of `Δ_{𝒳/𝒳'}` with the left-hand leg is `f` on the nose. So `Δ_{𝒳/𝒳'}` is the 1-morphism of a
pre-morphism of 2-commutative squares (**Stacks 003O**) from the square of 0CBB to the square of
04Z1, and `CategoryTheory.Bicategory.isTwoFibreProduct_of_isEquivalence_to` transports the
universal property back along it. The descent from the 2-category of categories fibred in
groupoids to its full sub-2-category of algebraic stacks is
`AlgebraicGeometry.Stack.AlgebraicStacks.isTwoFibreProduct_of_toCatFiberedInGroupoids`.

All of this happens over `(Sch/S)_fppf`: the 2-fibre products are those of categories fibred in
groupoids over the base, whose comparison isomorphisms lie over identities, and the 2-cells
involved are 2-morphisms of that 2-category.

The filler of the square is the filler of the 04Z1 square whiskered by `Δ_{𝒳/𝒳'}`, read through
the identification `Δ_{𝒳/𝒳'} ≫ i = Δ_{𝒳/𝒴}`
(`CategoryTheory.Bicategory.TwoCommSq.precomposeLegs`); with that choice the pre-morphism to the
04Z1 square is `CategoryTheory.Bicategory.TwoCommSq.PreHom.ofPrecomposeLegs`, and no 2-cell has to
be computed.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04Z1](https://stacks.math.columbia.edu/tag/04Z1)
* [Stacks Project, Tag 04ZZ](https://stacks.math.columbia.edu/tag/04ZZ)
* [Stacks Project, Tag 0CBB](https://stacks.math.columbia.edu/tag/0CBB)
-/

@[expose] public noncomputable section

open CategoryTheory Bicategory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒳' 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- The identification `Δ_{𝒳/𝒴} = Δ_{𝒳/𝒳'} ≫ i` of `AlgebraicGeometry.Stack.relativeDiagonal_comp`,
as a 2-isomorphism of categories fibred in groupoids over `(Sch/S)_fppf`. -/
def relativeDiagonalCompIso (f : 𝒳 ⟶ 𝒳') (g : 𝒳' ⟶ 𝒴) :
    (relativeDiagonalAlgebraicStacks B S hS (f ≫ g)).hom ≅
      (relativeDiagonalAlgebraicStacks B S hS f).hom ≫ (comparison B S hS f f g).hom :=
  eqToIso (congrArg InducedBicategory.Hom.hom (relativeDiagonal_comp B S hS f g))

/-- The filler `Δ_{𝒳/𝒴} ≫ (f × f) ≅ f ≫ Δ_{𝒳'/𝒴}` of the square of Stacks 0CBB, as a
2-isomorphism of categories fibred in groupoids over `(Sch/S)_fppf`: the filler of the square of
Stacks 04Z1 (`AlgebraicGeometry.Stack.comparisonSquare`) for `f`, `f` and `g` whiskered by
`Δ_{𝒳/𝒳'}`, read through `AlgebraicGeometry.Stack.relativeDiagonalCompIso` on the first leg and
through the identity on the second, `Δ_{𝒳/𝒳'}` followed by the second leg of that square being
`f` on the nose. -/
def monomorphismDiagonalFiller (f : 𝒳 ⟶ 𝒳') (g : 𝒳' ⟶ 𝒴) :
    (relativeDiagonalAlgebraicStacks B S hS (f ≫ g)).hom ≫
        (comparisonCospanRight B S hS f f g).hom ≅
      f.hom ≫ (relativeDiagonalAlgebraicStacks B S hS g).hom :=
  ((comparisonSquare B S hS f f g).precomposeLegs (relativeDiagonalAlgebraicStacks B S hS f).hom
    (relativeDiagonalAlgebraicStacks B S hS (f ≫ g)).hom f.hom
    (relativeDiagonalCompIso B S hS f g) (Iso.refl _)).iso

/-- **The square of Stacks 0CBB.** For 1-morphisms `f : 𝒳 ⟶ 𝒳'` and `g : 𝒳' ⟶ 𝒴` of algebraic
stacks over `S`, the 2-commutative square

```text
  𝒳  --Δ_{𝒳/𝒴}-->  𝒳 ×_𝒴 𝒳
  |                     |
 f|                     | f × f
  v                     v
  𝒳' --Δ_{𝒳'/𝒴}--> 𝒳' ×_𝒴 𝒳'
```

in the 2-category of algebraic stacks (Stacks 03YP), at the canonical 2-fibre products of
Stacks 04T2. Its right-hand leg `f × f` is `AlgebraicGeometry.Stack.comparisonCospanRight`, which
applies `f` to both factors, its horizontal legs are the relative diagonals
`AlgebraicGeometry.Stack.relativeDiagonalAlgebraicStacks`, and its filler is
`AlgebraicGeometry.Stack.monomorphismDiagonalFiller`. -/
def monomorphismDiagonalSquare (f : 𝒳 ⟶ 𝒳') (g : 𝒳' ⟶ 𝒴) :
    TwoCommSq (comparisonCospanRight B S hS f f g) (relativeDiagonalAlgebraicStacks B S hS g) where
  pt := 𝒳
  fst := relativeDiagonalAlgebraicStacks B S hS (f ≫ g)
  snd := f
  iso := InducedBicategory.isoMk (monomorphismDiagonalFiller B S hS f g)

/-- **The relative diagonal of `f` as a pre-morphism of 2-commutative squares** (Stacks 003O),
from the square of Stacks 0CBB, read in the 2-category of categories fibred in groupoids, to the
square of Stacks 04Z1. Its comparison 2-cells are
`AlgebraicGeometry.Stack.relativeDiagonalCompIso` and the identity, the composite of `Δ_{𝒳/𝒳'}`
with the left-hand leg of the 04Z1 square being `f` on the nose. -/
def monomorphismDiagonalPreHom (f : 𝒳 ⟶ 𝒳') (g : 𝒳' ⟶ 𝒴) :
    TwoCommSq.PreHom
      (AlgebraicStacks.toCatFiberedInGroupoids B S hS (monomorphismDiagonalSquare B S hS f g))
      (comparisonSquare B S hS f f g) :=
  TwoCommSq.PreHom.ofPrecomposeLegs (comparisonSquare B S hS f f g)
    (relativeDiagonalAlgebraicStacks B S hS f).hom
    (relativeDiagonalAlgebraicStacks B S hS (f ≫ g)).hom f.hom
    (relativeDiagonalCompIso B S hS f g) (Iso.refl _)

/-- **Stacks 0CBB.** Let `f : 𝒳 ⟶ 𝒳'` and `g : 𝒳' ⟶ 𝒴` be 1-morphisms of algebraic stacks over
`S`. If `f` is a monomorphism (Stacks 04ZW), then the canonical square

```text
  𝒳  --Δ_{𝒳/𝒴}-->  𝒳 ×_𝒴 𝒳
  |                     |
 f|                     | f × f
  v                     v
  𝒳' --Δ_{𝒳'/𝒴}--> 𝒳' ×_𝒴 𝒳'
```

`AlgebraicGeometry.Stack.monomorphismDiagonalSquare` is a 2-fibre product in the 2-category of
algebraic stacks over `(Sch/S)_fppf`.

This is the source's proof: `𝒳 = 𝒳 ×_{𝒳'} 𝒳` by **Stacks 04ZZ**, the relative diagonal of the
monomorphism `f` being an equivalence, and the square is then the 2-cartesian square of
**Stacks 04Z1** precomposed with that equivalence. -/
@[stacks 0CBB]
def isTwoFibreProduct_monomorphismDiagonalSquare (f : 𝒳 ⟶ 𝒳') (g : 𝒳' ⟶ 𝒴)
    (hf : AlgebraicStacks.IsMonomorphism B S hS f) :
    IsTwoFibreProduct (monomorphismDiagonalSquare B S hS f g) :=
  AlgebraicStacks.isTwoFibreProduct_of_toCatFiberedInGroupoids B S hS _
    (isTwoFibreProduct_of_isEquivalence_to (isTwoFibreProduct_comparisonSquare B S hS f f g)
      (monomorphismDiagonalPreHom B S hS f g)
      ((TwoFibreProductOver.full_and_faithful_iff_isEquivalence_diagonal
        𝒳.val.isFiberedInGroupoids 𝒳'.val.isFiberedInGroupoids
        (CatFiberedInGroupoids.homFunctor_comp_p f.hom)).mp
        (AlgebraicStacks.full_and_faithful_homFunctor_of_isMonomorphism B S hS f hf)))

end AlgebraicGeometry.Stack

end

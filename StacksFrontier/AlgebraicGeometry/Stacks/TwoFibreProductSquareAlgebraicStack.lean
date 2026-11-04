module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductAlgebraicStack
public import StacksFrontier.CategoryTheory.TwoFibreProduct.InducedBicategory

/-!
# The 2-fibre product of algebraic stacks (Stacks 04T2)

Let `f : 𝒳 ⟶ 𝒵` and `g : 𝒴 ⟶ 𝒵` be 1-morphisms of algebraic stacks over the big fppf site of
`S`. Then the 2-fibre product `𝒳 ×_{f, 𝒵, g} 𝒴` is an algebraic stack, and it is the 2-fibre
product *in the 2-category of algebraic stacks* (Stacks 03YP) and not merely in the ambient
2-category of categories fibred in groupoids.

## Main definitions

* `AlgebraicGeometry.Stack.twoFibreProductSquareAlgebraicStacks`: the canonical 2-commutative
  square of the cospan, read in the 2-category of algebraic stacks.
* `AlgebraicGeometry.Stack.twoFibreProductAlgebraicStack`: its apex.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicStack_twoFibreProductSquare`: the first assertion of
  **Stacks 04T2**.
* `AlgebraicGeometry.Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks`: the second
  assertion of **Stacks 04T2**, the 2-categorical universal property.

## Implementation notes

Both halves are the source's own argument. The first is Stacks 04TF
(`AlgebraicGeometry.Stack.isAlgebraicStack_twoFibreProduct`), which is strictly more general —
it asks only that the base be a stack in groupoids with representable diagonal — instantiated
at the stack and diagonal clauses of the algebraicity of `𝒵`. The second is the formal remark
that the 2-category of algebraic stacks is a *full* sub-2-category of the 2-category of
categories fibred in groupoids, so a 2-fibre product computed there is one here; that is
`CategoryTheory.Bicategory.isTwoFibreProduct_of_underlying` applied to
`CategoryTheory.CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare`, which is
unconditional.

The square's legs and filler are those of
`CategoryTheory.CatFiberedInGroupoids.twoFibreProductSquare` wrapped by
`CategoryTheory.Bicategory.InducedBicategory.mkHom` and `.isoMk`, so its underlying square is
that one on the nose and the universal property transfers with no transport.

## References

* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04TF](https://stacks.math.columbia.edu/tag/04TF)
* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 04T2, first assertion.** The apex of the canonical 2-commutative square of a
cospan of algebraic stacks over `S` is an algebraic stack. This is
`AlgebraicGeometry.Stack.isAlgebraicStack_twoFibreProduct`, Stacks 04TF, with base the common
target, whose stack and diagonal hypotheses there are two of the clauses of its algebraicity. -/
@[stacks 04T2]
theorem isAlgebraicStack_twoFibreProductSquare
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵) :
    IsAlgebraicStack.{u, w} B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom g.hom).pt.val := by
  obtain ⟨_, h𝒵stack, h𝒵diag, -⟩ := 𝒵.property
  exact isAlgebraicStack_twoFibreProduct B S hS 𝒳.val.val 𝒴.val.val 𝒵.val.val
    f.hom.hom g.hom.hom h𝒵stack h𝒵diag 𝒳.property 𝒴.property

/-- The canonical 2-commutative square over a cospan of algebraic stacks, read in the
2-category of algebraic stacks (Stacks 03YP). Its apex is the 2-fibre product over the base
site, which is an algebraic stack by
`AlgebraicGeometry.Stack.isAlgebraicStack_twoFibreProductSquare`, and its legs and filler are
those of `CategoryTheory.CatFiberedInGroupoids.twoFibreProductSquare` unchanged, since the
1-morphisms and 2-morphisms of the 2-category of algebraic stacks are those of the ambient
one. -/
def twoFibreProductSquareAlgebraicStacks
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵) :
    Bicategory.TwoCommSq f g where
  pt := ⟨(CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom g.hom).pt,
    isAlgebraicStack_twoFibreProductSquare B S hS f g⟩
  fst := Bicategory.InducedBicategory.mkHom
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom g.hom).fst
  snd := Bicategory.InducedBicategory.mkHom
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom g.hom).snd
  iso := Bicategory.InducedBicategory.isoMk
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom g.hom).iso

/-- The 2-fibre product `𝒳 ×_{f, 𝒵, g} 𝒴` of a cospan of algebraic stacks over `S`, as an
object of the 2-category of algebraic stacks: the apex of
`AlgebraicGeometry.Stack.twoFibreProductSquareAlgebraicStacks`. -/
def twoFibreProductAlgebraicStack
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵) :
    AlgebraicStacks.{u, w} B S hS :=
  (twoFibreProductSquareAlgebraicStacks B S hS f g).pt

/-- **Stacks 04T2, second assertion: the 2-categorical universal property.** The canonical
square of a cospan of algebraic stacks over `S` is a 2-fibre product in the 2-category of
algebraic stacks, and not merely in the ambient 2-category of categories fibred in groupoids:
the square underlying it is the canonical one there, which is a 2-fibre product
unconditionally, and the 2-category of algebraic stacks is a full sub-2-category.

This is also the **right square of Stacks 06PQ**, whose left square is
`AlgebraicGeometry.Stack.exists_cartesianRelativeInertiaSquare`: the right square of the
diagram there is the defining base-change square of the cospan `(π, f)`. -/
@[stacks 04T2 "2-categorical universal property", stacks 06PQ "right square of algebraic stacks"]
noncomputable def isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵) :
    Bicategory.IsTwoFibreProduct (twoFibreProductSquareAlgebraicStacks B S hS f g) :=
  Bicategory.isTwoFibreProduct_of_underlying
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      f.hom g.hom)

end AlgebraicGeometry.Stack

end

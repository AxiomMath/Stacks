module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningSurjective

/-!
# Stacks 0BPV at surjectivity and universal injectivity

For a morphism of thickenings of algebraic stacks, the comparison `𝒳 ×_𝒴 𝒳 ⟶ 𝒳' ×_{𝒴'} 𝒳'` is a
thickening by the first assertion of **Stacks 0BPU**,
`AlgebraicGeometry.Stack.isThickening_selfProductDiagonalMap`, so the two relative diagonals form
a morphism of thickenings `(Δ, Δ')`, `AlgebraicGeometry.Stack.diagonalThickeningMorphism`. This
file reads properties (c) and (i) of **Stacks 0BPV** off that morphism of thickenings, and proves
the base-change half of property (a).

## Main results

* `AlgebraicGeometry.Stack.isSurjective_relativeDiagonal_inner_iff_outer`: **Stacks 0BPV**,
  property (c), surjectivity.
* `AlgebraicGeometry.Stack.universallyInjective_relativeDiagonal_inner_iff_outer`:
  **Stacks 0BPV**, property (i), universal injectivity.
* `AlgebraicGeometry.Stack.isRepresentableMorphism_fst_of_isTwoFibreProduct`: **Stacks 02ZT**
  for a 2-fibre product square of algebraic stacks.
* `AlgebraicGeometry.Stack.isRepresentableMorphism_relativeDiagonal_inner_of_outer`: the
  implication from `Δ'` to `Δ` of property (a), as a base change across the cartesian diagonal
  square of Stacks 0BPU.

## Implementation notes

Both clauses are the corresponding parts of **Stacks 0CJ9** — part (2),
`AlgebraicGeometry.Stack.isSurjective_inner_iff_outer`, and part (6),
`AlgebraicGeometry.Stack.universallyInjective_inner_iff_outer` — applied to the morphism of
thickenings `(Δ, Δ')`.

## References

* [Stacks Project, Tag 02ZT](https://stacks.math.columbia.edu/tag/02ZT)
* [Stacks Project, Tag 0BPU](https://stacks.math.columbia.edu/tag/0BPU)
* [Stacks Project, Tag 0BPV](https://stacks.math.columbia.edu/tag/0BPV)
* [Stacks Project, Tag 0CJ9](https://stacks.math.columbia.edu/tag/0CJ9)
-/

@[expose] public section

open CategoryTheory
open Stacks.Thickenings

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section RepresentableBaseChange

variable {𝒵 𝒳₀ 𝒴₀ : AlgebraicStacks.{u, w} B S hS} {g : 𝒵 ⟶ 𝒴₀} {f : 𝒳₀ ⟶ 𝒴₀}

/-- **Stacks 02ZT for a 2-fibre product square of algebraic stacks.** If `f : 𝒳₀ ⟶ 𝒴₀` is
representable by schemes (**Stacks 02Y7**) and `P` is a 2-fibre product of the cospan `(g, f)` in
the 2-category of algebraic stacks, then the projection `P.fst : P.pt ⟶ 𝒵` is representable by
schemes. -/
theorem isRepresentableMorphism_fst_of_isTwoFibreProduct
    (P : Bicategory.TwoCommSq g f) (hP : Bicategory.IsTwoFibreProduct P)
    (hf : Stacks.RepresentableMorphism.IsRepresentableMorphism 𝒳₀.val.val.p 𝒴₀.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom)) :
    Stacks.RepresentableMorphism.IsRepresentableMorphism P.pt.val.val.p 𝒵.val.val.p
      (CatFiberedInGroupoids.homFunctor P.fst.hom) := by
  have hQ := isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g f
  let d := Bicategory.twoFibreProductPreHom hQ P
  have hd : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor d.hom.hom) :=
    isEquivalence_of_isTwoFibreProductAlgebraicStacks B S hS hP hQ d
  have hb : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor (𝟙 𝒵.val)) :=
    Functor.isEquivalence_refl (C := 𝒵.val.val.obj)
  exact (Stacks.RepresentableMorphism.isRepresentableMorphism_iff_of_equivalences
    P.fst.hom (twoFibreProductSquareAlgebraicStacks B S hS g f).fst.hom d.hom.hom (𝟙 𝒵.val)
    ((algebraicStacksTwoIsoHom B S hS d.isoFst).symm ≪≫
      (Bicategory.rightUnitor P.fst.hom).symm)).1
    (Stacks.RepresentableMorphism.isRepresentableMorphism_fst_twoFibreProductOver
      𝒳₀.val.val.p 𝒴₀.val.val.p 𝒵.val.val.p (CatFiberedInGroupoids.homFunctor f.hom)
      (CatFiberedInGroupoids.homFunctor g.hom) f.hom.hom.w g.hom.hom.w hf)

end RepresentableBaseChange

section Diagonal

variable {𝒳 𝒳' 𝒴 𝒴' : AlgebraicStacks.{u, w} B S hS}
  {i : 𝒳 ⟶ 𝒳'} {j : 𝒴 ⟶ 𝒴'} {hi : IsThickening i} {hj : IsThickening j}
  (m : ThickeningMorphism i j hi hj)

/-- For a morphism of thickenings `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` of algebraic stacks over `S`,
the relative diagonal `Δ : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is surjective (**Stacks 04ZS**) if and only if
`Δ' : 𝒳' ⟶ 𝒳' ×_{𝒴'} 𝒳'` is. -/
@[stacks 0BPV "property (c) of seventeen: surjective"]
theorem isSurjective_relativeDiagonal_inner_iff_outer :
    IsSurjective B S hS (AlgebraicStacks.relativeDiagonal B S hS m.inner) ↔
      IsSurjective B S hS (AlgebraicStacks.relativeDiagonal B S hS m.outer) :=
  isSurjective_inner_iff_outer
    (diagonalThickeningMorphism B S hS m (isThickening_selfProductDiagonalMap B S hS m))

/-- For a morphism of thickenings `(f, f') : (𝒳 ⊂ 𝒳') → (𝒴 ⊂ 𝒴')` of algebraic stacks over `S`,
the relative diagonal `Δ : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is universally injective (**Stacks 0CI2**) if and only
if `Δ' : 𝒳' ⟶ 𝒳' ×_{𝒴'} 𝒳'` is. -/
@[stacks 0BPV "property (i) of seventeen: universally injective"]
theorem universallyInjective_relativeDiagonal_inner_iff_outer :
    UniversallyInjective B S hS (AlgebraicStacks.relativeDiagonal B S hS m.inner) ↔
      UniversallyInjective B S hS (AlgebraicStacks.relativeDiagonal B S hS m.outer) :=
  universallyInjective_inner_iff_outer B S hS
    (diagonalThickeningMorphism B S hS m (isThickening_selfProductDiagonalMap B S hS m))

/-- **The implication from `Δ'` to `Δ` of property (a) of Stacks 0BPV.** If the ambient relative
diagonal `Δ' : 𝒳' ⟶ 𝒳' ×_{𝒴'} 𝒳'` of a morphism of thickenings of algebraic stacks is
representable by schemes (**Stacks 02Y7**), so is the restricted one `Δ : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳`. -/
theorem isRepresentableMorphism_relativeDiagonal_inner_of_outer
    (hout : Stacks.RepresentableMorphism.IsRepresentableMorphism 𝒳'.val.val.p
      (AlgebraicStacks.twoFibreProduct B S hS m.outer m.outer).val.val.p
      (CatFiberedInGroupoids.homFunctor (AlgebraicStacks.relativeDiagonal B S hS m.outer).hom)) :
    Stacks.RepresentableMorphism.IsRepresentableMorphism 𝒳.val.val.p
      (AlgebraicStacks.twoFibreProduct B S hS m.inner m.inner).val.val.p
      (CatFiberedInGroupoids.homFunctor
        (AlgebraicStacks.relativeDiagonal B S hS m.inner).hom) :=
  isRepresentableMorphism_fst_of_isTwoFibreProduct B S hS
    (selfProductDiagonalSquare B S hS m)
    (isTwoFibreProduct_selfProductDiagonalSquare B S hS m) hout

end Diagonal

end AlgebraicGeometry.Stack

end

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphismPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismComp
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# The morphism from a 2-fibre product to the base of its cospan

Let `a : 𝒴 ⟶ 𝒳` and `b : 𝒵 ⟶ 𝒳` be 1-morphisms of algebraic stacks over `S` and let `P` be a
2-fibre product of the cospan `(a, b)`, with apex `𝒫 = 𝒴 ×_𝒳 𝒵` and projections
`P.fst : 𝒫 ⟶ 𝒴`, `P.snd : 𝒫 ⟶ 𝒵`. The morphism `P.fst ≫ a : 𝒫 ⟶ 𝒳` — identified with
`P.snd ≫ b` by the filler `P.iso` — is quasi-compact, quasi-separated, respectively flat as
soon as both `a` and `b` are.

Each of the three is the base-change statement for `b` along `a`, which makes the projection
`P.fst` inherit the property, followed by the composition statement for that projection with
`a`: **Stacks 050V** and **Stacks 050W** for quasi-compactness, **Stacks 050F** and
**Stacks 050K** for quasi-separatedness, **Stacks 06PY** and **Stacks 06PX** for flatness.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiCompactMorphism_fst_comp`: the morphism to the
  base of the cospan is quasi-compact.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparated_fst_comp`: it is quasi-separated.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_fst_comp`: it is flat.

## Implementation notes

No `@[stacks]` attribute is placed: each statement is the composite of two source lemmas
at one cospan, and the source has no separate lemma for the composite.

Only `P.fst ≫ a` is treated. The same statements for `P.snd ≫ b` are these ones applied to the
exchanged square `P.swap`, which is a 2-fibre product of the exchanged cospan by **Stacks 003Q**
and whose first projection is `P.snd`.

Quasi-separatedness is the one of the three whose base-change lemma is stated about the second
projection of the square, so the exchanged square is used there to reach the first projection;
quasi-compactness and flatness have base-change lemmas about the first projection already.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 050F](https://stacks.math.columbia.edu/tag/050F)
* [Stacks Project, Tag 050K](https://stacks.math.columbia.edu/tag/050K)
* [Stacks Project, Tag 050V](https://stacks.math.columbia.edu/tag/050V)
* [Stacks Project, Tag 050W](https://stacks.math.columbia.edu/tag/050W)
* [Stacks Project, Tag 06PX](https://stacks.math.columbia.edu/tag/06PX)
* [Stacks Project, Tag 06PY](https://stacks.math.columbia.edu/tag/06PY)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- The morphism `𝒴 ×_𝒳 𝒵 ⟶ 𝒳` of a 2-fibre product of a cospan of quasi-compact 1-morphisms
of algebraic stacks over `S` is quasi-compact. -/
theorem isQuasiCompactMorphism_fst_comp (a : 𝒴 ⟶ 𝒳) (b : 𝒵 ⟶ 𝒳)
    (P : Bicategory.TwoCommSq a b) (hP : Bicategory.IsTwoFibreProduct P)
    (ha : IsQuasiCompactMorphism B S hS a) (hb : IsQuasiCompactMorphism B S hS b) :
    IsQuasiCompactMorphism B S hS (P.fst ≫ a) :=
  isQuasiCompactMorphism_comp B S hS P.fst a
    (isQuasiCompactMorphism_baseChange B S hS b a P hP hb) ha

/-- The morphism `𝒴 ×_𝒳 𝒵 ⟶ 𝒳` of a 2-fibre product of a cospan of quasi-separated 1-morphisms
of algebraic stacks over `S` is quasi-separated. -/
theorem isQuasiSeparated_fst_comp (a : 𝒴 ⟶ 𝒳) (b : 𝒵 ⟶ 𝒳)
    (P : Bicategory.TwoCommSq a b) (hP : Bicategory.IsTwoFibreProduct P)
    (ha : IsQuasiSeparated B S hS a) (hb : IsQuasiSeparated B S hS b) :
    IsQuasiSeparated B S hS (P.fst ≫ a) :=
  isQuasiSeparated_comp B S hS P.fst a
    (isQuasiSeparated_baseChange_of_isTwoFibreProduct B S hS b a P.swap
      (Bicategory.isTwoFibreProduct_swap hP) hb) ha

/-- The morphism `𝒴 ×_𝒳 𝒵 ⟶ 𝒳` of a 2-fibre product of a cospan of flat 1-morphisms of
algebraic stacks over `S` is flat. -/
theorem isFlat_fst_comp (a : 𝒴 ⟶ 𝒳) (b : 𝒵 ⟶ 𝒳)
    (P : Bicategory.TwoCommSq a b) (hP : Bicategory.IsTwoFibreProduct P)
    (ha : IsFlat B S hS a) (hb : IsFlat B S hS b) :
    IsFlat B S hS (P.fst ≫ a) :=
  isFlat_comp B S hS P.fst a (isFlat_baseChange B S hS b a P hP hb) ha

end AlgebraicGeometry.Stack.AlgebraicStacks

end

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomSpaceRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentStackIsomEqualizerFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonal

/-!
# The diagonal of the stack of coherent sheaves is representable (Stacks 08W6)

In Situation 08KB — a scheme `S` and a morphism `f : X ⟶ Y` of algebraic spaces over `S` of
finite presentation — let `𝒳 = Coh_{X/Y}` be the category of triples `(T, g, F)` of a scheme `T`
over `S`, a morphism `g : T ⟶ Y` over `S` and a quasi-coherent module `F` of finite presentation
on `X_T = T ×_{g, Y} X`, flat over `T`, with support proper over `T`. Stacks 08W6 asserts that the
diagonal `Δ : 𝒳 ⟶ 𝒳 × 𝒳` is representable by algebraic spaces.

## Main results

* `CoherentSituation.coherentCFG_diagonal_isRepresentableByAlgebraicSpaces`: **Stacks 08W6**,
  with no hypothesis beyond the standing data of Situation 08KB.

## Implementation notes

Unqualified names below are in the namespace `AlgebraicGeometry.Space`. The proof is the source's.
By Stacks 045G
(`AlgebraicGeometry.Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf`) it suffices
that each `Isom_𝒳(x, y)` is an algebraic space over the scheme `U` of the fibre. That presheaf lies
over the equalizer `E` of the two base maps, a scheme because the diagonal of `Y` is representable,
and over `E` it is the relative Isom functor `Isom(F, G)` of Stacks 08K7
(`CoherentSituation.coherentCFG_hasRepresentableDiagonal`). That functor is an algebraic space by
the argument of Stacks 08K9
(`CoherentSituation.coherentCFG_hasRepresentableDiagonal_of_finitePresentationHom`), whose one
input, the finite presentation part of Stacks 08K6 for the four relative Hom functors, is
`HomSituation.isAffineFinitePresentationAlgebraicSpaceOverBase_of_finitePresentation`.

The stack is `CoherentSituation.coherentCFG`: the category of Stacks 08KB at its canonical
category structure `CoherentSituation.categoryData`, with the fibred-in-groupoids structure of
Stacks 08W5 proved unconditionally. The product `𝒳 × 𝒳` is
`CategoryTheory.CatFiberedInGroupoids.product`, and `Δ` is
`AlgebraicGeometry.Stack.diagonalBasedFunctor`.

## References

* [Stacks Project, Tag 08W6](https://stacks.math.columbia.edu/tag/08W6)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 08K9](https://stacks.math.columbia.edu/tag/08K9)
* [Stacks Project, Tag 08K6](https://stacks.math.columbia.edu/tag/08K6)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Space.CoherentSituation

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 08W6.** In Situation 08KB, with `𝒳 = Coh_{X/Y}` the stack of coherent sheaves with
proper support of a morphism `f : X ⟶ Y` of finite presentation of algebraic spaces over `S`,
the diagonal `Δ : 𝒳 ⟶ 𝒳 × 𝒳` is representable by algebraic spaces. -/
@[stacks 08W6]
theorem coherentCFG_diagonal_isRepresentableByAlgebraicSpaces (D : CoherentSituation B S hS) :
    Stack.IsRepresentableByAlgebraicSpaces B S hS
      (Stack.diagonalBasedFunctor B S hS D.coherentCFG) :=
  (Stack.hasRepresentableDiagonal_iff B S hS D.coherentCFG).mp
    (D.coherentCFG_hasRepresentableDiagonal_of_finitePresentationHom
      fun s' hfp' hF hG hGflat hGsupp =>
        s'.isAffineFinitePresentationAlgebraicSpaceOverBase_of_finitePresentation hfp' hF hG
          hGflat hGsupp)

end AlgebraicGeometry.Space.CoherentSituation

end

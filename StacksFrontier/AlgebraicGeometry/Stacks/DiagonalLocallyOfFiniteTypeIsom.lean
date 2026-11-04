module

public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalLocallyOfFiniteType
public import StacksFrontier.Deformation.ArtinCriteria.VersalSmoothness

/-!
# Local finite type of the diagonal, read on isomorphism sheaves

The relative property of Stacks 03YK for the diagonal `Δ : 𝒳 ⟶ 𝒳 × 𝒳` of a category fibred in
groupoids says that every algebraic space representing a base change of `Δ` is locally of finite
type over `S`. This file reads it off on isomorphism sheaves: for objects `a`, `b` over `T`, any
algebraic space over `T` isomorphic to `Isom(a, b)` is locally of finite type over `T`. With
Stacks 0CXI this holds for every limit preserving `𝒳` with representable diagonal.

## Main results

* `AlgebraicGeometry.Stack.isLocallyOfFiniteType_isom_of_isLimitPreserving`: for a limit preserving
  `𝒳` with representable diagonal, every algebraic space isomorphic to `Isom(a, b)` is locally of
  finite type.

## References

* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 0CXI](https://stacks.math.columbia.edu/tag/0CXI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Local finite type of the diagonal, on isomorphism sheaves, for a limit preserving
category.** Let `𝒳` be a limit preserving category fibred in groupoids over the big fppf site of
`S` whose diagonal is representable by algebraic spaces. For objects `a`, `b` of `𝒳` over `T`,
every algebraic space over `T` isomorphic to `Isom(a, b)` is locally of finite type over `T`.
This is Stacks 0CXI read through Stacks 045G. -/
theorem isLocallyOfFiniteType_isom_of_isLimitPreserving
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (hΔ : HasRepresentableDiagonal B S hS 𝒳)
    (hlim : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u} B S hS 𝒳) :
    letI : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
    ∀ (T : BigFppfOver B S hS) (a b : 𝒳.val.p.Fiber T)
      (G : (BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u),
      IsAlgebraicSpace B T.left.1 T.left.2 G →
      Nonempty (G ⋙ uliftFunctor.{u, u} ≅
        ((Over.iteratedSliceBackward T).op ⋙ 𝒳.val.p.isomPresheaf a b) ⋙
          uliftFunctor.{u, u}) →
      Space.IsLocallyOfFiniteType B T.left.1 T.left.2
        (terminal.from G : G ⟶ ⊤_ ((BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u)) :=
  isLocallyOfFiniteType_terminal_of_isLocallyOfFiniteType_diagonal.{u, u, u + 1} B S hS 𝒳 hΔ
    (isLocallyOfFiniteType_diagonal B S hS 𝒳 hΔ hlim)

end AlgebraicGeometry.Stack

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.LineBundleFlatPullbackChow
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.VectorBundle.Fiber
public import StacksFrontier.AlgebraicGeometry.Spaces.VectorBundle.Projection
public import StacksFrontier.AlgebraicGeometry.Spaces.VectorBundle.SymmetricAlgebraBounded

/-!
# Flat pullback along a vector bundle is surjective up to rational equivalence

Let `W/B` be good, let `ℰ` be a finite locally free `𝒪_W`-module of rank `r`, and let
`p : E → W` be its vector bundle. Then every `(k + r)`-cycle on `E` is rationally equivalent to
`p^*β` for some `k`-cycle `β` on `W`. This is the surjectivity half of Stacks 0ERW.

The proof applies Stacks 0ERG
(`AlgebraicGeometry.Space.isFlatPullbackSurjective_of_isQuasiCompact_of_hasAffineSpaceFibres`)
to `p`. The projection is affine, hence quasi-compact
(`AlgebraicGeometry.Space.isQuasiCompact_vectorBundleProjection`), and flat of relative
dimension `r`. Its fibres over the residue fields are affine `r`-spaces
(`AlgebraicGeometry.Space.hasAffineSpaceFibres_vectorBundleProjection`).

## Main results

* `AlgebraicGeometry.Space.isFlatPullbackSurjective_vectorBundleProjection`: flat pullback along
  a vector bundle projection is surjective up to rational equivalence.

## References

* [Stacks Project, Tag 0ERG](https://stacks.math.columbia.edu/tag/0ERG)
* [Stacks Project, Tag 0ERW](https://stacks.math.columbia.edu/tag/0ERW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

section VectorBundle

variable (D : BaseSpaceDimensionSituation.{u}) (W : AlgebraicSpaces D.site D.base D.base_mem)
    (F : SheafOfModules.{u} (structureRingSheaf D.site D.base D.base_mem W))
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree F] (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank F r]
    (sW : W.1 ⟶ D.space) (hW : D.IsGood sW)

/-- **Flat pullback along a vector bundle is surjective up to rational equivalence.** In
Situation 0EDT let `W/B` be good, let `ℰ` be a finite locally free `𝒪_W`-module of rank `r` and
let `p : E → W` be its vector bundle. Then for every `α ∈ Z_{k+r}(E)` there is `β ∈ Z_k(W)` with
`p^*β - α` rationally equivalent to zero: the surjectivity half of Stacks 0ERW. -/
theorem isFlatPullbackSurjective_vectorBundleProjection (k : ℤ) :
    IsFlatPullbackSurjective D ((vectorBundleProjection D.site D.base D.base_mem W F).hom ≫ sW)
      (isGood_vectorBundle D W F sW hW) sW hW
      (vectorBundleProjection D.site D.base D.base_mem W F).hom rfl r
      (isFlat_vectorBundleProjection D.site D.base D.base_mem W F)
      (hasRelativeDimension_vectorBundleProjection D.site D.base D.base_mem W F r) k :=
  isFlatPullbackSurjective_of_isQuasiCompact_of_hasAffineSpaceFibres D _ _ sW hW _ rfl r _ _
    (isQuasiCompact_vectorBundleProjection D W F)
    (hasAffineSpaceFibres_vectorBundleProjection D W F sW hW r) k

end VectorBundle

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProjectiveBundleFormulaBijective
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.VectorBundleChowPullbackIso

/-!
# Stacks 0ERW: flat pullback along a vector bundle is an isomorphism on Chow groups

In Situation 0EDT let `X/B` be good, `ℰ` a finite locally free `𝒪_X`-module of rank `r` and
`p : E = Spec(Sym^*(ℰ)) → X` its vector bundle. Then `p^* : CH_k(X) → CH_{k+r}(E)` is an
isomorphism for every `k`, on the Chow groups of Stacks 0EQ6 at the canonical embeddings of
Stacks 0ENK (`AlgebraicGeometry.Space.chowGroupCanonical`).

## Main results

* `AlgebraicGeometry.Space.bijective_flatPullbackChowMapCanonical_vectorBundleProjection`:
  `p^* : CH_k(X) → CH_{k+r}(E)` is bijective (Stacks 0ERW).
* `AlgebraicGeometry.Space.vectorBundleChowPullbackEquiv`: the same as an isomorphism
  `CH_k(X) ≃+ CH_{k+r}(E)`.

## References

* [Stacks Project, Tag 0ERW](https://stacks.math.columbia.edu/tag/0ERW)
* [Stacks Project, Tag 0ERV](https://stacks.math.columbia.edu/tag/0ERV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (D : BaseSpaceDimensionSituation.{u}) (W : AlgebraicSpaces D.site D.base D.base_mem)
    (F : SheafOfModules.{u} (structureRingSheaf D.site D.base D.base_mem W)) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank F r]
    (sW : W.1 ⟶ D.space) (hW : D.IsGood sW)

/-- **Stacks 0ERW.** In Situation 0EDT let `X/B` be good, let `ℰ` be a finite locally free
`𝒪_X`-module of rank `r` and let `p : E = Spec(Sym^*(ℰ)) → X` be the associated vector bundle.
Then `p^* : CH_k(X) → CH_{k+r}(E)` is an isomorphism for all `k`. -/
@[stacks 0ERW]
theorem bijective_flatPullbackChowMapCanonical_vectorBundleProjection (k : ℤ) :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F r
    Function.Bijective (flatPullbackChowMapCanonical.{u + 1} D
      ((vectorBundleProjection D.site D.base D.base_mem W F).hom ≫ sW)
      (isGood_vectorBundle D W F sW hW) sW hW
      (vectorBundleProjection D.site D.base D.base_mem W F).hom
      rfl r (isFlat_vectorBundleProjection D.site D.base D.base_mem W F)
      (hasRelativeDimension_vectorBundleProjection D.site D.base D.base_mem W F r) k
      (k + (r : ℤ)) rfl) :=
  let := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F r
  have h := fun (_ : AlgebraicSpaces D.site D.base D.base_mem) sX hX E n hr N d hd =>
    bijective_bundleFormulaMap_projectiveBundle_of_twist D sX hX E n hr
      (fun U G G' hG hG' v σ hσ hfree hfree' =>
        ⟨@projectiveBundleSplitEpiTwistIso _ _ _ U G G' hG hG' v σ hσ hfree hfree'⟩) N d hd
  bijective_flatPullbackChowMapCanonical_vectorBundleProjection_of_bundleFormula D
    (h · · · · · · · · · |>.2)
    (h · · · · · · · · · |>.1)
    (fun _ E _ hr => projectiveCompletionInfinityTwistIso E hr) W F r sW hW k

/-- The flat pullback `p^*` along the vector bundle `p : E → X` of a finite locally free module of
rank `r` on a good `X/B`, as an isomorphism `CH_k(X) ≃+ CH_{k+r}(E)` (Stacks 0ERW). -/
def vectorBundleChowPullbackEquiv (k : ℤ) :
    letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F r
    chowGroupCanonical.{u + 1} D sW hW k ≃+
      chowGroupCanonical.{u + 1} D ((vectorBundleProjection D.site D.base D.base_mem W F).hom ≫ sW)
        (isGood_vectorBundle D W F sW hW) (k + (r : ℤ)) :=
  letI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F r
  AddEquiv.ofBijective _
    (bijective_flatPullbackChowMapCanonical_vectorBundleProjection D W F r sW hW k)

end AlgebraicGeometry.Space

end

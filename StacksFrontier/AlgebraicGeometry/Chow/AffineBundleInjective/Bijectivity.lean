module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineBundleSurjectivity
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundleInjective.AffineLineFibre
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundleInjective.AffineLineLocal

/-!
# Stacks 0GUB: flat pullback along an affine-space bundle is an isomorphism

Let `(S, δ)` be as in Situation 02QL, let `Y` be locally of finite type over `S`, let `r ≥ 0` and
let `f : X ⟶ Y` be a morphism such that every point of `Y` has an open neighbourhood `V` with
`f⁻¹(V) ≅ V × 𝔸^r` over `V`. Remark 0GUB sketches a proof that

  `f^* : CH_k(Y) ⟶ CH_{k+r}(X)`

is an isomorphism. This file proves it.

Surjectivity is Stacks 02TT, `Stacks.Chow.flatPullbackChow_surjective_isAffineSpaceBundle`.
Injectivity follows the remark's idea — the first higher Chow groups of Stacks 0GUA, the tame
symbol, and Milnor's computation of `K₂` of a rational function field (Step 3 of the remark) — but
carries it out on chains rather than through the six-term sequences, which removes the need for
Step 1 (finite dimensionality) and for a dense open over which the bundle is trivial:

* a rational equivalence `f^*α = div(a)` is given by a Milnor K₁-chain `a` on `X`
  (Stacks 0GU3);
* `a` is changed by tame-symbol boundaries, which do not change its divisor (Stacks 0GU9), one
  level of the base at a time, using that over a point `y` the fibre is `𝔸^r_{κ(y)}` and that
  `CH^M_t(𝔸^r_{κ(y)}, 1) = 0` for `t < r` (`Stacks.Chow.exists_devissage`);
* what is left lives at the generic points of the fibres over points of relative dimension
  `k + 1`, where `CH^M_r(𝔸^r_{κ(y)}, 1) = κ(y)^*` makes it the pullback of a K₁-chain `b` on
  `Y` (`Stacks.Chow.exists_eq_bundleChainPullback_of_fibreUnitDescent`), so that
  `f^*α = div(f^* b) = f^* div(b)` (Stacks 02RR) and `α = div(b) = 0` by injectivity of flat
  pullback of cycles.

The two computations over `𝔸^r_{κ(y)}` are proved by induction on `r` through
`𝔸^{r+1} = 𝔸^r × 𝔸^1` (`Stacks.Chow.hasFibreProperties_affineSpaceOver_succ`), the rank-one
case being Milnor's exact sequence on `Spec A[X] ⟶ Spec A`
(`Stacks.Chow.fibreBoundaryLift_specPolynomial`, `Stacks.Chow.fibreUnitDescent_specPolynomial`).

## Main results

* `Stacks.Chow.flatPullbackChow_injective_of_isAffineSpaceBundle` — injectivity.
* `Stacks.Chow.flatPullbackChow_bijective_of_isAffineSpaceBundle` — **Stacks 0GUB**.

## References

* [Stacks Project, Tag 0GUB](https://stacks.math.columbia.edu/tag/0GUB)
* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
* [Stacks Project, Tag 0GUA](https://stacks.math.columbia.edu/tag/0GUA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

attribute [local instance] isIntegral_integralComponentAt

/-- **Flat pullback along an affine-space bundle is injective on Chow groups.** Let `(S, δ)` be
the base situation of chapter 42, `Y` locally of finite type over `S` and `f : X ⟶ Y`
Zariski-locally on `Y` the projection `V × 𝔸^r ⟶ V`. Then `f^* : CH_k(Y) ⟶ CH_{k+r}(X)` is
injective. -/
theorem flatPullbackChow_injective_of_isAffineSpaceBundle (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f]
    [AlgebraicGeometry.Flat f] (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r)
    (hbundle : IsAffineSpaceBundle f r) (k : ℤ) :
    Function.Injective (flatPullbackChowOfRelativeDimension C (f ≫ sY) sY f rfl r hf k) :=
  flatPullbackChow_injective_of_isAffineSpaceBundle_of_affineLine C
    (hasFibreProperties_affineLine_of_specPolynomial C
      (fun R sV _ k y ↦ fibreBoundaryLift_specPolynomial C R sV k y)
      (fun R sV _ k y ↦ fibreUnitDescent_specPolynomial C R sV k y))
    (isDiscreteValuationRing_affineLine_of_specPolynomial fun R _ _ hw hfib hne ↦
      isDiscreteValuationRing_pointClosureStalk_specPolynomial R hw hfib hne)
    (f ≫ sY) sY f rfl r hf hbundle k

/-- **Stacks 0GUB.** Let `(S, δ)` be as in Situation 02QL, let `Y` be locally of finite type over
`S`, let `r ≥ 0` and let `f : X ⟶ Y` be a morphism of schemes such that every point of `Y` lies in
an open `V ⊆ Y` with `f⁻¹(V) ≅ V × 𝔸^r` as schemes over `V`. Then flat pullback

  `f^* : CH_k(Y) ⟶ CH_{k+r}(X)`

is an isomorphism for every `k`. The morphism `f` is locally of finite type, flat and of relative
dimension `r` because it is so locally on `Y`; these are not hypotheses but consequences of the
local triviality, recorded through `letI`. -/
@[stacks 0GUB]
theorem flatPullbackChow_bijective_of_isAffineSpaceBundle (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) (r : ℕ)
    (hbundle : IsAffineSpaceBundle f r) (k : ℤ) :
    letI := locallyOfFiniteType_of_isAffineSpaceBundle f r hbundle
    letI := flat_of_isAffineSpaceBundle f r hbundle
    Function.Bijective (flatPullbackChowOfRelativeDimension C (f ≫ sY) sY f rfl r
      (relativeDimension_of_isAffineSpaceBundle f r hbundle) k) :=
  let := locallyOfFiniteType_of_isAffineSpaceBundle f r hbundle
  let := flat_of_isAffineSpaceBundle f r hbundle
  ⟨flatPullbackChow_injective_of_isAffineSpaceBundle C sY f r
      (relativeDimension_of_isAffineSpaceBundle f r hbundle) hbundle k,
    flatPullbackChow_surjective_isAffineSpaceBundle C sY f r
      (relativeDimension_of_isAffineSpaceBundle f r hbundle) hbundle k⟩

end Stacks.Chow

end

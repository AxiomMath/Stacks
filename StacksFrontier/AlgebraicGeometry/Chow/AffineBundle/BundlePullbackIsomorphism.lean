module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.VectorBundleChowBijective
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundleInjective.Bijectivity

/-!
# Flat pullback along a vector bundle, and along an affine-space bundle, is an isomorphism

Let `(S, δ)` be as in Situation 02QL. Remark 02TU of the Stacks Project makes two assertions.

1. If `p : E ⟶ X` is the vector bundle of a finite locally free `𝒪_X`-module `ℰ` of rank `r`,
   then `p^* : A_k(X) ⟶ A_{k+r}(E)` is an isomorphism for every `k`. This is Lemma 02TY,
   `Stacks.Chow.flatPullbackChow_bijective_vectorBundleToBase`.
2. The same holds for every `f : X ⟶ Y` satisfying the assumptions of Lemma 02TT: `X`, `Y` locally
   of finite type over `S`, `f` flat of relative dimension `r` and Zariski-locally on `Y` the
   projection `U × 𝔸^r ⟶ U`. This is Remark 0GUB,
   `Stacks.Chow.flatPullbackChow_bijective_of_isAffineSpaceBundle`, which needs only the local
   triviality: flatness, local finiteness of type and the relative dimension follow from it.

Both assertions are registered by `add_to_stacks` on those declarations, and
`Stacks.Chow.flatPullbackChow_bijective_vectorBundle_and_affineSpaceBundle` states the whole
remark, the second assertion under exactly the assumptions of Lemma 02TT.

## Main results

* `Stacks.Chow.flatPullbackChow_bijective_vectorBundle_and_affineSpaceBundle` — the whole of
  Remark 02TU.

## References

* [Stacks Project, Tag 02TU](https://stacks.math.columbia.edu/tag/02TU)
* [Stacks Project, Tag 02TY](https://stacks.math.columbia.edu/tag/02TY)
* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
* [Stacks Project, Tag 0GUB](https://stacks.math.columbia.edu/tag/0GUB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

add_to_stacks 02TU "first assertion: flat pullback along the vector bundle of a finite locally \
free module of rank r is an isomorphism of Chow groups in every degree (Lemma 02TY)"
  Stacks.Chow.flatPullbackChow_bijective_vectorBundleToBase

add_to_stacks 02TU "second assertion: flat pullback along a morphism which is Zariski-locally on \
the target the projection U × A^r to U is an isomorphism of Chow groups in every degree \
(Remark 0GUB); flatness and relative dimension r follow from the local triviality"
  Stacks.Chow.flatPullbackChow_bijective_of_isAffineSpaceBundle

/-- **Remark 02TU.** Let `(S, δ)` be as in Situation 02QL.

1. If `X` is locally of finite type over `S`, `ℰ` is a finite locally free `𝒪_X`-module of rank
   `r` and `p : E ⟶ X` is its vector bundle, then `p^* : A_k(X) ⟶ A_{k+r}(E)` is an isomorphism
   for every `k` (Lemma 02TY).
2. If `X`, `Y` are locally of finite type over `S` and `f : X ⟶ Y` is flat of relative dimension
   `r` and Zariski-locally on `Y` the projection `U × 𝔸^r ⟶ U`, as in Lemma 02TT, then
   `f^* : A_k(Y) ⟶ A_{k+r}(X)` is an isomorphism for every `k` (Remark 0GUB). -/
@[stacks 02TU "the whole remark: both assertions"]
theorem flatPullbackChow_bijective_vectorBundle_and_affineSpaceBundle (C : ChowSituation.{u}) :
    (∀ {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (E : X.Modules)
      [E.IsQuasicoherent] (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
      (k : ℤ),
      letI := locallyOfFiniteType_vectorBundleToBase E r
      letI := flat_vectorBundleToBase E r
      Function.Bijective (flatPullbackChowOfRelativeDimension C
        (Scheme.Modules.vectorBundleToBase X E ≫ sX) sX (Scheme.Modules.vectorBundleToBase X E)
        rfl r (relativeDimension_vectorBundleToBase E r) k)) ∧
    (∀ {X Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
      [LocallyOfFiniteType f] [Flat f] (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r)
      (_ : IsAffineSpaceBundle f r) (k : ℤ),
      Function.Bijective (flatPullbackChowOfRelativeDimension C (f ≫ sY) sY f rfl r hf k)) :=
  ⟨fun sX _ E _ r _ k ↦ flatPullbackChow_bijective_vectorBundleToBase C sX E r k,
    fun sY _ f _ _ r _ hbundle k ↦ flatPullbackChow_bijective_of_isAffineSpaceBundle C sY f r
      hbundle k⟩

end Stacks.Chow

end

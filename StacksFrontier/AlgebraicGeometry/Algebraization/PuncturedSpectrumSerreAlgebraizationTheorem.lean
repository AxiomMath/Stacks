module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.PuncturedSpectrumSerreDepthInequalities
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.ExtensionPrincipalLocalTheorem

/-!
# Algebraization on the punctured spectrum from Serre's condition on the completed stalks

Let `(A, 𝔪)` be a Noetherian local ring which has a dualizing complex and is complete with respect
to an element `f ∈ 𝔪`, let `U` be the punctured spectrum of `A`, `Y = V(f) ⊆ X = Spec(A)`, and let
`(ℱₙ)` be an object of `Coh(U, f𝒪_U)`. [Stacks, Tag 0EJC] states that `(ℱₙ)` is the completion of
a coherent `𝒪_U`-module as soon as, at every `y ∈ U ∩ V(f)` closed in `U`, that is with
`dim({y}‾) = 1`, the `𝒪_{X,y}^∧`-module `ℱ_y^∧` satisfies

1. `ℱ_y^∧[1/f]` is `(S₂)` as an `𝒪_{X,y}^∧[1/f]`-module, and
2. `dim(𝒪_{X,y}^∧/𝔭) ≥ 3` for every `𝔭 ∈ Ass(ℱ_y^∧[1/f])`.

## Main results

* `Stacks.Algebraization.essImage_completionFunctor_of_hasSerreCompletedStalkConditions` —
  [Stacks, Tag 0EJC].

## Proof

As in the source, this follows from [Stacks, Tag 0EJA] and [Stacks, Tag 0EJ9]. The two conditions
give the `(2, 3)`-inequalities by
`Stacks.Algebraization.satisfiesDepthInequalities_of_completedStalk_serre`, which turns them into
the bound `depth((ℱ_y^∧)_𝔭) + dim(𝒪_{X,y}^∧/𝔭) > 2` at the points of `U ∩ Y` of dimension one and
then applies [Stacks, Tag 0EJA] in the form proved for a base with a dualizing complex. The
in-particular clause of [Stacks, Tag 0EJ9],
`Stacks.Algebraization.essImage_completionFunctor_of_isLocalRing_of_eq_span_singleton`, turns the
`(2, 3)`-inequalities into the conclusion.

## Implementation notes

The data `(A, 𝔪, f, U)` are an algebraization situation `S` with `A` local, `𝔞 = 𝔪` and
`I = (f)`; `U = X ∖ V(𝔪)` is then the punctured spectrum. "Complete with respect to `f`" is
`IsAdicComplete S.I S.A`, and `f ∈ 𝔪` follows from `I ⊆ 𝔞 = 𝔪`. The points `y ∈ U ∩ V(f)` closed
in `U` are the points of `U` lying over a point of `Y` whose closure in `X` has dimension one,
written `Order.height (S.U.ι.base y) = 1` in the specialization order. The two conditions at `y`
are `Stacks.Algebraization.HasSerreCompletedStalkConditions`.

The conclusion is membership of `Stacks.Algebraization.toKerSystem S F`, which is `(ℱₙ)` itself
read as a system along the pullback to `U` of the ideal sheaf of `Y ⊆ X`, in the essential image
of the completion functor of `U`: this is condition (2) of [Stacks, Tag 0EIL], that `(ℱₙ)` is the
completion of a coherent `𝒪_U`-module. It is the spelling of the conclusion of
[Stacks, Tag 0EJ9] that this file consumes.

## References

* [Stacks Project, Tag 0EJC](https://stacks.math.columbia.edu/tag/0EJC)
* [Stacks Project, Tag 0EJ9](https://stacks.math.columbia.edu/tag/0EJ9)
* [Stacks Project, Tag 0EJA](https://stacks.math.columbia.edu/tag/0EJA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

attribute [local instance high] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-- **Stacks Project, Tag 0EJC.** Let `(A, 𝔪)` be a Noetherian local ring which has a dualizing
complex and is complete with respect to `f ∈ 𝔪`, let `(ℱₙ)` be an object of `Coh(U, f𝒪_U)` where
`U` is the punctured spectrum of `A`, and set `Y = V(f) ⊆ X = Spec(A)`. If for every
`y ∈ U ∩ V(f)` closed in `U`, i.e. with `dim({y}‾) = 1`, the `𝒪_{X,y}^∧`-module `ℱ_y^∧` satisfies

1. `ℱ_y^∧[1/f]` is `(S₂)` as an `𝒪_{X,y}^∧[1/f]`-module, and
2. `dim(𝒪_{X,y}^∧/𝔭) ≥ 3` for every `𝔭 ∈ Ass(ℱ_y^∧[1/f])`,

then `(ℱₙ)` is the completion of a coherent `𝒪_U`-module. -/
@[stacks 0EJC]
public theorem essImage_completionFunctor_of_hasSerreCompletedStalkConditions
    (S : AlgebraizationSituation.{u}) [IsLocalRing S.A] [IsAdicComplete S.I S.A]
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) (f : S.A)
    (ha : S.a = IsLocalRing.maximalIdeal S.A)
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K)
    (hI : S.I = Ideal.span {f})
    (hserre : ∀ (y : S.U.toScheme) (z : S.Y), S.U.ι.base y = S.Yι.base z →
      Order.height (S.U.ι.base y) = 1 → HasSerreCompletedStalkConditions S F f y) :
    (completionFunctor S.U.toScheme (S.Yι.ker.comap S.U.ι)).essImage (toKerSystem S F) :=
  essImage_completionFunctor_of_isLocalRing_of_eq_span_singleton S F f ha hdual hI
    (satisfiesDepthInequalities_of_completedStalk_serre S F f ha hdual hI hserre)

end Stacks.Algebraization

end

module

public import StacksCore.Tactic.StacksAttribute
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.AlgebraizationCdOne
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.ImprovingFormalModulesDepthThreeCarrier
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.Algebraization

/-!
# Algebraization in cohomological dimension one: the theorem

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, the affine scheme
`X = Spec(A)`, its closed subschemes `Y = V(I)` and `Z = V(𝔞)`, and the open complement
`U = X ∖ Z`. [Stacks, Tag 0EJJ]: let `(ℱₙ)` be an object of `Coh(U, I𝒪_U)` and assume

1. `A` has a dualizing complex and `cd(A, I) = 1`, and
2. `(ℱₙ)` satisfies the `(2, 3)`-inequalities of [Stacks, Tag 0EJ3].

Then `(ℱₙ)` extends to `X`; in particular, if `A` is `I`-adically complete, then `(ℱₙ)` is the
completion of a coherent `𝒪_U`-module.

## The proof

As in the source. [Stacks, Tag 0EJG] with `d = 1 = cd(A, I)`, whose hypothesis is then exactly
the `(2, 3)`-inequalities, gives the inverse system `(ℱ''ₙ)` of coherent `𝒪_U`-modules of depth
`depth(ℱ''_{n,y}) + δ^Y_Z(y) ≥ 3` on `U ∩ Y`, an object `(ℋₙ)` of `Coh(U, I𝒪_U)` pro-isomorphic to
it, and a morphism `(ℱₙ) ⟶ (ℋₙ)` whose levelwise kernels and cokernels are annihilated by a power
of `I` (`Stacks.Algebraization.exists_proIso_coherentAdicSystem_depthThreeImprovedSystem`). Then
`Stacks.Algebraization.extendsToX_of_annihilated_of_proIso_depthThree` applies: `(ℋₙ)` extends
canonically to `X` by [Stacks, Tag 0EJI], hence extends to `X` by [Stacks, Tag 0EIR], and so does
`(ℱₙ)` by [Stacks, Tag 0EIU]. The final clause is [Stacks, Tag 0EIL]: extension to `X` over an
`I`-adically complete `A` makes the system the restriction of the completion of a coherent
`𝒪_X`-module, which is the completion of the restricted coherent `𝒪_U`-module.

## Main results

* `Stacks.Algebraization.extendsToX_of_cd_one_of_satisfiesDepthInequalities` — [Stacks, Tag 0EJJ].
* `Stacks.Algebraization.isCompletion_of_cd_one_of_satisfiesDepthInequalities` — its final clause.

## Implementation notes

`Stacks.Algebraization.ExtendsToX` and the completion functor are stated for systems along the
pullback to `U` of the kernel ideal sheaf of `Y ⟶ X`; the system `(ℱₙ)`, given along
`Stacks.Algebraization.idealOnOpen`, is read there through `Stacks.Algebraization.toKerSystem`,
which leaves its underlying diagram unchanged.

The dualizing complex lives in the derived category `HasDerivedCategory.standard` of `A`-modules,
as in [Stacks, Tag 0EJG] and [Stacks, Tag 0EJI] here; that instance is made local with high
priority because an imported file declares a global instance for module categories in a smaller
universe.

## References

* [Stacks Project, Tag 0EJJ](https://stacks.math.columbia.edu/tag/0EJJ)
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC), the situation.
* [Stacks Project, Tag 0EJ3](https://stacks.math.columbia.edu/tag/0EJ3), the inequalities.
* [Stacks Project, Tag 0EJG](https://stacks.math.columbia.edu/tag/0EJG)
* [Stacks Project, Tag 0EJI](https://stacks.math.columbia.edu/tag/0EJI)
* [Stacks Project, Tag 0EIR](https://stacks.math.columbia.edu/tag/0EIR)
* [Stacks Project, Tag 0EIU](https://stacks.math.columbia.edu/tag/0EIU)
* [Stacks Project, Tag 0EIL](https://stacks.math.columbia.edu/tag/0EIL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance high] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

variable (S : AlgebraizationSituation.{u})

/-- **Stacks Project, Tag 0EJJ (algebraization in cohomological dimension one).** In Situation
0EHC let `(ℱₙ)` be an object of `Coh(U, I𝒪_U)`. Assume (1) `A` has a dualizing complex and
`cd(A, I) = 1`, and (2) `(ℱₙ)` satisfies the `(2, 3)`-inequalities. Then `(ℱₙ)` extends to `X`. -/
@[stacks 0EJJ "(ℱₙ) extends to X"]
public theorem extendsToX_of_cd_one_of_satisfiesDepthInequalities
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K)
    (hcd : Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      (IsNoetherian.noetherian S.I) = 1)
    (hineq : SatisfiesDepthInequalities S F 2 3) :
    ExtendsToX S (toKerSystem S F) := by
  have hineq' : SatisfiesDepthInequalities S F 2 (2 + 1) := by
    norm_num
    exact hineq
  obtain ⟨F'', -, hcoh, hdepth, ⟨H, e, σ, -, -, -, hσ⟩, -⟩ :=
    exists_proIso_coherentAdicSystem_depthThreeImprovedSystem S hdual 1 hcd.le F hineq'
  have := hcoh
  exact extendsToX_of_annihilated_of_proIso_depthThree S hdual hcd F H σ.hom hσ F'' e
    fun n y z hyz => hdepth (op n) y z hyz

/-- **Stacks Project, Tag 0EJJ, the final clause.** In the situation of Tag 0EJJ, if moreover `A`
is `I`-adically complete, then `(ℱₙ)` is the completion of a coherent `𝒪_U`-module. -/
@[stacks 0EJJ "in particular, for I-adically complete A, (ℱₙ) is the completion of a coherent \
𝒪_U-module"]
public theorem isCompletion_of_cd_one_of_satisfiesDepthInequalities [IsAdicComplete S.I S.A]
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K)
    (hcd : Stacks.LocalCohomology.cohomologicalDimension S.A S.I
      (IsNoetherian.noetherian S.I) = 1)
    (hineq : SatisfiesDepthInequalities S F 2 3) :
    (completionFunctor S.U.toScheme (S.Yι.ker.comap S.U.ι)).essImage (toKerSystem S F) :=
  (isCompletion_iff_ofRestriction S (toKerSystem S F)).mpr
    ((isCompletionOfRestriction_iff_isRestrictionOfCompletion S (toKerSystem S F)).mpr
      (isRestrictionOfCompletion_of_extendsToX S (toKerSystem S F)
        (extendsToX_of_cd_one_of_satisfiesDepthInequalities S F hdual hcd hineq)))

end Stacks.Algebraization

end

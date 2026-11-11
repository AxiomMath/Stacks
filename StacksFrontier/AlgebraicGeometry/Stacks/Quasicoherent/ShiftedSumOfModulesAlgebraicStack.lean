module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ShiftedSumOfModules
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafLqcFbcDerivedLimitOfTruncations

/-!
# A sum of shifted modules in `LQCoh^fbc` on an algebraic stack is their product (Stacks 08IZ)

Let `𝒳` be an algebraic stack and let `ℱ_n`, `n ≥ 0`, be sheaves of `𝒪_𝒳`-modules on the big
fppf site of `𝒳` which are locally quasi-coherent (**Stacks 06WJ**) and have the flat base change
property of **Stacks 0762**.  **Stacks 08IZ** says that the canonical map

`⊕_n ℱ_n[n] ⟶ ∏_n ℱ_n[n]`

is an isomorphism in `D(𝒪_𝒳)`.  The canonical map is `Pi.lift (Sigma.π ...)`, the map whose
component from the `m`-th summand to the `n`-th factor is the identity for `m = n` and zero
otherwise.

The flat base change property is read as in the source, with the inverse image of *sheaves* of
modules: `AlgebraicGeometry.Stack.IsLocallyQuasicoherentWithSheafFlatBaseChange`, as in the
library's **Stacks 08IY**,
`AlgebraicGeometry.Stack.exists_isDerivedLimit_truncGETower_of_lqcohSheafFbc_algebraicStack`.

## The proof

It is the source's: Stacks 08IY applied to the sum.  The inputs of 08IY are discharged as in the
proof of 08IY in the library.

* The vanishing `H^q(x, ℱ_n) = 0` for `q > 0` and `x` lying over an affine scheme is
  `AlgebraicGeometry.Stack.isZero_rightDerived_evaluation_of_sheafFlatBaseChange_algebraicStack`.
* The objects lying over an affine scheme cover `𝒳_fppf`:
  `AlgebraicGeometry.Stack.hasEnoughObjects_isAffineOver_of_essentiallySmall`.
* The rest — the cohomology sheaves of the sum are the `ℱ_n`, the sum is the derived limit of its
  canonical truncations (**Stacks 0D6P** with `d = 0`), and these are the finite partial sums —
  is `AlgebraicGeometry.Stack.isIso_coproductToProduct_shiftedSingleFamily_of_isZero_rightDerived`.

Nothing is a hypothesis beyond the source's.  The total category of an algebraic stack has its
morphisms in the universe of the schemes and is essentially small
(`AlgebraicGeometry.Stack.essentiallySmall_obj_algebraicStack`), so its fppf modules form a
Grothendieck abelian category (`SheafOfModules.isGrothendieckAbelian_of_essentiallySmall`), which
supplies sheafification, enough injectives and the countable sums and products of `D(𝒪_𝒳)`
(**Stacks 07D9**).

## The index set

The source writes `ℱ_n` without saying over what the index `n` runs.  It is read here as `n ≥ 0`,
which is the case the section applies — immediately afterwards, to `E = ⊕_{m ≥ 0} 𝒪_𝒳[m]` — and
the case the source's proof, 08IY alone, supports.

## Main results

* `AlgebraicGeometry.Stack.isIso_coproductToProduct_shiftedSingleFamily_algebraicStack`:
  **Stacks 08IZ**.

## References

* [Stacks Project, Tag 08IZ](https://stacks.math.columbia.edu/tag/08IZ)
* [Stacks Project, Tag 08IY](https://stacks.math.columbia.edu/tag/08IY)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u w

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives
  AlgebraicGeometry.BigFppfOver.hasPointwiseRightKanExtension_op_homFunctor

namespace AlgebraicGeometry.Stack

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance 10] hasSheafifyEssentiallySmallSite
attribute [local instance] FibredSite.wEqualsLocallyBijective_associatedTopology
  enoughInjectives_fppfSiteModules_of_essentiallySmall
  Stacks.Cohomology.AcyclicCover.evaluation_additive
  SheafOfModules.isGrothendieckAbelian_of_essentiallySmall

/-- **Stacks 08IZ.** Let `𝒳` be an algebraic stack and let `ℱ_n`, `n ≥ 0`, be sheaves of
`𝒪_𝒳`-modules on its big fppf site which are locally quasi-coherent (**Stacks 06WJ**) and have
the flat base change property of **Stacks 0762**, read with the inverse image of sheaves of
modules.  Then the canonical map

`⊕_n ℱ_n[n] ⟶ ∏_n ℱ_n[n]`

is an isomorphism in `D(𝒪_𝒳)`.

As in the source, this is **Stacks 08IY** for the sum: the higher cohomology of each `ℱ_n`
vanishes over the objects lying over an affine scheme
(`AlgebraicGeometry.Stack.isZero_rightDerived_evaluation_of_sheafFlatBaseChange_algebraicStack`),
those objects cover `𝒳_fppf`
(`AlgebraicGeometry.Stack.hasEnoughObjects_isAffineOver_of_essentiallySmall`), and
`AlgebraicGeometry.Stack.isIso_coproductToProduct_shiftedSingleFamily_of_isZero_rightDerived`
concludes. -/
@[stacks 08IZ "for an algebraic stack 𝒳 and a family (ℱ_n)_{n ≥ 0} of locally quasi-coherent \
fppf 𝒪_𝒳-modules with the flat base change property of 0762 (read with the inverse image of \
sheaves of modules), the canonical map ⊕_n ℱ_n[n] → ∏_n ℱ_n[n] is an isomorphism in D(𝒪_𝒳); \
the index n runs over n ≥ 0, the case the section applies"]
theorem isIso_coproductToProduct_shiftedSingleFamily_algebraicStack
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (F : ℕ → fppfSiteModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids)
    (hF : ∀ n : ℕ, IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, _, _, u} B E h S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (F n).val) :
    IsIso (Pi.lift (Sigma.π (shiftedSingleFamily B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids F))) :=
  isIso_coproductToProduct_shiftedSingleFamily_of_isZero_rightDerived B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids F
    (hasEnoughObjects_isAffineOver_of_essentiallySmall B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids)
    (fun n V hV q hq =>
      isZero_rightDerived_evaluation_of_sheafFlatBaseChange_algebraicStack B E h S hS 𝒳 (F n)
        (hF n) V hV q hq)

end AlgebraicGeometry.Stack

end

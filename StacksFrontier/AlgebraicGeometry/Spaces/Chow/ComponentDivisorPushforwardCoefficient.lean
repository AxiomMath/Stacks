module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackPrincipalDivisorComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaCoefficients
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardClosedImmersionSquare

/-!
# The coefficients of the right-hand side of Stacks 0EQ2

The right-hand side of Stacks 0EQ2 is the cycle whose coefficient at an integral closed subspace
`Z ⊆ X` is `∑_{X'} ((X' → X)_* div_{X'}(g ∘ f|_{X'}))(Z)`, the sum running over the irreducible
components `X'` of `X`
(`AlgebraicGeometry.Space.EtaleComponentDivisorData.componentPushforwardCoeff`, read at the
canonical data of Stacks 0ENK through
`AlgebraicGeometry.Space.EtaleComponentDivisorDataOfGood.toEtaleComponentDivisorData`). This file
computes each term of that sum: the pushforward is along the inclusion of an integral closed
subspace, so its coefficient at `Z` is the coefficient of `div_{X'}(g ∘ f|_{X'})` at the integral
closed subspace of `X'` that `Z` comes from, and zero when `Z` comes from none.

## Main results

* `componentDivisorPushforward_eq_integralClosedSubspacePushforward`: the pushforward of
  Stacks 0EP1 along the inclusion of an irreducible component is the pushforward
  `AlgebraicGeometry.Space.integralClosedSubspacePushforward` with which rational equivalence is
  defined.
* `componentDivisorPushforward_apply_pushforward`: its coefficient at the image of an integral
  closed subspace `Z' ⊆ X'` is the coefficient of `div_{X'}(g ∘ f|_{X'})` at `Z'`.
* `componentDivisorPushforward_apply_of_forall_ne`: its coefficient vanishes at an integral closed
  subspace of `X` which is the image of none.

## References

* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
* [Stacks Project, Tag 0EQ2](https://stacks.math.columbia.edu/tag/0EQ2)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

namespace EtaleComponentDivisorDataOfGood

variable {D : BaseSpaceDimensionSituation.{u}}
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    {sX : X ⟶ D.space} {hX : D.IsGood sX} {sY : Y ⟶ D.space} {hY : D.IsGood sY}
    {f : X ⟶ Y} {hbase : f ≫ sY = sX} {hetale : IsEtale D.site D.base D.base_mem f}
    {hintY : IsIntegralSpace D.site D.base D.base_mem Y} {n : ℤ}
    {hnY : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (n : EInt)}
    {g : rationalFunctions D.site D.base D.base_mem hY.1} {hg : IsUnit g}
    (data : EtaleComponentDivisorDataOfGood D sX hX sY hY f hbase hetale hintY n hnY g hg)
    (W : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1)

/-- **The pushforward `(X' → X)_* div_{X'}(g ∘ f|_{X'})` is the pushforward of the localization
sequence.** The inclusion of an irreducible component is the inclusion of an integral closed
subspace, so the pushforward of Stacks 0EP1 along it is
`AlgebraicGeometry.Space.integralClosedSubspacePushforward`, the pushforward with which rational
equivalence is defined. -/
theorem componentDivisorPushforward_eq_integralClosedSubspacePushforward :
    data.toEtaleComponentDivisorData.componentDivisorPushforward W =
      integralClosedSubspacePushforward D sX hX W.1 (n - 1)
        (data.toEtaleComponentDivisorData.componentDivisorCycle W) :=
  properCyclePushforward_ι_eq_integralClosedSubspacePushforward D sX hX W.1 (n - 1)
    (data.toEtaleComponentDivisorData.componentDivisorCycle W)

/-- **The coefficient of `(X' → X)_* div_{X'}(g ∘ f|_{X'})` at the image of an integral closed
subspace `Z' ⊆ X'`** is the coefficient of `div_{X'}(g ∘ f|_{X'})` at `Z'`. This is one of the two
cases of the coefficient of a pushforward along a closed immersion, which is the extension by
zero of the coefficient family along the injection of integral closed subspaces. -/
theorem componentDivisorPushforward_apply_pushforward
    (Z' : IntegralClosedSubspace D.site D.base D.base_mem W.1.subspace.toFunctor) :
    (data.toEtaleComponentDivisorData.componentDivisorPushforward W).1
        (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1
          W.1.isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX) W.1.isClosedSubspace.2 Z') =
      (data.toEtaleComponentDivisorData.componentDivisorCycle W).1 Z' := by
  rw [data.componentDivisorPushforward_eq_integralClosedSubspacePushforward W]
  exact integralClosedSubspacePushforward_apply_pushforward D sX hX W.1
    (data.toEtaleComponentDivisorData.componentDivisorCycle W) Z'

/-- **The coefficient of `(X' → X)_* div_{X'}(g ∘ f|_{X'})` vanishes at an integral closed
subspace of `X` which is the image of none of `X'`.** -/
theorem componentDivisorPushforward_apply_of_forall_ne
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : ∀ Z' : IntegralClosedSubspace D.site D.base D.base_mem W.1.subspace.toFunctor,
      IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 W.1.isClosedSubspace.1
        (D.isDecentSpace_of_isGood sX hX) W.1.isClosedSubspace.2 Z' ≠ Z) :
    (data.toEtaleComponentDivisorData.componentDivisorPushforward W).1 Z = 0 := by
  rw [data.componentDivisorPushforward_eq_integralClosedSubspacePushforward W]
  exact integralClosedSubspacePushforward_apply_of_forall_ne D sX hX W.1
    (data.toEtaleComponentDivisorData.componentDivisorCycle W) Z hZ

end EtaleComponentDivisorDataOfGood

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentDivisorPushforwardCoefficient
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackPrincipalDivisorComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrimeDivisorDeltaDimensionOfGood

/-!
# The right-hand side of Stacks 0EQ2 as a sum of orders of vanishing

The right-hand side of Stacks 0EQ2 is the cycle whose coefficient at an integral closed subspace
`Z ⊆ X` is `∑_{X'} ((X' → X)_* div_{X'}(g ∘ f|_{X'}))(Z)`, the sum running over *all* the
irreducible components `X'` of `X`
(`AlgebraicGeometry.Space.EtaleComponentDivisorData.componentPushforwardCoeff`, read at the
canonical data of Stacks 0ENK through
`AlgebraicGeometry.Space.EtaleComponentDivisorDataOfGood.toEtaleComponentDivisorData`). This cuts
that sum down to the components *through the generic point of `Z`* and reads each surviving term
as an order of vanishing: for such a component `X'` the subspace `Z` is the image of an integral
closed subspace `Z ∩ X'` of `X'`, which has the same δ-dimension and so is a prime divisor of
`X'`, and the term is `ord_{Z ∩ X'}(g ∘ f|_{X'})`.

## Main results

* `IntegralClosedSubspace.exists_pushforward_eq_of_ambientGenericPoint_mem`: an integral closed
  subspace of `X` whose generic point lies on a closed subspace `X'` is the image of an integral
  closed subspace of `X'`.
* `EtaleComponentDivisorDataOfGood.componentDivisorPushforward_apply_eq_zero_of_notMem`: the term
  of a component not through the generic point of `Z` vanishes.
* `EtaleComponentDivisorDataOfGood.componentDivisorCycle_apply_eq_ord`: the coefficient of
  `div_{X'}(g ∘ f|_{X'})` at an integral closed subspace of `X'` of codimension one is the order
  of vanishing of `g ∘ f|_{X'}` along it.
* `EtaleComponentDivisorDataOfGood.componentPushforwardCoeff_eq_finsum_subtype`: the sum over all
  the components is the sum over the components through the generic point of `Z`.
* `EtaleComponentDivisorDataOfGood.componentPushforwardCoeff_eq_finsum_componentDivisorCycle`:
  the same sum, with the term of each component `X'` read as the coefficient of
  `div_{X'}(g ∘ f|_{X'})` at the subspace of `X'` that `Z` comes from.

## Implementation notes

**Why the sum is indexed by a subtype.** The family of irreducible components of `|X|` is only
locally finite, so the sum over all components is a `finsum`; cutting it down to the components
through the generic point of `Z` is `finsum_mem_subtype`-style bookkeeping on the subtype of
components containing that point, the complementary terms vanishing by
`EtaleComponentDivisorDataOfGood.componentDivisorPushforward_apply_of_forall_ne`.

**Why the restriction `Z ∩ X'` is a parameter.** The subspace of `X'` whose image is `Z` is
unique (`AlgebraicGeometry.Space.IntegralClosedSubspace.injective_pushforward`) but is produced
by an existence statement, so the statements below take the family of restrictions as a
universally quantified datum together with the equations it satisfies, rather than choosing one.

## References

* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
* [Stacks Project, Tag 0EPZ](https://stacks.math.columbia.edu/tag/0EPZ)
* [Stacks Project, Tag 0EQ1](https://stacks.math.columbia.edu/tag/0EQ1)
* [Stacks Project, Tag 0EQ2](https://stacks.math.columbia.edu/tag/0EQ2)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### An integral closed subspace whose generic point lies on a closed subspace -/

section Presentation

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **An integral closed subspace of `X` whose generic point lies on an integral closed subspace
`X' ⊆ X` is the image of an integral closed subspace of `X'`.** -/
theorem IntegralClosedSubspace.exists_pushforward_eq_of_ambientGenericPoint_mem
    (hX : IsAlgebraicSpace B S hS X) (hdec : IsDecentSpace B S hS X)
    (W : IntegralClosedSubspace B S hS X) (Z : IntegralClosedSubspace B S hS X)
    (hmem : Z.ambientGenericPoint B S hS ∈ subspacePointSet B S hS X W.subspace) :
    ∃ Z' : IntegralClosedSubspace B S hS W.subspace.toFunctor,
      IntegralClosedSubspace.pushforward B S hS hX W.isClosedSubspace.1 hdec
        W.isClosedSubspace.2 Z' = Z := by
  refine IntegralClosedSubspace.exists_pushforward_eq B S hS hX W.isClosedSubspace.1 hdec
    W.isIntegralSpace.2.1 W.isClosedSubspace.2 Z ?_
  rw [← Z.isGenericPoint_ambientGenericPoint B S hS hX]
  exact closure_minimal (Set.singleton_subset_iff.2 hmem)
    (isClosed_range_pointsMap_integralClosedSubspace B S hS hX W)

/-- The generic point of the image of an integral closed subspace along the inclusion of a closed
subspace lies on that closed subspace. -/
theorem IntegralClosedSubspace.ambientGenericPoint_pushforward_mem
    (hX : IsAlgebraicSpace B S hS X) (hdec : IsDecentSpace B S hS X)
    (W : IntegralClosedSubspace B S hS X)
    (Z' : IntegralClosedSubspace B S hS W.subspace.toFunctor) :
    (IntegralClosedSubspace.pushforward B S hS hX W.isClosedSubspace.1 hdec
          W.isClosedSubspace.2 Z').ambientGenericPoint B S hS ∈
      subspacePointSet B S hS X W.subspace := by
  rw [IntegralClosedSubspace.ambientGenericPoint_pushforward B S hS hX W.isClosedSubspace.1 hdec
    W.isClosedSubspace.2 Z']
  exact ⟨_, rfl⟩

end Presentation

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

/-! ### The terms of components not through the generic point -/

/-- **The term of a component not through the generic point of `Z` vanishes.** If the generic
point of `Z` does not lie on the irreducible component `X'`, the coefficient at `Z` of
`(X' → X)_* div_{X'}(g ∘ f|_{X'})` is zero. -/
theorem componentDivisorPushforward_apply_eq_zero_of_notMem
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : Z.ambientGenericPoint D.site D.base D.base_mem ∉
      subspacePointSet D.site D.base D.base_mem X W.1.subspace) :
    (data.toEtaleComponentDivisorData.componentDivisorPushforward W).1 Z = 0 := by
  refine data.componentDivisorPushforward_apply_of_forall_ne W Z fun Z' hZ' => hZ ?_
  rw [← hZ']
  exact IntegralClosedSubspace.ambientGenericPoint_pushforward_mem D.site D.base D.base_mem hX.1
    (D.isDecentSpace_of_isGood sX hX) W.1 Z'

/-! ### The surviving terms as orders of vanishing -/

/-- **The coefficient of `div_{X'}(g ∘ f|_{X'})` at an integral closed subspace of `X'` of
codimension one is an order of vanishing.** For an integral closed subspace `Z'` of the
irreducible component `X'` of codimension one in `|X'|`, the coefficient of the principal divisor
of `g ∘ f|_{X'}` at `Z'` is the order of vanishing of `g ∘ f|_{X'}` along the prime divisor `Z'`,
computed with the canonical embedding of Stacks 0ENK on `X'`. -/
theorem componentDivisorCycle_apply_eq_ord
    (Z' : IntegralClosedSubspace D.site D.base D.base_mem W.1.subspace.toFunctor)
    (hcod : codimension (integralClosedSubspaceSupport D.site D.base D.base_mem
      (isGood_integralClosedSubspace D sX hX W.1).1 Z') = 1) :
    (data.toEtaleComponentDivisorData.componentDivisorCycle W).1 Z' =
      (integralClosedSubspaceFractionEmbedding D sX hX W.1).ord
        (Units.map (rationalFunctionMap D.site D.base D.base_mem
          (isGood_integralClosedSubspace D sX hX W.1).1 hY.1 W.1.isIntegralSpace hintY
          (W.1.subspace.ι ≫ f) (data.dom W)).toMonoidHom hg.unit)
        (Z'.toPrimeDivisor D.site D.base D.base_mem
          (isGood_integralClosedSubspace D sX hX W.1).1 hcod) := by
  let E := integralClosedSubspaceFractionEmbedding D sX hX W.1
  let := E.nontrivial
  let := E.isNoetherianRing
  let := E.krullDimLE
  have hZ' := IntegralClosedSubspace.toIntegralClosedSubspace_toPrimeDivisor
    D.site D.base D.base_mem (isGood_integralClosedSubspace D sX hX W.1).1 Z' hcod
  have key := principalDivisorCycleCoefficients_toIntegralClosedSubspace D
    (W.1.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W.1)
    W.1.isIntegralSpace.2.1 E.emb
    (data.toEtaleComponentDivisorData.componentRationalFunction W)
    (fun Q => data.toEtaleComponentDivisorData.unit W Q)
    (Z'.toPrimeDivisor D.site D.base D.base_mem
      (isGood_integralClosedSubspace D sX hX W.1).1 hcod)
  rwa [hZ'] at key

include data sY hY hbase hetale hintY hnY in
/-- An integral closed subspace of an irreducible component `X'` whose image in `X` has
δ-dimension `n - 1` has codimension one in `|X'|`. -/
theorem codimension_eq_one_of_deltaDimension_pushforward_eq
    (Z' : IntegralClosedSubspace D.site D.base D.base_mem W.1.subspace.toFunctor)
    (hZ : deltaDimension D sX (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1
      W.1.isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX) W.1.isClosedSubspace.2 Z') =
      n - 1) :
    codimension (integralClosedSubspaceSupport D.site D.base D.base_mem
      (isGood_integralClosedSubspace D sX hX W.1).1 Z') = 1 := by
  have hdim : deltaDimension D (W.1.subspace.ι ≫ sX) Z' = n - 1 := by
    rw [← hZ]
    exact (IntegralClosedSubspace.deltaDimension_pushforward D sX hX.2.2 hX.1
      W.1.isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX) W.1.isClosedSubspace.2 Z').symm
  exact ((isPrimeDivisor_tfae_of_isIntegralSpace' D (W.1.subspace.ι ≫ sX)
    (isGood_integralClosedSubspace D sX hX W.1) W.1.isIntegralSpace
    (deltaDimensionClosed_univ_irreducibleComponentSubspace D sX hX sY hY hbase hetale hintY
      hnY W (isGood_integralClosedSubspace D sX hX W.1) (data.dom W)) Z').out 3 2).mp hdim

/-! ### The sum over the components through the generic point -/

/-- **The right-hand side of Stacks 0EQ2 at `Z` is a sum over the components through the generic
point of `Z`.** The `finsum` over all the irreducible components of `|X|` is the `finsum` over
the subtype of those containing the generic point of `Z`. -/
theorem componentPushforwardCoeff_eq_finsum_subtype
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    data.toEtaleComponentDivisorData.componentPushforwardCoeff Z =
      ∑ᶠ V : {V : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1 //
          Z.ambientGenericPoint D.site D.base D.base_mem ∈
            subspacePointSet D.site D.base D.base_mem X V.1.subspace},
        (data.toEtaleComponentDivisorData.componentDivisorPushforward V.1).1 Z := by
  classical
  rw [EtaleComponentDivisorData.componentPushforwardCoeff]
  refine Eq.trans ?_ (finsum_subtype_eq_finsum_cond
    (f := fun V : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1 =>
      (data.toEtaleComponentDivisorData.componentDivisorPushforward V).1 Z)
    (fun V => Z.ambientGenericPoint D.site D.base D.base_mem ∈
      subspacePointSet D.site D.base D.base_mem X V.1.subspace)).symm
  refine finsum_congr fun V => ?_
  by_cases hV : Z.ambientGenericPoint D.site D.base D.base_mem ∈
      subspacePointSet D.site D.base D.base_mem X V.1.subspace
  · rw [finsum_eq_if, ite_eq_left hV]
  · rw [finsum_eq_if, ite_eq_right hV]
    exact data.componentDivisorPushforward_apply_eq_zero_of_notMem V Z hV

/-- **The right-hand side of Stacks 0EQ2 at `Z`, each term read on the component.** For a
component `X'` through the generic point of `Z`, the subspace `Z` is the image of an integral
closed subspace `r X'` of `X'`, and the term of `X'` is the coefficient of
`div_{X'}(g ∘ f|_{X'})` at `r X'`.

The family of restrictions is a datum rather than a choice; it exists by
`AlgebraicGeometry.Space.IntegralClosedSubspace.exists_pushforward_eq_of_ambientGenericPoint_mem`
and is unique by `AlgebraicGeometry.Space.IntegralClosedSubspace.injective_pushforward`. -/
theorem componentPushforwardCoeff_eq_finsum_componentDivisorCycle
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (r : ∀ V : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1,
      Z.ambientGenericPoint D.site D.base D.base_mem ∈
        subspacePointSet D.site D.base D.base_mem X V.1.subspace →
      IntegralClosedSubspace D.site D.base D.base_mem V.1.subspace.toFunctor)
    (hr : ∀ (V : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1)
      (hV : Z.ambientGenericPoint D.site D.base D.base_mem ∈
        subspacePointSet D.site D.base D.base_mem X V.1.subspace),
      IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1
        V.1.isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX) V.1.isClosedSubspace.2
        (r V hV) = Z) :
    data.toEtaleComponentDivisorData.componentPushforwardCoeff Z =
      ∑ᶠ V : {V : IrreducibleComponentSubspace D.site D.base D.base_mem hX.1 //
          Z.ambientGenericPoint D.site D.base D.base_mem ∈
            subspacePointSet D.site D.base D.base_mem X V.1.subspace},
        (data.toEtaleComponentDivisorData.componentDivisorCycle V.1).1 (r V.1 V.2) := by
  rw [data.componentPushforwardCoeff_eq_finsum_subtype Z]
  refine finsum_congr fun V => ?_
  have h := data.componentDivisorPushforward_apply_pushforward V.1 (r V.1 V.2)
  rwa [hr V.1 V.2] at h

end EtaleComponentDivisorDataOfGood

end AlgebraicGeometry.Space

end

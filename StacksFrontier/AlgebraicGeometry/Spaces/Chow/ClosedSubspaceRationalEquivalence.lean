module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinPushforwardFirstChernCapCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaProof.ChowClass
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RefinedGysinPushforwardCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RegularSectionFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.TrivialRestrictionGysin

/-!
# Rational equivalences on a closed subspace, read on the ambient space

In Situation 0EDT let `X/B` be good and `i : Y → X` the inclusion of a closed subspace. The
pushforward `i_* : Z_k(Y) → Z_k(X)` of Stacks 0EQA is injective and identifies the integral
closed subspaces of `Y` with those of `X` contained in `Y`. Every integral closed subspace
`V ⊆ Y` is identified with its image `V' ⊆ X`, and the principal divisors on `V` and on `V'`,
both taken at the canonical embeddings of Stacks 0ENK, correspond under `i_*`; this is
`AlgebraicGeometry.Space.exists_integralClosedSubspacePushforward_eq_cycleGroupClosedPushforward`.

Consequently a locally finite sum of principal divisors on the images in `X` of integral closed
subspaces of `Y` is the pushforward of a cycle on `Y` which is rationally equivalent to zero on
`Y`, with the witnesses where they were.

## Main results

* `AlgebraicGeometry.Space.integralClosedSubspacePushforward_injective`: the pushforward from an
  integral closed subspace is injective on cycles.
* `AlgebraicGeometry.Space.integralClosedSubspacePushforward_cycleFamilySum`: the pushforward
  from an integral closed subspace of a locally finite sum.
* `AlgebraicGeometry.Space.exists_closedSubspaceCyclePushforward_eq_cycleFamilySum`: a locally
  finite sum of principal divisors on images of subspaces of `Y` is the pushforward of a
  rational equivalence on `Y`.

## References

* [Stacks Project, Tag 0EQA](https://stacks.math.columbia.edu/tag/0EQA)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u v w

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (Y : ClosedSubspaces D.site D.base D.base_mem X)

/-- The coefficient of `i_*β` at the image of an integral closed subspace `V ⊆ Y` is the
coefficient of `β` at `V`. -/
theorem closedSubspaceCyclePushforward_apply_closedSubspaceComponentImage {k : ℤ}
    (β : CycleGroup D (Y.1.ι ≫ sX) k)
    (V : IntegralClosedSubspace D.site D.base D.base_mem Y.1.toFunctor) :
    (closedSubspaceCyclePushforward D sX hX Y k β).1
        (closedSubspaceComponentImage D sX hX Y.1 Y.2 V) = β.1 V :=
  cycleClosedPushforward_apply_pushforward D hX.1 Y.2.1 (D.isDecentSpace_of_isGood sX hX)
    Y.2.2 β.1 V

omit Y in
/-- **The pushforward of cycles along the inclusion of an integral closed subspace is
injective.** -/
theorem integralClosedSubspacePushforward_injective
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) (k : ℤ) :
    Function.Injective (integralClosedSubspacePushforward D sX hX W k) :=
  injective_cycleGroupClosedPushforward D hX.1 W.isClosedSubspace.1
    (D.isDecentSpace_of_isGood sX hX) W.isClosedSubspace.2 sX hX.2.2 _ rfl k

/-- A pushforward from `Y` vanishes at an integral closed subspace of `X` which is not the image
of one of `Y`. -/
theorem closedSubspaceCyclePushforward_apply_of_forall_ne {k : ℤ}
    (β : CycleGroup D (Y.1.ι ≫ sX) k) (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : ∀ V, closedSubspaceComponentImage D sX hX Y.1 Y.2 V ≠ Z) :
    (closedSubspaceCyclePushforward D sX hX Y k β).1 Z = 0 :=
  cycleClosedPushforward_apply_of_forall_ne D hX.1 Y.2.1 (D.isDecentSpace_of_isGood sX hX)
    Y.2.2 β.1 Z hZ

omit Y in
/-- **The pushforward of a locally finite sum on an integral closed subspace.** If the
pushforward to `X` of each summand `(V_j → W)_* c_j` of a locally finite sum on an integral
closed subspace `W ⊆ X` is the pushforward of a cycle `c'_j` on the image `V'_j ⊆ X` of `V_j`,
then the pushforward to `X` of `∑ (V_j → W)_* c_j` is `∑ (V'_j → X)_* c'_j`. -/
theorem integralClosedSubspacePushforward_cycleFamilySum {J : Type v} {k : ℤ}
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (V : J → IntegralClosedSubspace D.site D.base D.base_mem W.subspace.toFunctor)
    (hV : LocallyFinite fun j =>
      subspacePointSet D.site D.base D.base_mem W.subspace.toFunctor (V j).subspace)
    (hV' : LocallyFinite fun j => subspacePointSet D.site D.base D.base_mem X
      (closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace (V j)).subspace)
    (c : ∀ j, CycleGroup D ((V j).subspace.ι ≫ W.subspace.ι ≫ sX) k)
    (c' : ∀ j, CycleGroup D
      ((closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace (V j)).subspace.ι ≫ sX)
      k)
    (hc : ∀ j, integralClosedSubspacePushforward D sX hX W k
        (integralClosedSubspacePushforward D (W.subspace.ι ≫ sX)
          (isGood_integralClosedSubspace D sX hX W) (V j) k (c j)) =
      integralClosedSubspacePushforward D sX hX
        (closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace (V j)) k (c' j)) :
    integralClosedSubspacePushforward D sX hX W k
        (cycleFamilySum D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W) V hV k c) =
      cycleFamilySum D sX hX
        (fun j => closedSubspaceComponentImage D sX hX W.subspace W.isClosedSubspace (V j)) hV' k
        c' :=
  cycleGroupClosedPushforward_cycleFamilySum (hX := hX) (W.subspace.ι ≫ sX)
    (isGood_integralClosedSubspace D sX hX W) W.isClosedSubspace.2 rfl V hV hV' c c' hc

/-- **A locally finite sum of principal divisors on images of subspaces of `Y` is the
pushforward of a rational equivalence on `Y`.** Let `{V_j}` be a family of integral closed
subspaces of `Y` whose images `V'_j ⊆ X` form a locally finite family of δ-dimension `k + 1`,
and `g_j` invertible rational functions on the `V'_j`. There is a `k`-cycle `β` on `Y`,
rationally equivalent to zero within any set containing the `|V_j|`, with
`i_*β = ∑ (V'_j → X)_* div(g_j)`: it is `∑ (V_j → Y)_* div(g'_j)` for the functions `g'_j`
carried along the isomorphisms `V'_j ≅ V_j` over `X`, the principal divisors being those of
Stacks 0EQ6 at the canonical embeddings of Stacks 0ENK. -/
theorem exists_closedSubspaceCyclePushforward_eq_cycleFamilySum
    {J : Type w} {k : ℤ}
    (V : J → IntegralClosedSubspace D.site D.base D.base_mem Y.1.toFunctor)
    (hV' : LocallyFinite fun j => subspacePointSet D.site D.base D.base_mem X
      (closedSubspaceComponentImage D sX hX Y.1 Y.2 (V j)).subspace)
    (g : ∀ j, (rationalFunctions D.site D.base D.base_mem (isGood_integralClosedSubspace D sX hX
      (closedSubspaceComponentImage D sX hX Y.1 Y.2 (V j))).1)ˣ)
    (hk : ∀ j, deltaDimensionClosed D
      ((closedSubspaceComponentImage D sX hX Y.1 Y.2 (V j)).subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D sX hX (closedSubspaceComponentImage D sX hX Y.1 Y.2 (V j)))
      Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt))
    (T : Set (points D.site D.base D.base_mem Y.1.toFunctor))
    (hT : ∀ j, subspacePointSet D.site D.base D.base_mem Y.1.toFunctor (V j).subspace ⊆ T) :
    ∃ β : CycleGroup D (Y.1.ι ≫ sX) k,
      closedSubspaceCyclePushforward D sX hX Y k β =
        cycleFamilySum D sX hX (fun j => closedSubspaceComponentImage D sX hX Y.1 Y.2 (V j)) hV' k
          (fun j => canonicalPrincipalDivisorCycleAt D _ (isGood_integralClosedSubspace D sX hX
            (closedSubspaceComponentImage D sX hX Y.1 Y.2 (V j)))
            (closedSubspaceComponentImage D sX hX Y.1 Y.2 (V j)).isIntegralSpace (g j) (hk j)) ∧
      IsCanonicallyRationallyEquivalentToZeroWithin.{u, max w v} D (Y.1.ι ≫ sX)
        (isGood_closedSubspace D sX hX Y) k β T := by
  have hYg := isGood_closedSubspace D sX hX Y
  choose c' hc' heq using fun j =>
    exists_integralClosedSubspacePushforward_eq_cycleGroupClosedPushforward (hX := hX) (Y.1.ι ≫ sX)
      hYg Y.2.2 rfl (V j) ⟨hk j, g j, rfl⟩
  have hV : LocallyFinite fun j =>
      subspacePointSet D.site D.base D.base_mem Y.1.toFunctor (V j).subspace := by
    refine (hV'.preimage_continuous (continuous_pointsMap D.site D.base D.base_mem Y.1.ι)).subset
      fun j => ?_
    rw [IntegralClosedSubspace.subspacePointSet_pushforward]
    exact Set.subset_preimage_image _ _
  refine ⟨cycleFamilySum D (Y.1.ι ≫ sX) hYg V hV k c',
    cycleGroupClosedPushforward_cycleFamilySum (hX := hX) _ hYg Y.2.2 rfl V hV hV' c' _ heq,
    ⟨ULift.{v} J, fun j => V j.down, hV.comp_injective Equiv.ulift.injective, fun j => c' j.down,
      fun j => hT j.down, fun j => hc' j.down, ?_⟩⟩
  exact (cycleFamilySum_comp_equiv D (Y.1.ι ≫ sX) hYg Equiv.ulift.{v} _ hV k _).symm

/-- Two families of integral closed subspaces which agree member by member carry the same
locally finite sums of principal divisors. -/
theorem exists_cycleFamilySum_canonicalPrincipalDivisorCycleAt_eq_of_forall_eq
    {J : Type w} {k : ℤ} (A B : J → IntegralClosedSubspace D.site D.base D.base_mem X)
    (hAB : ∀ j, A j = B j)
    (hB : LocallyFinite fun j => subspacePointSet D.site D.base D.base_mem X (B j).subspace)
    (g : ∀ j, (rationalFunctions D.site D.base D.base_mem
      (isGood_integralClosedSubspace D sX hX (B j)).1)ˣ)
    (hk : ∀ j, deltaDimensionClosed D ((B j).subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D sX hX (B j)) Set.univ isClosed_univ =
        ((k + 1 : ℤ) : EInt)) :
    ∃ (hA : LocallyFinite fun j => subspacePointSet D.site D.base D.base_mem X (A j).subspace)
      (hkA : ∀ j, deltaDimensionClosed D ((A j).subspace.ι ≫ sX)
        (isGood_integralClosedSubspace D sX hX (A j)) Set.univ isClosed_univ =
          ((k + 1 : ℤ) : EInt))
      (g' : ∀ j, (rationalFunctions D.site D.base D.base_mem
        (isGood_integralClosedSubspace D sX hX (A j)).1)ˣ),
      cycleFamilySum D sX hX A hA k (fun j => canonicalPrincipalDivisorCycleAt D _
          (isGood_integralClosedSubspace D sX hX (A j)) (A j).isIntegralSpace (g' j) (hkA j)) =
        cycleFamilySum D sX hX B hB k (fun j => canonicalPrincipalDivisorCycleAt D _
          (isGood_integralClosedSubspace D sX hX (B j)) (B j).isIntegralSpace (g j) (hk j)) := by
  obtain rfl : A = B := funext hAB
  exact ⟨hB, hk, g, rfl⟩

end AlgebraicGeometry.Space

end

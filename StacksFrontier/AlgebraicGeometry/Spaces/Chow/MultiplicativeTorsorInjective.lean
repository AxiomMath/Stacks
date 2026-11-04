module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatInverseImageDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.MultiplicativeTorsorIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChangeUnconditional

/-!
# Flat pullback along the multiplicative torsor is injective on cycles

In Situation 0EDT let `X/B` be good, let `ℒ` be an invertible `𝒪_X`-module and let
`q : T ⟶ X` be its multiplicative torsor (`AlgebraicGeometry.Space.torsorOfInvertible`).  This
file proves clause (4) of Stacks 0EQG: **the flat pullback `q^* : Z_k(X) → Z_{k+1}(T)` is
injective.**

## Main results

* `AlgebraicGeometry.Space.deltaDimension_torsorOfInvertiblePreimage`:
  `dim_δ(q^{-1}(W)) = dim_δ(W) + 1`.
* `AlgebraicGeometry.Space.injective_torsorOfInvertiblePreimage`: `W ↦ q^{-1}(W)` is injective.
* `AlgebraicGeometry.Space.flatPullbackMult_torsorOfInvertiblePreimage`: the coefficient of
  `q^{-1}(W')` in `q^*[W]` is `1` if `W = W'` and `0` otherwise.
* `AlgebraicGeometry.Space.torsorOfInvertibleFlatPullback_apply_preimage`: the coefficient of
  `q^*α` at `q^{-1}(W)` is the coefficient of `α` at `W`.
* `AlgebraicGeometry.Space.torsorOfInvertible_clause_four`: **Stacks 0EQG, clause (4).**

## References

* [Stacks Project, Tag 0EQG](https://stacks.math.columbia.edu/tag/0EQG)
* [Stacks Project, Tag 0EP5](https://stacks.math.columbia.edu/tag/0EP5)
* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1)
    (hL : IsInvertibleSheaf D p hp L)

/-- The set of points of `q^{-1}(W)` is the inverse image of the set of points of `W`. -/
theorem subspacePointSet_torsorOfInvertiblePreimage
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    subspacePointSet D.site D.base D.base_mem _
      (torsorOfInvertiblePreimage D p hp L hL W).subspace =
      pointsMap D.site D.base D.base_mem _ (torsorOfInvertibleProjection D p hp L hL).hom ⁻¹'
        subspacePointSet D.site D.base D.base_mem X W.subspace :=
  range_pointsMap_preimage_ι D.site D.base D.base_mem _ W.subspace

/-- **`W ↦ q^{-1}(W)` is injective.** -/
theorem injective_torsorOfInvertiblePreimage :
    Function.Injective (torsorOfInvertiblePreimage D p hp L hL) := by
  intro W W' h
  have hpts := congrArg (fun Z : IntegralClosedSubspace D.site D.base D.base_mem _ =>
    subspacePointSet D.site D.base D.base_mem _ Z.subspace) h
  simp only [subspacePointSet_torsorOfInvertiblePreimage] at hpts
  exact injective_integralClosedSubspaceSupport D.site D.base D.base_mem hp.1
    (TopologicalSpace.IrreducibleCloseds.ext
      ((isSurjective_torsorOfInvertibleProjection D p hp L hL).preimage_injective hpts))

/-- **`dim_δ(q^{-1}(W)) = dim_δ(W) + 1`** (Stacks 0EP5). -/
theorem deltaDimension_torsorOfInvertiblePreimage
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    deltaDimension D ((torsorOfInvertibleProjection D p hp L hL).hom ≫ p)
      (torsorOfInvertiblePreimage D p hp L hL W) = deltaDimension D p W + 1 := by
  have hT := isGood_torsorOfInvertible D p hp L hL
  have hirr : IsIrreducible (W.preimagePointSet D.site D.base D.base_mem
      (torsorOfInvertibleProjection D p hp L hL).hom) := by
    rw [IntegralClosedSubspace.preimagePointSet, ← subspacePointSet_torsorOfInvertiblePreimage]
    exact isIrreducible_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem _
  have := Subtype.irreducibleSpace hirr
  have hC : (Set.univ : Set (W.preimagePointSet D.site D.base D.base_mem
      (torsorOfInvertibleProjection D p hp L hL).hom)) ∈ irreducibleComponents _ := by
    rw [irreducibleComponents_eq_singleton]
    rfl
  have heq : torsorOfInvertiblePreimage D p hp L hL W =
      W.preimageComponent D.site D.base D.base_mem (torsorOfInvertibleProjection D p hp L hL).hom
        hT.1 (D.isDecentSpace_of_isGood _ hT) hp.1 ⟨_, hC⟩ := by
    refine eq_integralClosedSubspaceOfPoints D.site D.base D.base_mem hT.1
      (D.isDecentSpace_of_isGood _ hT) _ _ ?_
    rw [subspacePointSet_torsorOfInvertiblePreimage]
    change _ = Subtype.val '' Set.univ
    rw [Set.image_univ, Subtype.range_coe]
  rw [heq]
  exact IntegralClosedSubspace.deltaDimension_preimageComponent_of_isFlat D _ hT p hp rfl 1
    (isFlat_torsorOfInvertibleProjection D p hp L hL)
    (hasRelativeDimension_torsorOfInvertibleProjection D p hp L hL) W _

open Classical in
/-- **`q^*[W] = [q^{-1}(W)]`, coefficientwise**: the coefficient of `q^{-1}(W')` in `q^*[W]` is
`1` if `W' = W` and `0` otherwise. -/
theorem flatPullbackMult_torsorOfInvertiblePreimage
    (W W' : IntegralClosedSubspace D.site D.base D.base_mem X) :
    flatPullbackMult D _ (isGood_torsorOfInvertible D p hp L hL) p hp
        (torsorOfInvertibleProjection D p hp L hL).hom rfl 1
        (isFlat_torsorOfInvertibleProjection D p hp L hL)
        (hasRelativeDimension_torsorOfInvertibleProjection D p hp L hL) W
        (torsorOfInvertiblePreimage D p hp L hL W') = if W' = W then 1 else 0 := by
  have hT := isGood_torsorOfInvertible D p hp L hL
  set Z := torsorOfInvertiblePreimage D p hp L hL W with hZ
  have hdimZ : deltaDimensionSubspace D _ hT Z.subspace Z.isClosedSubspace ≤
      ((deltaDimension D ((torsorOfInvertibleProjection D p hp L hL).hom ≫ p) Z : ℤ) : EInt) :=
    (deltaDimensionSubspace_integralClosedSubspace D _ hT Z).le
  have hk : deltaDimension D p W + ((1 : ℕ) : ℤ) = deltaDimension D
    ((torsorOfInvertibleProjection D p hp L hL).hom ≫ p) Z := by
    rw [hZ, deltaDimension_torsorOfInvertiblePreimage, Nat.cast_one]
  have e1 : flatPullbackMult D _ hT p hp (torsorOfInvertibleProjection D p hp L hL).hom rfl 1
      (isFlat_torsorOfInvertibleProjection D p hp L hL)
      (hasRelativeDimension_torsorOfInvertibleProjection D p hp L hL) W
      (torsorOfInvertiblePreimage D p hp L hL W') =
      cycleCoeffOfClosedSubspace D _ hT Z.subspace Z.isClosedSubspace
        (deltaDimension D p W + ((1 : ℕ) : ℤ))
        (canonicalGeometricPoint D.site D.base D.base_mem Z.subspace.toFunctor)
        (torsorOfInvertiblePreimage D p hp L hL W') := rfl
  have e2 : (closedSubspaceCycle D _ hT Z.subspace Z.isClosedSubspace (deltaDimension D
    ((torsorOfInvertibleProjection D p hp L hL).hom ≫ p) Z)
      hdimZ).1 (torsorOfInvertiblePreimage D p hp L hL W') =
      cycleCoeffOfClosedSubspace D _ hT Z.subspace Z.isClosedSubspace (deltaDimension D
        ((torsorOfInvertibleProjection D p hp L hL).hom ≫ p) Z)
        (canonicalGeometricPoint D.site D.base D.base_mem Z.subspace.toFunctor)
        (torsorOfInvertiblePreimage D p hp L hL W') := rfl
  rw [e1, hk, ← e2]
  split_ifs with hW
  · subst hW
    exact closedSubspaceCycle_integral_apply_self D _ hT Z hdimZ
  · exact closedSubspaceCycle_integral_apply_of_ne D _ hT Z _ hdimZ
      fun h => hW (injective_torsorOfInvertiblePreimage D p hp L hL h)

/-- **The coefficient of `q^*α` at `q^{-1}(W)` is the coefficient of `α` at `W`.** -/
theorem torsorOfInvertibleFlatPullback_apply_preimage (k : ℤ) (α : CycleGroup D p k)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (torsorOfInvertibleFlatPullback D p hp L hL k α).1 (torsorOfInvertiblePreimage D p hp L hL W) =
      α.1 W := by
  change ∑ᶠ W' : IntegralClosedSubspace D.site D.base D.base_mem X,
    α.1 W' * flatPullbackMult D _ (isGood_torsorOfInvertible D p hp L hL) p hp
      (torsorOfInvertibleProjection D p hp L hL).hom rfl 1
      (isFlat_torsorOfInvertibleProjection D p hp L hL)
      (hasRelativeDimension_torsorOfInvertibleProjection D p hp L hL) W'
      (torsorOfInvertiblePreimage D p hp L hL W) = α.1 W
  simp_rw [flatPullbackMult_torsorOfInvertiblePreimage]
  rw [finsum_eq_single _ W (fun W' hW' => by rw [ite_eq_right (Ne.symm hW'), mul_zero]),
    ite_eq_left rfl, mul_one]

/-- **Stacks 0EQG, clause (4).** The flat pullback `q^* : Z_k(X) → Z_{k+1}(T)` is injective. -/
@[stacks 0EQG "clause (4): q^* : Z_k(X) → Z_{k+1}(T) is injective"]
theorem torsorOfInvertible_clause_four (k : ℤ) :
    Function.Injective (torsorOfInvertibleFlatPullback D p hp L hL k) := by
  intro α β h
  refine Subtype.ext (funext fun W => ?_)
  rw [← torsorOfInvertibleFlatPullback_apply_preimage D p hp L hL k α W,
    ← torsorOfInvertibleFlatPullback_apply_preimage D p hp L hL k β W, h]

end AlgebraicGeometry.Space

end

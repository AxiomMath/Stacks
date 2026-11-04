module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackIdentity
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralGoodSpace

/-!
# The coefficient of an étale pullback at a component of an inverse image

In Situation 0EDT let `f : X ⟶ Y` be an étale morphism of good algebraic spaces over the base, let
`Z ⊆ Y` be an integral closed subspace and let `Z'` be an irreducible component of the inverse
image `f^{-1}(Z)`, regarded as an integral closed subspace of `X`. For every cycle `α` on `Y` the
coefficient of the flat pullback `f^*α` (Stacks 0EP8) at `Z'` is the coefficient of `α` at `Z`:

`(f^*α)(Z') = α(Z)`.

By Stacks 0EPY, `f^*[W] = ∑ [W']` over the irreducible components `W'` of `f^{-1}(W)`, each with
coefficient one. The generic point of a component of `f^{-1}(W)` maps to the generic point of `W`,
so `Z'` is a component of `f^{-1}(W)` only for `W = Z`, and the sum defining `(f^*α)(Z')` has the
single term `α(Z) · 1`.

This is how a coefficient of a cycle on `Y` is read on an étale chart: the cycle is determined
by its pullback to a surjective étale chart, coefficient by coefficient.

## Main results

* `AlgebraicGeometry.Space.IntegralClosedSubspace.eq_of_preimageComponent_eq`: an integral
  closed subspace of `X` is a component of the inverse image of at most one integral closed
  subspace of `Y`.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.flatPullbackMap_apply_preimageComponent`:
  `(f^*α)(Z') = α(Z)`.

## References

* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
* [Stacks Project, Tag 0EPY](https://stacks.math.columbia.edu/tag/0EPY)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)

/-- **A component of an inverse image determines the subspace it lies over.** Along an étale
morphism `f : X ⟶ Y`, if an integral closed subspace of `X` is an irreducible component both of
`f^{-1}(Z)` and of `f^{-1}(W)`, then `Z = W`: its generic point maps to the generic points of
both. -/
theorem IntegralClosedSubspace.eq_of_preimageComponent_eq {f : X ⟶ Y}
    (hf : IsEtale D.site D.base D.base_mem f)
    {Z W : IntegralClosedSubspace D.site D.base D.base_mem Y}
    (C : irreducibleComponents (Z.preimagePointSet D.site D.base D.base_mem f))
    (C' : irreducibleComponents (W.preimagePointSet D.site D.base D.base_mem f))
    (h : Z.preimageComponent D.site D.base D.base_mem f hX.1 (D.isDecentSpace_of_isGood sX hX)
        hY.1 C =
      W.preimageComponent D.site D.base D.base_mem f hX.1 (D.isDecentSpace_of_isGood sX hX)
        hY.1 C') :
    Z = W := by
  set T := Z.preimageComponent D.site D.base D.base_mem f hX.1 (D.isDecentSpace_of_isGood sX hX)
    hY.1 C
  have hT := T.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hX.1
  have hZ := Z.isGenericPoint_pointsMap_of_isGenericPoint D sX hX sY hY hf C _ hT
  have hT' : IsGenericPoint (T.ambientGenericPoint D.site D.base D.base_mem)
      (subspacePointSet D.site D.base D.base_mem X
        (W.preimageComponent D.site D.base D.base_mem f hX.1 (D.isDecentSpace_of_isGood sX hX)
          hY.1 C').subspace) := by
    rw [← h]
    exact hT
  have hW := W.isGenericPoint_pointsMap_of_isGenericPoint D sX hX sY hY hf C' _ hT'
  exact (existsUnique_integralClosedSubspace_isGenericPoint_of_isGood D sY hY _).unique hZ hW

/-- **The coefficient of an étale pullback at a component of an inverse image.** Let
`f : X ⟶ Y` be an étale morphism of good algebraic spaces over the base, `Z ⊆ Y` an integral
closed subspace and `Z'` an irreducible component of `f^{-1}(Z)`. For every `k`-cycle `α` on `Y`
the coefficient at `Z'` of the flat pullback `f^*α ∈ Z_k(X)` (Stacks 0EP8, along `f` of relative
dimension `0`) is the coefficient of `α` at `Z`.

By Stacks 0EPY the multiplicity of `Z'` in `f^{-1}(W)` is one when `Z'` is a component of
`f^{-1}(W)` and zero otherwise, and the first happens only for `W = Z`
(`AlgebraicGeometry.Space.IntegralClosedSubspace.eq_of_preimageComponent_eq`). -/
theorem IntegralClosedSubspace.flatPullbackMap_apply_preimageComponent {f : X ⟶ Y}
    (hf : IsEtale D.site D.base D.base_mem f) (hfc : f ≫ sY = sX) (m n : ℤ)
    (hmn : m + ((0 : ℕ) : ℤ) = n) (α : CycleGroup D sY m)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (C : irreducibleComponents (Z.preimagePointSet D.site D.base D.base_mem f)) :
    (flatPullbackMap D sX hX sY hY f hfc 0 (isFlat_of_isEtale D.site D.base D.base_mem hf)
        (hasRelativeDimension_zero_of_isEtale D.site D.base D.base_mem f hY.1 hf) m n hmn α).1
        (Z.preimageComponent D.site D.base D.base_mem f hX.1 (D.isDecentSpace_of_isGood sX hX)
          hY.1 C) =
      α.1 Z := by
  set T := Z.preimageComponent D.site D.base D.base_mem f hX.1 (D.isDecentSpace_of_isGood sX hX)
    hY.1 C
  have hmult : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem Y,
      flatPullbackMult D sX hX sY hY f hfc 0 (isFlat_of_isEtale D.site D.base D.base_mem hf)
          (hasRelativeDimension_zero_of_isEtale D.site D.base D.base_mem f hY.1 hf) W T =
        W.preimageComponentsCycle D sX hX sY hY f T := fun W =>
    congrFun (W.flatPullbackMult_eq_preimageComponentsCycle D sX hX sY hY hf hfc) T
  rw [flatPullbackMap_apply, finsum_eq_single _ Z fun W hWZ => ?_]
  · have hmem : T ∈ {V : IntegralClosedSubspace D.site D.base D.base_mem X | ∃ C,
        Z.preimageComponent D.site D.base D.base_mem f hX.1 (D.isDecentSpace_of_isGood sX hX)
          hY.1 C = V} := ⟨C, rfl⟩
    rw [hmult, IntegralClosedSubspace.preimageComponentsCycle, Set.indicator_of_mem hmem,
      Pi.one_apply, mul_one]
  · rw [hmult]
    by_contra hne
    obtain ⟨C', hC'⟩ :=
      (W.preimageComponentsCycle_ne_zero_iff D sX hX sY hY f T).1 (right_ne_zero_of_mul hne)
    exact hWZ (IntegralClosedSubspace.eq_of_preimageComponent_eq D sX hX sY hY hf C' C hC')

end AlgebraicGeometry.Space

end

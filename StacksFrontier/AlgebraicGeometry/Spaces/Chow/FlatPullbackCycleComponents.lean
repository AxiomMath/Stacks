module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceCycleComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackOfCycles

/-!
# The flat pullback of a prime cycle as a sum over the components of the inverse image

In Situation 0EDT let `X/B` and `Y/B` be good and let `f : X ⟶ Y` be a morphism over the base
which is flat of relative dimension `r`. For an integral closed subspace `W ⊆ Y` of
δ-dimension `k`, part (1) of **Stacks 0EP8** sets `f^*[W] = [f^{-1}(W)]_{k+r}`.

The source repeatedly writes that cycle out over the irreducible components `W'_i` of
`W' = f^{-1}(W)` of δ-dimension `k + r`,

`[f^{-1}(W)]_{k+r} = ∑ n_i [W'_i]`,

and that expansion is what the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackOrderOfVanishing` and of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackFirstChernCap` record as the one step
their coefficientwise statements leave uncovered. This file supplies it, by applying
`AlgebraicGeometry.Space.closedSubspaceCycle_apply_eq_finsum` to the closed subspace
`f^{-1}(W)`: the flat pullback of a prime cycle is *defined* to be the cycle of that closed
subspace, so the expansion is the additivity of Stacks 0EE9, part (2) and nothing more.

**Nothing about the flat pullback is assumed.** The multiplicities `n_i` are the geometric
lengths of Stacks 0EE2 read inside `f^{-1}(W)`, that is
`AlgebraicGeometry.Space.closedSubspaceMultiplicity`, and the index set is the collection of
irreducible components of `|f^{-1}(W)|` of δ-dimension `k + r`, which is what
`AlgebraicGeometry.Space.exists_irreducibleComponents_closedSubspaceComponentImage` and
`AlgebraicGeometry.Space.exists_closedSubspaceComponentImage_eq_closedSetComponent` say about
the index type.

## Main results

* `AlgebraicGeometry.Space.flatPullbackMult_eq_finsum`: the multiplicity of an integral closed
  subspace `T ⊆ X` in `f^*[W]` is the sum, over the irreducible components of `f^{-1}(W)` of
  δ-dimension `dim_δ(W) + r`, of their multiplicities times the coefficient of `T` in their
  fundamental cycles.
* `AlgebraicGeometry.Space.flatPullbackIntegralCycle_coe_eq_finsum`: the same as an equality of
  coefficient families, that is of cycles in `Z_{k+r}(X)`.

## Implementation notes

The identity is coefficientwise for the reason recorded in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceCycleComponents`: the components of
`|f^{-1}(W)|` of top δ-dimension are a locally finite, not finite, collection, so the sum
cannot be formed in `Z_{k+r}(X)`.

**What this still does not give.** The second assertion of Stacks 0EPA, `(g ∘ f)^* = f^* ∘ g^*`,
does not follow. Expanding `g^*[A]` by the result below turns its right-hand side into
`∑ n_i [f^{-1}(A'_i)]_{k+s+r}`, and comparing that with `[(g ∘ f)^{-1}(A)]_{k+r+s}` — the two
closed subspaces do agree, by `CategoryTheory.Subfunctor.preimage_comp` — is the identity
`f^*[A']_{k+s} = [f^{-1}(A')]_{k+s+r}` for the *closed* subspace `A' = g^{-1}(A)`, that is
Stacks 0EP3, which has no declaration for algebraic spaces here. Equivalently it is the
multiplicativity `m_{T, f^{-1}(A')} = ∑_i n_i · m_{T, f^{-1}(A'_i)}` of geometric lengths along
a flat morphism, which is what the source proves from Algebra, Lemma 10.52.14 after choosing an
étale chart of schemes; it is not a consequence of the decomposition of a cycle over its
components.

## References

* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EE2](https://stacks.math.columbia.edu/tag/0EE2)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0EP3](https://stacks.math.columbia.edu/tag/0EP3)
* [Stacks Project, Tag 0EPA](https://stacks.math.columbia.edu/tag/0EPA)
* [Stacks Project, Tag 0EPB](https://stacks.math.columbia.edu/tag/0EPB)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y)

/-- **The expansion of `f^*[W]` over the irreducible components of `f^{-1}(W)`.** The
multiplicity of an integral closed subspace `T ⊆ X` in the flat pullback `f^*[W]` of the cycle
of an integral closed subspace `W ⊆ Y` of δ-dimension `k` is

`∑ n_i · [W'_i]_T`,

the sum over the integral closed subspaces `W'_i` of `f^{-1}(W)` whose image in `X` has
δ-dimension `k + r` — by Stacks 0EE6 exactly the irreducible components of `|f^{-1}(W)|` of
that δ-dimension — with `n_i` the multiplicity of `W'_i` in `f^{-1}(W)`.

This is `AlgebraicGeometry.Space.closedSubspaceCycle_apply_eq_finsum` at the closed subspace
`f^{-1}(W)`, which is legitimate because part (1) of Stacks 0EP8 *defines* `f^*[W]` to be the
cycle of that closed subspace, and because part (1) of Stacks 0EPB supplies the δ-dimension
bound. -/
theorem flatPullbackMult_eq_finsum
    (T : IntegralClosedSubspace D.site D.base D.base_mem X) :
    flatPullbackMult D sX hX sY hY f hbase r hflat hr W T =
      ∑ᶠ V : topComponentSubspaces D sX hX (W.subspace.preimage f)
          (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W)
          (deltaDimension D sY W + (r : ℤ)),
        closedSubspaceMultiplicity D (W.subspace.preimage f)
            (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W) V.1 *
          (integralCycle D sX (deltaDimension D sY W + (r : ℤ))
            (closedSubspaceComponentImage D sX hX (W.subspace.preimage f)
              (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W) V.1)
            V.2).1 T :=
  closedSubspaceCycle_apply_eq_finsum D sX hX (W.subspace.preimage f)
    (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W)
    (deltaDimension D sY W + (r : ℤ))
    (deltaDimensionSubspace_preimage_integralClosedSubspace_le D sX hX sY hY f hbase r hflat hr
      W) T

/-- **The expansion of `f^*[W]` over the irreducible components of `f^{-1}(W)`, as an equality
of cycles.** The coefficient family of `f^*[W] = [f^{-1}(W)]_{k+r}` is the componentwise sum of
`AlgebraicGeometry.Space.flatPullbackMult_eq_finsum`. -/
theorem flatPullbackIntegralCycle_coe_eq_finsum :
    (flatPullbackIntegralCycle D sX hX sY hY f hbase r hflat hr W).1 =
      fun T => ∑ᶠ V : topComponentSubspaces D sX hX (W.subspace.preimage f)
          (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W)
          (deltaDimension D sY W + (r : ℤ)),
        closedSubspaceMultiplicity D (W.subspace.preimage f)
            (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W) V.1 *
          (integralCycle D sX (deltaDimension D sY W + (r : ℤ))
            (closedSubspaceComponentImage D sX hX (W.subspace.preimage f)
              (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W) V.1)
            V.2).1 T :=
  funext fun T => flatPullbackMult_eq_finsum D sX hX sY hY f hbase r hflat hr W T

end AlgebraicGeometry.Space

end

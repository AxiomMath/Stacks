module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CycleMapsOfKernels

/-!
# Cycle maps of kernels whose kernels are locally finite sums

A homomorphism `Φ : Z_a(X) → Z_b(T)` is the cycle map of a kernel `φ` lying over the subspaces of
`X` along `π : |T| → |X|` (`AlgebraicGeometry.Space.IsCycleMapOfKernel`) when
`Φ(∑ n_W [W]) = ∑ n_W φ(W)`. Such a map sends `[W]` to `φ(W)`, and the difference of two cycle
maps of kernels over the same `π` is the cycle map of the difference of the kernels. If every
`φ(W)` is a locally finite sum `∑_j (T_{W,j} → T)_* c_{W,j}` over integral closed subspaces lying
over `|W|`, then `Φ(α)` is the locally finite sum of the `n_W c_{W,j}` over all pairs `(W, j)`
with `n_W ≠ 0`. The cap product with the first Chern class is a cycle map of a kernel.

## Main results

* `AlgebraicGeometry.Space.isCycleMapOfKernel_firstChernCapCycleMap`: the cap product with the
  first Chern class is the cycle map of its component cycles, along the identity.
* `AlgebraicGeometry.Space.IsCycleMapOfKernel.apply_integralCycle`: `Φ[W] = φ(W)`.
* `AlgebraicGeometry.Space.IsCycleMapOfKernel.sub`: differences.
* `AlgebraicGeometry.Space.IsCycleMapOfKernel.eq_cycleFamilySum`: `Φ(α)` as one locally finite
  sum, when every `φ(W)` is one over `|W|`.

## References

* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X T : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The cap product with the first Chern class is the cycle map of its component cycles, which
lie over the subspaces of `X` along the identity. -/
theorem isCycleMapOfKernel_firstChernCapCycleMap (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ)
    (chern : FirstChernComponentCycleRule D sX k) :
    IsCycleMapOfKernel D sX sX id (firstChernCapCycleMap D sX hX k chern)
      (firstChernComponentCycle D sX hX k chern) where
  apply α Z := firstChernCapCycleMap_apply D sX hX k chern α Z
  support W Z hZ :=
    subspacePointSet_subset_of_firstChernComponentCycle_ne_zero D sX hX k chern W Z hZ

namespace IsCycleMapOfKernel

variable {D} {sX : X ⟶ D.space} {sT : T ⟶ D.space}
    {π : points D.site D.base D.base_mem T → points D.site D.base D.base_mem X} {a b : ℤ}
    {Φ : CycleGroup D sX a →+ CycleGroup D sT b}
    {φ : IntegralClosedSubspace D.site D.base D.base_mem X → CycleGroup D sT b}

/-- The cycle map of a kernel sends the cycle `[W]` of an integral closed subspace to `φ(W)`. -/
theorem apply_integralCycle (h : IsCycleMapOfKernel D sX sT π Φ φ)
    {W : IntegralClosedSubspace D.site D.base D.base_mem X} (hW : deltaDimension D sX W = a) :
    Φ (integralCycle D sX a W hW) = φ W := by
  refine Subtype.ext (funext fun Z => ?_)
  rw [h.apply, finsum_eq_single _ W fun W' hW' => by
    rw [integralCycle_coe, integralCycleCoeff_eq_zero D W hW', zero_mul],
    integralCycle_coe, integralCycleCoeff_self, one_mul]

/-- The difference of two cycle maps of kernels over the same map of points is the cycle map of
the difference of the kernels. -/
theorem sub (h : IsCycleMapOfKernel D sX sT π Φ φ) {Ψ : CycleGroup D sX a →+ CycleGroup D sT b}
    {ψ : IntegralClosedSubspace D.site D.base D.base_mem X → CycleGroup D sT b}
    (h' : IsCycleMapOfKernel D sX sT π Ψ ψ) :
    IsCycleMapOfKernel D sX sT π (Φ - Ψ) fun W => φ W - ψ W where
  apply α Z := by
    show (Φ α).1 Z - (Ψ α).1 Z = _
    rw [h.apply, h'.apply, ← finsum_sub_distrib (h.finite_support α Z) (h'.finite_support α Z)]
    refine finsum_congr fun W => ?_
    show _ = α.1 W * ((φ W).1 Z - (ψ W).1 Z)
    rw [mul_sub]
  support W Z hZ := by
    change (φ W).1 Z - (ψ W).1 Z ≠ 0 at hZ
    by_cases h0 : (φ W).1 Z = 0
    · rw [h0, zero_sub, neg_ne_zero] at hZ
      exact h'.support W Z hZ
    · exact h.support W Z h0

/-- Let `Φ` be the cycle map of a kernel `φ` lying over the subspaces of `X` along a continuous
`π`, let `α` be an `a`-cycle, and suppose that for every `W` occurring in `α` the cycle `φ(W)` is a
locally finite sum `∑_j (T_{W,j} → T)_* c_{W,j}` over integral closed subspaces `T_{W,j} ⊆ T`
lying over `|W|`. Then `Φ(α)` is the locally finite sum of the `α(W) c_{W,j}` over all pairs
`(W, j)`. -/
theorem eq_cycleFamilySum (h : IsCycleMapOfKernel D sX sT π Φ φ) (hπ : Continuous π)
    (hT : D.IsGood sT) (α : CycleGroup D sX a)
    {J : {W : IntegralClosedSubspace D.site D.base D.base_mem X // α.1 W ≠ 0} → Type v}
    (V : ∀ W, J W → IntegralClosedSubspace D.site D.base D.base_mem T)
    (hV : ∀ W, LocallyFinite fun j : J W =>
      subspacePointSet D.site D.base D.base_mem T (V W j).subspace)
    (hVW : ∀ W j, subspacePointSet D.site D.base D.base_mem T (V W j).subspace ⊆
      π ⁻¹' subspacePointSet D.site D.base D.base_mem X W.1.subspace)
    (c : ∀ W j, CycleGroup D ((V W j).subspace.ι ≫ sT) b)
    (hφ : ∀ W, φ W.1 = cycleFamilySum D sT hT (V W) (hV W) b (c W))
    (hfin : LocallyFinite fun p : Σ W, J W =>
      subspacePointSet D.site D.base D.base_mem T (V p.1 p.2).subspace :=
      locallyFinite_sigma_of_subset
        ((α.2.1.comp_injective Subtype.val_injective).preimage_continuous hπ |>.subset
          fun W => by simp [W.2]) hV hVW) :
    Φ α = cycleFamilySum D sT hT (fun p : Σ W, J W => V p.1 p.2) hfin b
      fun p => α.1 p.1.1 • c p.1 p.2 := by
  refine Subtype.ext (funext fun Z => ?_)
  show (Φ α).1 Z = (cycleFamilySum D sT hT _ hfin b _).1 Z
  rw [h.apply, cycleFamilySum_apply,
    Stacks.Chow.finsum_sigma _ (finite_support_cycleFamilyCoeff D sT hT _ hfin b _ Z)]
  have hsub : (∑ᶠ W, α.1 W * (φ W).1 Z) =
      ∑ᶠ W : {W : IntegralClosedSubspace D.site D.base D.base_mem X // α.1 W ≠ 0},
        α.1 W.1 * (φ W.1).1 Z := by
    rw [finsum_subtype_eq_finsum_cond (p := fun W => α.1 W ≠ 0)
      (f := fun W => α.1 W * (φ W).1 Z)]
    refine finsum_congr fun W => ?_
    by_cases hW : α.1 W = 0
    · rw [finsum_eq_if, ite_eq_right (not_not.2 hW), hW, zero_mul]
    · rw [finsum_eq_if, ite_eq_left hW]
  rw [hsub]
  refine finsum_congr fun W => ?_
  rw [hφ W, cycleFamilySum_apply, mul_finsum]
  refine finsum_congr fun j => ?_
  rw [map_zsmul]
  show _ = α.1 W.1 • ((integralClosedSubspacePushforward D sT hT (V W j) b) (c W j)).1 Z
  rw [smul_eq_mul]

end IsCycleMapOfKernel

end AlgebraicGeometry.Space

end

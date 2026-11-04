module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisorCycleOfGoodDifference
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalenceCanonical

/-!
# The cap product of Stacks 0EQJ into the Chow group at the canonical embeddings

In Situation 0EDT let `X/B` be good and let `𝒩` be an invertible `𝒪_X`-module.  The cap product
`AlgebraicGeometry.Space.canonicalFirstChernCap` of Stacks 0EQJ lands in
`AlgebraicGeometry.Space.chowGroup`, the quotient of `Z_k(X)` by the subgroup of cycles
rationally equivalent to zero in the reading in which the embeddings `R(W) → Q(𝒪^h_{W,ξ})` of
Stacks 0ENK are quantified existentially with no compatibility condition.  That subgroup is in
general strictly larger than the set of cycles the source displays, so that quotient is in
general a proper quotient of `CH_k(X)`; the source's Chow group is
`AlgebraicGeometry.Space.chowGroupCanonical`, with the embeddings pinned to the canonical ones.

This file states the cap product and the two assertions of Stacks 0EQK with the target
`AlgebraicGeometry.Space.chowGroupCanonical`; the comparison map to
`AlgebraicGeometry.Space.chowGroup` carries them onto the corresponding statements there.

## Main definitions

* `AlgebraicGeometry.Space.canonicalFirstChernCapCanonical`: the cap product
  `c₁(𝒩) ∩ - : Z_{k+1}(X) ⟶ CH_k(X)` of Stacks 0EQJ, with `CH_k(X)` the Chow group at the
  canonical embeddings.

## Main results

* `AlgebraicGeometry.Space.canonicalFirstChernCapCanonical_integralCycle`: case (1) of
  Stacks 0EQJ, the value of the cap product on the fundamental cycle of an integral closed
  subspace.
* `AlgebraicGeometry.Space.canonicalFirstChernCapCanonical_eq_chowClassCanonical_cycleFamilySum`:
  the cap product as the class of a locally finite sum of Stacks 0EQ6, part (1).
* `AlgebraicGeometry.Space.canonicalFirstChernCapCanonical_picardTensorModule`: the first
  assertion of Stacks 0EQK, in `CH_k(X)` at the canonical embeddings.
* `AlgebraicGeometry.Space.canonicalFirstChernCapCanonical_congr_iso`: the cap product depends on
  the invertible module only through its isomorphism class.
* `AlgebraicGeometry.Space.canonicalFirstChernCapCanonical_tensorUnit_eq_zero`: the second
  assertion of Stacks 0EQK, in `CH_k(X)` at the canonical embeddings.
* `AlgebraicGeometry.Space.chowGroupCanonicalToChowGroup_canonicalFirstChernCapCanonical`: the
  comparison map carries the cap product onto `AlgebraicGeometry.Space.canonicalFirstChernCap`.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EPT](https://stacks.math.columbia.edu/tag/0EPT)
* [Stacks Project, Tag 0EPV](https://stacks.math.columbia.edu/tag/0EPV)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EQK](https://stacks.math.columbia.edu/tag/0EQK)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Cap

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX)

attribute [local instance] modulesMonoidalCategory

variable (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)

/-- **Stacks 0EQJ into the Chow group at the canonical embeddings of Stacks 0ENK.**  The cap
product `c₁(𝒩) ∩ - : Z_{k+1}(X) ⟶ CH_k(X)`, the component rule being
`AlgebraicGeometry.Space.canonicalFirstChernRule` and the target
`AlgebraicGeometry.Space.chowGroupCanonical`, the quotient of `Z_k(X)` by the cycles the source
displays as rationally equivalent to zero. -/
def canonicalFirstChernCapCanonical (k : ℤ) :
    CycleGroup D sX (k + 1) →+ chowGroupCanonical.{v} D sX hX k :=
  (chowClassCanonical.{v} D sX hX k).comp
    (firstChernCapCycleMap D sX hX k (canonicalFirstChernRule D sX hX N hN k))

/-- The comparison map `AlgebraicGeometry.Space.chowGroupCanonicalToChowGroup` of Stacks 0EQ6
carries `AlgebraicGeometry.Space.canonicalFirstChernCapCanonical` onto
`AlgebraicGeometry.Space.canonicalFirstChernCap`. -/
theorem chowGroupCanonicalToChowGroup_canonicalFirstChernCapCanonical (k : ℤ)
    (α : CycleGroup D sX (k + 1)) :
    chowGroupCanonicalToChowGroup.{v} D sX hX k
        (canonicalFirstChernCapCanonical.{v} D sX hX N hN k α) =
      canonicalFirstChernCap.{u, v} D sX hX N hN k α :=
  rfl

/-- **Stacks 0EQJ, case (1), at the canonical embeddings.**  On the fundamental cycle `[W]` of an
integral closed subspace `i : W → X` of δ-dimension `k + 1` the cap product is the class of
`i_*(c₁(𝒩|_W) ∩ [W])`. -/
theorem canonicalFirstChernCapCanonical_integralCycle (k : ℤ)
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D sX W = k + 1) :
    canonicalFirstChernCapCanonical.{v} D sX hX N hN k (integralCycle D sX (k + 1) W hW) =
      chowClassCanonical.{v} D sX hX k (integralClosedSubspacePushforward D sX hX W k
        (canonicalFirstChernRule D sX hX N hN k W hW)) := by
  rw [canonicalFirstChernCapCanonical, AddMonoidHom.comp_apply,
    firstChernCapCycleMap_integralCycle D sX hX k _ hW]

end Cap

section Additive

variable {D : BaseSpaceDimensionSituation.{u}}
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} {sX : X ⟶ D.space}
    (hX : D.IsGood sX)

attribute [local instance] modulesMonoidalCategory

/-- **The cap product at the canonical embeddings as a sum of Stacks 0EQ6, part (1).**  Evaluated
on a `(k+1)`-cycle `α`, it is the class of the locally finite sum
`∑_W α(W) · (W → X)_*(c₁(ℒ|_W) ∩ [W])` over the integral closed subspaces at which `α` has a
nonzero coefficient. -/
theorem canonicalFirstChernCapCanonical_eq_chowClassCanonical_cycleFamilySum
    (M : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hM : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) M)
    (k : ℤ) (α : CycleGroup D sX (k + 1)) :
    canonicalFirstChernCapCanonical.{u + 1} D sX hX M hM k α =
      chowClassCanonical.{u + 1} D sX hX k (cycleFamilySum D sX hX Subtype.val
        (locallyFinite_cycleSupport α) k
        fun i : {W : IntegralClosedSubspace D.site D.base D.base_mem X // α.1 W ≠ 0} =>
          α.1 i.1 • canonicalFirstChernRule D sX hX M hM k i.1 (α.2.2 i.1 i.2)) := by
  rw [canonicalFirstChernCapCanonical, AddMonoidHom.comp_apply,
    firstChernCapCycleMap_eq_cycleFamilySum D sX hX k (canonicalFirstChernRule D sX hX M hM k)
      α Subtype.val Subtype.val_injective (locallyFinite_cycleSupport α)
      (fun i : {W : IntegralClosedSubspace D.site D.base D.base_mem X // α.1 W ≠ 0} =>
        α.2.2 i.1 i.2) fun W hW => ⟨⟨W, hW⟩, rfl⟩]

/-- **Stacks 0EQK, first assertion, in the Chow group at the canonical embeddings.**  For
invertible `𝒪_X`-modules `ℒ` and `𝒩` on a good algebraic space `X/B` and every `α ∈ Z_{k+1}(X)`,

  `c₁(ℒ) ∩ α + c₁(𝒩) ∩ α = c₁(ℒ ⊗_{𝒪_X} 𝒩) ∩ α`   in   `CH_k(X)`,

the Chow group being `AlgebraicGeometry.Space.chowGroupCanonical`, the quotient of `Z_k(X)` by
the cycles the source displays as rationally equivalent to zero. -/
theorem canonicalFirstChernCapCanonical_picardTensorModule
    (L N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)
    (k : ℤ) (α : CycleGroup D sX (k + 1)) :
    canonicalFirstChernCapCanonical.{u + 1} D sX hX L hL k α +
        canonicalFirstChernCapCanonical.{u + 1} D sX hX N hN k α =
      canonicalFirstChernCapCanonical.{u + 1} D sX hX
        (picardTensorModule D.site D.base D.base_mem hX.1 L N)
        (isInvertibleModule_picardTensorModule D.site D.base D.base_mem hX.1 L N hL hN) k α := by
  rw [canonicalFirstChernCapCanonical_eq_chowClassCanonical_cycleFamilySum hX L hL k α,
    canonicalFirstChernCapCanonical_eq_chowClassCanonical_cycleFamilySum hX N hN k α,
    canonicalFirstChernCapCanonical_eq_chowClassCanonical_cycleFamilySum hX _ _ k α, eq_comm,
    ← sub_eq_zero, sub_add_eq_sub_sub, ← map_sub, ← map_sub, ← cycleFamilySum_sub,
    ← cycleFamilySum_sub]
  refine chowClassCanonical_cycleFamilySum_eq_zero.{u + 1} D sX hX k Subtype.val
    (locallyFinite_cycleSupport α) _
    (fun i : {W : IntegralClosedSubspace D.site D.base D.base_mem X // α.1 W ≠ 0} =>
      α.2.2 i.1 i.2) fun i => ?_
  have h := isPrincipalDivisorCycleOfGood_zsmul_canonicalFirstChernRule_picardTensorModule_sub
    hX L N hL hN k i.1 (α.2.2 i.1 i.2) (α.1 i.1)
  rwa [smul_sub, smul_add, ← sub_sub] at h

/-- **The cap product at the canonical embeddings depends on the invertible module only through
its isomorphism class.**  For `e : ℳ ≅ ℳ'` the two cap products agree on every `α ∈ Z_{k+1}(X)`. -/
theorem canonicalFirstChernCapCanonical_congr_iso
    (M M' : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hM : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) M)
    (hM' : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) M')
    (e : M ≅ M') (k : ℤ) (α : CycleGroup D sX (k + 1)) :
    canonicalFirstChernCapCanonical.{u + 1} D sX hX M hM k α =
      canonicalFirstChernCapCanonical.{u + 1} D sX hX M' hM' k α := by
  rw [canonicalFirstChernCapCanonical_eq_chowClassCanonical_cycleFamilySum hX M hM k α,
    canonicalFirstChernCapCanonical_eq_chowClassCanonical_cycleFamilySum hX M' hM' k α,
    ← sub_eq_zero, ← map_sub, ← cycleFamilySum_sub]
  refine chowClassCanonical_cycleFamilySum_eq_zero.{u + 1} D sX hX k Subtype.val
    (locallyFinite_cycleSupport α) _
    (fun i : {W : IntegralClosedSubspace D.site D.base D.base_mem X // α.1 W ≠ 0} =>
      α.2.2 i.1 i.2) fun i => ?_
  have h := isPrincipalDivisorCycleOfGood_zsmul_canonicalFirstChernRule_sub_of_iso hX M' M hM' hM
    e.symm k i.1 (α.2.2 i.1 i.2) (α.1 i.1)
  rwa [smul_sub] at h

/-- **Stacks 0EQK, second assertion, in the Chow group at the canonical embeddings.**
`c₁(𝒪_X) ∩ α = 0` in `CH_k(X)` for every `α ∈ Z_{k+1}(X)`, the structure sheaf being the tensor
unit of `AlgebraicGeometry.Space.Modules`, which is `𝒪_X` as a module over itself. -/
theorem canonicalFirstChernCapCanonical_tensorUnit_eq_zero (k : ℤ)
    (α : CycleGroup D sX (k + 1)) :
    canonicalFirstChernCapCanonical.{u + 1} D sX hX
      (𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1))
      (isInvertibleModule_tensorUnit hX) k α = 0 := by
  have h := canonicalFirstChernCapCanonical_picardTensorModule hX _ _
    (isInvertibleModule_tensorUnit hX) (isInvertibleModule_tensorUnit hX) k α
  rw [canonicalFirstChernCapCanonical_congr_iso hX _ _
    (isInvertibleModule_picardTensorModule D.site D.base D.base_mem hX.1 _ _
      (isInvertibleModule_tensorUnit hX) (isInvertibleModule_tensorUnit hX))
    (isInvertibleModule_tensorUnit hX) (picardTensorModuleUnitIso hX _) k α] at h
  exact add_left_cancel (h.trans (add_zero _).symm)

end Additive

end AlgebraicGeometry.Space

end

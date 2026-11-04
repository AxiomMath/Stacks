module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CycleMapOfKernelFamilySum
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalenceLocallyFiniteSums
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.TrivialRestrictionGysin

/-!
# The refined Gysin map against the cap product: reduction to one integral closed subspace

In Situation 0EDT let `X/B` be good, let `(ℒ, s, i : E → X)` be a triple as in Stacks 0ER1 —
`ℒ` invertible, `s ∈ Γ(X, ℒ)` and `E = Z(s)` — and let `𝒩` be an invertible `𝒪_X`-module.
Stacks 0ERB asserts

`i^*(c₁(𝒩) ∩ α) = c₁(i^*𝒩) ∩ i^*α` in `CH_{k-2}(E)` for `α ∈ CH_k(X)`,

and its proof begins as the proof of Stacks 0ERA does: both sides are computed on a cycle
`α = ∑ n_W [W]` by rules on the integral closed subspaces `W` occurring in it, so that a rational
equivalence between the two sides for every `[W]`, supported on `E ∩ W`, assembles into one for
`α`.

This file carries out that reduction at the level of cycles, at the canonical choices: the
refined Gysin map `i^*` of Stacks 0ER1 with clause (1)(a) the cycle `[E ∩ W]_k` of Stacks 0EE9
and clause (1)(b) the cap product of Stacks 0EQJ, the cap products of Stacks 0EQJ by `𝒩` on `X`
and by `i^*𝒩` on `E`, each with the component cycle `div_{𝒩|_W}(t_W)` of
`AlgebraicGeometry.Space.canonicalFirstChernRule`.  The conclusion is an identity of cycles: the
difference `i^*(c₁(𝒩) ∩ α) - c₁(i^*𝒩) ∩ i^*α ∈ Z_{k-2}(E)` is the locally finite sum over all
pairs `(W, j)` of the multiples `n_W c_{W,j}` of the cycles presenting the differences for the
single subspaces `[W]`.  It does not mention rational equivalence, so it applies to any notion
of principal divisor closed under integer multiples
(`AlgebraicGeometry.Space.exists_gysinCycleMap_firstChernCapCycleMap_sub_eq_cycleFamilySum`).

## Main results

* `AlgebraicGeometry.Space.isCycleMapOfKernel_gysinCycleMap_comp_firstChernCapCycleMap` and
  `AlgebraicGeometry.Space.isCycleMapOfKernel_firstChernCapCycleMap_comp_gysinCycleMap`: the two
  sides of Stacks 0ERB, as cycle maps of kernels lying over the subspaces of `X` along `i`.
* `AlgebraicGeometry.Space.gysinCycleMap_firstChernCapCycleMap_sub_eq_cycleFamilySum`: the
  reduction, with the presenting families of the single subspaces as data.
* `AlgebraicGeometry.Space.exists_gysinCycleMap_firstChernCapCycleMap_sub_eq_cycleFamilySum`: the
  same, for presenting families whose summands satisfy a predicate closed under integer
  multiples.
* `AlgebraicGeometry.Space.isRationallyEquivalentToZero_gysinCycleMap_firstChernCapCycleMap_sub`:
  the same for the rational equivalence of Stacks 0EQ6, through
  `AlgebraicGeometry.Space.isRationallyEquivalentToZeroWithin_sub_of_isCycleMapOfKernel`.

## Implementation notes

The source reduces to an integral `X` through the proper morphism `∐ W_j → X`.  Here the
reduction stops at the cycle `[W]` on `X` itself: the two operations are cycle maps of kernels
(`AlgebraicGeometry.Space.IsCycleMapOfKernel`), the rule of `α ↦ i^*(c₁(𝒩) ∩ α)` at `W`
being `i^*` of the component cycle of Stacks 0EQJ at `W` and that of `α ↦ c₁(i^*𝒩) ∩ i^*α`
being the cap product on `E` of the component cycle of Stacks 0ER1 at `W`, both supported along
`i`; the assembly is `AlgebraicGeometry.Space.IsCycleMapOfKernel.eq_cycleFamilySum`.

The degrees are written `k + 1 + 1`, `k + 1` and `k` for the source's `k`, `k - 1` and `k - 2`,
which is the grading of the cycle maps `Z_{m+1} → Z_m` of Stacks 0EQJ and Stacks 0ER1.

## References

* [Stacks Project, Tag 0ERB](https://stacks.math.columbia.edu/tag/0ERB)
* [Stacks Project, Tag 0ERA](https://stacks.math.columbia.edu/tag/0ERA)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (s : L.sections) (N : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hN : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N) (k : ℤ)

/-- The map `α ↦ i^*(c₁(𝒩) ∩ α)`, `Z_{k+2}(X) → Z_k(E)`, at the canonical choices, is the cycle
map of the kernel `W ↦ i^*(c₁(𝒩|_W) ∩ [W])`, lying over the subspaces of `X` along `i : E → X`. -/
theorem isCycleMapOfKernel_gysinCycleMap_comp_firstChernCapCycleMap :
    IsCycleMapOfKernel D sX ((vanishingLocus D sX hX L s).1.ι ≫ sX)
      (pointsMap D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor
        (vanishingLocus D sX hX L s).1.ι)
      ((gysinCycleMap D sX (vanishingLocus D sX hX L s) (isGood_vanishingLocus D sX hX L s) k
          (canonicalGysinComponentRule D sX hX (vanishingLocus D sX hX L s)
            (isGood_vanishingLocus D sX hX L s) k (canonicalFirstChernRule D sX hX L hL k))).comp
        (firstChernCapCycleMap D sX hX (k + 1) (canonicalFirstChernRule D sX hX N hN (k + 1))))
      fun W => gysinCycleMap D sX (vanishingLocus D sX hX L s) (isGood_vanishingLocus D sX hX L s) k
          (canonicalGysinComponentRule D sX hX (vanishingLocus D sX hX L s)
            (isGood_vanishingLocus D sX hX L s) k (canonicalFirstChernRule D sX hX L hL k))
        (firstChernComponentCycle D sX hX (k + 1) (canonicalFirstChernRule D sX hX N hN (k + 1))
          W) :=
  (isCycleMapOfKernel_firstChernCapCycleMap D sX hX (k + 1) _).comp
    (isCycleMapOfKernel_gysinCycleMap D sX _ _ k _)

/-- The map `α ↦ c₁(i^*𝒩) ∩ i^*α`, `Z_{k+2}(X) → Z_k(E)`, at the canonical choices, is the cycle
map of the kernel `W ↦ c₁(i^*𝒩) ∩ i^*[W]`, lying over the subspaces of `X` along `i : E → X`. -/
theorem isCycleMapOfKernel_firstChernCapCycleMap_comp_gysinCycleMap :
    IsCycleMapOfKernel D sX ((vanishingLocus D sX hX L s).1.ι ≫ sX)
      (pointsMap D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor
        (vanishingLocus D sX hX L s).1.ι)
      ((firstChernCapCycleMap D ((vanishingLocus D sX hX L s).1.ι ≫ sX)
          (isGood_vanishingLocus D sX hX L s) k
          (canonicalFirstChernRule D _ (isGood_vanishingLocus D sX hX L s)
            ((modulePullback D.site D.base D.base_mem
              (vanishingLocusInclusion D sX hX L s)).obj N)
            (modulePullbackInvertible (vanishingLocusInclusion D sX hX L s) N hN) k)).comp
        (gysinCycleMap D sX (vanishingLocus D sX hX L s) (isGood_vanishingLocus D sX hX L s)
            (k + 1)
            (canonicalGysinComponentRule D sX hX (vanishingLocus D sX hX L s)
              (isGood_vanishingLocus D sX hX L s) (k + 1)
              (canonicalFirstChernRule D sX hX L hL (k + 1)))))
      fun W => firstChernCapCycleMap D ((vanishingLocus D sX hX L s).1.ι ≫ sX)
          (isGood_vanishingLocus D sX hX L s) k
          (canonicalFirstChernRule D _ (isGood_vanishingLocus D sX hX L s)
            ((modulePullback D.site D.base D.base_mem
              (vanishingLocusInclusion D sX hX L s)).obj N)
            (modulePullbackInvertible (vanishingLocusInclusion D sX hX L s) N hN) k)
        (gysinComponentCycle D sX (vanishingLocus D sX hX L s)
          (isGood_vanishingLocus D sX hX L s) (k + 1)
          (canonicalGysinComponentRule D sX hX (vanishingLocus D sX hX L s)
            (isGood_vanishingLocus D sX hX L s) (k + 1)
            (canonicalFirstChernRule D sX hX L hL (k + 1))) W) :=
  (isCycleMapOfKernel_gysinCycleMap D sX _ _ (k + 1) _).comp
    (isCycleMapOfKernel_firstChernCapCycleMap D _ _ k _)

/-- **The reduction of Stacks 0ERB to a single integral closed subspace, at the level of
cycles.**  In Situation 0EDT let `X/B` be good, let `(ℒ, s, i : E → X)` be a triple as in
Stacks 0ER1 and let `𝒩` be an invertible `𝒪_X`-module; all cycle maps are at the canonical
choices.  Let `α = ∑ n_W [W] ∈ Z_{k+2}(X)`, and suppose that for every integral closed subspace
`W ⊆ X` occurring in `α` the difference

`i^*(c₁(𝒩) ∩ [W]) - c₁(i^*𝒩) ∩ i^*[W] ∈ Z_k(E)`

is a locally finite sum `∑ (T_{W,j} → E)_* c_{W,j}` over integral closed subspaces
`T_{W,j} ⊆ E` lying over `|W|`.  Then `i^*(c₁(𝒩) ∩ α) - c₁(i^*𝒩) ∩ i^*α` is the locally finite
sum of the `n_W c_{W,j}` over all pairs `(W, j)`. -/
theorem gysinCycleMap_firstChernCapCycleMap_sub_eq_cycleFamilySum
    (α : CycleGroup D sX (k + 1 + 1))
    {J : {W : IntegralClosedSubspace D.site D.base D.base_mem X // α.1 W ≠ 0} → Type v}
    (T : ∀ W, J W →
      IntegralClosedSubspace D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor)
    (hT : ∀ W, LocallyFinite fun j : J W =>
      subspacePointSet D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor
        (T W j).subspace)
    (hTW : ∀ W j,
      subspacePointSet D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor
          (T W j).subspace ⊆
        pointsMap D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor
            (vanishingLocus D sX hX L s).1.ι ⁻¹'
          subspacePointSet D.site D.base D.base_mem X W.1.subspace)
    (e : ∀ W j, CycleGroup D ((T W j).subspace.ι ≫ (vanishingLocus D sX hX L s).1.ι ≫ sX) k)
    (h : ∀ W, gysinCycleMap D sX (vanishingLocus D sX hX L s) (isGood_vanishingLocus D sX hX L s) k
          (canonicalGysinComponentRule D sX hX (vanishingLocus D sX hX L s)
            (isGood_vanishingLocus D sX hX L s) k (canonicalFirstChernRule D sX hX L hL k))
          (firstChernCapCycleMap D sX hX (k + 1) (canonicalFirstChernRule D sX hX N hN (k + 1))
            (integralCycle D sX (k + 1 + 1) W.1 (α.2.2 W.1 W.2))) -
        firstChernCapCycleMap D ((vanishingLocus D sX hX L s).1.ι ≫ sX)
          (isGood_vanishingLocus D sX hX L s) k
          (canonicalFirstChernRule D _ (isGood_vanishingLocus D sX hX L s)
            ((modulePullback D.site D.base D.base_mem
              (vanishingLocusInclusion D sX hX L s)).obj N)
            (modulePullbackInvertible (vanishingLocusInclusion D sX hX L s) N hN) k)
          (gysinCycleMap D sX (vanishingLocus D sX hX L s) (isGood_vanishingLocus D sX hX L s)
            (k + 1)
            (canonicalGysinComponentRule D sX hX (vanishingLocus D sX hX L s)
              (isGood_vanishingLocus D sX hX L s) (k + 1)
              (canonicalFirstChernRule D sX hX L hL (k + 1)))
            (integralCycle D sX (k + 1 + 1) W.1 (α.2.2 W.1 W.2))) =
        cycleFamilySum D _ (isGood_vanishingLocus D sX hX L s) (T W) (hT W) k (e W)) :
    gysinCycleMap D sX (vanishingLocus D sX hX L s) (isGood_vanishingLocus D sX hX L s) k
          (canonicalGysinComponentRule D sX hX (vanishingLocus D sX hX L s)
            (isGood_vanishingLocus D sX hX L s) k (canonicalFirstChernRule D sX hX L hL k))
          (firstChernCapCycleMap D sX hX (k + 1) (canonicalFirstChernRule D sX hX N hN (k + 1))
            α) -
        firstChernCapCycleMap D ((vanishingLocus D sX hX L s).1.ι ≫ sX)
          (isGood_vanishingLocus D sX hX L s) k
          (canonicalFirstChernRule D _ (isGood_vanishingLocus D sX hX L s)
            ((modulePullback D.site D.base D.base_mem
              (vanishingLocusInclusion D sX hX L s)).obj N)
            (modulePullbackInvertible (vanishingLocusInclusion D sX hX L s) N hN) k)
          (gysinCycleMap D sX (vanishingLocus D sX hX L s) (isGood_vanishingLocus D sX hX L s)
            (k + 1)
            (canonicalGysinComponentRule D sX hX (vanishingLocus D sX hX L s)
              (isGood_vanishingLocus D sX hX L s) (k + 1)
              (canonicalFirstChernRule D sX hX L hL (k + 1)))
            α) =
      cycleFamilySum D _ (isGood_vanishingLocus D sX hX L s)
        (fun p : Σ W, J W => T p.1 p.2)
        (locallyFinite_sigma_of_subset
          ((α.2.1.comp_injective Subtype.val_injective).preimage_continuous
            (continuous_pointsMap D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.ι)
              |>.subset fun W => by simp [W.2]) hT hTW) k
        fun p => α.1 p.1.1 • e p.1 p.2 := by
  have hA := isCycleMapOfKernel_gysinCycleMap_comp_firstChernCapCycleMap D sX hX L hL s N hN k
  have hB := isCycleMapOfKernel_firstChernCapCycleMap_comp_gysinCycleMap D sX hX L hL s N hN k
  refine (hA.sub hB).eq_cycleFamilySum
    (continuous_pointsMap D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.ι)
    (isGood_vanishingLocus D sX hX L s) α T hT hTW e fun W => ?_
  exact ((hA.sub hB).apply_integralCycle (α.2.2 W.1 W.2)).symm.trans (h W)

/-- **The reduction of Stacks 0ERB to a single integral closed subspace, for a class of
presenting cycles.**  Let `P` be a property of cycles on the integral closed subspaces of `E`
which is stable under integer multiples — for instance "is a principal divisor on a subspace of
δ-dimension `k + 1`".  If for every integral closed subspace `W ⊆ X` of δ-dimension `k + 2` the
difference `i^*(c₁(𝒩) ∩ [W]) - c₁(i^*𝒩) ∩ i^*[W]` is a locally finite sum of cycles with
property `P` on integral closed subspaces of `E` lying over `|W|`, then for every
`α ∈ Z_{k+2}(X)` the difference `i^*(c₁(𝒩) ∩ α) - c₁(i^*𝒩) ∩ i^*α` is a locally finite sum of
cycles with property `P`. -/
theorem exists_gysinCycleMap_firstChernCapCycleMap_sub_eq_cycleFamilySum
    (P : ∀ T : IntegralClosedSubspace D.site D.base D.base_mem
        (vanishingLocus D sX hX L s).1.toFunctor,
      CycleGroup D (T.subspace.ι ≫ (vanishingLocus D sX hX L s).1.ι ≫ sX) k → Prop)
    (hP : ∀ T (n : ℤ) c, P T c → P T (n • c))
    (h : ∀ W (hW : deltaDimension D sX W = k + 1 + 1), ∃ (J : Type v)
      (T : J →
        IntegralClosedSubspace D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor)
      (hT : LocallyFinite fun j : J =>
        subspacePointSet D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor
          (T j).subspace)
      (e : ∀ j, CycleGroup D ((T j).subspace.ι ≫ (vanishingLocus D sX hX L s).1.ι ≫ sX) k),
      (∀ j, subspacePointSet D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor
          (T j).subspace ⊆
        pointsMap D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor
            (vanishingLocus D sX hX L s).1.ι ⁻¹'
          subspacePointSet D.site D.base D.base_mem X W.subspace) ∧
      (∀ j, P (T j) (e j)) ∧
      gysinCycleMap D sX (vanishingLocus D sX hX L s) (isGood_vanishingLocus D sX hX L s) k
          (canonicalGysinComponentRule D sX hX (vanishingLocus D sX hX L s)
            (isGood_vanishingLocus D sX hX L s) k (canonicalFirstChernRule D sX hX L hL k))
          (firstChernCapCycleMap D sX hX (k + 1) (canonicalFirstChernRule D sX hX N hN (k + 1))
            (integralCycle D sX (k + 1 + 1) W hW)) -
        firstChernCapCycleMap D ((vanishingLocus D sX hX L s).1.ι ≫ sX)
          (isGood_vanishingLocus D sX hX L s) k
          (canonicalFirstChernRule D _ (isGood_vanishingLocus D sX hX L s)
            ((modulePullback D.site D.base D.base_mem
              (vanishingLocusInclusion D sX hX L s)).obj N)
            (modulePullbackInvertible (vanishingLocusInclusion D sX hX L s) N hN) k)
          (gysinCycleMap D sX (vanishingLocus D sX hX L s) (isGood_vanishingLocus D sX hX L s)
            (k + 1)
            (canonicalGysinComponentRule D sX hX (vanishingLocus D sX hX L s)
              (isGood_vanishingLocus D sX hX L s) (k + 1)
              (canonicalFirstChernRule D sX hX L hL (k + 1)))
            (integralCycle D sX (k + 1 + 1) W hW)) =
        cycleFamilySum D _ (isGood_vanishingLocus D sX hX L s) T hT k e)
    (α : CycleGroup D sX (k + 1 + 1)) :
    ∃ (J : Type (max (u + 1) v))
      (T : J →
        IntegralClosedSubspace D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor)
      (hT : LocallyFinite fun j : J =>
        subspacePointSet D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor
          (T j).subspace)
      (e : ∀ j, CycleGroup D ((T j).subspace.ι ≫ (vanishingLocus D sX hX L s).1.ι ≫ sX) k),
      (∀ j, P (T j) (e j)) ∧
      gysinCycleMap D sX (vanishingLocus D sX hX L s) (isGood_vanishingLocus D sX hX L s) k
          (canonicalGysinComponentRule D sX hX (vanishingLocus D sX hX L s)
            (isGood_vanishingLocus D sX hX L s) k (canonicalFirstChernRule D sX hX L hL k))
          (firstChernCapCycleMap D sX hX (k + 1) (canonicalFirstChernRule D sX hX N hN (k + 1))
            α) -
        firstChernCapCycleMap D ((vanishingLocus D sX hX L s).1.ι ≫ sX)
          (isGood_vanishingLocus D sX hX L s) k
          (canonicalFirstChernRule D _ (isGood_vanishingLocus D sX hX L s)
            ((modulePullback D.site D.base D.base_mem
              (vanishingLocusInclusion D sX hX L s)).obj N)
            (modulePullbackInvertible (vanishingLocusInclusion D sX hX L s) N hN) k)
          (gysinCycleMap D sX (vanishingLocus D sX hX L s) (isGood_vanishingLocus D sX hX L s)
            (k + 1)
            (canonicalGysinComponentRule D sX hX (vanishingLocus D sX hX L s)
              (isGood_vanishingLocus D sX hX L s) (k + 1)
              (canonicalFirstChernRule D sX hX L hL (k + 1)))
            α) =
        cycleFamilySum D _ (isGood_vanishingLocus D sX hX L s) T hT k e := by
  choose J T hT e hTW hPe heq using
    fun W : {W : IntegralClosedSubspace D.site D.base D.base_mem X // α.1 W ≠ 0} =>
      h W.1 (α.2.2 W.1 W.2)
  exact ⟨_, _, _, _, fun p => hP _ _ _ (hPe p.1 p.2),
    gysinCycleMap_firstChernCapCycleMap_sub_eq_cycleFamilySum D sX hX L hL s N hN k α T hT hTW e
      heq⟩

/-- **The reduction of Stacks 0ERB to a single integral closed subspace, for rational
equivalence.**  If for every integral closed subspace `W ⊆ X` of δ-dimension `k + 2` the
difference `i^*(c₁(𝒩) ∩ [W]) - c₁(i^*𝒩) ∩ i^*[W]` is rationally equivalent to zero on `E` through
integral closed subspaces lying over `|W|`, then `i^*(c₁(𝒩) ∩ α) - c₁(i^*𝒩) ∩ i^*α` is
rationally equivalent to zero for every `α ∈ Z_{k+2}(X)`. -/
theorem isRationallyEquivalentToZero_gysinCycleMap_firstChernCapCycleMap_sub
    (h : ∀ W (hW : deltaDimension D sX W = k + 1 + 1),
      IsRationallyEquivalentToZeroWithin.{v} D _ (isGood_vanishingLocus D sX hX L s) k
        (gysinCycleMap D sX (vanishingLocus D sX hX L s) (isGood_vanishingLocus D sX hX L s) k
          (canonicalGysinComponentRule D sX hX (vanishingLocus D sX hX L s)
            (isGood_vanishingLocus D sX hX L s) k (canonicalFirstChernRule D sX hX L hL k))
          (firstChernCapCycleMap D sX hX (k + 1) (canonicalFirstChernRule D sX hX N hN (k + 1))
            (integralCycle D sX (k + 1 + 1) W hW)) -
        firstChernCapCycleMap D ((vanishingLocus D sX hX L s).1.ι ≫ sX)
          (isGood_vanishingLocus D sX hX L s) k
          (canonicalFirstChernRule D _ (isGood_vanishingLocus D sX hX L s)
            ((modulePullback D.site D.base D.base_mem
              (vanishingLocusInclusion D sX hX L s)).obj N)
            (modulePullbackInvertible (vanishingLocusInclusion D sX hX L s) N hN) k)
          (gysinCycleMap D sX (vanishingLocus D sX hX L s) (isGood_vanishingLocus D sX hX L s)
            (k + 1)
            (canonicalGysinComponentRule D sX hX (vanishingLocus D sX hX L s)
              (isGood_vanishingLocus D sX hX L s) (k + 1)
              (canonicalFirstChernRule D sX hX L hL (k + 1)))
            (integralCycle D sX (k + 1 + 1) W hW)))
        (pointsMap D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.toFunctor
            (vanishingLocus D sX hX L s).1.ι ⁻¹'
          subspacePointSet D.site D.base D.base_mem X W.subspace))
    (α : CycleGroup D sX (k + 1 + 1)) :
    IsRationallyEquivalentToZero.{max (u + 1) v} D _ (isGood_vanishingLocus D sX hX L s) k
      (gysinCycleMap D sX (vanishingLocus D sX hX L s) (isGood_vanishingLocus D sX hX L s) k
          (canonicalGysinComponentRule D sX hX (vanishingLocus D sX hX L s)
            (isGood_vanishingLocus D sX hX L s) k (canonicalFirstChernRule D sX hX L hL k))
          (firstChernCapCycleMap D sX hX (k + 1) (canonicalFirstChernRule D sX hX N hN (k + 1))
            α) -
        firstChernCapCycleMap D ((vanishingLocus D sX hX L s).1.ι ≫ sX)
          (isGood_vanishingLocus D sX hX L s) k
          (canonicalFirstChernRule D _ (isGood_vanishingLocus D sX hX L s)
            ((modulePullback D.site D.base D.base_mem
              (vanishingLocusInclusion D sX hX L s)).obj N)
            (modulePullbackInvertible (vanishingLocusInclusion D sX hX L s) N hN) k)
          (gysinCycleMap D sX (vanishingLocus D sX hX L s) (isGood_vanishingLocus D sX hX L s)
            (k + 1)
            (canonicalGysinComponentRule D sX hX (vanishingLocus D sX hX L s)
              (isGood_vanishingLocus D sX hX L s) (k + 1)
              (canonicalFirstChernRule D sX hX L hL (k + 1)))
            α)) := by
  have hA := isCycleMapOfKernel_gysinCycleMap_comp_firstChernCapCycleMap D sX hX L hL s N hN k
  have hB := isCycleMapOfKernel_firstChernCapCycleMap_comp_gysinCycleMap D sX hX L hL s N hN k
  refine isRationallyEquivalentToZero_sub_of_isCycleMapOfKernel _
    (isGood_vanishingLocus D sX hX L s)
    (continuous_pointsMap D.site D.base D.base_mem (vanishingLocus D sX hX L s).1.ι) hA
    hB (fun W => ?_) α
  by_cases hW : deltaDimension D sX W = k + 1 + 1
  · exact ((hA.sub hB).apply_integralCycle hW).symm ▸ h W hW
  · rw [firstChernComponentCycle_of_deltaDimension_ne D sX hX (k + 1) _ hW,
      gysinComponentCycle_of_deltaDimension_ne D sX _ _ (k + 1) _ hW, map_zero, map_zero,
      sub_zero]
    exact isRationallyEquivalentToZeroWithin_zero D _ _ k _

end AlgebraicGeometry.Space

end

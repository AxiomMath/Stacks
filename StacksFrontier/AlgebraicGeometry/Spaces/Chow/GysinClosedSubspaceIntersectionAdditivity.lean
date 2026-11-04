module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalGysinRule
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinIntersectionRestrictedSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinOfClosedSubspaceNonContainment
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedSubspaceComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.InverseImageDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.VanishingLocusCycleOnDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ZeroSchemeChartGeneralChart
public import StacksFrontier.Topology.Dimension.TopDimensionalComponents

/-!
# Stacks 0ER7: the refined Gysin map on the cycle of a closed subspace

In Situation 0EDT let `X/B` be good and let `(ℒ, s, i : E → X)` be a triple as in Definition
0ER1: `ℒ` an invertible `𝒪_X`-module, `s` a global section of it and `E = Z(s)` the vanishing
locus of Stacks 0845, with its closed immersion into `X`.  **Stacks 0ER7** says that for a closed
subspace `Z ⊆ X` with `dim_δ(Z) ≤ k + 1` whose intersection `E ∩ Z` is an effective Cartier
divisor on `Z`,

  `i^*([Z]_{k + 1}) = [E ∩ Z]_k`.

The letter `D` is the dimension situation of Stacks 0EDT, so the closed subspace the source calls
`D` is called `E` here, as in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.EffectiveCartierIntersection`.

This file proves it with nothing of the source's argument assumed.  What
`AlgebraicGeometry.Space.gysinCycleMap_eq_of_cycleCoeffOfClosedSubspace` and
`AlgebraicGeometry.Space.gysinCycleMap_closedSubspaceCycle_eq` still carry is **Stacks 0EQL for
`(Z, ℒ|_Z, s|_Z)`**, the identity `[E ∩ Z]_k = ∑ n_W [E ∩ W]_k` over the irreducible components
`W ⊆ Z` of δ-dimension `k + 1`; Stacks 0EQL is now available on the nose, as
`AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace_zeroScheme_eq_componentZeroCycleSumCoeff`
(`StacksFrontier/AlgebraicGeometry/Spaces/Chow/ZeroSchemeChartGeneralChart.lean`), and the work here
is to instantiate it at the triple `(Z, ℒ|_Z, s|_Z)` and transport both of its sides into the
ambient space `X`, where the Gysin coefficient family of Stacks 0ER1(2) lives.

## Main results

* `AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace_interOnVanishingLocus_eq_finsum`:
  **Stacks 0EQL at the closed subspace `Z`, in the shape Stacks 0ER7 needs**: the coefficient
  family of `[E ∩ Z]_k` read on `E` is the `[Z]_{k+1}`-weighted sum of the component cycles of
  Stacks 0ER1(1).
* `AlgebraicGeometry.Space.gysinCycleMap_closedSubspaceCycle_coe_eq`: **Stacks 0ER7**,
  unconditionally, at the component rule `AlgebraicGeometry.Space.canonicalGysinComponentRule`,
  stated coefficientwise.
* `AlgebraicGeometry.Space.gysinCycleMap_canonical_eq_of_cycleCoeffOfClosedSubspace`: the same
  identity as an equality `i^*([Z]_{k+1}) = [E ∩ Z]_k` in `Z_k(E)`, for cycles `α` and `β`
  supplied with their coefficient families pinned to Stacks 0EE9.  This is the shape in which
  `AlgebraicGeometry.Space.gysinCycleMap_eq_of_cycleCoeffOfClosedSubspace`
  (`StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinOfClosedSubspace`) states Stacks 0ER7 at an
  arbitrary component rule, with its two inputs now discharged.
* `AlgebraicGeometry.Space.cycleClosedPushforward_componentZeroCycleCoeff_eq`: the two readings
  of `E ∩ W`, for `W ⊆ Z` an integral closed subspace, give the same cycle on `X` — one as the
  zero scheme `Z(s|_W)` of Stacks 0EQL on `W`, the other as clause (1)(a) of Stacks 0ER1 on `E`.
* `AlgebraicGeometry.Space.isIrreducibleComponent_of_cycleCoeffOfClosedSubspace_ne_zero`: an
  integral closed subspace of `Z` whose image in `X` occurs in `[Z]_n` is an irreducible
  component of `Z` in the sense of Stacks 0EE8.  This is what makes the index set of Stacks 0EQL
  — the components of `Z` of δ-dimension `k + 1` — carry the whole of the sum of Stacks 0ER1(2).
* `AlgebraicGeometry.Space.deltaDimensionClosed_univ_closedSubspace_le`: the bound
  `dim_δ(Z) ≤ n` read on `Z` as a good algebraic space over the base, which is the form Stacks
  0EQL asks for.

## Implementation notes

### The three ambient spaces, and how the two sides are matched

Stacks 0EQL on `Z` is an identity of coefficient families on the integral closed subspaces of
`Z`; the Gysin coefficient family of Stacks 0ER1(2) is one on the integral closed subspaces of
`E`.  Both are compared by pushing forward to `X` along the respective closed immersions, which
is injective on coefficient families
(`AlgebraicGeometry.Space.cycleClosedPushforward_apply_pushforward`), and the pushforward
commutes with the weighted sums on either side
(`AlgebraicGeometry.Space.cycleClosedPushforward_finsum_mul`).  Term by term:

* The left-hand sides agree because the cycle of a closed subspace does not depend on the ambient
  space: the two readings of `E ∩ Z`, inside `E` and inside `Z`, have the same pushforward to
  `X`, which is
  `cycleClosedPushforward_interOnVanishingLocus_eq_cycleClosedPushforward_interOnClosedSubspace`
  (in the namespace `AlgebraicGeometry.Space`).
* On the right-hand sides the summand of Stacks 0EQL at a component `W ⊆ Z` is the cycle of
  `Z(s|_W)` formed on `W` and pushed to `Z`, while the summand of Stacks 0ER1(1)(a) at the image
  of `W` in `X` is the cycle of `E ∩ W` formed on `E`.  Both push forward to the cycle of the
  intersection `E ⊓ W` formed in `X`, by
  `AlgebraicGeometry.Space.cycleClosedPushforward_cycleCoeffOfClosedSubspace_eq` applied three
  times.  The comparison of `(E ∩ Z) ⊓ W` inside `Z` with `E ⊓ W` inside `X` is
  `AlgebraicGeometry.Space.interInfPushforwardHom`, built from the identification of an integral
  closed subspace with its image, `AlgebraicGeometry.Space.IntegralClosedSubspace.pushforwardIso`.
* The two weights agree: the coefficient of `[Z]_{k+1}` at the image of `W` is, by
  `AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace_closedSubspaceComponentImage`, the length
  of `𝒪_Z` at the generic point of `W`, which is the coefficient of the fundamental cycle
  `[Z]_{k+1}` formed on `Z` at `W`; the δ-dimensions match by Stacks 0EDX.
* The two index sets agree: the sum of Stacks 0ER1(2) runs over all integral closed subspaces of
  `X`, and a nonzero coefficient in `[Z]_{k+1}` forces the subspace to be the image of an
  irreducible component of `Z` of δ-dimension `k + 1`, which is the index set of Stacks 0EQL.

### What the statement proves and what it does not carry

The identity is stated coefficientwise rather than as an equality in `Z_k(E)`.  Forming
`[E ∩ Z]_k` as an element of `Z_k(E)` asks in addition for `dim_δ(E ∩ Z) ≤ k`, which the source
gets from the effective Cartier hypothesis and which has no declaration in this library; the
coefficientwise form needs no such bound and weakens nothing, both sides being the coefficient
families the source's two cycles have.  Clause (1)(b) of Stacks 0ER1 — the cap product
`c₁(ℒ|_W) ∩ [W]` of Stacks 0EQJ — remains the explicit parameter `chern` that Definition 0ER1
takes it to be in this library; it plays no part in the identity, every component occurring in
`[Z]_{k+1}` falling under clause (1)(a).

## References

* [Stacks Project, Tag 0ER7](https://stacks.math.columbia.edu/tag/0ER7)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0EQL](https://stacks.math.columbia.edu/tag/0EQL)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDX](https://stacks.math.columbia.edu/tag/0EDX)
* [Stacks Project, Tag 0EE8](https://stacks.math.columbia.edu/tag/0EE8)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0845](https://stacks.math.columbia.edu/tag/0845)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p)

/-- **The bound `dim_δ(Z) ≤ n` read on `Z` as a good algebraic space over the base.**  The
δ-dimension of the whole of `Z` computed along `Z → B` is at most the δ-dimension of `|Z|`
computed along `X → B`: the inclusion `Z → X` is locally quasi-finite, so by Stacks 0EDN the two
induced dimension functions agree at corresponding points.  This is the form in which Stacks
0EQL asks for the bound on the space it is applied to. -/
theorem deltaDimensionClosed_univ_closedSubspace_le
    (Z : ClosedSubspaces D.site D.base D.base_mem X) (n : ℤ)
    (hdim : deltaDimensionSubspace D p hp Z.1 Z.2 ≤ (n : EInt)) :
    deltaDimensionClosed D (Z.1.ι ≫ p) (isGood_closedSubspace D p hp Z) Set.univ isClosed_univ
      ≤ (n : EInt) := by
  have hq := isGood_closedSubspace D p hp Z
  rw [deltaDimensionSubspace_eq_deltaDimensionClosed] at hdim
  have hpt := (deltaDimensionClosed_le_coe_iff D p hp _ _ n).1 hdim
  have hlqf : IsLocallyQuasiFinite D.site D.base D.base_mem Z.1.ι :=
    isLocallyQuasiFinite_of_isImmersion D.site D.base D.base_mem _
      (isImmersion_of_isClosedImmersion D.site D.base D.base_mem Z.2.2)
  refine (deltaDimensionClosed_le_coe_iff D _ hq _ _ n).2 fun t _ => ?_
  have hcomp : inducedDimensionValue D.site D.base D.base_mem D.delta (Z.1.ι ≫ p) t =
      inducedDimensionValue D.site D.base D.base_mem D.delta p
        (pointsMap D.site D.base D.base_mem Z.1.toFunctor Z.1.ι t) :=
    D.deltaValue_comp_of_isLocallyQuasiFinite hq.1 hp.1 _ p hlqf hp.2.2 t
  rw [hcomp]
  exact hpt _ ⟨t, rfl⟩

/-- The coefficient family of `[A]_n` depends only on the subfunctor `A`, not on the proof that
it is a closed subspace, so two equal subfunctors have the same cycle.  (The same statement at a
single integral closed subspace is private to
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinFlatPullbackPreimage`.) -/
theorem cycleCoeffOfClosedSubspace_eq_of_subfunctor_eq
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (n : ℤ) {A A' : Subfunctor Y}
    (hA : IsClosedSubspace D.site D.base D.base_mem A)
    (hA' : IsClosedSubspace D.site D.base D.base_mem A') (h : A = A') :
    cycleCoeffOfClosedSubspace D sY hY A hA n
        (canonicalGeometricPoint D.site D.base D.base_mem A.toFunctor) =
      cycleCoeffOfClosedSubspace D sY hY A' hA' n
        (canonicalGeometricPoint D.site D.base D.base_mem A'.toFunctor) := by
  subst h
  rfl

/-- **An integral closed subspace of `Z` whose image in `X` occurs in `[Z]_n` is an irreducible
component of `Z`**, in the sense of Stacks 0EE8, when `dim_δ(Z) ≤ n`.

Stacks 0EE6 makes the point set of the image an irreducible component of `|Z|` read as a closed
subset of `|X|`
(`AlgebraicGeometry.Space.exists_irreducibleComponents_of_cycleCoeffOfClosedSubspace_ne_zero`),
and that is carried back along the closed embedding `|Z| → |X|`: an irreducible subset of `|Z|`
containing the subspace has an image containing that component, hence equal to it by maximality
(`eq_image_of_image_subset_of_mem_irreducibleComponents`), and the embedding is injective. -/
theorem isIrreducibleComponent_of_cycleCoeffOfClosedSubspace_ne_zero
    (Z : ClosedSubspaces D.site D.base D.base_mem X) (n : ℤ)
    (hdim : deltaDimensionSubspace D p hp Z.1 Z.2 ≤ (n : EInt))
    (γ : points D.site D.base D.base_mem Z.1.toFunctor →
      GeometricPoint D.site D.base D.base_mem Z.1.toFunctor)
    (Wz : IntegralClosedSubspace D.site D.base D.base_mem Z.1.toFunctor)
    (hWz : cycleCoeffOfClosedSubspace D p hp Z.1 Z.2 n γ
      (closedSubspaceComponentImage D p hp Z.1 Z.2 Wz) ≠ 0) :
    IsIrreducibleComponent D.site D.base D.base_mem
      (isGood_closedSubspace D p hp Z).1 Wz.subspace := by
  obtain ⟨C, hC⟩ := exists_irreducibleComponents_of_cycleCoeffOfClosedSubspace_ne_zero D p hp
    Z.1 Z.2 n γ hdim _ hWz
  rw [IntegralClosedSubspace.subspacePointSet_pushforward] at hC
  have hinj : Function.Injective
      (pointsMap D.site D.base D.base_mem Z.1.toFunctor Z.1.ι) :=
    (isClosedEmbedding_pointsMap_of_isClosedImmersion D.site D.base D.base_mem hp.1
      Z.2.2).injective
  refine ⟨Wz.isClosedSubspace, Wz.isIntegralSpace,
    isIrreducible_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem Wz,
    fun S hS hsub => ?_⟩
  have himg : pointsMap D.site D.base D.base_mem Z.1.toFunctor Z.1.ι '' S =
      Subtype.val '' (C : Set (subspacePointSet D.site D.base D.base_mem X Z.1)) := by
    refine eq_image_of_image_subset_of_mem_irreducibleComponents C.2
      (hS.image _ (continuous_pointsMap D.site D.base D.base_mem Z.1.ι).continuousOn)
      (fun _ ⟨y, _, hy⟩ => hy ▸ ⟨y, rfl⟩) ?_
    rw [← hC]
    exact Set.image_mono hsub
  intro x hx
  have hmem : pointsMap D.site D.base D.base_mem Z.1.toFunctor Z.1.ι x ∈
      pointsMap D.site D.base D.base_mem Z.1.toFunctor Z.1.ι ''
        subspacePointSet D.site D.base D.base_mem Z.1.toFunctor Wz.subspace := by
    rw [hC, ← himg]
    exact ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hxy⟩ := hmem
  exact hinj hxy ▸ hy

/-- **Pushforward of coefficient families commutes with a pointwise weighted sum.**  At the image
of an integral closed subspace both sides are the sum of the weighted coefficients there, and
elsewhere every term of both sides vanishes. -/
theorem cycleClosedPushforward_finsum_mul {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (hY : IsAlgebraicSpace D.site D.base D.base_mem Y)
    (hXdec : IsDecentSpace D.site D.base D.base_mem X) {i : Y ⟶ X}
    (hi : IsClosedImmersion D.site D.base D.base_mem i) {ι : Type*} (a : ι → ℤ)
    (c : ι → IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ)
    (V : IntegralClosedSubspace D.site D.base D.base_mem X) :
    cycleClosedPushforward D hX hY hXdec hi (fun T => ∑ᶠ j : ι, a j * c j T) V =
      ∑ᶠ j : ι, a j * cycleClosedPushforward D hX hY hXdec hi (c j) V := by
  by_cases hex : ∃ T, IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX hY hXdec
      hi T = V
  · obtain ⟨T, rfl⟩ := hex
    rw [cycleClosedPushforward_apply_pushforward]
    exact finsum_congr fun j => by rw [cycleClosedPushforward_apply_pushforward]
  · rw [cycleClosedPushforward_apply_of_forall_ne D hX hY hXdec hi _ V
      fun T hT => hex ⟨T, hT⟩]
    refine (finsum_eq_zero_of_forall_eq_zero fun j => ?_).symm
    rw [cycleClosedPushforward_apply_of_forall_ne D hX hY hXdec hi _ V
      fun T hT => hex ⟨T, hT⟩, mul_zero]


section InterInf

variable (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections)
    (Z : ClosedSubspaces D.site D.base D.base_mem X)
    (Wz : IntegralClosedSubspace D.site D.base D.base_mem Z.1.toFunctor)

/-- **The intersection of `E` with an integral closed subspace `W ⊆ Z`, compared inside `Z` and
inside `X`.**  For a closed subspace `Z ⊆ X` and an integral closed subspace `W ⊆ Z` with image
`W' ⊆ X`, the intersection `(E ∩ Z) ⊓ W` formed in `Z` and the intersection `E ⊓ W'` formed in
`X` are identified over `X`.

The map is the inclusion of `Z` restricted to the first; it is bijective on sections because `W`
is carried isomorphically onto `W'` by
`AlgebraicGeometry.Space.IntegralClosedSubspace.pushforwardIso`. -/
def interInfPushforwardHom :
    ((vanishingLocus D p hp L s).1.preimage Z.1.ι ⊓ Wz.subspace).toFunctor ⟶
      ((vanishingLocus D p hp L s).1 ⊓
        (closedSubspaceComponentImage D p hp Z.1 Z.2 Wz).subspace).toFunctor :=
  Subfunctor.lift
    (((vanishingLocus D p hp L s).1.preimage Z.1.ι ⊓ Wz.subspace).ι ≫ Z.1.ι) (by
      intro U y hy
      obtain ⟨x, rfl⟩ := hy
      have hψ := IntegralClosedSubspace.pushforwardIso_hom_comp_ι D.site D.base D.base_mem hp.1
        Z.2.1 (D.isDecentSpace_of_isGood p hp) Z.2.2 Wz
      have h := ConcreteCategory.congr_hom (congr_app hψ U) (⟨x.1, x.2.2⟩ :
        Wz.subspace.toFunctor.obj U)
      have h' : (((IntegralClosedSubspace.pushforwardIso D.site D.base D.base_mem hp.1 Z.2.1
            (D.isDecentSpace_of_isGood p hp) Z.2.2 Wz).hom.app U
              (⟨x.1, x.2.2⟩ : Wz.subspace.toFunctor.obj U) :
            (closedSubspaceComponentImage D p hp Z.1 Z.2 Wz).subspace.toFunctor.obj U) :
          X.obj U) = ((x.1 : Z.1.toFunctor.obj U) : X.obj U) := h
      refine ⟨x.2.1, ?_⟩
      rw [show ((((vanishingLocus D p hp L s).1.preimage Z.1.ι ⊓ Wz.subspace).ι ≫
          Z.1.ι).app U x) = ((x.1 : Z.1.toFunctor.obj U) : X.obj U) from rfl, ← h']
      exact ((IntegralClosedSubspace.pushforwardIso D.site D.base D.base_mem hp.1 Z.2.1
        (D.isDecentSpace_of_isGood p hp) Z.2.2 Wz).hom.app U
          (⟨x.1, x.2.2⟩ : Wz.subspace.toFunctor.obj U)).2)

/-- The comparison `interInfPushforwardHom` is a morphism over `X`. -/
theorem interInfPushforwardHom_comp_ι :
    interInfPushforwardHom D p hp L s Z Wz ≫
        ((vanishingLocus D p hp L s).1 ⊓
          (closedSubspaceComponentImage D p hp Z.1 Z.2 Wz).subspace).ι =
      ((vanishingLocus D p hp L s).1.preimage Z.1.ι ⊓ Wz.subspace).ι ≫ Z.1.ι :=
  rfl

/-- The comparison `interInfPushforwardHom` is an isomorphism. -/
instance : IsIso (interInfPushforwardHom D p hp L s Z Wz) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun U => ?_
  rw [isIso_iff_bijective]
  refine ⟨fun a b hab => have h := congrArg Subtype.val hab; Subtype.ext (Subtype.ext h),
    fun z => ?_⟩
  let w : Wz.subspace.toFunctor.obj U :=
    (IntegralClosedSubspace.pushforwardIso D.site D.base D.base_mem hp.1 Z.2.1
      (D.isDecentSpace_of_isGood p hp) Z.2.2 Wz).inv.app U
        (⟨z.1, z.2.2⟩ : (closedSubspaceComponentImage D p hp Z.1 Z.2 Wz).subspace.toFunctor.obj U)
  have h := ConcreteCategory.congr_hom (congr_app
    (IntegralClosedSubspace.pushforwardIso_inv_comp_ι_comp D.site D.base D.base_mem hp.1 Z.2.1
      (D.isDecentSpace_of_isGood p hp) Z.2.2 Wz) U)
    (⟨z.1, z.2.2⟩ : (closedSubspaceComponentImage D p hp Z.1 Z.2 Wz).subspace.toFunctor.obj U)
  have h' : (((w : Z.1.toFunctor.obj U) : X.obj U)) = z.1 := h
  have hmem : ((w : Z.1.toFunctor.obj U) : X.obj U) ∈ (vanishingLocus D p hp L s).1.obj U :=
    h' ▸ z.2.1
  exact ⟨⟨(w : Z.1.toFunctor.obj U), hmem, w.2⟩, Subtype.ext h'⟩

end InterInf


section Transport

variable (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections) (k : ℤ)
    (Z : ClosedSubspaces D.site D.base D.base_mem X)

/-- **The zero scheme `Z(s|_W)` of Stacks 0EQL, for `W ⊆ Z` an integral closed subspace of a
closed subspace of `X`, is the intersection `E ∩ W` read in `W`.**  This is
`AlgebraicGeometry.Space.interOnClosedSubspace_eq_zeroScheme` applied twice: once on `X` to
identify `E ∩ Z` with `Z(s|_Z)`, and once on `Z` to identify `(E ∩ Z) ∩ W` with
`Z((s|_Z)|_W)`. -/
theorem componentVanishingLocus_closedSubspaceRestrict_eq
    (hL : IsInvertibleSheaf D p hp L)
    (Wz : IntegralClosedSubspace D.site D.base D.base_mem Z.1.toFunctor) :
    (componentVanishingLocus D (Z.1.ι ≫ p) (isGood_closedSubspace D p hp Z)
          (closedSubspaceRestrictSheaf D p hp L Z)
          (closedSubspaceRestrictSection D p hp L s Z) Wz).1 =
      ((vanishingLocus D p hp L s).1.preimage Z.1.ι).preimage Wz.subspace.ι := by
  have hq := isGood_closedSubspace D p hp Z
  have hLZ : IsInvertibleSheaf D (Z.1.ι ≫ p) hq (closedSubspaceRestrictSheaf D p hp L Z) :=
    isInvertible_closedSubspaceRestrictSheaf D p hp L Z hL
  have h0 : vanishingLocus D (Z.1.ι ≫ p) hq (closedSubspaceRestrictSheaf D p hp L Z)
      (closedSubspaceRestrictSection D p hp L s Z) = interOnClosedSubspace D p hp L s Z :=
    (interOnClosedSubspace_eq_zeroScheme D p hp L s Z hL).symm
  have h1 := interOnClosedSubspace_eq_zeroScheme D (Z.1.ι ≫ p) hq
    (closedSubspaceRestrictSheaf D p hp L Z) (closedSubspaceRestrictSection D p hp L s Z)
    ⟨Wz.subspace, Wz.isClosedSubspace⟩ hLZ
  rw [show (componentVanishingLocus D (Z.1.ι ≫ p) hq
        (closedSubspaceRestrictSheaf D p hp L Z)
        (closedSubspaceRestrictSection D p hp L s Z) Wz) =
      interOnClosedSubspace D (Z.1.ι ≫ p) hq (closedSubspaceRestrictSheaf D p hp L Z)
        (closedSubspaceRestrictSection D p hp L s Z) ⟨Wz.subspace, Wz.isClosedSubspace⟩
      from h1.symm]
  exact congrArg (fun Y => Subfunctor.preimage Y.1 Wz.subspace.ι) h0

/-- **The two readings of `E ∩ W` give the same cycle on `X`, for `W ⊆ Z` an integral closed
subspace of a closed subspace of `X`.**  On the one hand `E ∩ W` is the zero scheme `Z(s|_W)` on
`W`, whose cycle pushed to `Z` is the summand of Stacks 0EQL; on the other it is the inverse image
of the image `W'` of `W` along `i : E → X`, whose cycle on `E` is clause (1)(a) of Stacks 0ER1 at
`W'`.  Both push forward to the cycle of `E ⊓ W'` formed in `X`. -/
theorem cycleClosedPushforward_componentZeroCycleCoeff_eq
    (hL : IsInvertibleSheaf D p hp L)
    (hE : D.IsGood ((vanishingLocus D p hp L s).1.ι ≫ p))
    (Wz : IntegralClosedSubspace D.site D.base D.base_mem Z.1.toFunctor) :
    cycleClosedPushforward D hp.1 Z.2.1 (D.isDecentSpace_of_isGood p hp) Z.2.2
        (componentZeroCycleCoeff D (Z.1.ι ≫ p) (isGood_closedSubspace D p hp Z)
          (closedSubspaceRestrictSheaf D p hp L Z)
          (closedSubspaceRestrictSection D p hp L s Z) k Wz
          (canonicalGeometricPoint D.site D.base D.base_mem
            (componentVanishingLocus D (Z.1.ι ≫ p) (isGood_closedSubspace D p hp Z)
              (closedSubspaceRestrictSheaf D p hp L Z)
              (closedSubspaceRestrictSection D p hp L s Z) Wz).1.toFunctor)) =
      cycleClosedPushforward D hp.1 (vanishingLocus D p hp L s).2.1
          (D.isDecentSpace_of_isGood p hp) (vanishingLocus D p hp L s).2.2
        (cycleCoeffOfClosedSubspace D ((vanishingLocus D p hp L s).1.ι ≫ p) hE
          (gysinIntersectionSubspace D p hp (vanishingLocus D p hp L s) hE
            (closedSubspaceComponentImage D p hp Z.1 Z.2 Wz)).1
          (gysinIntersectionSubspace D p hp (vanishingLocus D p hp L s) hE
            (closedSubspaceComponentImage D p hp Z.1 Z.2 Wz)).2 k
          (canonicalGeometricPoint D.site D.base D.base_mem
            (gysinIntersectionSubspace D p hp (vanishingLocus D p hp L s) hE
              (closedSubspaceComponentImage D p hp Z.1 Z.2 Wz)).1.toFunctor)) := by
  have hq := isGood_closedSubspace D p hp Z
  have hinf : IsClosedSubspace D.site D.base D.base_mem
      ((vanishingLocus D p hp L s).1 ⊓
        (closedSubspaceComponentImage D p hp Z.1 Z.2 Wz).subspace) :=
    inf_isClosedSubspace D.site D.base D.base_mem X hp.1 (vanishingLocus D p hp L s)
      ⟨(closedSubspaceComponentImage D p hp Z.1 Z.2 Wz).subspace,
        (closedSubspaceComponentImage D p hp Z.1 Z.2 Wz).isClosedSubspace⟩
  have hinfZ : IsClosedSubspace D.site D.base D.base_mem
      ((vanishingLocus D p hp L s).1.preimage Z.1.ι ⊓ Wz.subspace) :=
    inf_isClosedSubspace D.site D.base D.base_mem Z.1.toFunctor hq.1
      (interOnClosedSubspace D p hp L s Z) ⟨Wz.subspace, Wz.isClosedSubspace⟩
  have hinner : componentZeroCycleCoeff D (Z.1.ι ≫ p) hq (closedSubspaceRestrictSheaf D p hp L Z)
        (closedSubspaceRestrictSection D p hp L s Z) k Wz
        (canonicalGeometricPoint D.site D.base D.base_mem
          (componentVanishingLocus D (Z.1.ι ≫ p) hq (closedSubspaceRestrictSheaf D p hp L Z)
            (closedSubspaceRestrictSection D p hp L s Z) Wz).1.toFunctor) =
      cycleCoeffOfClosedSubspace D (Z.1.ι ≫ p) hq
        ((vanishingLocus D p hp L s).1.preimage Z.1.ι ⊓ Wz.subspace) hinfZ k
        (canonicalGeometricPoint D.site D.base D.base_mem
          ((vanishingLocus D p hp L s).1.preimage Z.1.ι ⊓ Wz.subspace).toFunctor) := by
    have hcv := componentVanishingLocus_closedSubspaceRestrict_eq D p hp L s Z hL Wz
    rw [show componentZeroCycleCoeff D (Z.1.ι ≫ p) hq (closedSubspaceRestrictSheaf D p hp L Z)
          (closedSubspaceRestrictSection D p hp L s Z) k Wz
          (canonicalGeometricPoint D.site D.base D.base_mem
            (componentVanishingLocus D (Z.1.ι ≫ p) hq (closedSubspaceRestrictSheaf D p hp L Z)
              (closedSubspaceRestrictSection D p hp L s Z) Wz).1.toFunctor) =
        cycleClosedPushforward D hq.1 Wz.isClosedSubspace.1
            (D.isDecentSpace_of_isGood (Z.1.ι ≫ p) hq) Wz.isClosedSubspace.2
          (cycleCoeffOfClosedSubspace D (Wz.subspace.ι ≫ Z.1.ι ≫ p)
            (isGood_integralClosedSubspace D (Z.1.ι ≫ p) hq Wz)
            (componentVanishingLocus D (Z.1.ι ≫ p) hq (closedSubspaceRestrictSheaf D p hp L Z)
              (closedSubspaceRestrictSection D p hp L s Z) Wz).1
            (componentVanishingLocus D (Z.1.ι ≫ p) hq (closedSubspaceRestrictSheaf D p hp L Z)
              (closedSubspaceRestrictSection D p hp L s Z) Wz).2 k
            (canonicalGeometricPoint D.site D.base D.base_mem
              (componentVanishingLocus D (Z.1.ι ≫ p) hq (closedSubspaceRestrictSheaf D p hp L Z)
                (closedSubspaceRestrictSection D p hp L s Z) Wz).1.toFunctor)) from rfl]
    rw [cycleCoeffOfClosedSubspace_eq_of_subfunctor_eq D (Wz.subspace.ι ≫ Z.1.ι ≫ p)
      (isGood_integralClosedSubspace D (Z.1.ι ≫ p) hq Wz) k
      (componentVanishingLocus D (Z.1.ι ≫ p) hq (closedSubspaceRestrictSheaf D p hp L Z)
        (closedSubspaceRestrictSection D p hp L s Z) Wz).2
      (hcv ▸ (componentVanishingLocus D (Z.1.ι ≫ p) hq (closedSubspaceRestrictSheaf D p hp L Z)
        (closedSubspaceRestrictSection D p hp L s Z) Wz).2) hcv]
    exact cycleClosedPushforward_cycleCoeffOfClosedSubspace_eq D (Z.1.ι ≫ p) hq Wz.subspace
      Wz.isClosedSubspace (isGood_integralClosedSubspace D (Z.1.ι ≫ p) hq Wz)
      (((vanishingLocus D p hp L s).1.preimage Z.1.ι).preimage Wz.subspace.ι) _
      ((vanishingLocus D p hp L s).1.preimage Z.1.ι ⊓ Wz.subspace) hinfZ
      (preimageInfHom' ((vanishingLocus D p hp L s).1.preimage Z.1.ι) Wz.subspace)
      (preimageInfHom'_comp_ι ((vanishingLocus D p hp L s).1.preimage Z.1.ι) Wz.subspace) k
  rw [cycleClosedPushforward_cycleCoeffOfClosedSubspace_eq D p hp (vanishingLocus D p hp L s).1
    (vanishingLocus D p hp L s).2 hE
    ((closedSubspaceComponentImage D p hp Z.1 Z.2 Wz).subspace.preimage
      (vanishingLocus D p hp L s).1.ι) _
    ((vanishingLocus D p hp L s).1 ⊓
      (closedSubspaceComponentImage D p hp Z.1 Z.2 Wz).subspace) hinf
    (preimageInfHom (vanishingLocus D p hp L s).1
      (closedSubspaceComponentImage D p hp Z.1 Z.2 Wz).subspace)
    (preimageInfHom_comp_ι (vanishingLocus D p hp L s).1
      (closedSubspaceComponentImage D p hp Z.1 Z.2 Wz).subspace) k, hinner,
    cycleClosedPushforward_cycleCoeffOfClosedSubspace_eq D p hp Z.1 Z.2 hq
      ((vanishingLocus D p hp L s).1.preimage Z.1.ι ⊓ Wz.subspace) hinfZ
      ((vanishingLocus D p hp L s).1 ⊓
        (closedSubspaceComponentImage D p hp Z.1 Z.2 Wz).subspace) hinf
      (interInfPushforwardHom D p hp L s Z Wz)
      (interInfPushforwardHom_comp_ι D p hp L s Z Wz) k]

end Transport


section Additivity

variable (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections) (k : ℤ)
    (Z : ClosedSubspaces D.site D.base D.base_mem X)

/-- **Stacks 0EQL at the closed subspace `Z`, in the shape Stacks 0ER7 needs it.**  For `X/B`
good, `ℒ` invertible with global section `s` and vanishing locus `E = Z(s)`, and a closed
subspace `Z ⊆ X` with `dim_δ(Z) ≤ k + 1` whose intersection with `E` is an effective Cartier
divisor on `Z`, the coefficient family of the cycle `[E ∩ Z]_k` of Stacks 0EE9 read on `E` is the
`[Z]_{k+1}`-weighted sum of the component cycles of Stacks 0ER1(1).

This is Lemma 0EQL for the triple `(Z, ℒ|_Z, s|_Z)` — whose hypotheses the effective Cartier
condition supplies, by
`AlgebraicGeometry.Space.isEffectiveCartierDivisor_interOnClosedSubspace_iff_isRegularSection` —
transported into the ambient `X`; see the implementation notes of the module. -/
theorem cycleCoeffOfClosedSubspace_interOnVanishingLocus_eq_finsum
    (hL : IsInvertibleSheaf D p hp L)
    (hE : D.IsGood ((vanishingLocus D p hp L s).1.ι ≫ p))
    (chern : FirstChernComponentCycleRule D p k)
    (hZdim : deltaDimensionSubspace D p hp Z.1 Z.2 ≤ ((k + 1 : ℤ) : EInt))
    (hCartier : IsEffectiveCartierDivisor D.site D.base D.base_mem ⟨Z.1.toFunctor, Z.2.1⟩
      (interOnClosedSubspace D p hp L s Z))
    (T : IntegralClosedSubspace D.site D.base D.base_mem
      (vanishingLocus D p hp L s).1.toFunctor) :
    cycleCoeffOfClosedSubspace D ((vanishingLocus D p hp L s).1.ι ≫ p) hE
        (interOnVanishingLocus D p hp L s Z).1 (interOnVanishingLocus D p hp L s Z).2 k
        (canonicalGeometricPoint D.site D.base D.base_mem
          (interOnVanishingLocus D p hp L s Z).1.toFunctor) T =
      ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem X,
        (closedSubspaceCycle D p hp Z.1 Z.2 (k + 1) hZdim).1 W *
          (gysinComponentCycle D p (vanishingLocus D p hp L s) hE k
            (canonicalGysinComponentRule D p hp (vanishingLocus D p hp L s) hE k chern) W).1 T := by
  have hq := isGood_closedSubspace D p hp Z
  -- Stacks 0EQL on `Z`, at the canonical geometric representatives
  have h0EQL := cycleCoeffOfClosedSubspace_zeroScheme_eq_componentZeroCycleSumCoeff
    D (Z.1.ι ≫ p) hq (closedSubspaceRestrictSheaf D p hp L Z)
    (closedSubspaceRestrictSection D p hp L s Z) k
    (isInvertible_closedSubspaceRestrictSheaf D p hp L Z hL)
    ((isEffectiveCartierDivisor_interOnClosedSubspace_iff_isRegularSection D p hp L s Z
      hL).1 hCartier)
    (deltaDimensionClosed_univ_closedSubspace_le D p hp Z (k + 1) hZdim)
    (canonicalGeometricPoint D.site D.base D.base_mem Z.1.toFunctor)
    (fun x => canonicalGeometricPoint_image D.site D.base D.base_mem Z.1.toFunctor x)
    (fun W => canonicalGeometricPoint D.site D.base D.base_mem
      (componentVanishingLocus D (Z.1.ι ≫ p) hq (closedSubspaceRestrictSheaf D p hp L Z)
        (closedSubspaceRestrictSection D p hp L s Z) W.1).1.toFunctor)
    (fun W y => canonicalGeometricPoint_image D.site D.base D.base_mem _ y)
    (canonicalGeometricPoint D.site D.base D.base_mem
      (vanishingLocus D (Z.1.ι ≫ p) hq (closedSubspaceRestrictSheaf D p hp L Z)
        (closedSubspaceRestrictSection D p hp L s Z)).1.toFunctor)
    (fun y => canonicalGeometricPoint_image D.site D.base D.base_mem _ y)
  classical
  have hkey : (cycleClosedPushforward D hp.1 (vanishingLocus D p hp L s).2.1
        (D.isDecentSpace_of_isGood p hp) (vanishingLocus D p hp L s).2.2)
        (cycleCoeffOfClosedSubspace D ((vanishingLocus D p hp L s).1.ι ≫ p) hE
          (interOnVanishingLocus D p hp L s Z).1 (interOnVanishingLocus D p hp L s Z).2 k
          (canonicalGeometricPoint D.site D.base D.base_mem
            (interOnVanishingLocus D p hp L s Z).1.toFunctor)) =
      (cycleClosedPushforward D hp.1 (vanishingLocus D p hp L s).2.1
        (D.isDecentSpace_of_isGood p hp) (vanishingLocus D p hp L s).2.2)
        (fun T' => ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem X,
          (closedSubspaceCycle D p hp Z.1 Z.2 (k + 1) hZdim).1 W *
            (gysinComponentCycle D p (vanishingLocus D p hp L s) hE k
              (canonicalGysinComponentRule D p hp (vanishingLocus D p hp L s) hE k chern)
              W).1 T') := by
    refine funext fun V => ?_
    -- the index map: an integral closed subspace of `Z` of δ-dimension `k+1` to its image in `X`
    have hginj : Function.Injective
        (fun Wz : ComponentsOfDeltaDimension D (Z.1.ι ≫ p) hq (k + 1) =>
          (closedSubspaceComponentImage D p hp Z.1 Z.2) Wz.1) := by
      intro a b hab
      exact Subtype.ext (IntegralClosedSubspace.injective_pushforward D.site D.base D.base_mem hp.1
        Z.2.1 (D.isDecentSpace_of_isGood p hp) Z.2.2 hab)
    -- the coefficient of `[Z]_{k+1}` at the image of `Wz` is the fundamental coefficient on `Z`
    have hcoeff : ∀ Wz : IntegralClosedSubspace D.site D.base D.base_mem Z.1.toFunctor,
        (closedSubspaceCycle D p hp Z.1 Z.2 (k + 1) hZdim).1
            ((closedSubspaceComponentImage D p hp Z.1 Z.2) Wz) =
          fundamentalCycleCoeff D (Z.1.ι ≫ p) hq (k + 1)
            (canonicalGeometricPoint D.site D.base D.base_mem Z.1.toFunctor) Wz := by
      intro Wz
      rw [closedSubspaceCycle_coe, cycleCoeffOfClosedSubspace_closedSubspaceComponentImage,
        deltaDimension_closedSubspaceComponentImage]
      rfl
    -- the summand at a component of `Z`
    have hval : ∀ Wz : ComponentsOfDeltaDimension D (Z.1.ι ≫ p) hq (k + 1),
        (closedSubspaceCycle D p hp Z.1 Z.2 (k + 1) hZdim).1
            ((closedSubspaceComponentImage D p hp Z.1 Z.2) Wz.1) *
            (cycleClosedPushforward D hp.1 (vanishingLocus D p hp L s).2.1
              (D.isDecentSpace_of_isGood p hp) (vanishingLocus D p hp L s).2.2)
              ((gysinComponentCycle D p (vanishingLocus D p hp L s) hE k
                (canonicalGysinComponentRule D p hp (vanishingLocus D p hp L s) hE k chern)
                ((closedSubspaceComponentImage D p hp Z.1 Z.2) Wz.1)).1) V =
          fundamentalCycleCoeff D (Z.1.ι ≫ p) hq (k + 1)
              (canonicalGeometricPoint D.site D.base D.base_mem Z.1.toFunctor) Wz.1 *
            (cycleClosedPushforward D hp.1 Z.2.1 (D.isDecentSpace_of_isGood p hp) Z.2.2)
              (componentZeroCycleCoeff D (Z.1.ι ≫ p) hq (closedSubspaceRestrictSheaf D p hp L Z)
                (closedSubspaceRestrictSection D p hp L s Z) k Wz.1
                ((fun W => canonicalGeometricPoint D.site D.base D.base_mem
                  (componentVanishingLocus D (Z.1.ι ≫ p) hq
                    (closedSubspaceRestrictSheaf D p hp L Z)
                    (closedSubspaceRestrictSection D p hp L s Z) W.1).1.toFunctor) Wz)) V := by
      intro Wz
      rw [hcoeff Wz.1]
      by_cases hn : fundamentalCycleCoeff D (Z.1.ι ≫ p) hq (k + 1)
          (canonicalGeometricPoint D.site D.base D.base_mem Z.1.toFunctor) Wz.1 = 0
      · rw [hn, zero_mul, zero_mul]
      · have hne : (closedSubspaceCycle D p hp Z.1 Z.2 (k + 1) hZdim).1
            ((closedSubspaceComponentImage D p hp Z.1 Z.2) Wz.1) ≠ 0 := by
          rwa [hcoeff Wz.1]
        have hWdim :
            deltaDimension D p ((closedSubspaceComponentImage D p hp Z.1 Z.2) Wz.1) = k + 1 :=
          (deltaDimension_closedSubspaceComponentImage D p hp Z.1 Z.2 Wz.1).trans Wz.2.2
        have hWE : ¬ ((closedSubspaceComponentImage D p hp Z.1 Z.2) Wz.1).subspace ≤
            (vanishingLocus D p hp L s).1 := by
          rw [closedSubspaceCycle_coe] at hne
          exact not_le_vanishingLocus_of_cycleCoeffOfClosedSubspace_ne_zero D p hp L s (k + 1) Z
            hZdim hCartier _ ((closedSubspaceComponentImage D p hp Z.1 Z.2) Wz.1) hne
        rw [gysinComponentCycle_of_not_le D p (vanishingLocus D p hp L s) hE k
            (canonicalGysinComponentRule D p hp (vanishingLocus D p hp L s) hE k chern) hWdim hWE,
          canonicalGysinComponentRule_intersectionCycle, gysinIntersectionCycle_coe]
        exact congrArg _ (congrFun (cycleClosedPushforward_componentZeroCycleCoeff_eq D p hp L s k Z
          hL hE Wz.1).symm V)
    -- a subspace with a nonzero coefficient in `[Z]_{k+1}` comes from a component of `Z`
    have hsupp : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
        (closedSubspaceCycle D p hp Z.1 Z.2 (k + 1) hZdim).1 W *
            (cycleClosedPushforward D hp.1 (vanishingLocus D p hp L s).2.1
              (D.isDecentSpace_of_isGood p hp) (vanishingLocus D p hp L s).2.2)
              ((gysinComponentCycle D p (vanishingLocus D p hp L s) hE k
                (canonicalGysinComponentRule D p hp (vanishingLocus D p hp L s) hE k chern)
                W).1) V ≠ 0 →
          W ∈ Set.range
            (fun Wz : ComponentsOfDeltaDimension D (Z.1.ι ≫ p) hq (k + 1) =>
              (closedSubspaceComponentImage D p hp Z.1 Z.2) Wz.1) := by
      intro W hb
      have hn : (closedSubspaceCycle D p hp Z.1 Z.2 (k + 1) hZdim).1 W ≠ 0 :=
        fun h => hb (by rw [h, zero_mul])
      rw [closedSubspaceCycle_coe] at hn
      by_cases hex : ∃ Wz, (closedSubspaceComponentImage D p hp Z.1 Z.2) Wz = W
      · obtain ⟨Wz, rfl⟩ := hex
        have hdimX :
            deltaDimension D p ((closedSubspaceComponentImage D p hp Z.1 Z.2) Wz) = k + 1 := by
          by_contra hdne
          exact hn (cycleCoeffOfClosedSubspace_eq_zero_of_deltaDimension_ne D p hp Z.1 Z.2 (k + 1)
            _ _ hdne)
        exact ⟨⟨Wz, isIrreducibleComponent_of_cycleCoeffOfClosedSubspace_ne_zero D p hp Z (k + 1)
          hZdim _ Wz hn,
          ((deltaDimension_closedSubspaceComponentImage D p hp Z.1 Z.2 Wz).symm.trans hdimX)⟩, rfl⟩
      · exact absurd (cycleCoeffOfClosedSubspace_eq_zero D p hp Z.1 Z.2 (k + 1) _ W
          fun Wz h => hex ⟨Wz, h⟩) hn
    -- the two readings of `E ∩ Z`, and Stacks 0EQL on `Z`
    have h0 : vanishingLocus D (Z.1.ι ≫ p) hq (closedSubspaceRestrictSheaf D p hp L Z)
        (closedSubspaceRestrictSection D p hp L s Z) = interOnClosedSubspace D p hp L s Z :=
      (interOnClosedSubspace_eq_zeroScheme D p hp L s Z hL).symm
    have hZfam : cycleCoeffOfClosedSubspace D (Z.1.ι ≫ p) hq
          (interOnClosedSubspace D p hp L s Z).1 (interOnClosedSubspace D p hp L s Z).2 k
          (canonicalGeometricPoint D.site D.base D.base_mem
            (interOnClosedSubspace D p hp L s Z).1.toFunctor) =
        componentZeroCycleSumCoeff D (Z.1.ι ≫ p) hq (closedSubspaceRestrictSheaf D p hp L Z)
          (closedSubspaceRestrictSection D p hp L s Z) k
          (canonicalGeometricPoint D.site D.base D.base_mem Z.1.toFunctor)
          (fun W => canonicalGeometricPoint D.site D.base D.base_mem
            (componentVanishingLocus D (Z.1.ι ≫ p) hq (closedSubspaceRestrictSheaf D p hp L Z)
              (closedSubspaceRestrictSection D p hp L s Z) W.1).1.toFunctor) := by
      rw [← h0EQL]
      exact cycleCoeffOfClosedSubspace_eq_of_subfunctor_eq D (Z.1.ι ≫ p) hq k _ _
        (congrArg Subtype.val h0).symm
    rw [cycleClosedPushforward_interOnVanishingLocus_eq_cycleClosedPushforward_interOnClosedSubspace
      D p hp L s k Z, hZfam]
    unfold componentZeroCycleSumCoeff
    rw [cycleClosedPushforward_finsum_mul, cycleClosedPushforward_finsum_mul]
    refine Eq.trans (finsum_congr fun Wz => (hval Wz).symm) (Eq.trans
      (finsum_mem_range (f := (fun W : IntegralClosedSubspace D.site D.base D.base_mem X =>
          (closedSubspaceCycle D p hp Z.1 Z.2 (k + 1) hZdim).1 W *
            (cycleClosedPushforward D hp.1 (vanishingLocus D p hp L s).2.1
              (D.isDecentSpace_of_isGood p hp) (vanishingLocus D p hp L s).2.2)
              ((gysinComponentCycle D p (vanishingLocus D p hp L s) hE k
                (canonicalGysinComponentRule D p hp (vanishingLocus D p hp L s) hE k chern)
                W).1) V)) hginj).symm ?_)
    rw [finsum_mem_def, Set.indicator_eq_self.2 hsupp]
  have hT := congrFun hkey (closedSubspaceComponentImage D p hp (vanishingLocus D p hp L s).1
    (vanishingLocus D p hp L s).2 T)
  rwa [cycleClosedPushforward_apply_pushforward,
    cycleClosedPushforward_apply_pushforward] at hT


/-- **Stacks 0ER7.**  In Situation 0EDT let `X/B` be good and let `(ℒ, s, i : E → X)` be a triple
as in Definition 0ER1: `ℒ` invertible, `s` a global section of it and `E = Z(s)` its vanishing
locus.  Let `Z ⊆ X` be a closed subspace with `dim_δ(Z) ≤ k + 1` whose intersection `E ∩ Z` is an
effective Cartier divisor on `Z`.  Then

  `i^*([Z]_{k + 1}) = [E ∩ Z]_k`.

The left-hand side is the refined Gysin map of Stacks 0ER1 at the component rule
`AlgebraicGeometry.Space.canonicalGysinComponentRule`, so clause (1)(a) is the cycle
`[E ∩ W]_k` of Stacks 0EE9 that the source means and only clause (1)(b) — the cap product
`c₁(ℒ|_W) ∩ [W]` of Stacks 0EQJ — is the free parameter `chern` that Definition 0ER1 takes it to
be in this library.  The cycle `[Z]_{k+1}` is `AlgebraicGeometry.Space.closedSubspaceCycle`, which
is Stacks 0EE9 as an element of `Z_{k+1}(X)`, and the identity is stated coefficientwise so that
`[E ∩ Z]_k` needs no δ-dimension bound of its own: both sides are coefficient families on the
integral closed subspaces of `E`.

**Nothing of the source's proof is assumed.**  The first two sentences — that the hypothesis is
the regularity of `s|_Z` and that therefore `E ∩ Z = Z(s|_Z)` — are
`AlgebraicGeometry.Space.isEffectiveCartierDivisor_interOnClosedSubspace_iff_isRegularSection` and
`AlgebraicGeometry.Space.interOnClosedSubspace_eq_zeroScheme`; Lemma 0EQL for `(Z, ℒ|_Z, s|_Z)` is
`AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace_zeroScheme_eq_componentZeroCycleSumCoeff`,
transported to the ambient `X` by
`AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace_interOnVanishingLocus_eq_finsum`; the
non-containment `Z_i ⊄ E` is
`AlgebraicGeometry.Space.not_le_vanishingLocus_of_cycleCoeffOfClosedSubspace_ne_zero`; and the
final matching against the definition of the Gysin map is
`AlgebraicGeometry.Space.gysinComponentCycle_of_not_le`. -/
@[stacks 0ER7 "i^*([Z]_{k+1}) = [D ∩ Z]_k for a closed subspace Z with dim_δ(Z) ≤ k+1 whose
intersection with D is an effective Cartier divisor on Z, stated coefficientwise on the integral
closed subspaces of D so that no δ-dimension bound on D ∩ Z is needed; the Gysin map is the one
of Stacks 0ER1 at canonicalGysinComponentRule, so clause (1)(a) is the cycle [D ∩ W]_k of
Stacks 0EE9 and only clause (1)(b), the cap product of Stacks 0EQJ, is the free parameter chern
that Definition 0ER1 takes it to be here; Stacks 0EQL for (Z, s|_Z) and the non-containment of
the components of Z in D are proved, not assumed"]
theorem gysinCycleMap_closedSubspaceCycle_coe_eq
    (hL : IsInvertibleSheaf D p hp L)
    (chern : FirstChernComponentCycleRule D p k)
    (hZdim : deltaDimensionSubspace D p hp Z.1 Z.2 ≤ ((k + 1 : ℤ) : EInt))
    (hCartier : IsEffectiveCartierDivisor D.site D.base D.base_mem ⟨Z.1.toFunctor, Z.2.1⟩
      (interOnClosedSubspace D p hp L s Z)) :
    (gysinCycleMap D p (vanishingLocus D p hp L s) (isGood_vanishingLocus D p hp L s) k
        (canonicalGysinComponentRule D p hp (vanishingLocus D p hp L s)
          (isGood_vanishingLocus D p hp L s) k chern)
        (closedSubspaceCycle D p hp Z.1 Z.2 (k + 1) hZdim)).1 =
      cycleCoeffOfClosedSubspace D ((vanishingLocus D p hp L s).1.ι ≫ p)
        (isGood_vanishingLocus D p hp L s)
        (interOnVanishingLocus D p hp L s Z).1 (interOnVanishingLocus D p hp L s Z).2 k
        (canonicalGeometricPoint D.site D.base D.base_mem
          (interOnVanishingLocus D p hp L s Z).1.toFunctor) := by
  funext T
  rw [gysinCycleMap_apply]
  exact (cycleCoeffOfClosedSubspace_interOnVanishingLocus_eq_finsum D p hp L s k Z hL
    (isGood_vanishingLocus D p hp L s) chern hZdim hCartier T).symm

/-- **Stacks 0ER7, as an equality of cycles.**  In Situation 0EDT let `X/B` be good and let
`(ℒ, s, i : E → X)` be a triple as in Definition 0ER1.  Let `Z ⊆ X` be a closed subspace with
`dim_δ(Z) ≤ k + 1` whose intersection `E ∩ Z` is an effective Cartier divisor on `Z`.  Then

  `i^*([Z]_{k + 1}) = [E ∩ Z]_k`

in `Z_k(E)`, for the refined Gysin map of Stacks 0ER1 at the component rule
`AlgebraicGeometry.Space.canonicalGysinComponentRule`.

This is `AlgebraicGeometry.Space.gysinCycleMap_closedSubspaceCycle_coe_eq` read as an equality of
cycles rather than of coefficient families.  The two cycles are the elements `α` of `Z_{k+1}(X)`
and `β` of `Z_k(E)` whose coefficient families `hα` and `hβ` pin to those of Stacks 0EE9 — on the
left `[Z]_{k+1}`, on the right `[E ∩ Z]_k` for the intersection read inside `E`.  For the left
one that is no restriction, `α` being forced to be
`AlgebraicGeometry.Space.closedSubspaceCycle`; supplying the right one takes the place of the
bound `dim_δ(E ∩ Z) ≤ k`, which the source gets from the effective Cartier hypothesis and which
has no declaration in this library.  Nothing weakens: both are the coefficient families the
source's two cycles have.

This is the shape in which
`AlgebraicGeometry.Space.gysinCycleMap_eq_of_cycleCoeffOfClosedSubspace` states the identity at an
arbitrary component rule, where clause 0ER1(1)(a) is free data; here the rule is the canonical one
of Stacks 0ER1, so that clause is the cycle `[E ∩ W]_k` of Stacks 0EE9 and the two inputs that
lemma takes for it — Stacks 0EQL for `(Z, ℒ|_Z, s|_Z)` and the non-containment `Z_i ⊄ E` — are
`AlgebraicGeometry.Space.cycleCoeffOfClosedSubspace_interOnVanishingLocus_eq_finsum` and
`AlgebraicGeometry.Space.not_le_vanishingLocus_of_cycleCoeffOfClosedSubspace_ne_zero`. -/
@[stacks 0ER7 "i^*([Z]_{k+1}) = [D ∩ Z]_k as an equality in Z_k(D), for a closed subspace Z with
dim_δ(Z) ≤ k+1 whose intersection with D is an effective Cartier divisor on Z; the Gysin map is
the one of Stacks 0ER1 at canonicalGysinComponentRule, so clause (1)(a) is the cycle [D ∩ W]_k of
Stacks 0EE9 and only clause (1)(b), the cap product of Stacks 0EQJ, is the free parameter chern
that Definition 0ER1 takes it to be here; the two cycles are elements α and β of the cycle groups
whose coefficient families hα and hβ pin to Stacks 0EE9, which replaces the δ-dimension bound on
D ∩ Z; Stacks 0EQL for (Z, s|_Z) and the non-containment of the components of Z in D are proved,
not assumed"]
theorem gysinCycleMap_canonical_eq_of_cycleCoeffOfClosedSubspace
    (hL : IsInvertibleSheaf D p hp L)
    (chern : FirstChernComponentCycleRule D p k)
    (hZdim : deltaDimensionSubspace D p hp Z.1 Z.2 ≤ ((k + 1 : ℤ) : EInt))
    (hCartier : IsEffectiveCartierDivisor D.site D.base D.base_mem ⟨Z.1.toFunctor, Z.2.1⟩
      (interOnClosedSubspace D p hp L s Z))
    (α : CycleGroup D p (k + 1))
    (hα : α.1 = cycleCoeffOfClosedSubspace D p hp Z.1 Z.2 (k + 1)
      (canonicalGeometricPoint D.site D.base D.base_mem Z.1.toFunctor))
    (β : CycleGroup D ((vanishingLocus D p hp L s).1.ι ≫ p) k)
    (hβ : β.1 = cycleCoeffOfClosedSubspace D ((vanishingLocus D p hp L s).1.ι ≫ p)
      (isGood_vanishingLocus D p hp L s)
      (interOnVanishingLocus D p hp L s Z).1 (interOnVanishingLocus D p hp L s Z).2 k
      (canonicalGeometricPoint D.site D.base D.base_mem
        (interOnVanishingLocus D p hp L s Z).1.toFunctor)) :
    gysinCycleMap D p (vanishingLocus D p hp L s) (isGood_vanishingLocus D p hp L s) k
        (canonicalGysinComponentRule D p hp (vanishingLocus D p hp L s)
          (isGood_vanishingLocus D p hp L s) k chern) α = β := by
  obtain rfl : α = closedSubspaceCycle D p hp Z.1 Z.2 (k + 1) hZdim :=
    Subtype.ext (hα.trans (closedSubspaceCycle_coe D p hp Z.1 Z.2 (k + 1) hZdim).symm)
  exact Subtype.ext ((gysinCycleMap_closedSubspaceCycle_coe_eq D p hp L s k Z hL chern hZdim
    hCartier).trans hβ.symm)

end Additivity


end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinClosedSubspaceIntersectionAdditivity
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroSchemeFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroSchemeMaximality

/-!
# The pushforward to `X` of the refined Gysin map of Stacks 0ER1

In Situation 0EDT let `X/B` be good, let `ℒ` be an invertible `𝒪_X`-module with a global section
`s` and let `i : E → X` be the closed immersion of the vanishing locus `E = Z(s)` of
Stacks 0845.  Stacks 0ER1 defines `i^* : Z_{k+1}(X) ⟶ Z_k(E)` by the dichotomy

* `[E ∩ W]_k` on `E`, for an integral closed subspace `W ⊆ X` of δ-dimension `k + 1` with
  `W ⊄ E`, and
* `i'_*(c₁(ℒ|_W) ∩ [W])`, for `W ⊆ E`,

extended additively.  This file computes the pushforward `i_*(i^* α)` to `X`.

The answer is that `i_*(i^* -)` is a sum of exactly the shape of the cap product of Stacks 0EQJ —
`∑_W α(W) (W → X)_* c_W` — whose component `c_W` on `W` is the cycle `[E ∩ W]_k` **read on `W`**,
that is the cycle of the zero scheme `Z(s|_W)` of Stacks 0EQL, when `W ⊄ E`, and the component
cycle `c₁(ℒ|_W) ∩ [W]` of Stacks 0EQJ when `W ⊆ E`.  The Gysin map forms the cycle of `E ∩ W` on
`E`; the two readings are identified by
`cycleClosedPushforward_interOnVanishingLocus_eq_cycleClosedPushforward_interOnClosedSubspace`.

## Main definitions

* `AlgebraicGeometry.Space.gysinPushforwardComponentCoeff`: the coefficient family on `X` of the
  component `(W → X)_* c_W`, by the dichotomy above.
* `AlgebraicGeometry.Space.firstChernCapPushforwardComponentCoeff`: the same for the cap product
  of Stacks 0EQJ formed on a closed subspace `E ⊆ X`, whose component at an integral closed
  subspace `T ⊆ E` is pushed forward along the composite `T → E → X`.

## Main results

* `AlgebraicGeometry.Space.cycleClosedPushforward_containedPushforward_eq`: for `W ⊆ E` the
  pushforward along `W → E → X` is the pushforward along `W → X`; this is the clause (1)(b) half.
* `AlgebraicGeometry.Space.cycleClosedPushforward_gysinIntersectionCycle_eq`: for `W ⊄ E` the
  pushforward to `X` of `[E ∩ W]_k` formed on `E` is the pushforward to `X` of the cycle of
  `E ∩ W` formed on `W`; this is the clause (1)(a) half.
* `AlgebraicGeometry.Space.top_le_zeroSchemeSubfunctor_zero`: the zero scheme of the zero section
  is the whole space.
* `AlgebraicGeometry.Space.closedSubspaceRestrictSection_ne_zero`: **`s|_Z ≠ 0` for a closed
  subspace `Z ⊄ Z(s)`**.
* `AlgebraicGeometry.Space.cycleClosedPushforward_gysinComponentCycle_eq`: the pushforward to `X`
  of the component cycle of Stacks 0ER1(1) is the component of the dichotomy above.
* `AlgebraicGeometry.Space.cycleClosedPushforward_gysinCycleMap_eq_finsum`: **the pushforward to
  `X` of the refined Gysin map of Stacks 0ER1 is the cap-product-shaped sum
  `∑_W α(W) (W → X)_* c_W`.**
* `AlgebraicGeometry.Space.gysinPushforwardComponentCoeff_of_not_le_eq_zeroScheme`: the component
  at `W ⊄ E` is the cycle of the zero scheme `Z(s|_W)` of the restricted section, when `ℒ` is
  invertible.
* `AlgebraicGeometry.Space.gysinPushforwardComponentCoeff_of_not_le_eq_sectionWeilDivisor`:
  **that component is the Weil divisor `div_{ℒ|_W}(s|_W)`**, by Stacks 0EQF for the triple
  `(W, ℒ|_W, s|_W)`.
* `AlgebraicGeometry.Space.cycleClosedPushforward_firstChernComponentCycle_eq` and
  `AlgebraicGeometry.Space.cycleClosedPushforward_firstChernCapCycleMap_eq_finsum`: the same
  computation for the cap product of Stacks 0EQJ formed on `E`.

## Implementation notes

Everything is stated at the level of coefficient families rather than of elements of `Z_k(X)`.
Forming `[E ∩ W]_k` on `W` as an element of `Z_k(W)` would ask in addition for the δ-dimension
bound `dim_δ(Z(s|_W)) ≤ k` on `W`, which the coefficient family does not need and which is a
property of `(ℒ, s, W)` rather than of the comparison; this is the same choice that
`AlgebraicGeometry.Space.gysinCycleMap_closedSubspaceCycle_coe_eq` (Stacks 0ER7) makes.

Clause (1)(b) stays the free parameter `chern` of Stacks 0EQJ that Definition 0ER1 takes it to be
in this library, exactly as in Stacks 0ER7; the identification of `c₁(ℒ|_W) ∩ [W]` with the Weil
divisor `div_{ℒ|_W}(s_W)` of a meromorphic section is the separate instantiation
`AlgebraicGeometry.Space.componentDivisorCycleRule`.

## References

* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0ER9](https://stacks.math.columbia.edu/tag/0ER9)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EQL](https://stacks.math.columbia.edu/tag/0EQL)
* [Stacks Project, Tag 0EQV](https://stacks.math.columbia.edu/tag/0EQV)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0845](https://stacks.math.columbia.edu/tag/0845)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] Classical.propDecidable

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p)

/-- Pushing forward a weighted sum of cycles termwise: if each cycle pushes forward to `d j`, the
sum pushes forward to the weighted sum of the `d j`. -/
private theorem cycleClosedPushforward_finsum_mul_eq_of_forall
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (hY : IsAlgebraicSpace D.site D.base D.base_mem Y)
    (hXdec : IsDecentSpace D.site D.base D.base_mem X) {i : Y ⟶ X}
    (hi : IsClosedImmersion D.site D.base D.base_mem i) {ι : Type*} (a : ι → ℤ)
    (c : ι → IntegralClosedSubspace D.site D.base D.base_mem Y → ℤ)
    (d : ι → IntegralClosedSubspace D.site D.base D.base_mem X → ℤ)
    (hcd : ∀ j, cycleClosedPushforward D hX hY hXdec hi (c j) = d j)
    (V : IntegralClosedSubspace D.site D.base D.base_mem X) :
    cycleClosedPushforward D hX hY hXdec hi (fun T => ∑ᶠ j : ι, a j * c j T) V =
      ∑ᶠ j : ι, a j * d j V := by
  rw [cycleClosedPushforward_finsum_mul]
  exact finsum_congr fun j => by rw [hcd j]

/-! ### Clause (1)(b): the pushforward along `W → E → X` -/

/-- **The pushforward along `W → E` followed by the pushforward along `i : E → X` is the
pushforward along `W → X`.**  This is the clause (1)(b) half of the computation below: the
`i'_*` of Stacks 0ER1(1)(b) composed with `i_*` is the pushforward
`AlgebraicGeometry.Space.integralClosedSubspacePushforward` of Stacks 0EQJ along `W → X`.

The inclusion `W → E` followed by the inclusion of `E` is the inclusion of `W`, so this is
`AlgebraicGeometry.Space.cycleClosedPushforward_comp` together with
`AlgebraicGeometry.Space.cycleClosedPushforward_congr`. -/
theorem cycleClosedPushforward_containedPushforward_eq
    (E : ClosedSubspaces D.site D.base D.base_mem X) (hE : D.IsGood (E.1.ι ≫ p)) (k : ℤ)
    {W : IntegralClosedSubspace D.site D.base D.base_mem X} (hWE : W.subspace ≤ E.1)
    (c : CycleGroup D (W.subspace.ι ≫ p) k) :
    cycleClosedPushforward D hp.1 E.2.1 (D.isDecentSpace_of_isGood p hp) E.2.2
        (containedPushforward D p E hE k hWE c).1 =
      (integralClosedSubspacePushforward D p hp W k c).1 :=
  (cycleClosedPushforward_comp D hp.1 E.2.1 W.isClosedSubspace.1
    (D.isDecentSpace_of_isGood p hp) (D.isDecentSpace_of_isGood (E.1.ι ≫ p) hE)
    (isClosedImmersion_homOfLe_of_le D E hWE) E.2.2 c.1).symm.trans
    (cycleClosedPushforward_congr D hp.1 W.isClosedSubspace.1 (D.isDecentSpace_of_isGood p hp) _
      W.isClosedSubspace.2 (Subfunctor.homOfLe_ι hWE) c.1)

/-! ### Clause (1)(a): the two readings of `E ∩ W` -/

section Intersection

variable (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections) (k : ℤ)

/-- **For `W ⊄ E` the pushforward to `X` of `[E ∩ W]_k` formed on `E` is the pushforward to `X`
of the cycle of `E ∩ W` formed on `W`.**  Clause (1)(a) of Stacks 0ER1 forms the cycle of the
intersection inside `E`; the two agree because the cycle of a closed subspace does not depend on
the ambient space. -/
theorem cycleClosedPushforward_gysinIntersectionCycle_eq
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D p W = k + 1) (hWE : ¬ W.subspace ≤ (vanishingLocus D p hp L s).1) :
    cycleClosedPushforward D hp.1 (vanishingLocus D p hp L s).2.1
        (D.isDecentSpace_of_isGood p hp) (vanishingLocus D p hp L s).2.2
        (gysinIntersectionCycle D p hp (vanishingLocus D p hp L s)
          (isGood_vanishingLocus D p hp L s) k W hW hWE).1 =
      cycleClosedPushforward D hp.1 W.isClosedSubspace.1 (D.isDecentSpace_of_isGood p hp)
        W.isClosedSubspace.2
        (cycleCoeffOfClosedSubspace D (W.subspace.ι ≫ p)
          (isGood_closedSubspace D p hp ⟨W.subspace, W.isClosedSubspace⟩)
          (interOnClosedSubspace D p hp L s ⟨W.subspace, W.isClosedSubspace⟩).1
          (interOnClosedSubspace D p hp L s ⟨W.subspace, W.isClosedSubspace⟩).2 k
          (canonicalGeometricPoint D.site D.base D.base_mem
            (interOnClosedSubspace D p hp L s ⟨W.subspace, W.isClosedSubspace⟩).1.toFunctor)) :=
  cycleClosedPushforward_interOnVanishingLocus_eq_cycleClosedPushforward_interOnClosedSubspace
    D p hp L s k ⟨W.subspace, W.isClosedSubspace⟩

end Intersection

/-! ### The restriction of the section to a subspace not contained in the vanishing locus -/

section Nonvanishing

/-- **The zero scheme of the zero section is the whole space.**  By the maximality half of
Stacks 0846 (1) it suffices that the evaluation ideal of the zero section is the zero ideal on
every affine étale chart, which is
`AlgebraicGeometry.Space.sectionEvaluationIdealAt_eq_bot`. -/
theorem top_le_zeroSchemeSubfunctor_zero (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (Y : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (⊤ : Subfunctor Y.1) ≤ zeroSchemeSubfunctor B S hS Y M 0 := by
  refine le_zeroSchemeSubfunctor B S hS Y M 0
    ⟨⊤, isClosedSubspace_top_subfunctor B S hS Y.2⟩ fun U hU => ?_
  rw [sectionEvaluationIdealAt_eq_bot B S hS Y M 0 (fun _ => rfl) U]
  exact bot_le

/-- **The restriction `s|_Z` of a global section of an invertible sheaf to a closed subspace
`Z ⊄ Z(s)` is nonzero.**  The intersection `Z(s) ∩ Z` read on `Z` is the vanishing locus of
`s|_Z` (`AlgebraicGeometry.Space.interOnClosedSubspace_eq_zeroScheme`); were `s|_Z` zero that
vanishing locus would be all of `Z`, and the inverse image of `Z(s)` along `Z → X` is all of `Z`
exactly when `Z ⊆ Z(s)`. -/
theorem closedSubspaceRestrictSection_ne_zero
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections)
    (hL : IsInvertibleSheaf D p hp L) (Z : ClosedSubspaces D.site D.base D.base_mem X)
    (hZ : ¬ Z.1 ≤ (vanishingLocus D p hp L s).1) :
    closedSubspaceRestrictSection D p hp L s Z ≠ 0 := by
  intro h0
  refine hZ ?_
  have h1 : (vanishingLocus D p hp L s).1.preimage Z.1.ι =
      zeroSchemeSubfunctor D.site D.base D.base_mem
        (closedSubspaceToSpace D.site D.base D.base_mem ⟨X, hp.1⟩ Z)
        (closedSubspaceRestrictSheaf D p hp L Z)
        (closedSubspaceRestrictSection D p hp L s Z) :=
    congrArg Subtype.val (interOnClosedSubspace_eq_zeroScheme D p hp L s Z hL)
  rw [h0] at h1
  have htop : (vanishingLocus D p hp L s).1.preimage Z.1.ι = ⊤ :=
    h1.trans (eq_top_iff.2 (top_le_zeroSchemeSubfunctor_zero D.site D.base D.base_mem
      (closedSubspaceToSpace D.site D.base D.base_mem ⟨X, hp.1⟩ Z)
      (closedSubspaceRestrictSheaf D p hp L Z)))
  have hrange := (Subfunctor.preimage_eq_top_iff (vanishingLocus D p hp L s).1 Z.1.ι).1 htop
  rwa [Subfunctor.range_ι] at hrange

end Nonvanishing

/-! ### The component of the pushed-forward Gysin map -/

section Components

variable (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (s : L.sections) (k : ℤ)
    (chern : FirstChernComponentCycleRule D p k)

/-- **The component on `X` of the pushed-forward refined Gysin map.**  For an integral closed
subspace `W ⊆ X` of δ-dimension `k + 1` this is the coefficient family on `X` of
`(W → X)_* c_W`, where `c_W` is the cycle `c₁(ℒ|_W) ∩ [W]` of Stacks 0EQJ when `W ⊆ E` and the
cycle of the intersection `E ∩ W` read on `W` when `W ⊄ E`; at a subspace of any other
δ-dimension it is zero, such a subspace not occurring in a `(k+1)`-cycle.

This is the dichotomy of Stacks 0ER1(1) with clause (1)(a) transported from `E` to `W`. -/
def gysinPushforwardComponentCoeff
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    IntegralClosedSubspace D.site D.base D.base_mem X → ℤ :=
  if hW : deltaDimension D p W = k + 1 then
    if W.subspace ≤ (vanishingLocus D p hp L s).1 then
      (integralClosedSubspacePushforward D p hp W k (chern W hW)).1
    else
      cycleClosedPushforward D hp.1 W.isClosedSubspace.1 (D.isDecentSpace_of_isGood p hp)
        W.isClosedSubspace.2
        (cycleCoeffOfClosedSubspace D (W.subspace.ι ≫ p)
          (isGood_closedSubspace D p hp ⟨W.subspace, W.isClosedSubspace⟩)
          (interOnClosedSubspace D p hp L s ⟨W.subspace, W.isClosedSubspace⟩).1
          (interOnClosedSubspace D p hp L s ⟨W.subspace, W.isClosedSubspace⟩).2 k
          (canonicalGeometricPoint D.site D.base D.base_mem
            (interOnClosedSubspace D p hp L s ⟨W.subspace, W.isClosedSubspace⟩).1.toFunctor))
  else 0

/-- For `W ⊆ E` of δ-dimension `k + 1` the component is `(W → X)_*(c₁(ℒ|_W) ∩ [W])`. -/
theorem gysinPushforwardComponentCoeff_of_le
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D p W = k + 1)
    (hWE : W.subspace ≤ (vanishingLocus D p hp L s).1) :
    gysinPushforwardComponentCoeff D p hp L s k chern W =
      (integralClosedSubspacePushforward D p hp W k (chern W hW)).1 := by
  rw [gysinPushforwardComponentCoeff, dite_eq_left hW, if_pos hWE]

/-- For `W ⊄ E` of δ-dimension `k + 1` the component is the pushforward to `X` of the cycle of
`E ∩ W` formed on `W`. -/
theorem gysinPushforwardComponentCoeff_of_not_le
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D p W = k + 1)
    (hWE : ¬ W.subspace ≤ (vanishingLocus D p hp L s).1) :
    gysinPushforwardComponentCoeff D p hp L s k chern W =
      cycleClosedPushforward D hp.1 W.isClosedSubspace.1 (D.isDecentSpace_of_isGood p hp)
        W.isClosedSubspace.2
        (cycleCoeffOfClosedSubspace D (W.subspace.ι ≫ p)
          (isGood_closedSubspace D p hp ⟨W.subspace, W.isClosedSubspace⟩)
          (interOnClosedSubspace D p hp L s ⟨W.subspace, W.isClosedSubspace⟩).1
          (interOnClosedSubspace D p hp L s ⟨W.subspace, W.isClosedSubspace⟩).2 k
          (canonicalGeometricPoint D.site D.base D.base_mem
            (interOnClosedSubspace D p hp L s ⟨W.subspace, W.isClosedSubspace⟩).1.toFunctor)) := by
  rw [gysinPushforwardComponentCoeff, dite_eq_left hW, if_neg hWE]

/-- At a subspace of δ-dimension other than `k + 1` the component is zero. -/
theorem gysinPushforwardComponentCoeff_of_deltaDimension_ne
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D p W ≠ k + 1) :
    gysinPushforwardComponentCoeff D p hp L s k chern W = 0 := by
  rw [gysinPushforwardComponentCoeff, dite_eq_right hW]

/-- **The component at `W ⊄ E` is the cycle of the zero scheme `Z(s|_W)` of the restricted
section**, when `ℒ` is invertible.  The intersection `E ∩ W` read on `W` is the vanishing locus
of `s|_W` on `W`, by `AlgebraicGeometry.Space.interOnClosedSubspace_eq_zeroScheme`. -/
theorem gysinPushforwardComponentCoeff_of_not_le_eq_zeroScheme
    (hL : IsInvertibleSheaf D p hp L)
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D p W = k + 1)
    (hWE : ¬ W.subspace ≤ (vanishingLocus D p hp L s).1) :
    gysinPushforwardComponentCoeff D p hp L s k chern W =
      cycleClosedPushforward D hp.1 W.isClosedSubspace.1 (D.isDecentSpace_of_isGood p hp)
        W.isClosedSubspace.2
        (cycleCoeffOfClosedSubspace D (W.subspace.ι ≫ p)
          (isGood_closedSubspace D p hp ⟨W.subspace, W.isClosedSubspace⟩)
          (vanishingLocus D (W.subspace.ι ≫ p)
            (isGood_closedSubspace D p hp ⟨W.subspace, W.isClosedSubspace⟩)
            (closedSubspaceRestrictSheaf D p hp L ⟨W.subspace, W.isClosedSubspace⟩)
            (closedSubspaceRestrictSection D p hp L s ⟨W.subspace, W.isClosedSubspace⟩)).1
          (vanishingLocus D (W.subspace.ι ≫ p)
            (isGood_closedSubspace D p hp ⟨W.subspace, W.isClosedSubspace⟩)
            (closedSubspaceRestrictSheaf D p hp L ⟨W.subspace, W.isClosedSubspace⟩)
            (closedSubspaceRestrictSection D p hp L s ⟨W.subspace, W.isClosedSubspace⟩)).2 k
          (canonicalGeometricPoint D.site D.base D.base_mem
            (vanishingLocus D (W.subspace.ι ≫ p)
              (isGood_closedSubspace D p hp ⟨W.subspace, W.isClosedSubspace⟩)
              (closedSubspaceRestrictSheaf D p hp L ⟨W.subspace, W.isClosedSubspace⟩)
              (closedSubspaceRestrictSection D p hp L s
                ⟨W.subspace, W.isClosedSubspace⟩)).1.toFunctor)) := by
  rw [gysinPushforwardComponentCoeff_of_not_le D p hp L s k chern hW hWE]
  exact congrArg _ <| cycleCoeffOfClosedSubspace_eq_of_subfunctor_eq D (W.subspace.ι ≫ p)
    (isGood_closedSubspace D p hp ⟨W.subspace, W.isClosedSubspace⟩) k _ _
    (congrArg Subtype.val
      (interOnClosedSubspace_eq_zeroScheme D p hp L s ⟨W.subspace, W.isClosedSubspace⟩ hL))

/-- **The component at `W ⊄ E` is the Weil divisor `div_{ℒ|_W}(s|_W)`, pushed forward to `X`**,
when `ℒ` is invertible.  This is Stacks 0EQF for the triple `(W, ℒ|_W, s|_W)`:

  `div_{ℒ|_W}(s|_W) = [Z(s|_W)]_k = [E ∩ W]_k`,

where `W` is integral and good over the base, `ℒ|_W` is invertible by Stacks 0B8P, the
δ-dimension of `W` computed on `W` is `k + 1`, and `s|_W ≠ 0` by
`AlgebraicGeometry.Space.closedSubspaceRestrictSection_ne_zero`. -/
theorem gysinPushforwardComponentCoeff_of_not_le_eq_sectionWeilDivisor
    (hL : IsInvertibleSheaf D p hp L)
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hW : deltaDimension D p W = k + 1)
    (hWE : ¬ W.subspace ≤ (vanishingLocus D p hp L s).1) :
    gysinPushforwardComponentCoeff D p hp L s k chern W =
      cycleClosedPushforward D hp.1 W.isClosedSubspace.1 (D.isDecentSpace_of_isGood p hp)
        W.isClosedSubspace.2
        (sectionWeilDivisor D (W.subspace.ι ≫ p)
          (isGood_closedSubspace D p hp ⟨W.subspace, W.isClosedSubspace⟩) W.isIntegralSpace
          (closedSubspaceRestrictSheaf D p hp L ⟨W.subspace, W.isClosedSubspace⟩)
          (isInvertible_closedSubspaceRestrictSheaf D p hp L
            ⟨W.subspace, W.isClosedSubspace⟩ hL)
          ((deltaDimensionClosed_univ_integralClosedSubspace D p hp W).trans
            (congrArg (fun m : ℤ => (m : EInt)) hW))
          (globalSectionMeromorphic D.site D.base D.base_mem W.isClosedSubspace.1
            (closedSubspaceRestrictSheaf D p hp L ⟨W.subspace, W.isClosedSubspace⟩)
            (closedSubspaceRestrictSection D p hp L s ⟨W.subspace, W.isClosedSubspace⟩))
          (globalSectionMeromorphic_ne_zero_of_isInvertibleSheaf D (W.subspace.ι ≫ p)
            (isGood_closedSubspace D p hp ⟨W.subspace, W.isClosedSubspace⟩)
            (closedSubspaceRestrictSheaf D p hp L ⟨W.subspace, W.isClosedSubspace⟩)
            (isInvertible_closedSubspaceRestrictSheaf D p hp L
              ⟨W.subspace, W.isClosedSubspace⟩ hL)
            (closedSubspaceRestrictSection_ne_zero D p hp L s hL
              ⟨W.subspace, W.isClosedSubspace⟩ hWE))).1 := by
  have harith : k + 1 - 1 = k := by ring
  have h0EQF := congrArg Subtype.val
    (sectionWeilDivisor_eq_zeroSchemeCycle_and_weilDivisorOfInvertibleSheaf_eq.{u, u} D
      (W.subspace.ι ≫ p) (isGood_closedSubspace D p hp ⟨W.subspace, W.isClosedSubspace⟩)
      W.isIntegralSpace (closedSubspaceRestrictSheaf D p hp L ⟨W.subspace, W.isClosedSubspace⟩)
      (isInvertible_closedSubspaceRestrictSheaf D p hp L ⟨W.subspace, W.isClosedSubspace⟩ hL)
      ((deltaDimensionClosed_univ_integralClosedSubspace D p hp W).trans
        (congrArg (fun m : ℤ => (m : EInt)) hW))
      (closedSubspaceRestrictSection_ne_zero D p hp L s hL
        ⟨W.subspace, W.isClosedSubspace⟩ hWE)).1
  rw [zeroSchemeCycle_coe] at h0EQF
  conv at h0EQF => rhs; rw [harith]
  rw [gysinPushforwardComponentCoeff_of_not_le_eq_zeroScheme D p hp L s k chern hL hW hWE]
  exact congrArg _ h0EQF.symm

/-- **The pushforward to `X` of the component cycle of Stacks 0ER1(1).**  For every integral
closed subspace `W ⊆ X` the pushforward along `i : E → X` of the component cycle of the refined
Gysin map at the component rule `AlgebraicGeometry.Space.canonicalGysinComponentRule` is the
component `AlgebraicGeometry.Space.gysinPushforwardComponentCoeff`. -/
theorem cycleClosedPushforward_gysinComponentCycle_eq
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    cycleClosedPushforward D hp.1 (vanishingLocus D p hp L s).2.1
        (D.isDecentSpace_of_isGood p hp) (vanishingLocus D p hp L s).2.2
        (gysinComponentCycle D p (vanishingLocus D p hp L s)
          (isGood_vanishingLocus D p hp L s) k
          (canonicalGysinComponentRule D p hp (vanishingLocus D p hp L s)
            (isGood_vanishingLocus D p hp L s) k chern) W).1 =
      gysinPushforwardComponentCoeff D p hp L s k chern W := by
  by_cases hW : deltaDimension D p W = k + 1
  · by_cases hWE : W.subspace ≤ (vanishingLocus D p hp L s).1
    · rw [gysinComponentCycle_of_le D p (vanishingLocus D p hp L s)
        (isGood_vanishingLocus D p hp L s) k _ hW hWE,
        canonicalGysinComponentRule_chernCycle,
        gysinPushforwardComponentCoeff_of_le D p hp L s k chern hW hWE]
      exact cycleClosedPushforward_containedPushforward_eq D p hp
        (vanishingLocus D p hp L s) (isGood_vanishingLocus D p hp L s) k hWE (chern W hW)
    · rw [gysinComponentCycle_of_not_le D p (vanishingLocus D p hp L s)
        (isGood_vanishingLocus D p hp L s) k _ hW hWE,
        canonicalGysinComponentRule_intersectionCycle,
        gysinPushforwardComponentCoeff_of_not_le D p hp L s k chern hW hWE]
      exact cycleClosedPushforward_gysinIntersectionCycle_eq D p hp L s k hW hWE
  · rw [gysinComponentCycle_of_deltaDimension_ne D p (vanishingLocus D p hp L s)
      (isGood_vanishingLocus D p hp L s) k _ hW,
      gysinPushforwardComponentCoeff_of_deltaDimension_ne D p hp L s k chern hW]
    exact cycleClosedPushforward_zero D hp.1 (vanishingLocus D p hp L s).2.1
      (D.isDecentSpace_of_isGood p hp) (vanishingLocus D p hp L s).2.2

/-- **The pushforward to `X` of the refined Gysin map of Stacks 0ER1.**  For a `(k+1)`-cycle `α`
on `X`,

  `i_*(i^* α) = ∑_W α(W) (W → X)_* c_W`,

the sum over all integral closed subspaces `W ⊆ X`, with `c_W` the component of
`AlgebraicGeometry.Space.gysinPushforwardComponentCoeff`: the cycle of `E ∩ W` read on `W` when
`W ⊄ E`, and the component cycle `c₁(ℒ|_W) ∩ [W]` of Stacks 0EQJ when `W ⊆ E`.  The right-hand
side has the shape of the cap product of Stacks 0EQJ. -/
theorem cycleClosedPushforward_gysinCycleMap_eq_finsum (α : CycleGroup D p (k + 1))
    (V : IntegralClosedSubspace D.site D.base D.base_mem X) :
    cycleClosedPushforward D hp.1 (vanishingLocus D p hp L s).2.1
        (D.isDecentSpace_of_isGood p hp) (vanishingLocus D p hp L s).2.2
        (gysinCycleMap D p (vanishingLocus D p hp L s) (isGood_vanishingLocus D p hp L s) k
          (canonicalGysinComponentRule D p hp (vanishingLocus D p hp L s)
            (isGood_vanishingLocus D p hp L s) k chern) α).1 V =
      ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem X,
        α.1 W * gysinPushforwardComponentCoeff D p hp L s k chern W V := by
  exact cycleClosedPushforward_finsum_mul_eq_of_forall D hp.1 (vanishingLocus D p hp L s).2.1
    (D.isDecentSpace_of_isGood p hp) (vanishingLocus D p hp L s).2.2 (fun W => α.1 W)
    (fun W T => (gysinComponentCycle D p (vanishingLocus D p hp L s)
      (isGood_vanishingLocus D p hp L s) k
      (canonicalGysinComponentRule D p hp (vanishingLocus D p hp L s)
        (isGood_vanishingLocus D p hp L s) k chern) W).1 T)
    (fun W => gysinPushforwardComponentCoeff D p hp L s k chern W)
    (cycleClosedPushforward_gysinComponentCycle_eq D p hp L s k chern) V

end Components

/-! ### The pushforward to `X` of the cap product of Stacks 0EQJ on a closed subspace

The cap product of Stacks 0EQJ formed on a closed subspace `E ⊆ X`, pushed forward to `X`, is a
weighted sum of pushforwards to `X` of the component cycles, the pushforward being along the
composite `T → E → X` for `T ⊆ E` an integral closed subspace. -/

section CapPushforward

variable (E : ClosedSubspaces D.site D.base D.base_mem X) (hE : D.IsGood (E.1.ι ≫ p)) (k : ℤ)
    (chernE : FirstChernComponentCycleRule D (E.1.ι ≫ p) k)

/-- **The component on `X` of the pushed-forward cap product of Stacks 0EQJ on a closed subspace
`E ⊆ X`.**  For an integral closed subspace `T ⊆ E` of δ-dimension `k + 1` this is the
coefficient family on `X` of the pushforward of the component cycle `c₁(𝒩|_T) ∩ [T]` along the
composite closed immersion `T → E → X`; at a subspace of any other δ-dimension it is zero. -/
def firstChernCapPushforwardComponentCoeff
    (T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor) :
    IntegralClosedSubspace D.site D.base D.base_mem X → ℤ :=
  if hT : deltaDimension D (E.1.ι ≫ p) T = k + 1 then
    cycleClosedPushforward D hp.1 T.isClosedSubspace.1 (D.isDecentSpace_of_isGood p hp)
      (isClosedImmersion_comp D.site D.base D.base_mem T.subspace.ι E.1.ι
        T.isClosedSubspace.2 E.2.2) (chernE T hT).1
  else 0

/-- For `T ⊆ E` of δ-dimension `k + 1` the component is the pushforward of `c₁(𝒩|_T) ∩ [T]` along
`T → E → X`. -/
theorem firstChernCapPushforwardComponentCoeff_of_deltaDimension_eq
    {T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor}
    (hT : deltaDimension D (E.1.ι ≫ p) T = k + 1) :
    firstChernCapPushforwardComponentCoeff D p hp E k chernE T =
      cycleClosedPushforward D hp.1 T.isClosedSubspace.1 (D.isDecentSpace_of_isGood p hp)
        (isClosedImmersion_comp D.site D.base D.base_mem T.subspace.ι E.1.ι
          T.isClosedSubspace.2 E.2.2) (chernE T hT).1 := by
  rw [firstChernCapPushforwardComponentCoeff, dite_eq_left hT]

/-- At a subspace of δ-dimension other than `k + 1` the component is zero. -/
theorem firstChernCapPushforwardComponentCoeff_of_deltaDimension_ne
    {T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor}
    (hT : deltaDimension D (E.1.ι ≫ p) T ≠ k + 1) :
    firstChernCapPushforwardComponentCoeff D p hp E k chernE T = 0 := by
  rw [firstChernCapPushforwardComponentCoeff, dite_eq_right hT]

include hE in
/-- **The pushforward to `X` of the component cycle of the cap product of Stacks 0EQJ formed on
`E`.**  Pushing the component cycle `i'_*(c₁(𝒩|_T) ∩ [T])` on `E` forward along `i : E → X` is
pushing `c₁(𝒩|_T) ∩ [T]` forward along the composite `T → E → X`; this is
`AlgebraicGeometry.Space.cycleClosedPushforward_comp`. -/
theorem cycleClosedPushforward_firstChernComponentCycle_eq
    (T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor) :
    cycleClosedPushforward D hp.1 E.2.1 (D.isDecentSpace_of_isGood p hp) E.2.2
        (firstChernComponentCycle D (E.1.ι ≫ p) hE k chernE T).1 =
      firstChernCapPushforwardComponentCoeff D p hp E k chernE T := by
  by_cases hT : deltaDimension D (E.1.ι ≫ p) T = k + 1
  · rw [firstChernComponentCycle_of_deltaDimension_eq D (E.1.ι ≫ p) hE k chernE hT,
      firstChernCapPushforwardComponentCoeff_of_deltaDimension_eq D p hp E k chernE hT]
    exact (cycleClosedPushforward_comp D hp.1 E.2.1 T.isClosedSubspace.1
      (D.isDecentSpace_of_isGood p hp) (D.isDecentSpace_of_isGood (E.1.ι ≫ p) hE)
      T.isClosedSubspace.2 E.2.2 (chernE T hT).1).symm
  · rw [firstChernComponentCycle_of_deltaDimension_ne D (E.1.ι ≫ p) hE k chernE hT,
      firstChernCapPushforwardComponentCoeff_of_deltaDimension_ne D p hp E k chernE hT]
    exact cycleClosedPushforward_zero D hp.1 E.2.1 (D.isDecentSpace_of_isGood p hp) E.2.2

include hE in
/-- **The pushforward to `X` of the cap product of Stacks 0EQJ formed on a closed subspace.**
For a `(k+1)`-cycle `α` on `E`,

  `i_*(c₁(𝒩|_E) ∩ α) = ∑_T α(T) (T → X)_*(c₁(𝒩|_T) ∩ [T])`,

the sum over the integral closed subspaces `T ⊆ E`, the pushforward being along the composite
`T → E → X`. -/
theorem cycleClosedPushforward_firstChernCapCycleMap_eq_finsum
    (α : CycleGroup D (E.1.ι ≫ p) (k + 1))
    (V : IntegralClosedSubspace D.site D.base D.base_mem X) :
    cycleClosedPushforward D hp.1 E.2.1 (D.isDecentSpace_of_isGood p hp) E.2.2
        (firstChernCapCycleMap D (E.1.ι ≫ p) hE k chernE α).1 V =
      ∑ᶠ T : IntegralClosedSubspace D.site D.base D.base_mem E.1.toFunctor,
        α.1 T * firstChernCapPushforwardComponentCoeff D p hp E k chernE T V := by
  exact cycleClosedPushforward_finsum_mul_eq_of_forall D hp.1 E.2.1
    (D.isDecentSpace_of_isGood p hp) E.2.2 (fun T => α.1 T)
    (fun T Z => (firstChernComponentCycle D (E.1.ι ≫ p) hE k chernE T).1 Z)
    (fun T => firstChernCapPushforwardComponentCoeff D p hp E k chernE T)
    (cycleClosedPushforward_firstChernComponentCycle_eq D p hp E hE k chernE) V

end CapPushforward

end AlgebraicGeometry.Space

end

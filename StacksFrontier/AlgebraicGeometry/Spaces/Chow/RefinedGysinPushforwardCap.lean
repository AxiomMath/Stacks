module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChowLocalizationSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceCycleTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GlobalSectionDivisorCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinPushforwardFirstChernCapCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisorCycleOfGoodDifference
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalenceCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RefinedGysinOfSection
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroSchemeOfCanonicalSection
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroSchemePullback
public import StacksFrontier.CategoryTheory.SubfunctorFactor

/-!
# The pushforward of the refined Gysin map is the cap product with the first Chern class

In Situation 0EDT let `X/B` be good, let `ℒ` be an invertible `𝒪_X`-module with a global
section `s`, let `E = Z(s)` be its vanishing locus and `i : E → X` the closed immersion.
**Stacks 0ER4** asserts that for every `(k+1)`-cycle `α` on `X`

`i_* i^* α = c₁(ℒ) ∩ α` in `CH_k(X)`,

where `i^*` is the refined Gysin homomorphism of Stacks 0ER1 and `c₁(ℒ) ∩ -` the cap product
of Stacks 0EQJ; in particular, when `E` is an effective Cartier divisor, `E · α = c₁(𝒪_X(E)) ∩ α`.

## The proof

It is the source's. Both sides are additive extensions of rules on the integral closed
subspaces `W ⊆ X` of δ-dimension `k + 1`, and for `W ⊆ E` the two rules agree. For `W ⊄ E` the
restriction `s|_W` is a nonzero section of `ℒ|_W` whose zero scheme is `W ×_X E` (Stacks 0846
part (2), `AlgebraicGeometry.Space.zeroScheme_modulePullbackSections`), so by Stacks 0EQF on the
integral space `W` the cycle `[W ×_X E]_k` is the Weil divisor `div_{ℒ|_W}(s|_W)`; its pushforward
to `X` is that of `i^*[W] = [E ∩ W]_k`. The class of `c₁(ℒ|_W) ∩ [W]` is the class of the Weil
divisor of any nonzero meromorphic section of `ℒ|_W` (Stacks 0EQE part (2)), and two such Weil
divisors differ by the principal divisor of their ratio. The cycle identity
`AlgebraicGeometry.Space.closedSubspaceCyclePushforward_gysinCycleMap_sub_firstChernCapCycleMap`
then writes `i_* i^* α - c₁(ℒ) ∩ α` as a locally finite sum of pushforwards of principal
divisors, which is zero in `CH_k(X)` by Stacks 0EQ6.

## Main results

* `AlgebraicGeometry.Space.isInvertibleSheaf_integralClosedSubspaceRestrict` and
  `AlgebraicGeometry.Space.integralClosedSubspaceRestrictSection_ne_zero_of_not_le`: `ℒ|_W` is
  invertible, and `s|_W ≠ 0` when `W ⊄ Z(s)`.
* `AlgebraicGeometry.Space.closedSubspaceCycle_preimage_vanishingLocus_eq_canonicalDivisorCycleAt`:
  for an integral closed subspace `W ⊄ Z(s)` of δ-dimension `k + 1`, `[W ×_X Z(s)]_k` is the
  Weil divisor of the meromorphic section `s|_W` of `ℒ|_W`.
* `AlgebraicGeometry.Space.cycleFamilySum_comp_equiv`: a locally finite sum of Stacks 0EQ6,
  part (1), is unchanged by reindexing the family along an equivalence.
* `Space.chowClassCanonical_closedSubspaceCyclePushforward_gysinCycleMap_sectionGysinRule`:
  **Stacks 0ER4** on representatives, `i_* i^* α = c₁(ℒ) ∩ α` in the Chow group of Stacks 0EQ6
  at the canonical embeddings of Stacks 0ENK.
* `Space.chowClassCanonical_closedSubspaceCyclePushforward_gysinCycleMap_canonicalSection`:
  **Stacks 0ER4, in particular**, `D · α = c₁(𝒪_X(D)) ∩ α` for an effective Cartier divisor
  `D ⊆ X`, `D · α` being formed for the pair `(𝒪_X(D), 1_D)` of Stacks 0847.
* `AlgebraicGeometry.Space.chowClass_closedSubspaceCyclePushforward_gysinCycleMap_sectionGysinRule`
  and `AlgebraicGeometry.Space.chowGroupClosedPushforward_sectionRefinedGysin`: the image of
  Stacks 0ER4 in the coarser quotient `AlgebraicGeometry.Space.chowGroup`, on representatives and
  through `AlgebraicGeometry.Space.sectionRefinedGysin`.
* `AlgebraicGeometry.Space.sectionCartierIntersection_eq_canonicalFirstChernCap`: the first
  form of the last assertion, `E · α = c₁(ℒ) ∩ α` for `E = Z(s)` an effective Cartier divisor.
* `AlgebraicGeometry.Space.sectionCartierIntersection_canonicalSection_eq_canonicalFirstChernCap`:
  its image in `AlgebraicGeometry.Space.chowGroup`, `D · α` being the operation
  `AlgebraicGeometry.Space.sectionCartierIntersection`.

## Implementation notes

The cap product `c₁(ℒ) ∩ -` is `AlgebraicGeometry.Space.canonicalFirstChernCap`, whose component
cycle on `W` is the Weil divisor of the regular meromorphic section of `ℒ|_W` chosen by
`AlgebraicGeometry.Space.componentMeromorphicSection`. The refined Gysin map
`AlgebraicGeometry.Space.sectionRefinedGysin` uses, in clause (1)(b) of Stacks 0ER1, the Weil
divisor of another regular meromorphic section, the one of
`AlgebraicGeometry.Space.restrictedSectionOfIntegralClosedSubspace`. The source's `c₁(ℒ|_W) ∩ [W]`
is a class, so the two are interchangeable; here the difference is carried through the proof as
a locally finite sum of principal divisors, so that the statement holds for the two
constructions as they are.

The Chow groups are taken at the index universe `max (u + 1) v`, `u` being the universe of the
spaces: the source's rational equivalences are sums over arbitrary locally finite families of
integral closed subspaces, and the families used here are indexed by sets of integral closed
subspaces of `X`, which live in `Type (u + 1)`. This is the convention of the other results on
locally finite sums of principal divisors, for instance
`AlgebraicGeometry.Space.isRationallyEquivalentToZero_finsum_max`.

The letter `D` is taken by the dimension situation of Stacks 0EDT, so the closed subspace which
the source calls `D` in the first assertion is called `E`.

## References

* [Stacks Project, Tag 0ER4](https://stacks.math.columbia.edu/tag/0ER4)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EQF](https://stacks.math.columbia.edu/tag/0EQF)
* [Stacks Project, Tag 0EQE](https://stacks.math.columbia.edu/tag/0EQE)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0846](https://stacks.math.columbia.edu/tag/0846)
* [Stacks Project, Tag 0847](https://stacks.math.columbia.edu/tag/0847)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe w w' v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (hL : IsInvertibleSheaf D p hp L)
    (s : L.sections)

/-! ### The restriction of `s` to an integral closed subspace -/

include hL in
/-- **Stacks 0B8P for the restriction to an integral closed subspace**, in the form of
Stacks 0ER1: the restriction `ℒ|_W` of an invertible module to an integral closed subspace
`W ⊆ X` is an invertible `𝒪_W`-module. -/
theorem isInvertibleSheaf_integralClosedSubspaceRestrict
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    IsInvertibleSheaf D (W.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp W)
      (integralClosedSubspaceRestrict D p hp L W) :=
  isInvertible_modulePullback_obj D.site D.base D.base_mem
    (closedSubspaceHom D.site D.base D.base_mem hp.1 W.subspace W.isClosedSubspace) L hL

include hL in
/-- **The restriction of `s` to an integral closed subspace not contained in `Z(s)` is
nonzero.** If `s|_W = 0` then the inclusion `W → X` factors through `Z(s)` by Stacks 0846
part (2), so `W ⊆ Z(s)`. -/
theorem integralClosedSubspaceRestrictSection_ne_zero_of_not_le
    {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hWE : ¬ W.subspace ≤ (vanishingLocus D p hp L s).1) :
    integralClosedSubspaceRestrictSection D p hp L s W ≠ 0 := by
  intro h0
  obtain ⟨g, hg⟩ := (modulePullbackSections_eq_zero_iff_exists_comp_eq_zeroScheme D.site D.base
    D.base_mem ⟨X, hp.1⟩ ⟨W.subspace.toFunctor, W.isClosedSubspace.1⟩ L hL s
    (closedSubspaceHom D.site D.base D.base_mem hp.1 W.subspace W.isClosedSubspace)).1 h0
  exact hWE (Subfunctor.le_of_comp_eq_ι g.hom (congrArg (fun f => f.hom) hg))

include hL in
/-- **`[W ×_X Z(s)]_k` is the Weil divisor of `s|_W`.** Let `W ⊆ X` be an integral closed
subspace of δ-dimension `k + 1` not contained in `Z(s)`. The cycle `[W ×_X Z(s)]_k` of
Stacks 0EE9 of the fibre product, read as a closed subspace of `W`, is the Weil divisor
`div_{ℒ|_W}(s|_W)` of Stacks 0EQE part (1) of the nonzero section `s|_W` of `ℒ|_W`.

The zero scheme of `s|_W` is `W ×_X Z(s)` (Stacks 0846 part (2)), and Stacks 0EQF on `W`
identifies its cycle with `div_{ℒ|_W}(s|_W)`. -/
theorem closedSubspaceCycle_preimage_vanishingLocus_eq_canonicalDivisorCycleAt (k : ℤ)
    {W : IntegralClosedSubspace D.site D.base D.base_mem X} (hW : deltaDimension D p W = k + 1)
    (hWE : ¬ W.subspace ≤ (vanishingLocus D p hp L s).1) :
    closedSubspaceCycle D (W.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp W)
        ((vanishingLocus D p hp L s).1.preimage W.subspace.ι)
        (isClosedSubspace_preimage D.site D.base D.base_mem W.subspace.ι
          (vanishingLocus D p hp L s).1 hp.1 W.isClosedSubspace.1 (vanishingLocus D p hp L s).2)
        k (deltaDimensionSubspace_preimage_integralClosedSubspace_le_of_not_le D p hp
          (vanishingLocus D p hp L s) W (isGood_integralClosedSubspace D p hp W) k hW hWE) =
      canonicalDivisorCycleAt D (W.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp W)
        W.isIntegralSpace (integralClosedSubspaceRestrict D p hp L W)
        (isInvertibleModule_integralClosedSubspaceRestrict_of_isInvertibleSheaf D p hp L hL W)
        (globalSectionMeromorphic D.site D.base D.base_mem
          (isGood_integralClosedSubspace D p hp W).1 (integralClosedSubspaceRestrict D p hp L W)
          (integralClosedSubspaceRestrictSection D p hp L s W))
        ((isRegularMeromorphicSection_iff_ne_zero D.site D.base D.base_mem
          (isGood_integralClosedSubspace D p hp W).1 W.isIntegralSpace
          (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D (W.subspace.ι ≫ p)
            (isGood_integralClosedSubspace D p hp W))
          (integralClosedSubspaceRestrict D p hp L W)
          (isInvertibleModule_integralClosedSubspaceRestrict_of_isInvertibleSheaf D p hp L hL W)
          _).2
          (globalSectionMeromorphic_ne_zero_of_isInvertibleSheaf D (W.subspace.ι ≫ p)
            (isGood_integralClosedSubspace D p hp W) (integralClosedSubspaceRestrict D p hp L W)
            (isInvertibleSheaf_integralClosedSubspaceRestrict D p hp L hL W)
            (integralClosedSubspaceRestrictSection_ne_zero_of_not_le D p hp L hL s hWE)))
        (by rw [deltaDimensionClosed_univ_integralClosedSubspace D p hp W, hW]) := by
  have hWg := isGood_integralClosedSubspace D p hp W
  have hk : deltaDimensionClosed D (W.subspace.ι ≫ p) hWg Set.univ isClosed_univ =
      ((k + 1 : ℤ) : EInt) := by
    rw [deltaDimensionClosed_univ_integralClosedSubspace D p hp W, hW]
  have hZ : vanishingLocus D (W.subspace.ι ≫ p) hWg (integralClosedSubspaceRestrict D p hp L W)
      (integralClosedSubspaceRestrictSection D p hp L s W) =
      ⟨(vanishingLocus D p hp L s).1.preimage W.subspace.ι,
        isClosedSubspace_preimage D.site D.base D.base_mem W.subspace.ι
          (vanishingLocus D p hp L s).1 hp.1 W.isClosedSubspace.1
          (vanishingLocus D p hp L s).2⟩ :=
    zeroScheme_modulePullbackSections D.site D.base D.base_mem ⟨X, hp.1⟩
      ⟨W.subspace.toFunctor, W.isClosedSubspace.1⟩ L hL s
      (closedSubspaceHom D.site D.base D.base_mem hp.1 W.subspace W.isClosedSubspace)
  have h0EQF := zeroSchemeCycleCoeff_eq_invertibleDivisorCoefficients_globalSection D
    (W.subspace.ι ≫ p) hWg W.isIntegralSpace (integralClosedSubspaceRestrict D p hp L W)
    (isInvertibleSheaf_integralClosedSubspaceRestrict D p hp L hL W) hk
    (integralClosedSubspaceRestrictSection_ne_zero_of_not_le D p hp L hL s hWE)
    (canonicalGeometricPoint D.site D.base D.base_mem _) (canonicalGeometricPoint_liesOver D _)
  refine Subtype.ext ?_
  refine Eq.trans ?_ h0EQF
  rw [add_sub_cancel_right]
  have key : ∀ Y : ClosedSubspaces D.site D.base D.base_mem W.subspace.toFunctor,
      Y = ⟨(vanishingLocus D p hp L s).1.preimage W.subspace.ι,
        isClosedSubspace_preimage D.site D.base D.base_mem W.subspace.ι
          (vanishingLocus D p hp L s).1 hp.1 W.isClosedSubspace.1
          (vanishingLocus D p hp L s).2⟩ →
      cycleCoeffOfClosedSubspace D (W.subspace.ι ≫ p) hWg Y.1 Y.2 k
          (canonicalGeometricPoint D.site D.base D.base_mem Y.1.toFunctor) =
        cycleCoeffOfClosedSubspace D (W.subspace.ι ≫ p) hWg
          ((vanishingLocus D p hp L s).1.preimage W.subspace.ι)
          (isClosedSubspace_preimage D.site D.base D.base_mem W.subspace.ι
            (vanishingLocus D p hp L s).1 hp.1 W.isClosedSubspace.1
            (vanishingLocus D p hp L s).2) k
          (canonicalGeometricPoint D.site D.base D.base_mem
            ((vanishingLocus D p hp L s).1.preimage W.subspace.ι).toFunctor) := by
    rintro Y rfl
    rfl
  exact (key _ hZ).symm

/-- The component cycle `c₁(ℒ|_W) ∩ [W]` of clause (1)(b) of Stacks 0ER1, as the refined Gysin
map `AlgebraicGeometry.Space.sectionRefinedGysin` takes it, is the Weil divisor of the regular
meromorphic section `AlgebraicGeometry.Space.restrictedSectionOfIntegralClosedSubspace` of `ℒ|_W`
at the canonical choices of `AlgebraicGeometry.Space.canonicalDivisorCycleAt`. -/
theorem restrictedDivisorCycle_eq_canonicalDivisorCycleAt (k : ℤ)
    {W : IntegralClosedSubspace D.site D.base D.base_mem X} (hW : deltaDimension D p W = k + 1) :
    restrictedDivisorCycle D p hp L k hL W hW =
      canonicalDivisorCycleAt D (W.subspace.ι ≫ p) (isGood_integralClosedSubspace D p hp W)
        W.isIntegralSpace (integralClosedSubspaceRestrict D p hp L W)
        (isInvertibleModule_integralClosedSubspaceRestrict_of_isInvertibleSheaf D p hp L hL W)
        (restrictedSectionOfIntegralClosedSubspace D p hp L hL W)
        (isRegularMeromorphicSection_regularMeromorphicSection D.site D.base D.base_mem
          (isGood_integralClosedSubspace D p hp W).1 W.isIntegralSpace
          (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D (W.subspace.ι ≫ p)
            (isGood_integralClosedSubspace D p hp W))
          _ (isInvertibleModule_integralClosedSubspaceRestrict_of_isInvertibleSheaf D p hp L hL W))
        (by rw [deltaDimensionClosed_univ_integralClosedSubspace D p hp W, hW]) :=
  rfl

/-! ### Reindexing a locally finite sum -/

section Reindex

variable {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sY : Y ⟶ D.space)
    (hY : D.IsGood sY)

/-- The locally finite sum `∑ (i_j)_* c_j` of Stacks 0EQ6, part (1), does not change when the
family is reindexed along an equivalence of index types. -/
theorem cycleFamilySum_comp_equiv {J : Type w} {J' : Type w'} (e : J' ≃ J)
    (W : J → IntegralClosedSubspace D.site D.base D.base_mem Y)
    (hWfin : LocallyFinite fun j : J =>
      subspacePointSet D.site D.base D.base_mem Y (W j).subspace)
    (k : ℤ) (c : ∀ j, CycleGroup D ((W j).subspace.ι ≫ sY) k) :
    cycleFamilySum D sY hY (fun j' => W (e j')) (hWfin.comp_injective e.injective) k
        (fun j' => c (e j')) =
      cycleFamilySum D sY hY W hWfin k c :=
  Subtype.ext (funext fun Z =>
    finsum_comp_equiv e (f := fun j => (integralClosedSubspacePushforward D sY hY (W j) k
      (c j)).1 Z))

end Reindex

/-! ### Stacks 0ER4 -/

/-- A locally finite sum of principal divisors of `(k+1)`-dimensional integral closed subspaces
has class zero in `CH_k(X)`, also for a family indexed by `ULift J`. -/
private theorem chowClassCanonical_cycleFamilySum_ulift_eq_zero (k : ℤ) {J : Type w}
    (W : J → IntegralClosedSubspace D.site D.base D.base_mem X)
    (hWfin : LocallyFinite fun j : J =>
      subspacePointSet D.site D.base D.base_mem X (W j).subspace)
    (c : ∀ j, CycleGroup D ((W j).subspace.ι ≫ p) k)
    (hWdim : ∀ j, deltaDimension D p (W j) = k + 1)
    (hWprin : ∀ j, IsPrincipalDivisorCycleOfGood D ((W j).subspace.ι ≫ p)
      (isGood_integralClosedSubspace D p hp (W j)) (W j).isIntegralSpace k (c j)) :
    chowClassCanonical.{max w v} D p hp k (cycleFamilySum D p hp W hWfin k c) = 0 :=
  (congrArg (chowClassCanonical D p hp k)
    (cycleFamilySum_comp_equiv D p hp Equiv.ulift.{v} W hWfin k c)).symm.trans
    (chowClassCanonical_cycleFamilySum_eq_zero D p hp k _ _ _ (fun _ => hWdim _)
      fun _ => hWprin _)

/-- **Stacks 0ER4.** In Situation 0EDT let `X/B` be good, let `ℒ` be an invertible
`𝒪_X`-module with a global section `s`, and let `i : E → X` be the closed immersion of the
vanishing locus `E = Z(s)`. For every `(k+1)`-cycle `α` on `X`

`i_* i^* α = c₁(ℒ) ∩ α` in `CH_k(X)`.

Here `i^* α` is represented by the cycle `∑ n_W i^*[W]` of the refined Gysin map of Stacks 0ER1,
`AlgebraicGeometry.Space.gysinCycleMap` at the rule
`AlgebraicGeometry.Space.sectionGysinRule`; `i_*` is the pushforward of cycles along the closed
immersion; `c₁(ℒ) ∩ α` is represented by the cycle of Stacks 0EQJ,
`AlgebraicGeometry.Space.firstChernCapCycleMap` at the canonical component rule; and both classes
are taken in `CH_k(X)` of Stacks 0EQ6, `AlgebraicGeometry.Space.chowGroupCanonical`, whose
rational equivalences are sums of principal divisors at the canonical embeddings of Stacks 0ENK.
As every class of `CH_{k+1}(X)` is the class of a cycle, this is the identity of the source on
representatives.

The difference of the two sides is, by
`AlgebraicGeometry.Space.closedSubspaceCyclePushforward_gysinCycleMap_sub_firstChernCapCycleMap`
and `AlgebraicGeometry.Space.firstChernCapCycleMap_eq_cycleFamilySum`, the locally finite sum of
the pushforwards of the cycles `n_W ([W ×_X Z(s)]_k - c₁(ℒ|_W) ∩ [W])` for `W ⊄ Z(s)` and
`n_W (c₁(ℒ|_W) ∩ [W] - c₁(ℒ|_W) ∩' [W])` for all `W`, the two cap products being formed with the
two regular meromorphic sections of `ℒ|_W` the two constructions choose. By Stacks 0EQF on `W`
(`AlgebraicGeometry.Space.closedSubspaceCycle_preimage_vanishingLocus_eq_canonicalDivisorCycleAt`)
each of these is an integer multiple of the difference of the Weil divisors of two regular
meromorphic sections of `ℒ|_W`, hence a principal divisor at the canonical embeddings
(`AlgebraicGeometry.Space.isPrincipalDivisorCycleOfGood_zsmul_canonicalDivisorCycleAt_sub`). -/
@[stacks 0ER4 "i_* i^* α = c₁(L) ∩ α in CH_k(X) for every (k+1)-cycle α, for X/B good, L \
invertible, s a global section and i : D = Z(s) → X: i^* α is the cycle of the refined Gysin map \
of Stacks 0ER1 (gysinCycleMap at sectionGysinRule), i_* the pushforward of cycles along the closed \
immersion, c₁(L) ∩ α the cycle of Stacks 0EQJ at the canonical choices, both classes taken in the \
Chow group of Stacks 0EQ6 at the canonical embeddings of Stacks 0ENK (chowGroupCanonical); nothing \
carried"]
theorem chowClassCanonical_closedSubspaceCyclePushforward_gysinCycleMap_sectionGysinRule (k : ℤ)
    (α : CycleGroup D p (k + 1)) :
    chowClassCanonical.{max (u + 1) v} D p hp k (closedSubspaceCyclePushforward D p hp
        (vanishingLocus D p hp L s) k (gysinCycleMap D p (vanishingLocus D p hp L s)
          (isGood_vanishingLocus D p hp L s) k (sectionGysinRule D p hp L s k hL) α)) =
      chowClassCanonical.{max (u + 1) v} D p hp k (firstChernCapCycleMap D p hp k
        (canonicalFirstChernRule D p hp L
          (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) k) α) := by
  have hE := isGood_vanishingLocus D p hp L s
  have hLm := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL
  -- `i_* i^* α - c₁ ∩ α` against the component rule of clause (1)(b) of `i^*`
  have hA := closedSubspaceCyclePushforward_gysinCycleMap_sub_firstChernCapCycleMap D p hp
    (vanishingLocus D p hp L s) hE k (sectionGysinRule D p hp L s k hL)
    (restrictedDivisorCycle D p hp L k hL) (fun _ _ _ => rfl)
    (fun W hW hWE => closedSubspaceCycle D (W.subspace.ι ≫ p)
      (isGood_integralClosedSubspace D p hp W)
      ((vanishingLocus D p hp L s).1.preimage W.subspace.ι)
      (isClosedSubspace_preimage D.site D.base D.base_mem W.subspace.ι
        (vanishingLocus D p hp L s).1 hp.1 W.isClosedSubspace.1 (vanishingLocus D p hp L s).2)
      k (deltaDimensionSubspace_preimage_integralClosedSubspace_le_of_not_le D p hp
        (vanishingLocus D p hp L s) W (isGood_integralClosedSubspace D p hp W) k hW hWE))
    (fun W hW hWE =>
      integralClosedSubspacePushforward_closedSubspaceCycle_preimage_eq_gysinIntersectionCycle
        D p hp (vanishingLocus D p hp L s) hE W (isGood_integralClosedSubspace D p hp W) k hW
        hWE) α
  -- the two component rules of the cap product differ by a rule of principal divisors
  have hB := firstChernCapCycleMap_add_of_componentCycle_add D p hp k
    (canonicalFirstChernRule D p hp L hLm k)
    (fun W hW => restrictedDivisorCycle D p hp L k hL W hW -
      canonicalFirstChernRule D p hp L hLm k W hW)
    (restrictedDivisorCycle D p hp L k hL) (fun _ _ => (add_sub_cancel _ _).symm) α
  have hfin : LocallyFinite fun W : {W : IntegralClosedSubspace D.site D.base D.base_mem X //
      α.1 W ≠ 0} => subspacePointSet D.site D.base D.base_mem X W.1.subspace :=
    (α.2.1.comp_injective Subtype.val_injective).subset fun W => by
      simp only [Function.comp_apply, if_neg W.2, subset_refl]
  have hC := firstChernCapCycleMap_eq_cycleFamilySum D p hp k
    (fun W hW => restrictedDivisorCycle D p hp L k hL W hW -
      canonicalFirstChernRule D p hp L hLm k W hW) α
    (fun W : {W : IntegralClosedSubspace D.site D.base D.base_mem X // α.1 W ≠ 0} => W.1)
    Subtype.val_injective hfin (fun W => α.2.2 W.1 W.2) fun W hW => ⟨⟨W, hW⟩, rfl⟩
  rw [← sub_eq_zero, ← map_sub, ← sub_add_cancel
      (closedSubspaceCyclePushforward D p hp (vanishingLocus D p hp L s) k
        (gysinCycleMap D p (vanishingLocus D p hp L s) hE k (sectionGysinRule D p hp L s k hL) α))
      (firstChernCapCycleMap D p hp k (restrictedDivisorCycle D p hp L k hL) α), hA, hB, hC,
    map_sub, map_add, map_add]
  have key : ∀ a b c : chowGroupCanonical.{max (u + 1) v} D p hp k,
      a = 0 → c = 0 → a + (b + c) - b = 0 := by
    rintro a b c rfl rfl
    abel
  refine key _ _ _
    (chowClassCanonical_cycleFamilySum_ulift_eq_zero D p hp k _ _ _
      (fun j => α.2.2 _ j.2.1) fun j => ?_)
    (chowClassCanonical_cycleFamilySum_ulift_eq_zero D p hp k _ _ _
      (fun j => α.2.2 _ j.2) fun j => ?_)
  · rw [closedSubspaceCycle_preimage_vanishingLocus_eq_canonicalDivisorCycleAt D p hp L hL s k
        (α.2.2 j.1 j.2.1) j.2.2,
      restrictedDivisorCycle_eq_canonicalDivisorCycleAt D p hp L hL k
        (α.2.2 j.1 j.2.1)]
    exact isPrincipalDivisorCycleOfGood_zsmul_canonicalDivisorCycleAt_sub D _
      (isGood_integralClosedSubspace D p hp j.1) j.1.isIntegralSpace
      _ _ _ _ _ _ _ _
  · rw [restrictedDivisorCycle_eq_canonicalDivisorCycleAt D p hp L hL k
      (α.2.2 j.1 j.2)]
    exact isPrincipalDivisorCycleOfGood_zsmul_canonicalDivisorCycleAt_sub D _
      (isGood_integralClosedSubspace D p hp j.1) j.1.isIntegralSpace
      _ _ _ _ _ _ _ _

/-- Stacks 0ER4 on representatives, in the Chow group `AlgebraicGeometry.Space.chowGroup` whose
rational equivalences quantify the embedding `R(W) → Q(𝒪^h_{W,ξ})` existentially: the image of
`chowClassCanonical_closedSubspaceCyclePushforward_gysinCycleMap_sectionGysinRule`
under the comparison map `AlgebraicGeometry.Space.chowGroupCanonicalToChowGroup`. -/
theorem chowClass_closedSubspaceCyclePushforward_gysinCycleMap_sectionGysinRule (k : ℤ)
    (α : CycleGroup D p (k + 1)) :
    chowClass.{max (u + 1) v} D p hp k (closedSubspaceCyclePushforward D p hp
        (vanishingLocus D p hp L s) k (gysinCycleMap D p (vanishingLocus D p hp L s)
          (isGood_vanishingLocus D p hp L s) k (sectionGysinRule D p hp L s k hL) α)) =
      canonicalFirstChernCap.{u, max (u + 1) v} D p hp L
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) k α :=
  congrArg (chowGroupCanonicalToChowGroup.{max (u + 1) v} D p hp k)
    (chowClassCanonical_closedSubspaceCyclePushforward_gysinCycleMap_sectionGysinRule D p hp L hL s
      k α)

/-- Stacks 0ER4 in the Chow group `AlgebraicGeometry.Space.chowGroup` whose rational
equivalences quantify the embedding `R(W) → Q(𝒪^h_{W,ξ})` existentially, through the operations
on Chow groups. In Situation 0EDT let `X/B` be good, let `ℒ` be an invertible `𝒪_X`-module with a
global section `s`, and let `i : E → X` be the closed immersion of the vanishing locus `E = Z(s)`.
For every `(k+1)`-cycle `α` on `X`

`i_* i^* α = c₁(ℒ) ∩ α` in `CH_k(X)`,

where `i^* : Z_{k+1}(X) → CH_k(E)` is the refined Gysin homomorphism of Stacks 0ER1
(`AlgebraicGeometry.Space.sectionRefinedGysin`), `i_* : CH_k(E) → CH_k(X)` is the pushforward
along the closed immersion (`AlgebraicGeometry.Space.chowGroupClosedPushforward`), and
`c₁(ℒ) ∩ -` is the cap product of Stacks 0EQJ (`AlgebraicGeometry.Space.canonicalFirstChernCap`),
all with values in the Chow groups of Stacks 0EQ6. -/
theorem chowGroupClosedPushforward_sectionRefinedGysin (k : ℤ) (α : CycleGroup D p (k + 1)) :
    chowGroupClosedPushforward.{max (u + 1) v} D p hp (vanishingLocus D p hp L s).1
        (vanishingLocus D p hp L s).2 k (sectionRefinedGysin.{max (u + 1) v} D p hp L s k hL α) =
      canonicalFirstChernCap.{u, max (u + 1) v} D p hp L
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) k α :=
  chowClass_closedSubspaceCyclePushforward_gysinCycleMap_sectionGysinRule.{v} D p hp L hL s k α

/-- **Stacks 0ER4, the last assertion, for the pair `(ℒ, s)`.** If the vanishing locus
`E = Z(s)` is an effective Cartier divisor, then `E · α = c₁(ℒ) ∩ α` in `CH_k(X)` for every
`(k+1)`-cycle `α`, `E · α = i_* i^* α` being the operation of Stacks 0ER1, part (3). -/
theorem sectionCartierIntersection_eq_canonicalFirstChernCap
    (hCartier : IsEffectiveCartierDivisor D.site D.base D.base_mem ⟨X, hp.1⟩
      (vanishingLocus D p hp L s)) (k : ℤ) (α : CycleGroup D p (k + 1)) :
    sectionCartierIntersection.{max (u + 1) v} D p hp L s k hL hCartier α =
      canonicalFirstChernCap.{u, max (u + 1) v} D p hp L
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) k α :=
  chowClass_closedSubspaceCyclePushforward_gysinCycleMap_sectionGysinRule.{v} D p hp L hL s k α

omit L hL s in
/-- The vanishing locus of the canonical section `1_D` of `𝒪_X(D)` is the effective Cartier
divisor `D` (Stacks 0847, part (2)), so it is an effective Cartier divisor. -/
theorem isEffectiveCartierDivisor_vanishingLocus_canonicalSection
    (Dv : ClosedSubspaces D.site D.base D.base_mem X)
    (hDv : IsEffectiveCartierDivisor D.site D.base D.base_mem ⟨X, hp.1⟩ Dv) :
    IsEffectiveCartierDivisor D.site D.base D.base_mem ⟨X, hp.1⟩
      (vanishingLocus D p hp
        (associatedInvertibleSheaf D.site D.base D.base_mem ⟨X, hp.1⟩ Dv hDv)
        (canonicalSection D.site D.base D.base_mem ⟨X, hp.1⟩ Dv hDv)) :=
  (congrArg (IsEffectiveCartierDivisor D.site D.base D.base_mem ⟨X, hp.1⟩)
    (zeroScheme_canonicalSection_eq D.site D.base D.base_mem ⟨X, hp.1⟩ Dv hDv)).mpr hDv

omit L hL s in
/-- **Stacks 0ER4, in particular.** In Situation 0EDT let `X/B` be good and let `D ⊆ X` be an
effective Cartier divisor, with invertible sheaf `𝒪_X(D)` and canonical section `1_D`
(Stacks 0841), whose vanishing locus `Z(1_D)` is `D` (Stacks 0847). For every `(k+1)`-cycle `α`
on `X`

`D · α = c₁(𝒪_X(D)) ∩ α` in `CH_k(X)`,

where `D · α = i_* i^* α` is the operation of Stacks 0ER1, part (3), for the pair
`(𝒪_X(D), 1_D)`: `i^* α` is represented by the cycle of the refined Gysin map,
`AlgebraicGeometry.Space.gysinCycleMap` at `AlgebraicGeometry.Space.sectionGysinRule`, and `i_*`
is the pushforward of cycles along `i : Z(1_D) → X`. The cap product `c₁(𝒪_X(D)) ∩ α` is
represented by the cycle of Stacks 0EQJ at the canonical choices, and both classes are taken in
`CH_k(X)` of Stacks 0EQ6, `AlgebraicGeometry.Space.chowGroupCanonical`. This is
`chowClassCanonical_closedSubspaceCyclePushforward_gysinCycleMap_sectionGysinRule` for that
pair. -/
@[stacks 0ER4 "in particular: D · α = c₁(O_X(D)) ∩ α in CH_k(X) for an effective Cartier \
divisor D ⊆ X, with D · α = i_* i^* α of Stacks 0ER1 part (3) formed on cycles for the pair \
(O_X(D), 1_D) of Stacks 0847, whose vanishing locus is D, c₁(O_X(D)) ∩ α the cycle of Stacks 0EQJ \
at the canonical choices, and the classes taken in the Chow group of Stacks 0EQ6 at the canonical \
embeddings of Stacks 0ENK (chowGroupCanonical)"]
theorem chowClassCanonical_closedSubspaceCyclePushforward_gysinCycleMap_canonicalSection
    (Dv : ClosedSubspaces D.site D.base D.base_mem X)
    (hDv : IsEffectiveCartierDivisor D.site D.base D.base_mem ⟨X, hp.1⟩ Dv) (k : ℤ)
    (α : CycleGroup D p (k + 1)) :
    chowClassCanonical.{max (u + 1) v} D p hp k (closedSubspaceCyclePushforward D p hp
        (vanishingLocus D p hp
          (associatedInvertibleSheaf D.site D.base D.base_mem ⟨X, hp.1⟩ Dv hDv)
          (canonicalSection D.site D.base D.base_mem ⟨X, hp.1⟩ Dv hDv)) k
        (gysinCycleMap D p (vanishingLocus D p hp
            (associatedInvertibleSheaf D.site D.base D.base_mem ⟨X, hp.1⟩ Dv hDv)
            (canonicalSection D.site D.base D.base_mem ⟨X, hp.1⟩ Dv hDv))
          (isGood_vanishingLocus D p hp _ _) k
          (sectionGysinRule D p hp
            (associatedInvertibleSheaf D.site D.base D.base_mem ⟨X, hp.1⟩ Dv hDv)
            (canonicalSection D.site D.base D.base_mem ⟨X, hp.1⟩ Dv hDv) k
            (associatedInvertibleSheaf_isInvertible D.site D.base D.base_mem ⟨X, hp.1⟩ Dv hDv))
          α)) =
      chowClassCanonical.{max (u + 1) v} D p hp k (firstChernCapCycleMap D p hp k
        (canonicalFirstChernRule D p hp
          (associatedInvertibleSheaf D.site D.base D.base_mem ⟨X, hp.1⟩ Dv hDv)
          (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
            (associatedInvertibleSheaf_isInvertible D.site D.base D.base_mem ⟨X, hp.1⟩ Dv hDv))
          k) α) :=
  chowClassCanonical_closedSubspaceCyclePushforward_gysinCycleMap_sectionGysinRule D p hp _
    (associatedInvertibleSheaf_isInvertible D.site D.base D.base_mem ⟨X, hp.1⟩ Dv hDv) _ k α

omit L hL s in
/-- Stacks 0ER4, in particular, in the Chow group `AlgebraicGeometry.Space.chowGroup` whose
rational equivalences quantify the embedding `R(W) → Q(𝒪^h_{W,ξ})` existentially. In Situation
0EDT let `X/B` be good and let `D ⊆ X` be an effective Cartier divisor. For every `(k+1)`-cycle
`α` on `X`

`D · α = c₁(𝒪_X(D)) ∩ α` in `CH_k(X)`,

where `D · α = i_* i^* α` is the operation of Stacks 0ER1, part (3), for the pair
`(𝒪_X(D), 1_D)` of the invertible sheaf `𝒪_X(D)` and its canonical section, whose vanishing
locus is `D` (Stacks 0847), and `c₁(𝒪_X(D)) ∩ -` is the cap product of Stacks 0EQJ. -/
theorem sectionCartierIntersection_canonicalSection_eq_canonicalFirstChernCap
    (Dv : ClosedSubspaces D.site D.base D.base_mem X)
    (hDv : IsEffectiveCartierDivisor D.site D.base D.base_mem ⟨X, hp.1⟩ Dv) (k : ℤ)
    (α : CycleGroup D p (k + 1)) :
    sectionCartierIntersection.{max (u + 1) v} D p hp
        (associatedInvertibleSheaf D.site D.base D.base_mem ⟨X, hp.1⟩ Dv hDv)
        (canonicalSection D.site D.base D.base_mem ⟨X, hp.1⟩ Dv hDv) k
        (associatedInvertibleSheaf_isInvertible D.site D.base D.base_mem ⟨X, hp.1⟩ Dv hDv)
        (isEffectiveCartierDivisor_vanishingLocus_canonicalSection D p hp Dv hDv) α =
      canonicalFirstChernCap.{u, max (u + 1) v} D p hp
        (associatedInvertibleSheaf D.site D.base D.base_mem ⟨X, hp.1⟩ Dv hDv)
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
          (associatedInvertibleSheaf_isInvertible D.site D.base D.base_mem ⟨X, hp.1⟩ Dv hDv))
        k α :=
  sectionCartierIntersection_eq_canonicalFirstChernCap.{v} D p hp _
    (associatedInvertibleSheaf_isInvertible D.site D.base D.base_mem ⟨X, hp.1⟩ Dv hDv) _ _ k α

end AlgebraicGeometry.Space

end

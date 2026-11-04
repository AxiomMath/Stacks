module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.AffineSpaceFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.AffineSpaceFibresSpreadOut
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalLocalizationSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CyclesIrreducible
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.InfiniteSumsRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.OpenRestrictionFlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalenceSmallFamilies
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RepresentedAffineSpacePullback

/-!
# Flat pullback along an affine-space fibration is surjective up to rational equivalence

In Situation 0EDT let `X, Y/B` be good and let `f : X → Y` be a quasi-compact morphism over the
base, flat of relative dimension `r`, with `X_y ≅ 𝐀^r_{κ(y)}` for every `y ∈ |Y|`. Stacks 0ERG
asserts that `f^* : CH_k(Y) → CH_{k+r}(X)` is surjective: every `α ∈ Z_{k+r}(X)` is rationally
equivalent to `f^*β` for some `β ∈ Z_k(Y)`, rational equivalence being that of Stacks 0EQ6, a
locally finite sum of principal divisors at the canonical embeddings of Stacks 0ENK
(`AlgebraicGeometry.Space.IsCanonicallyRationallyEquivalentToZeroWithin`).

The proof is the source's.

* *Reduction to `Y` integral.* Write `α = ∑ n_W [W]`. The closures `Z_W` of the images of the
  `W` form a locally finite family because `f` is quasi-compact (Stacks 0ENZ). If
  `[W] ∼_rat f_W^*β_W` on `f^{-1}(Z_W)` for `f_W : f^{-1}(Z_W) → Z_W`, then
  `β = ∑ n_W (Z_W → Y)_*β_W` works, the locally finite sum of the rational equivalences being a
  rational equivalence by Stacks 0EQ8 and the compatibility `f^*(i_*β_W) = i'_*(f_W^*β_W)` of
  flat pullback with pushforward along the closed immersion `i : Z_W → Y`.
* *Induction on `dim_δ(Y)`.* For `Y` integral there is a nonempty open `V ⊆ Y`, an affine scheme
  of the site, over which `f` is an affine-space bundle `𝐀 → V` (Stacks 07SK spreading out the
  isomorphism of the generic fibre with affine space). By Stacks 02TT on `V`,
  `α|_{f^{-1}(V)} ∼_rat f_V^*β_0`; by Stacks 0EP9 `β_0` extends to `β_1 ∈ Z_k(Y)`; by Stacks 0EQ7
  `α ∼_rat f^*β_1 + i_*γ` with `γ` a cycle on `f^{-1}(Y ∖ V)`, and `dim_δ(Y ∖ V) < dim_δ(Y)`.

## Main definitions

* `AlgebraicGeometry.Space.IsFlatPullbackSurjective`: every `(k + r)`-cycle on `X` is rationally
  equivalent to the flat pullback of a `k`-cycle on `Y`, through canonical principal divisors.
* `AlgebraicGeometry.Space.FlatPullbackClosedPushforwardCompatible`: the identity
  `f^*(i_*β) = i'_*(f'^*β)` for the inclusion `i` of a closed subspace, the closed-immersion case
  of the third assertion of Stacks 0EPD.

## Main results

* `AlgebraicGeometry.Space.eq_zero_of_forall_deltaValue_le`: `Z_{k+r}(X) = 0` when `δ_Y < k`.
* `AlgebraicGeometry.Space.flatPullbackMap_coe_locallyFiniteCycleSum`: flat pullback commutes
  with locally finite sums of cycles.
* `AlgebraicGeometry.Space.isFlatPullbackSurjective_of_forall_integralClosedSubspace`: the
  reduction to integral `Y`.
* `AlgebraicGeometry.Space.isFlatPullbackSurjective_of_isIntegralSpace`: the induction step for
  an integral base.
* `AlgebraicGeometry.Space.isFlatPullbackSurjective_of_forall_deltaValue_le_add`: the case of a
  base of bounded dimension.
* `AlgebraicGeometry.Space.isFlatPullbackSurjective_of_hasAffineSpaceFibres`: the statement of
  Stacks 0ERG, given the compatibility of flat pullback with pushforward along closed
  subspaces.

## Implementation notes

The source's `f^* : CH_k(Y) → CH_{k+r}(X)` is read on cycles: its surjectivity is the assertion
that every `α ∈ Z_{k+r}(X)` has some `β ∈ Z_k(Y)` with `f^*β - α` rationally equivalent to zero,
which does not presuppose that flat pullback preserves rational equivalence. Rational equivalence
is the source's, through the canonical embeddings of Stacks 0ENK: every rational equivalence used
— Stacks 02TT on a represented affine-space bundle, Stacks 0EQ7, the closed pushforwards and the
locally finite sums of Stacks 0EQ8 — is constructed from canonical principal divisors.

The source uses, in the reduction to an integral base and in the induction step, that flat
pullback commutes with pushforward along the inclusion of a closed subspace. That identity is
the hypothesis `AlgebraicGeometry.Space.FlatPullbackClosedPushforwardCompatible D` of the
results here; it is the closed-immersion case of the third assertion of Stacks 0EPD, and is
discharged in `StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackSurjectiveAffineFibres`.

## References

* [Stacks Project, Tag 0ERG](https://stacks.math.columbia.edu/tag/0ERG)
* [Stacks Project, Tag 0EQ7](https://stacks.math.columbia.edu/tag/0EQ7)
* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
* [Stacks Project, Tag 0EP9](https://stacks.math.columbia.edu/tag/0EP9)
* [Stacks Project, Tag 0ENZ](https://stacks.math.columbia.edu/tag/0ENZ)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Statement

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- **Flat pullback is surjective up to rational equivalence.** For a morphism `f : X → Y` of
good algebraic spaces over the base, flat of relative dimension `r`, every `(k + r)`-cycle on
`X` is rationally equivalent to the flat pullback of a `k`-cycle on `Y`: `f^*β - α` is a locally
finite sum of canonical principal divisors. This is the surjectivity of
`f^* : CH_k(Y) → CH_{k+r}(X)`, read on cycles. -/
def IsFlatPullbackSurjective (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f) (k : ℤ) : Prop :=
  ∀ α : CycleGroup D sX (k + (r : ℤ)), ∃ β : CycleGroup D sY k,
    IsCanonicallyRationallyEquivalentToZeroWithin.{u, u} D sX hX (k + (r : ℤ))
      (flatPullbackMap D sX hX sY hY f hbase r hflat hr k (k + (r : ℤ)) rfl β - α) Set.univ

/-- The compatibility `f^*(i_*β) = i'_*(f'^*β)` of flat pullback of cycles with pushforward
along the inclusion `i : Z → Y` of a closed subspace, `f' : f^{-1}(Z) → Z` being the base change
of `f` and `i' : f^{-1}(Z) → X` the inclusion, for every flat morphism `f` of good algebraic
spaces over the base. -/
def FlatPullbackClosedPushforwardCompatible : Prop :=
  ∀ ⦃X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u⦄ (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y) (hbase : f ≫ sY = sX)
    (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f) (Z : Subfunctor Y)
    (hZ : IsClosedSubspace D.site D.base D.base_mem Z) (m : ℤ) (β : CycleGroup D (Z.ι ≫ sY) m),
    flatPullbackMap D sX hX sY hY f hbase r hflat hr m (m + (r : ℤ)) rfl
        (cycleGroupClosedPushforward D hY.1 hZ.1 (D.isDecentSpace_of_isGood sY hY) hZ.2 sY hY.2.2
          (Z.ι ≫ sY) rfl m β) =
      cycleGroupClosedPushforward D hX.1
        (isClosedSubspace_preimage_of_isClosedSubspace D sX hX sY hY f Z hZ).1
        (D.isDecentSpace_of_isGood sX hX)
        (isClosedSubspace_preimage_of_isClosedSubspace D sX hX sY hY f Z hZ).2 sX hX.2.2
        ((Z.preimage f).ι ≫ sX) rfl (m + (r : ℤ))
        (flatPullbackMap D ((Z.preimage f).ι ≫ sX)
          (isGood_ι_of_isClosedSubspace D sX hX _
            (isClosedSubspace_preimage_of_isClosedSubspace D sX hX sY hY f Z hZ))
          (Z.ι ≫ sY) (isGood_ι_of_isClosedSubspace D sY hY Z hZ) (Z.fromPreimage f)
          (fromPreimage_comp_structureMorphism D sX sY f hbase Z) r
          (isFlat_and_hasRelativeDimension_fromPreimage_of_closed D sX hX sY hY f hbase Z hZ r
            hflat hr).1
          (isFlat_and_hasRelativeDimension_fromPreimage_of_closed D sX hX sY hY f hbase Z hZ r
            hflat hr).2
          m (m + (r : ℤ)) rfl β)

end Statement

section Vanishing

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)

include hX hY hbase hr in
/-- **`Z_{k+r}(X) = 0` below the dimension.** If `δ_Y ≤ d < k` at every point of `Y`, then every
`(k + r)`-cycle on `X` vanishes: an integral closed subspace of `X` has δ-dimension at most
`d + r`, the dimension function growing by at most `r` along a morphism of relative dimension
`r`. -/
theorem eq_zero_of_forall_deltaValue_le {d k : ℤ}
    (hd : ∀ y, D.deltaValue sY y ≤ d) (hdk : d < k) (α : CycleGroup D sX (k + (r : ℤ))) :
    α = 0 := by
  refine Subtype.ext (funext fun T => ?_)
  by_contra hT
  have hdim := α.2.2 T hT
  have hle := inducedDimensionValue_le_add_of_hasRelativeDimension D sX hX sY hY f hbase r hr
    (T.ambientGenericPoint D.site D.base D.base_mem)
  have hy := hd (pointsMap D.site D.base D.base_mem X f
    (T.ambientGenericPoint D.site D.base D.base_mem))
  change deltaDimension D sX T ≤ _ at hle
  change D.deltaValue sY _ ≤ d at hy
  simp only [BaseSpaceDimensionSituation.deltaValue] at hy
  omega

end Vanishing

section Sums

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)

/-- The flat pullback multiplicity at `A` vanishes away from a `Z₀` where it is nonzero. -/
private theorem flatPullbackMult_eq_zero_of_ne
    {Z₀ Z : IntegralClosedSubspace D.site D.base D.base_mem Y}
    {A : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hZ₀ : flatPullbackMult D sX hX sY hY f hbase r hflat hr Z₀ A ≠ 0) (hZ : Z ≠ Z₀) :
    flatPullbackMult D sX hX sY hY f hbase r hflat hr Z A = 0 := by
  by_contra h
  exact hZ (eq_of_flatPullbackMult_ne_zero D sX hX sY hY f hbase r hflat hr Z Z₀ A h hZ₀)

/-- **Flat pullback commutes with locally finite sums of cycles.** At an integral closed
subspace `A ⊆ X` at most one integral closed subspace `Z ⊆ Y` has `A` in `f^{-1}(Z)`, so the
coefficient of `f^*γ` at `A` is the coefficient of `γ` at `Z` times one multiplicity, which is
additive in `γ`. -/
theorem flatPullbackMap_coe_locallyFiniteCycleSum {I : Type*} (m n : ℤ) (hmn : m + (r : ℤ) = n)
    (T : I → Set (points D.site D.base D.base_mem Y)) (hT : LocallyFinite T)
    (γ : I → CycleGroup D sY m)
    (hγT : ∀ (i : I) (Z : IntegralClosedSubspace D.site D.base D.base_mem Y),
      (γ i).1 Z ≠ 0 → subspacePointSet D.site D.base D.base_mem Y Z.subspace ⊆ T i)
    (A : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn
        (locallyFiniteCycleSum D sY m T hT γ hγT)).1 A =
      ∑ᶠ i : I, (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn (γ i)).1 A := by
  simp only [flatPullbackMap_apply, locallyFiniteCycleSum_apply]
  by_cases hex : ∃ Z₀, flatPullbackMult D sX hX sY hY f hbase r hflat hr Z₀ A ≠ 0
  · obtain ⟨Z₀, hZ₀⟩ := hex
    have huniq := fun Z (hZ : Z ≠ Z₀) =>
      flatPullbackMult_eq_zero_of_ne D sX hX sY hY f hbase r hflat hr hZ₀ hZ
    rw [finsum_eq_single _ Z₀ (fun Z hZ => by rw [huniq Z hZ, mul_zero]),
      finsum_mul]
    refine finsum_congr fun i => ?_
    rw [finsum_eq_single _ Z₀ (fun Z hZ => by rw [huniq Z hZ, mul_zero])]
  · simp only [not_exists, not_not] at hex
    simp only [hex, mul_zero, finsum_zero]

/-- The coefficients at a fixed integral closed subspace of the flat pullbacks of the members of
a family of cycles supported on a locally finite family of sets are nonzero for only finitely
many members. -/
theorem finite_support_flatPullbackMap_coe {I : Type*} (m n : ℤ) (hmn : m + (r : ℤ) = n)
    (T : I → Set (points D.site D.base D.base_mem Y)) (hT : LocallyFinite T)
    (γ : I → CycleGroup D sY m)
    (hγT : ∀ (i : I) (Z : IntegralClosedSubspace D.site D.base D.base_mem Y),
      (γ i).1 Z ≠ 0 → subspacePointSet D.site D.base D.base_mem Y Z.subspace ⊆ T i)
    (A : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (Function.support fun i : I =>
      (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn (γ i)).1 A).Finite := by
  by_cases hex : ∃ Z₀, flatPullbackMult D sX hX sY hY f hbase r hflat hr Z₀ A ≠ 0
  · obtain ⟨Z₀, hZ₀⟩ := hex
    refine (finite_support_locallyFiniteCycleCoeff D sY m T hT γ hγT Z₀).subset fun i hi => ?_
    simp only [Function.mem_support, flatPullbackMap_apply] at hi ⊢
    intro h0
    refine hi (finsum_eq_zero_of_forall_eq_zero fun Z => ?_)
    by_cases hZ : Z = Z₀
    · rw [hZ, h0, zero_mul]
    · rw [flatPullbackMult_eq_zero_of_ne D sX hX sY hY f hbase r hflat hr hZ₀ hZ, mul_zero]
  · simp only [not_exists, not_not] at hex
    refine Set.finite_empty.subset fun i hi => hi ?_
    simp only [flatPullbackMap_apply, hex, mul_zero, finsum_zero]

end Sums

section Reduction

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)

/-- The pushforward along a closed immersion of the cycle of an integral closed subspace is the
cycle of its image. -/
theorem cycleGroupClosedPushforward_integralCycle_coe {i : X ⟶ Y}
    (hi : IsClosedImmersion D.site D.base D.base_mem i) (hic : i ≫ sY = sX) (k : ℤ)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) (hW : deltaDimension D sX W = k) :
    (cycleGroupClosedPushforward D hY.1 hX.1 (D.isDecentSpace_of_isGood sY hY) hi sY hY.2.2 sX
        hic k (integralCycle D sX k W hW)).1 =
      integralCycleCoeff D (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hY.1 hX.1
        (D.isDecentSpace_of_isGood sY hY) hi W) := by
  classical
  funext T
  show cycleClosedPushforward D hY.1 hX.1 _ hi (integralCycleCoeff D W) T = _
  by_cases hT : ∃ T0, IntegralClosedSubspace.pushforward D.site D.base D.base_mem hY.1 hX.1
      (D.isDecentSpace_of_isGood sY hY) hi T0 = T
  · obtain ⟨T0, rfl⟩ := hT
    rw [cycleClosedPushforward_apply_pushforward]
    by_cases h : T0 = W
    · rw [h, integralCycleCoeff_self, integralCycleCoeff_self]
    · rw [integralCycleCoeff_eq_zero D W h, integralCycleCoeff_eq_zero]
      exact fun h' => h (IntegralClosedSubspace.injective_pushforward D.site D.base D.base_mem
        hY.1 hX.1 _ hi h')
  · rw [cycleClosedPushforward_apply_of_forall_ne D hY.1 hX.1 _ hi _ T fun T0 hT0 => hT ⟨T0, hT0⟩,
      integralCycleCoeff_eq_zero]
    rintro rfl
    exact hT ⟨W, rfl⟩

variable (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)

/-- **Stacks 0ERG, the reduction to `Y` integral.** If for every integral closed subspace
`Z ⊆ Y` flat pullback along `f^{-1}(Z) → Z` is surjective up to rational equivalence, then so is
flat pullback along `f`, provided `f` is quasi-compact and flat pullback commutes with
pushforward along closed subspaces.

For `α = ∑ n_W [W]` let `Z_W` be the closure of the image of `W`; the family `{Z_W}` is locally
finite because `f` is quasi-compact (Stacks 0ENZ). Lifting `W` to `f^{-1}(Z_W)` and choosing
`β_W` with `f_W^*β_W ∼_rat [W]` there, `β = ∑ n_W (Z_W → Y)_*β_W` has
`f^*β - α = ∑ n_W ((f^{-1}(Z_W) → X)_*(f_W^*β_W - [W]))`, a locally finite sum of cycles
rationally equivalent to zero within the `f^{-1}(Z_W)`, hence rationally equivalent to zero by
Stacks 0EQ8. -/
theorem isFlatPullbackSurjective_of_forall_integralClosedSubspace
    (hbc : FlatPullbackClosedPushforwardCompatible D)
    (hqc : IsQuasiCompact D.site D.base D.base_mem f) (k : ℤ)
    (hZ : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem Y,
      IsFlatPullbackSurjective D ((Z.subspace.preimage f).ι ≫ sX)
        (isGood_ι_of_isClosedSubspace D sX hX _
          (isClosedSubspace_preimage_of_isClosedSubspace D sX hX sY hY f Z.subspace
            Z.isClosedSubspace))
        (Z.subspace.ι ≫ sY) (isGood_ι_of_isClosedSubspace D sY hY Z.subspace Z.isClosedSubspace)
        (Z.subspace.fromPreimage f)
        (fromPreimage_comp_structureMorphism D sX sY f hbase Z.subspace) r
        (isFlat_and_hasRelativeDimension_fromPreimage_of_closed D sX hX sY hY f hbase
          Z.subspace Z.isClosedSubspace r hflat hr).1
        (isFlat_and_hasRelativeDimension_fromPreimage_of_closed D sX hX sY hY f hbase
          Z.subspace Z.isClosedSubspace r hflat hr).2 k) :
    IsFlatPullbackSurjective D sX hX sY hY f hbase r hflat hr k := by
  classical
  intro α
  have hXdec := D.isDecentSpace_of_isGood sX hX
  have hYdec := D.isDecentSpace_of_isGood sY hY
  let I := {W : IntegralClosedSubspace D.site D.base D.base_mem X // α.1 W ≠ 0}
  let ZW : I → IntegralClosedSubspace D.site D.base D.base_mem Y := fun W =>
    IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1 hYdec f W.1
  have hPc : ∀ W : I, IsClosedSubspace D.site D.base D.base_mem ((ZW W).subspace.preimage f) :=
    fun W => isClosedSubspace_preimage_of_isClosedSubspace D sX hX sY hY f _
      (ZW W).isClosedSubspace
  have hPgood : ∀ W : I, D.IsGood (((ZW W).subspace.preimage f).ι ≫ sX) := fun W =>
    isGood_ι_of_isClosedSubspace D sX hX _ (hPc W)
  have hPpts : ∀ W : I, subspacePointSet D.site D.base D.base_mem X
      ((ZW W).subspace.preimage f) = pointsMap D.site D.base D.base_mem X f ⁻¹'
        subspacePointSet D.site D.base D.base_mem Y (ZW W).subspace := fun W =>
    subspacePointSet_preimage D.site D.base D.base_mem f _
  -- each `W` lies in the inverse image of the closure of its image
  have hsubW : ∀ W : I, subspacePointSet D.site D.base D.base_mem X W.1.subspace ⊆
      Set.range (pointsMap D.site D.base D.base_mem _ ((ZW W).subspace.preimage f).ι) := by
    intro W x hx
    show x ∈ subspacePointSet D.site D.base D.base_mem X ((ZW W).subspace.preimage f)
    rw [hPpts W, Set.mem_preimage, IntegralClosedSubspace.subspacePointSet_closureImage]
    exact subset_closure ⟨x, hx, rfl⟩
  choose W' hW' using fun W : I => IntegralClosedSubspace.exists_pushforward_eq D.site D.base
    D.base_mem hX.1 (hPc W).1 hXdec (D.isDecentSpace_of_isGood _ (hPgood W)) (hPc W).2 W.1
    (hsubW W)
  have hW'dim : ∀ W : I, deltaDimension D (((ZW W).subspace.preimage f).ι ≫ sX) (W' W) =
      k + (r : ℤ) := fun W => by
    rw [← IntegralClosedSubspace.deltaDimension_pushforward D sX hX.2.2 hX.1 (hPc W).1 hXdec
      (hPc W).2 (W' W), hW' W]
    exact α.2.2 W.1 W.2
  choose β' hβ' using fun W : I => hZ (ZW W)
    (integralCycle D _ (k + (r : ℤ)) (W' W) (hW'dim W))
  -- the summands of `β`
  let γ : I → CycleGroup D sY k := fun W => α.1 W.1 •
    cycleGroupClosedPushforward D hY.1 (ZW W).isClosedSubspace.1 hYdec (ZW W).isClosedSubspace.2
      sY hY.2.2 ((ZW W).subspace.ι ≫ sY) rfl k (β' W)
  have hγT : ∀ (W : I) (Z : IntegralClosedSubspace D.site D.base D.base_mem Y),
      (γ W).1 Z ≠ 0 → subspacePointSet D.site D.base D.base_mem Y Z.subspace ⊆
        subspacePointSet D.site D.base D.base_mem Y (ZW W).subspace := by
    intro W Z hZne
    have hne : (cycleGroupClosedPushforward D hY.1 (ZW W).isClosedSubspace.1 hYdec
        (ZW W).isClosedSubspace.2 sY hY.2.2 ((ZW W).subspace.ι ≫ sY) rfl k (β' W)).1 Z ≠ 0 := by
      intro h0
      apply hZne
      simp only [γ, AddSubgroup.coe_zsmul, Pi.smul_apply, h0, smul_zero]
    by_cases hT : ∃ T0, IntegralClosedSubspace.pushforward D.site D.base D.base_mem hY.1
        (ZW W).isClosedSubspace.1 hYdec (ZW W).isClosedSubspace.2 T0 = Z
    · obtain ⟨T0, rfl⟩ := hT
      rw [IntegralClosedSubspace.subspacePointSet_pushforward]
      rintro _ ⟨y, -, rfl⟩
      exact ⟨y, rfl⟩
    · exact absurd (cycleClosedPushforward_apply_of_forall_ne D hY.1 _ hYdec _ _ Z
        fun T0 hT0 => hT ⟨T0, hT0⟩) hne
  -- local finiteness of the closures of the images
  have hαlf : LocallyFinite fun W : I => subspacePointSet D.site D.base D.base_mem X W.1.subspace :=
    by
      have h := α.2.1.comp_injective (Subtype.val_injective (p := fun W => α.1 W ≠ 0))
      refine h.subset fun W => ?_
      simp only [Function.comp_apply, if_neg W.2, subset_refl]
  have hlf : LocallyFinite fun W : I => subspacePointSet D.site D.base D.base_mem Y
      (ZW W).subspace := by
    have h := (locallyFinite_closure_image_pointsMap D sX hX sY hY hbase hqc
      (fun W : I => subspacePointSet D.site D.base D.base_mem X W.1.subspace)
      (fun W => isClosed_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem hX.1 W.1)
      hαlf).1
    refine h.subset fun W => ?_
    rw [IntegralClosedSubspace.subspacePointSet_closureImage]
  refine ⟨locallyFiniteCycleSum D sY k _ hlf γ hγT, ?_⟩
  -- the rational equivalences on the inverse images
  have hRW : ∀ W : I, IsCanonicallyRationallyEquivalentToZeroWithin.{u, u} D sX hX (k + (r : ℤ))
      (flatPullbackMap D sX hX sY hY f hbase r hflat hr k (k + (r : ℤ)) rfl
          (cycleGroupClosedPushforward D hY.1 (ZW W).isClosedSubspace.1 hYdec
            (ZW W).isClosedSubspace.2 sY hY.2.2 ((ZW W).subspace.ι ≫ sY) rfl k (β' W)) -
        integralCycle D sX (k + (r : ℤ)) W.1 (α.2.2 W.1 W.2))
      (subspacePointSet D.site D.base D.base_mem X ((ZW W).subspace.preimage f)) := by
    intro W
    have h1 := ((hβ' W).closedPushforward (sT := ((ZW W).subspace.preimage f).ι ≫ sX)
      (hX := hX) (hPgood W) (hj := (hPc W).2) rfl).mono (by rw [Set.image_univ])
    rw [map_sub, ← hbc sX hX sY hY f hbase r hflat hr (ZW W).subspace (ZW W).isClosedSubspace k
      (β' W)] at h1
    convert h1 using 2
    refine Subtype.ext ?_
    rw [cycleGroupClosedPushforward_integralCycle_coe D _ (hPgood W) sX hX (hPc W).2 rfl
      (k + (r : ℤ)) (W' W) (hW'dim W), hW' W]
    rfl
  have hfam : LocallyFinite fun W : I => subspacePointSet D.site D.base D.base_mem X
      ((ZW W).subspace.preimage f) := by
    have h := hlf.preimage_continuous (continuous_pointsMap D.site D.base D.base_mem f)
    refine h.subset fun W => ?_
    rw [hPpts W]
  have hrat := isCycleFamilySumWithin_finsum D sX hX (k + (r : ℤ)) _ hfam
    (fun W => α.1 W.1 • (flatPullbackMap D sX hX sY hY f hbase r hflat hr k (k + (r : ℤ)) rfl
          (cycleGroupClosedPushforward D hY.1 (ZW W).isClosedSubspace.1 hYdec
            (ZW W).isClosedSubspace.2 sY hY.2.2 ((ZW W).subspace.ι ≫ sY) rfl k (β' W)) -
        integralCycle D sX (k + (r : ℤ)) W.1 (α.2.2 W.1 W.2)))
    (fun W => (hRW W).zsmul neg_mem_canonicalPrincipalDivisors (α.1 W.1))
    (α := flatPullbackMap D sX hX sY hY f hbase r hflat hr k
      (k + (r : ℤ)) rfl (locallyFiniteCycleSum D sY k _ hlf γ hγT) - α) (fun A => ?_)
  · exact IsCycleFamilySumWithin.down D (hrat.mono (Set.subset_univ _))
  -- the coefficient identity
  have hsum := flatPullbackMap_coe_locallyFiniteCycleSum D sX hX sY hY f hbase r hflat hr k
    (k + (r : ℤ)) rfl _ hlf γ hγT A
  have hfin₁ := finite_support_flatPullbackMap_coe D sX hX sY hY f hbase r hflat hr k
    (k + (r : ℤ)) rfl _ hlf γ hγT A
  have hα : α.1 A = ∑ᶠ W : I, α.1 W.1 * integralCycleCoeff D W.1 A := by
    by_cases hA : α.1 A = 0
    · rw [hA]
      refine (finsum_eq_zero_of_forall_eq_zero fun W => ?_).symm
      have hWA : A ≠ W.1 := fun h => W.2 (h ▸ hA)
      rw [integralCycleCoeff_eq_zero D W.1 hWA, mul_zero]
    · rw [finsum_eq_single _ ⟨A, hA⟩ (fun W hW => by
        have hWA : A ≠ W.1 := fun h => hW (Subtype.ext h.symm)
        rw [integralCycleCoeff_eq_zero D W.1 hWA, mul_zero]),
        integralCycleCoeff_self, mul_one]
  have hfin₂ : (Function.support fun W : I => α.1 W.1 * integralCycleCoeff D W.1 A).Finite := by
    refine Set.Subsingleton.finite fun W₁ hW₁ W₂ hW₂ => Subtype.ext ?_
    have key : ∀ W : I, W ∈ Function.support (fun W : I => α.1 W.1 * integralCycleCoeff D W.1 A) →
        W.1 = A := fun W hW => by
      by_contra hWA
      exact hW (show α.1 W.1 * integralCycleCoeff D W.1 A = 0 by
        rw [integralCycleCoeff_eq_zero D W.1 (Ne.symm hWA), mul_zero])
    rw [key W₁ hW₁, key W₂ hW₂]
  have hγc : ∀ W : I, (flatPullbackMap D sX hX sY hY f hbase r hflat hr k (k + (r : ℤ)) rfl
      (γ W)).1 A = α.1 W.1 * (flatPullbackMap D sX hX sY hY f hbase r hflat hr k (k + (r : ℤ))
        rfl (cycleGroupClosedPushforward D hY.1 (ZW W).isClosedSubspace.1 hYdec
          (ZW W).isClosedSubspace.2 sY hY.2.2 ((ZW W).subspace.ι ≫ sY) rfl k (β' W))).1 A :=
    fun W => by simp only [γ, map_zsmul, AddSubgroup.coe_zsmul, Pi.smul_apply, smul_eq_mul]
  rw [AddSubgroupClass.coe_sub, Pi.sub_apply, hsum, hα, ← finsum_sub_distrib hfin₁ hfin₂]
  refine finsum_congr fun W => ?_
  rw [hγc W]
  simp only [AddSubgroup.coe_zsmul, AddSubgroupClass.coe_sub, Pi.smul_apply, Pi.sub_apply,
    smul_eq_mul, integralCycle_coe, mul_sub]

end Reduction

section Integral

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- An open immersion into a good algebraic space over the base is good over the base. -/
theorem isGood_comp_of_isOpenImmersion {U : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (hU : IsAlgebraicSpace D.site D.base D.base_mem U)
    {j : U ⟶ X} (hj : IsOpenImmersion D.site D.base D.base_mem j) : D.IsGood (j ≫ sX) :=
  ⟨hU,
    isQuasiSeparated_comp D.site D.base D.base_mem hU hX.1 _ _
      (isQuasiSeparated_of_mono D.site D.base D.base_mem j
        (mono_of_isOpenImmersion D.site D.base D.base_mem j hj)) hX.2.1,
    isLocallyOfFiniteType_comp D.site D.base D.base_mem hU hX.1 D.isAlgebraicSpace _ _
      (isLocallyOfFiniteType_of_isImmersion D.site D.base D.base_mem j
        (isImmersion_of_isOpenImmersion D.site D.base D.base_mem hj)) hX.2.2⟩

variable (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)

/-- The δ-value of a closed subspace's inclusion composed with the structure morphism is the
δ-value at the image point. -/
private theorem deltaValue_ι_comp_of_isClosedSubspace (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    {Z : Subfunctor Y} (hZ : IsClosedSubspace D.site D.base D.base_mem Z)
    (z : points D.site D.base D.base_mem _) :
    D.deltaValue (Z.ι ≫ sY) z = D.deltaValue sY (pointsMap D.site D.base D.base_mem _ Z.ι z) :=
  D.deltaValue_comp_of_isLocallyQuasiFinite hZ.1 hY.1 Z.ι sY
    (isLocallyQuasiFinite_of_isImmersion D.site D.base D.base_mem Z.ι
      (isImmersion_of_isClosedImmersion D.site D.base D.base_mem hZ.2)) hY.2.2 z

/-- **Stacks 0ERG for an integral base, the induction step on `dim_δ(Y)`.** Let `Y` be integral
with `δ_Y ≤ d`, and suppose the lemma holds over every base on which `δ ≤ d - 1`. Over a nonempty
open `V ⊆ Y` which is an affine scheme of the site, `f` is an affine-space bundle `𝐀 → V`; by
Stacks 02TT there `α|_𝐀 ∼_rat f_V^*β_0`, by Stacks 0EP9 `β_0 = β_1|_V`, and by Stacks 0EQ7
`f^*β_1 ∼_rat α + i_*γ` for a cycle `γ` on the inverse image of the closed complement `Y'` of `V`,
on which `δ ≤ d - 1` because the generic point of `Y` lies in `V`. -/
theorem isFlatPullbackSurjective_of_isIntegralSpace
    (hbc : FlatPullbackClosedPushforwardCompatible D)
    (hqc : IsQuasiCompact D.site D.base D.base_mem f) (hfib : HasAffineSpaceFibres D sY hY f r)
    (hint : IsIntegralSpace D.site D.base D.base_mem Y) (k d : ℤ)
    (hd : ∀ y, D.deltaValue sY y ≤ d)
    (IH : ∀ ⦃X' Y' : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u⦄ (sX' : X' ⟶ D.space)
      (hX' : D.IsGood sX') (sY' : Y' ⟶ D.space) (hY' : D.IsGood sY') (f' : X' ⟶ Y')
      (hbase' : f' ≫ sY' = sX') (hflat' : IsFlat D.site D.base D.base_mem f')
      (hr' : HasRelativeDimension r D.site D.base D.base_mem f'),
      IsQuasiCompact D.site D.base D.base_mem f' → HasAffineSpaceFibres D sY' hY' f' r →
        (∀ y, D.deltaValue sY' y ≤ d - 1) →
          IsFlatPullbackSurjective D sX' hX' sY' hY' f' hbase' r hflat' hr' k) :
    IsFlatPullbackSurjective D sX hX sY hY f hbase r hflat hr k := by
  classical
  intro α
  obtain ⟨V, A, jY, jX, g, hjY, hne, sq, hg₁, hg₂, hg₃, hg₄⟩ :=
    exists_isPullback_isAffineSpaceBundle_of_isIntegralSpace D sX hX sY hY f hbase r hqc hfib hint
  have hVsp := isAlgebraicSpace_yoneda D.site D.base D.base_mem V
  have hAsp := isAlgebraicSpace_yoneda D.site D.base D.base_mem A
  have hjX : IsOpenImmersion D.site D.base D.base_mem jX :=
    isOpenImmersion_of_isPullback D.site D.base D.base_mem
      (isPullback_homMk D.site D.base D.base_mem hVsp hX.1 hY.1 hAsp sq.flip) hjY
  have hV := isGood_comp_of_isOpenImmersion D sY hY hVsp hjY
  have hA := isGood_comp_of_isOpenImmersion D sX hX hAsp hjX
  have hgbase : yoneda.map g ≫ jY ≫ sY = jX ≫ sX := by
    rw [← Category.assoc, ← sq.w, Category.assoc, hbase]
  have hgflat := isFlat_yoneda_map_of_flat (D := D) g
  have hgr := (hasRelativeDimension_yoneda_map_iff D.site D.base D.base_mem g r).2 hg₃
  -- Stacks 02TT on the bundle
  obtain ⟨β₀, hβ₀⟩ :=
    exists_isCanonicallyRationallyEquivalentToZeroWithin_flatPullbackMap_sub_of_isAffineSpaceBundle
      g r hg₃ hg₄ (jY ≫ sY) hV (jX ≫ sX) hA hgbase k
      (cycleGroupRestrict D sX hX (jX ≫ sX) hA hjX rfl (k + (r : ℤ)) α)
  -- Stacks 0EP9
  obtain ⟨β₁, hβ₁⟩ := cycleGroupRestrict_surjective D sY hY (jY ≫ sY) hV hjY rfl k β₀
  have hres := cycleGroupRestrict_flatPullbackMap D sX hX sY hY (jX ≫ sX) hA (jY ≫ sY) hV hbase r
    hflat hr hgbase hgflat hgr hjX rfl hjY rfl sq.w k β₁
  -- the closed complement of `V` and its inverse image
  set F : Set (points D.site D.base D.base_mem Y) :=
    (Set.range (pointsMap D.site D.base D.base_mem _ jY))ᶜ with hF
  have hFc : IsClosed F :=
    (isOpen_range_pointsMap_of_isOpenImmersion D.site D.base D.base_mem jY hjY).isClosed_compl
  obtain ⟨Y', hY'c, hY'pts⟩ : ∃ Y' : Subfunctor Y, IsClosedSubspace D.site D.base D.base_mem Y' ∧
      Set.range (pointsMap D.site D.base D.base_mem Y'.toFunctor Y'.ι) = F :=
    ⟨_, isClosedSubspace_reducedClosedSubspace D.site D.base D.base_mem Y hY.1 F hFc,
      range_pointsMap_ι_reducedClosedSubspace D.site D.base D.base_mem Y hY.1 F hFc⟩
  have hX'c := isClosedSubspace_preimage_of_isClosedSubspace D sX hX sY hY f Y' hY'c
  have hY'good := isGood_ι_of_isClosedSubspace D sY hY Y' hY'c
  have hX'good := isGood_ι_of_isClosedSubspace D sX hX _ hX'c
  have hcomp : Set.range (pointsMap D.site D.base D.base_mem _ (Y'.preimage f).ι) =
      (Set.range (pointsMap D.site D.base D.base_mem _ jX))ᶜ := by
    have h₁ := subspacePointSet_preimage D.site D.base D.base_mem f Y'
    have h₂ := preimage_image_pointsMap_of_isPullback D.site D.base D.base_mem sq.flip Set.univ
    simp only [Set.image_univ, Set.preimage_univ] at h₂
    show subspacePointSet D.site D.base D.base_mem X (Y'.preimage f) = _
    rw [h₁, ← h₂, subspacePointSet, hY'pts, hF, Set.preimage_compl]
  -- Stacks 0EQ7
  obtain ⟨γ, hγ⟩ :=
    exists_isCanonicallyRationallyEquivalentToZeroWithin_sub_add_cycleGroupClosedPushforward.{u, u}
      D sX hX ((Y'.preimage f).ι ≫ sX) hX'good (jX ≫ sX) hA hX'c.2 rfl hjX rfl hcomp
      (k + (r : ℤ)) (flatPullbackMap D sX hX sY hY f hbase r hflat hr k (k + (r : ℤ)) rfl β₁) α
      (by rw [hres, hβ₁]; exact hβ₀)
  -- the induction hypothesis on the complement
  have hη : ∃ η, IsGenericPoint η (Set.univ : Set (points D.site D.base D.base_mem Y)) := by
    have := quasiSober_points_of_isGood D sY hY
    have := hint.2.2
    exact ⟨_root_.genericPoint _, _root_.genericPoint_spec _⟩
  obtain ⟨η, hη⟩ := hη
  have hηV : η ∈ Set.range (pointsMap D.site D.base D.base_mem _ jY) :=
    (hη.mem_open_set_iff
      (isOpen_range_pointsMap_of_isOpenImmersion D.site D.base D.base_mem jY hjY)).2
      (by simpa using hne)
  have hdY' : ∀ y, D.deltaValue (Y'.ι ≫ sY) y ≤ d - 1 := by
    intro y
    rw [deltaValue_ι_comp_of_isClosedSubspace D sY hY hY'c]
    have hyF : pointsMap D.site D.base D.base_mem _ Y'.ι y ∈ F := by
      rw [← hY'pts]
      exact ⟨y, rfl⟩
    have hne' : pointsMap D.site D.base D.base_mem _ Y'.ι y ≠ η := fun h => hyF (h ▸ hηV)
    have := deltaValue_lt_of_isGenericPoint D sY hY hη _ hne'
    have := hd η
    omega
  have hf' := isFlat_and_hasRelativeDimension_fromPreimage_of_closed D sX hX sY hY f hbase Y'
    hY'c r hflat hr
  obtain ⟨β', hβ'⟩ := IH _ hX'good _ hY'good (Y'.fromPreimage f)
    (fromPreimage_comp_structureMorphism D sX sY f hbase Y') hf'.1 hf'.2
    (isQuasiCompact_fromPreimage D f Y' hqc) (hfib.fromPreimage D sY hY f Y' hY'c) hdY' γ
  -- assemble
  refine ⟨β₁ - cycleGroupClosedPushforward D hY.1 hY'c.1 (D.isDecentSpace_of_isGood sY hY) hY'c.2
    sY hY.2.2 (Y'.ι ≫ sY) rfl k β', ?_⟩
  have hpush := (hβ'.closedPushforward (sT := (Y'.preimage f).ι ≫ sX) (hX := hX) hX'good
    (hj := hX'c.2) rfl).mono (Set.subset_univ _)
  rw [map_sub] at hpush
  have key : flatPullbackMap D sX hX sY hY f hbase r hflat hr k (k + (r : ℤ)) rfl
      (β₁ - cycleGroupClosedPushforward D hY.1 hY'c.1 (D.isDecentSpace_of_isGood sY hY) hY'c.2
        sY hY.2.2 (Y'.ι ≫ sY) rfl k β') - α =
      (flatPullbackMap D sX hX sY hY f hbase r hflat hr k (k + (r : ℤ)) rfl β₁ -
        (α + cycleGroupClosedPushforward D hX.1 hX'c.1 (D.isDecentSpace_of_isGood sX hX) hX'c.2 sX
          hX.2.2 ((Y'.preimage f).ι ≫ sX) rfl (k + (r : ℤ)) γ)) -
      (cycleGroupClosedPushforward D hX.1 hX'c.1 (D.isDecentSpace_of_isGood sX hX) hX'c.2 sX
          hX.2.2 ((Y'.preimage f).ι ≫ sX) rfl (k + (r : ℤ))
          (flatPullbackMap D ((Y'.preimage f).ι ≫ sX) hX'good (Y'.ι ≫ sY) hY'good
            (Y'.fromPreimage f) (fromPreimage_comp_structureMorphism D sX sY f hbase Y') r hf'.1
            hf'.2 k (k + (r : ℤ)) rfl β') -
        cycleGroupClosedPushforward D hX.1 hX'c.1 (D.isDecentSpace_of_isGood sX hX) hX'c.2 sX
          hX.2.2 ((Y'.preimage f).ι ≫ sX) rfl (k + (r : ℤ)) γ) := by
    rw [map_sub, hbc sX hX sY hY f hbase r hflat hr Y' hY'c k β']
    abel
  rw [key]
  exact hγ.sub hpush neg_mem_canonicalPrincipalDivisors

end Integral

section Induction

variable (D : BaseSpaceDimensionSituation.{u})

/-- **Stacks 0ERG over a base of bounded dimension.** Flat pullback along a quasi-compact
morphism, flat of relative dimension `r` with affine `r`-space fibres, is surjective up to
rational equivalence onto `(k + r)`-cycles whenever `δ_Y ≤ k - 1 + n`, by induction on `n`: for
`n = 0` there are no nonzero `(k + r)`-cycles, and the induction step is the reduction to
integral closed subspaces of `Y` followed by the integral case. -/
theorem isFlatPullbackSurjective_of_forall_deltaValue_le_add
    (hbc : FlatPullbackClosedPushforwardCompatible D) (r : ℕ) (k : ℤ) (n : ℕ) :
    ∀ ⦃X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u⦄ (sX : X ⟶ D.space)
      (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y)
      (hbase : f ≫ sY = sX) (hflat : IsFlat D.site D.base D.base_mem f)
      (hr : HasRelativeDimension r D.site D.base D.base_mem f),
      IsQuasiCompact D.site D.base D.base_mem f → HasAffineSpaceFibres D sY hY f r →
        (∀ y, D.deltaValue sY y ≤ k - 1 + n) →
          IsFlatPullbackSurjective D sX hX sY hY f hbase r hflat hr k := by
  induction n with
  | zero =>
    intro X Y sX hX sY hY f hbase hflat hr _ _ hd α
    refine ⟨0, ?_⟩
    rw [map_zero, eq_zero_of_forall_deltaValue_le D sX hX sY hY f hbase r hr
      (d := k - 1) (fun y => by simpa using hd y) (by omega) α, sub_zero]
    exact isCycleFamilySumWithin_zero D sX hX _ Set.univ
  | succ n ih =>
    intro X Y sX hX sY hY f hbase hflat hr hqc hfib hd
    refine isFlatPullbackSurjective_of_forall_integralClosedSubspace D sX hX sY hY f hbase r
      hflat hr hbc hqc k fun Z => ?_
    have hf' := isFlat_and_hasRelativeDimension_fromPreimage_of_closed D sX hX sY hY f hbase
      Z.subspace Z.isClosedSubspace r hflat hr
    refine isFlatPullbackSurjective_of_isIntegralSpace D _ _ _ _ _ _ r hf'.1 hf'.2 hbc
      (isQuasiCompact_fromPreimage D f Z.subspace hqc)
      (hfib.fromPreimage D sY hY f Z.subspace Z.isClosedSubspace) Z.isIntegralSpace k
      (k - 1 + ((n + 1 : ℕ) : ℤ)) (fun z => ?_) ?_
    · rw [deltaValue_ι_comp_of_isClosedSubspace D sY hY Z.isClosedSubspace]
      exact hd _
    · intro X' Y' sX' hX' sY' hY' f' hbase' hflat' hr' hqc' hfib' hd'
      exact ih sX' hX' sY' hY' f' hbase' hflat' hr' hqc' hfib' fun y => by
        have := hd' y
        push_cast at this
        omega

end Induction

section Main

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)

/-- **Stacks 0ERG, granted the compatibility of flat pullback with closed pushforward.** In
Situation 0EDT let `X, Y/B` be good and let `f : X → Y` be a quasi-compact morphism over the base,
flat of relative dimension `r`, with `X_y ≅ 𝐀^r_{κ(y)}` for every `y ∈ |Y|`. Then for every
`k ∈ ℤ` and every `α ∈ Z_{k+r}(X)` there is `β ∈ Z_k(Y)` with `f^*β - α` rationally equivalent
to zero: `f^* : CH_k(Y) → CH_{k+r}(X)` is surjective.

By the reduction to integral closed subspaces `Z ⊆ Y`, it suffices to treat `f^{-1}(Z) → Z`,
over which `δ` is bounded by its value at the generic point of `Z`; there the bounded case
applies. -/
theorem isFlatPullbackSurjective_of_hasAffineSpaceFibres
    (hbc : FlatPullbackClosedPushforwardCompatible D)
    (hqc : IsQuasiCompact D.site D.base D.base_mem f) (hfib : HasAffineSpaceFibres D sY hY f r)
    (k : ℤ) : IsFlatPullbackSurjective D sX hX sY hY f hbase r hflat hr k := by
  refine isFlatPullbackSurjective_of_forall_integralClosedSubspace D sX hX sY hY f hbase r hflat
    hr hbc hqc k fun Z => ?_
  have hf' := isFlat_and_hasRelativeDimension_fromPreimage_of_closed D sX hX sY hY f hbase
    Z.subspace Z.isClosedSubspace r hflat hr
  have hZgood := isGood_ι_of_isClosedSubspace D sY hY Z.subspace Z.isClosedSubspace
  set dZ := D.deltaValue (Z.subspace.ι ≫ sY) (Z.genericPoint D.site D.base D.base_mem)
  refine isFlatPullbackSurjective_of_forall_deltaValue_le_add D hbc r k (dZ - k + 1).toNat _ _ _
    _ _ _ hf'.1 hf'.2 (isQuasiCompact_fromPreimage D f Z.subspace hqc)
    (hfib.fromPreimage D sY hY f Z.subspace Z.isClosedSubspace) fun z => ?_
  have hle : D.deltaValue (Z.subspace.ι ≫ sY) z ≤ dZ := by
    by_cases hz : z = Z.genericPoint D.site D.base D.base_mem
    · rw [hz]
    · exact (deltaValue_lt_of_isGenericPoint D _ hZgood
        (Z.closure_singleton_genericPoint D.site D.base D.base_mem) z hz).le
  omega

end Main

end AlgebraicGeometry.Space

end

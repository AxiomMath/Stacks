module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatCompositeRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackFirstChernCap

/-!
# Flat pullback of cycles

In Situation 0EDT let `X/B` and `Y/B` be good and let `f : X ⟶ Y` be a morphism over the base which
is flat of relative dimension `r`. Stacks 0EP8 defines the *flat pullback* of cycles along `f` in
three steps.

Part (1): for an integral closed subspace `W ⊆ Y` of δ-dimension `k`, `f^*[W]` is the `(k+r)`-cycle
of the scheme-theoretic inverse image,

`f^*[W] = [f^{-1}(W)]_{k+r}`,

which is legitimate because `dim_δ(f^{-1}(W)) ≤ k + r`.

Part (2): for a general `k`-cycle `α = ∑ n_i [W_i]` the flat pullback is `f^*α = ∑ n_i f^*[W_i]`, a
locally finite sum.

Part (3): the resulting map is a homomorphism `f^* : Z_k(Y) → Z_{k+r}(X)` of abelian groups.

The three steps are assembled into an inhabitant of the bundled
`AlgebraicGeometry.Space.FlatCyclePullback`.

## Main definitions

* `AlgebraicGeometry.Space.flatPullbackIntegralCycle`: the cycle `f^*[W] = [f^{-1}(W)]_{k+r}` of
  the inverse image of an integral closed subspace.
* `AlgebraicGeometry.Space.flatPullbackMult`: the multiplicity of an integral closed subspace
  `T ⊆ X` in `f^{-1}(W)`, that is the coefficient of `T` in `f^*[W]`.
* `AlgebraicGeometry.Space.flatPullbackCoeff`: the coefficient family of `f^*α`.
* `AlgebraicGeometry.Space.flatPullbackMap`: the flat pullback as a homomorphism `Z_m(Y) →+ Z_n(X)`
  for `m + r = n`.
* `AlgebraicGeometry.Space.flatCyclePullback`: the flat pullback, as an inhabitant of
  `AlgebraicGeometry.Space.FlatCyclePullback`.
* `AlgebraicGeometry.Space.flatCyclePullbackComp`: the same construction along a composite of flat
  morphisms, at the degree shift `r + s`.

## Main results

* `AlgebraicGeometry.Space.deltaDimensionSubspace_integralClosedSubspace`: the δ-dimension of an
  integral closed subspace, read as a closed subspace, is its δ-dimension as an integral closed
  subspace.
* `AlgebraicGeometry.Space.deltaDimensionSubspace_preimage_integralClosedSubspace_le`: the bound
  `dim_δ(f^{-1}(W)) ≤ dim_δ(W) + r` for an integral closed subspace `W`.
* `AlgebraicGeometry.Space.deltaDimension_eq_of_flatPullbackMult_ne_zero`: a subspace occurring in
  `f^*[W]` has δ-dimension `dim_δ(W) + r`.
* `AlgebraicGeometry.Space.subspacePointSet_subset_of_flatPullbackMult_ne_zero`: a subspace
  occurring in `f^*[W]` is carried by `f^{-1}(|W|)`.
* `AlgebraicGeometry.Space.finite_support_flatPullbackTerm`: at a fixed integral closed subspace of
  `X` only finitely many terms of the defining sum are nonzero.
* `AlgebraicGeometry.Space.locallyFinite_flatPullbackCoeff` and
  `AlgebraicGeometry.Space.flatPullbackCoeff_mem_cyclesOfDimension`: the coefficient family of
  `f^*α` is an `n`-cycle.
* `AlgebraicGeometry.Space.flatPullbackMap_integralCycle`: the pullback of the cycle of a single
  integral closed subspace is the multiplicity family.

## References

* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDX](https://stacks.math.columbia.edu/tag/0EDX)
* [Stacks Project, Tag 0EDZ](https://stacks.math.columbia.edu/tag/0EDZ)
* [Stacks Project, Tag 0EE1](https://stacks.math.columbia.edu/tag/0EE1)
* [Stacks Project, Tag 0EE2](https://stacks.math.columbia.edu/tag/0EE2)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 0EP5](https://stacks.math.columbia.edu/tag/0EP5)
* [Stacks Project, Tag 0EP6](https://stacks.math.columbia.edu/tag/0EP6)
* [Stacks Project, Tag 0EP9](https://stacks.math.columbia.edu/tag/0EP9)
* [Stacks Project, Tag 0EPA](https://stacks.math.columbia.edu/tag/0EPA)
* [Stacks Project, Tag 0EPB](https://stacks.math.columbia.edu/tag/0EPB)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The δ-dimension of an integral closed subspace, read as a closed subspace -/

section DeltaDimension

variable (D : BaseSpaceDimensionSituation.{u})
    {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The δ-dimension of an integral closed subspace, read as a closed subspace through
`AlgebraicGeometry.Space.deltaDimensionSubspace`, is its δ-dimension as an integral closed
subspace. -/
theorem deltaDimensionSubspace_integralClosedSubspace (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    deltaDimensionSubspace D sY hY W.subspace W.isClosedSubspace =
      ((deltaDimension D sY W : ℤ) : EInt) := by
  set T : IrreducibleCloseds (points D.site D.base D.base_mem Y) :=
    ⟨subspacePointSet D.site D.base D.base_mem Y W.subspace,
      isIrreducible_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem W,
      isClosed_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem hY.1 W⟩
    with hT
  have hgen : IsGenericPoint (W.ambientGenericPoint D.site D.base D.base_mem)
      (T : Set (points D.site D.base D.base_mem Y)) :=
    W.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hY.1
  calc deltaDimensionSubspace D sY hY W.subspace W.isClosedSubspace
      = deltaDimensionClosed D sY hY (T : Set (points D.site D.base D.base_mem Y)) T.isClosed :=
        rfl
    _ = ((deltaDimensionIrreducible D sY hY T : ℤ) : EInt) :=
        deltaDimensionClosed_eq_deltaDimensionIrreducible D sY hY T
    _ = ((deltaDimension D sY W : ℤ) : EInt) := by
        have h : deltaDimensionIrreducible D sY hY T = deltaDimension D sY W :=
          deltaDimensionIrreducible_eq_of_isGenericPoint D sY hY T hgen
        rw [h]

end DeltaDimension

/-! ### The inverse image of an integral closed subspace -/

section Preimage

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The scheme-theoretic inverse image of an integral closed subspace of `Y` along a morphism
`f : X ⟶ Y` of algebraic spaces over the base is a closed subspace of `X`. -/
theorem isClosedSubspace_preimage_integralClosedSubspace (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    IsClosedSubspace D.site D.base D.base_mem (W.subspace.preimage f) :=
  isClosedSubspace_preimage D.site D.base D.base_mem f W.subspace hY.1 hX.1 W.isClosedSubspace

/-- Along a morphism `f : X ⟶ Y` of good algebraic spaces over the base which is flat of relative
dimension `r`, the inverse image of an integral closed subspace `W ⊆ Y` satisfies
`dim_δ(f^{-1}(W)) ≤ dim_δ(W) + r`. -/
theorem deltaDimensionSubspace_preimage_integralClosedSubspace_le (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y)
    (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    deltaDimensionSubspace D sX hX (W.subspace.preimage f)
        (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W) ≤
      (((deltaDimension D sY W + (r : ℤ) : ℤ)) : EInt) :=
  deltaDimensionSubspace_preimage_le D sX hX sY hY f hbase r hflat hr (deltaDimension D sY W)
    W.subspace W.isClosedSubspace
    (deltaDimensionSubspace_integralClosedSubspace D sY hY W).le

end Preimage

/-! ### The flat pullback of the cycle of an integral closed subspace -/

section IntegralCycle

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)

/-- The flat pullback of the cycle of an integral closed subspace `W ⊆ Y` of δ-dimension `k`: the
`(k+r)`-cycle `[f^{-1}(W)]_{k+r}` of the scheme-theoretic inverse image. -/
@[stacks 0EP8 "part (1): f^*[W] = [f^{-1}(W)]_{k+r} for an integral closed subspace W"]
def flatPullbackIntegralCycle (W : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    CycleGroup D sX (deltaDimension D sY W + (r : ℤ)) :=
  closedSubspaceCycle D sX hX (W.subspace.preimage f)
    (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W)
    (deltaDimension D sY W + (r : ℤ))
    (deltaDimensionSubspace_preimage_integralClosedSubspace_le D sX hX sY hY f hbase r hflat hr W)

/-- The multiplicity of an integral closed subspace `T ⊆ X` in the inverse image `f^{-1}(W)` of an
integral closed subspace `W ⊆ Y`, that is the coefficient of `T` in `f^*[W]`. -/
def flatPullbackMult (W : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X) : ℤ :=
  (flatPullbackIntegralCycle D sX hX sY hY f hbase r hflat hr W).1 T

/-- An integral closed subspace of `X` occurring in `f^*[W]` has δ-dimension `r` more than `W`. -/
theorem deltaDimension_eq_of_flatPullbackMult_ne_zero
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hT : flatPullbackMult D sX hX sY hY f hbase r hflat hr W T ≠ 0) :
    deltaDimension D sX T = deltaDimension D sY W + (r : ℤ) :=
  (flatPullbackIntegralCycle D sX hX sY hY f hbase r hflat hr W).2.2 T hT

/-- An integral closed subspace of `X` occurring in `f^*[W]` is carried by the inverse image of
`|W|`. -/
theorem subspacePointSet_subset_of_flatPullbackMult_ne_zero
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hT : flatPullbackMult D sX hX sY hY f hbase r hflat hr W T ≠ 0) :
    subspacePointSet D.site D.base D.base_mem X T.subspace ⊆
      pointsMap D.site D.base D.base_mem X f ⁻¹'
        subspacePointSet D.site D.base D.base_mem Y W.subspace := by
  have h := subspacePointSet_subset_of_closedSubspaceCycle_ne_zero D sX hX
    (W.subspace.preimage f)
    (isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f W)
    (deltaDimension D sY W + (r : ℤ))
    (deltaDimensionSubspace_preimage_integralClosedSubspace_le D sX hX sY hY f hbase r hflat hr W)
    T hT
  rwa [subspacePointSet_preimage] at h

/-- The generic point of an integral closed subspace of `X` occurring in `f^*[W]` lies over a point
of `W`. -/
theorem mem_subspacePointSet_of_flatPullbackMult_ne_zero
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hT : flatPullbackMult D sX hX sY hY f hbase r hflat hr W T ≠ 0) :
    pointsMap D.site D.base D.base_mem X f
        (T.ambientGenericPoint D.site D.base D.base_mem) ∈
      subspacePointSet D.site D.base D.base_mem Y W.subspace :=
  subspacePointSet_subset_of_flatPullbackMult_ne_zero D sX hX sY hY f hbase r hflat hr W T hT
    ⟨_, rfl⟩

end IntegralCycle

/-! ### The flat pullback of a general cycle -/

section Cycle

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)

/-- The coefficient family of the flat pullback `f^*α` of a cycle `α` on `Y`: at an integral closed
subspace `T ⊆ X` it is `∑_W α_W · m_{T, f^{-1}(W)}`. -/
def flatPullbackCoeff (m : ℤ) (α : CycleGroup D sY m)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X) : ℤ :=
  ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem Y,
    α.1 W * flatPullbackMult D sX hX sY hY f hbase r hflat hr W T

/-- A nonzero coefficient of `f^*α` comes from a nonzero term of the defining sum. -/
theorem exists_ne_zero_of_flatPullbackCoeff_ne_zero (m : ℤ) (α : CycleGroup D sY m)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hT : flatPullbackCoeff D sX hX sY hY f hbase r hflat hr m α T ≠ 0) :
    ∃ W : IntegralClosedSubspace D.site D.base D.base_mem Y,
      α.1 W ≠ 0 ∧ flatPullbackMult D sX hX sY hY f hbase r hflat hr W T ≠ 0 := by
  by_contra hall
  refine hT ?_
  have hzero : (fun W : IntegralClosedSubspace D.site D.base D.base_mem Y ↦
      α.1 W * flatPullbackMult D sX hX sY hY f hbase r hflat hr W T) = fun _ ↦ (0 : ℤ) := by
    funext W
    rcases not_and_or.1 (not_exists.1 hall W) with h | h
    · rw [not_not.1 h, zero_mul]
    · rw [not_not.1 h, mul_zero]
  show (∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem Y,
    α.1 W * flatPullbackMult D sX hX sY hY f hbase r hflat hr W T) = 0
  rw [hzero, finsum_zero]

/-- At a fixed integral closed subspace of `X` only finitely many terms of the defining sum of
`f^*α` are nonzero. -/
theorem finite_support_flatPullbackTerm (m : ℤ) (α : CycleGroup D sY m)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (Function.support fun W : IntegralClosedSubspace D.site D.base D.base_mem Y =>
      α.1 W * flatPullbackMult D sX hX sY hY f hbase r hflat hr W T).Finite := by
  set ξ : points D.site D.base D.base_mem Y :=
    pointsMap D.site D.base D.base_mem X f
      (T.ambientGenericPoint D.site D.base D.base_mem) with hξ
  obtain ⟨V, hV, hVfin⟩ := α.2.1 ξ
  refine hVfin.subset fun W hW ↦ ?_
  have hterm : α.1 W * flatPullbackMult D sX hX sY hY f hbase r hflat hr W T ≠ 0 := hW
  refine ⟨ξ, ?_, mem_of_mem_nhds hV⟩
  simp only [Set.mem_ite_empty_left]
  exact ⟨left_ne_zero_of_mul hterm, mem_subspacePointSet_of_flatPullbackMult_ne_zero D sX hX sY hY
    f hbase r hflat hr W T (right_ne_zero_of_mul hterm)⟩

/-- The point sets of the integral closed subspaces with nonzero coefficient in `f^*α` form a
locally finite collection. -/
theorem locallyFinite_flatPullbackCoeff (m : ℤ) (α : CycleGroup D sY m) :
    LocallyFinite fun T : IntegralClosedSubspace D.site D.base D.base_mem X =>
      if flatPullbackCoeff D sX hX sY hY f hbase r hflat hr m α T = 0 then
        (∅ : Set (points D.site D.base D.base_mem X))
      else subspacePointSet D.site D.base D.base_mem X T.subspace := by
  classical
  have hpre := locallyFinite_preimage_pointsMap D.site D.base D.base_mem hX.1 hY.1 f
    (fun W : IntegralClosedSubspace D.site D.base D.base_mem Y ↦
      if α.1 W = 0 then (∅ : Set (points D.site D.base D.base_mem Y))
        else subspacePointSet D.site D.base D.base_mem Y W.subspace) α.2.1
  intro p
  obtain ⟨V, hV, hVfin⟩ := hpre p
  choose U hU hUfin using fun W : IntegralClosedSubspace D.site D.base D.base_mem Y ↦
    (flatPullbackIntegralCycle D sX hX sY hY f hbase r hflat hr W).2.1 p
  set F : Set (IntegralClosedSubspace D.site D.base D.base_mem Y) :=
    {W | ((pointsMap D.site D.base D.base_mem X f ⁻¹'
      (if α.1 W = 0 then (∅ : Set (points D.site D.base D.base_mem Y))
        else subspacePointSet D.site D.base D.base_mem Y W.subspace)) ∩ V).Nonempty} with hF
  refine ⟨V ∩ (⋂ W ∈ F, U W),
    Filter.inter_mem hV ((Filter.biInter_mem hVfin).2 fun W _ ↦ hU W), ?_⟩
  refine (hVfin.biUnion fun W _ ↦ hUfin W).subset ?_
  intro T hT
  obtain ⟨q, hqT, hqV⟩ := hT
  rw [Set.mem_ite_empty_left] at hqT
  obtain ⟨W, hαW, hmult⟩ := exists_ne_zero_of_flatPullbackCoeff_ne_zero D sX hX sY hY f hbase r
    hflat hr m α T hqT.1
  have hqW : q ∈ pointsMap D.site D.base D.base_mem X f ⁻¹'
      subspacePointSet D.site D.base D.base_mem Y W.subspace :=
    subspacePointSet_subset_of_flatPullbackMult_ne_zero D sX hX sY hY f hbase r hflat hr W T
      hmult hqT.2
  have hWF : W ∈ F := ⟨q, by simpa only [Set.mem_preimage, ite_eq_right hαW] using hqW, hqV.1⟩
  refine Set.mem_iUnion₂.2 ⟨W, hWF, q, ?_, Set.mem_iInter₂.1 hqV.2 W hWF⟩
  simp only [Set.mem_ite_empty_left]
  exact ⟨hmult, hqT.2⟩

/-- The coefficient family of `f^*α` is an `n`-cycle, for `n = m + r`. -/
theorem flatPullbackCoeff_mem_cyclesOfDimension (m n : ℤ) (hmn : m + (r : ℤ) = n)
    (α : CycleGroup D sY m) :
    flatPullbackCoeff D sX hX sY hY f hbase r hflat hr m α ∈ cyclesOfDimension D sX n := by
  refine ⟨?_, fun T hT ↦ ?_⟩
  · exact locallyFinite_flatPullbackCoeff D sX hX sY hY f hbase r hflat hr m α
  · obtain ⟨W, hαW, hmult⟩ := exists_ne_zero_of_flatPullbackCoeff_ne_zero D sX hX sY hY f hbase r
      hflat hr m α T hT
    rw [deltaDimension_eq_of_flatPullbackMult_ne_zero D sX hX sY hY f hbase r hflat hr W T
      hmult, α.2.2 W hαW, hmn]

/-- The flat pullback of cycles along a morphism `f : X ⟶ Y` of good algebraic spaces over the base
which is flat of relative dimension `r`, as a homomorphism `f^* : Z_m(Y) →+ Z_n(X)` for
`m + r = n`. -/
@[stacks 0EP8 "parts (2) and (3): the flat pullback of a cycle and the homomorphism
  Z_k(Y) → Z_{k+r}(X)"]
def flatPullbackMap (m n : ℤ) (hmn : m + (r : ℤ) = n) :
    CycleGroup D sY m →+ CycleGroup D sX n where
  toFun α := ⟨flatPullbackCoeff D sX hX sY hY f hbase r hflat hr m α,
    flatPullbackCoeff_mem_cyclesOfDimension D sX hX sY hY f hbase r hflat hr m n hmn α⟩
  map_zero' := by
    refine Subtype.ext (funext fun T ↦ ?_)
    change (∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem Y,
      (0 : ℤ) * flatPullbackMult D sX hX sY hY f hbase r hflat hr W T) = 0
    simp
  map_add' α β := by
    refine Subtype.ext (funext fun T ↦ ?_)
    change (∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem Y,
        (α.1 W + β.1 W) * flatPullbackMult D sX hX sY hY f hbase r hflat hr W T) =
      (∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem Y,
          α.1 W * flatPullbackMult D sX hX sY hY f hbase r hflat hr W T) +
        ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem Y,
          β.1 W * flatPullbackMult D sX hX sY hY f hbase r hflat hr W T
    rw [← finsum_add_distrib
      (finite_support_flatPullbackTerm D sX hX sY hY f hbase r hflat hr m α T)
      (finite_support_flatPullbackTerm D sX hX sY hY f hbase r hflat hr m β T)]
    exact finsum_congr fun W ↦ add_mul _ _ _

/-- The coefficient of `f^*α` at an integral closed subspace of `X` is the defining sum. -/
@[simp]
theorem flatPullbackMap_apply (m n : ℤ) (hmn : m + (r : ℤ) = n) (α : CycleGroup D sY m)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn α).1 T =
      ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem Y,
        α.1 W * flatPullbackMult D sX hX sY hY f hbase r hflat hr W T :=
  rfl

end Cycle

/-! ### The bundled flat pullback -/

section Bundled

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The flat pullback of cycles along a morphism `f : X ⟶ Y` of good algebraic spaces over the base
which is flat of relative dimension `r`, as an inhabitant of the bundled
`AlgebraicGeometry.Space.FlatCyclePullback`: the multiplicities of the inverse images, the
homomorphisms `Z_m(Y) →+ Z_n(X)` for `m + r = n`, the defining formula relating them, and the
containment of the support of `f^*[W]` in `f^{-1}(W)`. -/
@[stacks 0EP8 "the whole definition, bundled with its defining formula"]
def flatCyclePullback (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f) :
    FlatCyclePullback D sX hX sY hY f r where
  mult := flatPullbackMult D sX hX sY hY f hbase r hflat hr
  map m n hmn := flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn
  coeff _ _ _ _ _ := rfl
  mult_support W T hWT :=
    mem_subspacePointSet_of_flatPullbackMult_ne_zero D sX hX sY hY f hbase r hflat hr W T hWT

/-- The multiplicity of the bundled flat pullback is the coefficient of the cycle of the inverse
image. -/
@[simp]
theorem flatCyclePullback_mult (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (flatCyclePullback D sX hX sY hY f hbase r hflat hr).mult W T =
      (flatPullbackIntegralCycle D sX hX sY hY f hbase r hflat hr W).1 T :=
  rfl

/-- The flat pullback of the cycle of a single integral closed subspace `W ⊆ Y` of δ-dimension `m`
is the multiplicity family of `f^{-1}(W)`, that is the cycle `[f^{-1}(W)]_{m+r}` of part (1). -/
theorem flatPullbackMap_integralCycle (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (m n : ℤ) (hmn : m + (r : ℤ) = n)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (hW : deltaDimension D sY W = m)
    (T : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (flatPullbackMap D sX hX sY hY f hbase r hflat hr m n hmn
        (integralCycle D sY m W hW)).1 T =
      flatPullbackMult D sX hX sY hY f hbase r hflat hr W T :=
  (flatCyclePullback D sX hX sY hY f hbase r hflat hr).apply_integralCycle m n hmn W hW T

end Bundled

/-! ### Composing two flat morphisms -/

section Composite

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y Z : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The composite of two morphisms over the base is a morphism over the base. -/
theorem comp_structureMorphism_eq (sX : X ⟶ D.space) (sY : Y ⟶ D.space) (sZ : Z ⟶ D.space)
    (f : X ⟶ Y) (g : Y ⟶ Z) (hfbase : f ≫ sY = sX) (hgbase : g ≫ sZ = sY) :
    (f ≫ g) ≫ sZ = sX := by
  rw [Category.assoc, hgbase, hfbase]

/-- The flat pullback of cycles along the composite `g ∘ f` of morphisms of good algebraic spaces
over the base which are flat of relative dimensions `r` and `s`, at the degree shift `r + s`. -/
def flatCyclePullbackComp (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (sZ : Z ⟶ D.space) (hZ : D.IsGood sZ) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hfbase : f ≫ sY = sX) (hgbase : g ≫ sZ = sY) (r s : ℕ)
    (hff : IsFlat D.site D.base D.base_mem f)
    (hfr : HasRelativeDimension r D.site D.base D.base_mem f)
    (hgf : IsFlat D.site D.base D.base_mem g)
    (hgs : HasRelativeDimension s D.site D.base D.base_mem g) :
    FlatCyclePullback D sX hX sZ hZ (f ≫ g) (r + s) :=
  flatCyclePullback D sX hX sZ hZ (f ≫ g)
    (comp_structureMorphism_eq D sX sY sZ f g hfbase hgbase) (r + s)
    (isFlat_and_hasRelativeDimension_comp D sX hX sY hY sZ hZ f g hfbase hgbase r s hff hfr
      hgf hgs).2.1
    (isFlat_and_hasRelativeDimension_comp D sX hX sY hY sZ hZ f g hfbase hgbase r s hff hfr
      hgf hgs).2.2

end Composite

end AlgebraicGeometry.Space

end

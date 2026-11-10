module

public import Mathlib.Algebra.BigOperators.Finprod
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedImageDegree
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforward

/-!
# Proper pushforward of cycles on an algebraic space

In the situation of Stacks 0EDT let `X/B` and `Y/B` be good and let `f : X ⟶ Y` be a proper
morphism over `B`. For an integral closed subspace `Z ⊂ X` of δ-dimension `k`, with integral
closed image `Z' ⊂ Y`, the pushforward of the cycle `[Z]` is `0` when `dim_δ(Z') < k` and
`deg(Z/Z')·[Z']` when `dim_δ(Z') = k`; the pushforward of a `k`-cycle `α = ∑ n_Z [Z]` is
`∑ n_Z f_*[Z]`. This is a homomorphism `Z_k(X) → Z_k(Y)`, and it is functorial in `f`.

## Main definitions

* `AlgebraicGeometry.Space.cycleOfIntegralClosedSubspace`: the cycle `[Z]` of an integral closed
  subspace of δ-dimension `k`.
* `AlgebraicGeometry.Space.properPushforwardWeightInDimension`: **Stacks 0EP1**, the
  multiplicity with which an integral closed subspace of `X` is recorded in the pushforward.
* `AlgebraicGeometry.Space.properPushforwardInDimension`: **Stacks 0EP1**, the proper pushforward
  `f_* : Z_k(X) → Z_k(Y)`.

## Main results

* `AlgebraicGeometry.Space.properPushforwardInDimension_cycleOfIntegralClosedSubspace_eq_zero` and
  `AlgebraicGeometry.Space.properPushforwardInDimension_cycleOfIntegralClosedSubspace`:
  **Stacks 0EP1**, the two cases of the pushforward of the cycle of an integral closed
  subspace.
* `AlgebraicGeometry.Space.properPushforwardInDimension_zero`,
  `AlgebraicGeometry.Space.properPushforwardInDimension_add`,
  `AlgebraicGeometry.Space.properPushforwardInDimension_neg`: proper pushforward is a
  homomorphism of abelian groups.
* `AlgebraicGeometry.Space.properPushforwardInDimension_comp`: **Stacks 0EP2**, proper
  pushforward is functorial.

## Implementation notes

A `k`-cycle is a coefficient family on the integral closed subspaces of `X`, so the pushforward
of `α` has at `Z' ⊂ Y` the coefficient `∑ n_Z deg(Z/Z')` summed over the integral closed
subspaces `Z` of `X` whose integral closed image is `Z'`. That sum has finitely many nonzero
terms, by `AlgebraicGeometry.Space.finite_integralClosedImage_eq_and_ne_zero`.

The multiplicity tests `dim_δ(Z') = k`; since `dim_δ(Z') ≤ dim_δ(Z)`
(`AlgebraicGeometry.Space.IntegralClosedSubspace.deltaDimension_closureImage_le`), on the support
of a `k`-cycle this is the complement of the case `dim_δ(Z') < k` of the source.

## References

* [Stacks Project, Tag 0AD6](https://stacks.math.columbia.edu/tag/0AD6)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDZ](https://stacks.math.columbia.edu/tag/0EDZ)
* [Stacks Project, Tag 0EEG](https://stacks.math.columbia.edu/tag/0EEG)
* [Stacks Project, Tag 0ENH](https://stacks.math.columbia.edu/tag/0ENH)
* [Stacks Project, Tag 0ENZ](https://stacks.math.columbia.edu/tag/0ENZ)
* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
* [Stacks Project, Tag 0EP2](https://stacks.math.columbia.edu/tag/0EP2)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### A fibrewise rearrangement of a locally finite sum -/

/-- Fubini for a two-step fibration of index sets with multiplicative weights: summing the
pushforward of `c` along `φ`, weighted by `w`, over the fibre of `ψ` is summing `c` weighted by
`w ∘ φ` over the fibre of the composite, provided only finitely many indices in the fibre of the
composite have `c i ≠ 0`. -/
theorem finsum_fiberwise_mul {I J K : Type*} (φ : I → J) (ψ : J → K) (c : I → ℤ) (w : J → ℤ)
    (k : K) (hfin : {i | ψ (φ i) = k ∧ c i ≠ 0}.Finite) :
    (∑ᶠ j ∈ ψ ⁻¹' {k}, (∑ᶠ i ∈ φ ⁻¹' {j}, c i) * w j) =
      ∑ᶠ i ∈ (fun i ↦ ψ (φ i)) ⁻¹' {k}, c i * w (φ i) := by
  classical
  have hmemT : ∀ i, i ∈ hfin.toFinset ↔ ψ (φ i) = k ∧ c i ≠ 0 := fun i ↦ hfin.mem_toFinset
  have hinner : ∀ j, ψ j = k →
      (∑ᶠ i ∈ φ ⁻¹' {j}, c i) = ∑ i ∈ hfin.toFinset with φ i = j, c i := by
    intro j hj
    refine finsum_mem_eq_sum_of_subset _ ?_ ?_
    · rintro i ⟨hi, hci⟩
      have hij : φ i = j := hi
      exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨(hmemT i).2 ⟨hij ▸ hj, hci⟩, hij⟩)
    · intro i hi
      exact (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).2
  have hR : (∑ᶠ i ∈ (fun i ↦ ψ (φ i)) ⁻¹' {k}, c i * w (φ i)) =
      ∑ i ∈ hfin.toFinset, c i * w (φ i) := by
    refine finsum_mem_eq_sum_of_subset _ ?_ ?_
    · rintro i ⟨hi, hne⟩
      exact Finset.mem_coe.2 ((hmemT i).2 ⟨hi, left_ne_zero_of_mul hne⟩)
    · intro i hi
      exact ((hmemT i).1 (Finset.mem_coe.1 hi)).1
  have hfib : ∀ j ∈ hfin.toFinset.image φ, ψ j = k := by
    intro j hj
    obtain ⟨i, hiT, hij⟩ := Finset.mem_image.1 hj
    have hi := ((hmemT i).1 hiT).1
    rwa [hij] at hi
  have hL : (∑ᶠ j ∈ ψ ⁻¹' {k}, (∑ᶠ i ∈ φ ⁻¹' {j}, c i) * w j) =
      ∑ j ∈ hfin.toFinset.image φ, (∑ᶠ i ∈ φ ⁻¹' {j}, c i) * w j := by
    refine finsum_mem_eq_sum_of_subset _ ?_ ?_
    · rintro j ⟨hj, hne⟩
      have hsum : (∑ᶠ i ∈ φ ⁻¹' {j}, c i) ≠ 0 := left_ne_zero_of_mul hne
      obtain ⟨i, hi, hci⟩ := exists_ne_zero_of_finsum_mem_ne_zero hsum
      have hij : φ i = j := hi
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, (hmemT i).2 ⟨hij ▸ hj, hci⟩, hij⟩)
    · intro j hj
      exact hfib j (Finset.mem_coe.1 hj)
  rw [hR, hL, Finset.sum_congr rfl (fun j hj ↦ by rw [hinner j (hfib j hj), Finset.sum_mul]),
    ← Finset.sum_fiberwise_of_maps_to (g := φ) (f := fun i ↦ c i * w (φ i))
      (fun i hi ↦ Finset.mem_image_of_mem φ hi)]
  exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i hi ↦ by
    rw [(Finset.mem_filter.1 hi).2]

/-! ### The cycle of an integral closed subspace -/

section Generator

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The coefficient family of the cycle `[Z]` of an integral closed subspace: the indicator of
`Z` among the integral closed subspaces. -/
noncomputable def cycleCoeff (Z V : IntegralClosedSubspace D.site D.base D.base_mem X) : ℤ :=
  @ite ℤ (V = Z) (Classical.propDecidable _) 1 0

/-- The indicator of `Z` is `1` at `Z`. -/
@[simp]
theorem cycleCoeff_self (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    cycleCoeff D Z Z = 1 := by
  simp [cycleCoeff]

/-- The indicator of `Z` vanishes away from `Z`. -/
theorem cycleCoeff_eq_zero {Z V : IntegralClosedSubspace D.site D.base D.base_mem X}
    (h : V ≠ Z) : cycleCoeff D Z V = 0 := by
  simp [cycleCoeff, h]

/-- The indicator of `Z` vanishes except at `Z`. -/
theorem eq_of_cycleCoeff_ne_zero {Z V : IntegralClosedSubspace D.site D.base D.base_mem X}
    (h : cycleCoeff D Z V ≠ 0) : V = Z :=
  of_not_not fun hne ↦ h (cycleCoeff_eq_zero D hne)

/-- **Stacks 0EDZ, the generators of the cycle group.** The cycle `[Z]` of an integral closed
subspace `Z` of δ-dimension `k`: the coefficient family which is `1` at `Z` and `0`
elsewhere. -/
noncomputable def cycleOfIntegralClosedSubspace (sX : X ⟶ D.space) (k : ℤ)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : deltaDimension D sX Z = k) : CycleGroup D sX k := by
  refine ⟨cycleCoeff D Z,
    fun p ↦ ⟨Set.univ, Filter.univ_mem, (Set.finite_singleton Z).subset ?_⟩, fun V hV ↦ ?_⟩
  · rintro V ⟨q, hq, -⟩
    have hq' : q ∈ (if cycleCoeff D Z V = 0 then (∅ : Set (points D.site D.base D.base_mem X))
        else subspacePointSet D.site D.base D.base_mem X V.subspace) := hq
    by_cases h : cycleCoeff D Z V = 0
    · simp [h] at hq'
    · exact Set.mem_singleton_iff.2 (eq_of_cycleCoeff_ne_zero D h)
  · rwa [eq_of_cycleCoeff_ne_zero D hV]

/-- The coefficients of the cycle of an integral closed subspace. -/
theorem cycleOfIntegralClosedSubspace_coe (sX : X ⟶ D.space) (k : ℤ)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : deltaDimension D sX Z = k) :
    (cycleOfIntegralClosedSubspace D sX k Z hZ).1 = cycleCoeff D Z :=
  rfl

end Generator

/-! ### The multiplicity and the coefficients of the pushforward -/

section Pushforward

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The degree of an integral closed subspace of a good algebraic space over its integral closed
image: the degree `deg(Z/Z')` of Spaces over Fields, Definition 0AD6. -/
noncomputable abbrev IntegralClosedSubspace.degreeOverImage (sX : X ⟶ D.space)
    (sY : Y ⟶ D.space) (hX : D.IsGood sX) (hY : D.IsGood sY) (f : X ⟶ Y)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) : ℕ :=
  IntegralClosedSubspace.degreeOverClosureImage D.site D.base D.base_mem hY.1
    (isDecentSpace_of_isGood D sX hX) (isDecentSpace_of_isGood D sY hY) f Z

/-- **Stacks 0EP1, part (1).** The multiplicity with which proper pushforward along `f` records
an integral closed subspace `Z` of `X` in the cycle group of δ-dimension `k`: the degree
`deg(Z/Z')` of `Z` over its integral closed image `Z'` when `dim_δ(Z') = k`, and `0` when
`dim_δ(Z') < k`, which for `Z` of δ-dimension `k` is the only other case. -/
@[stacks 0EP1 "part (1): the multiplicity of an integral closed subspace in the pushforward"]
noncomputable def properPushforwardWeightInDimension (sX : X ⟶ D.space) (sY : Y ⟶ D.space)
    (hX : D.IsGood sX) (hY : D.IsGood sY) (f : X ⟶ Y) (k : ℤ)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) : ℤ :=
  if deltaDimension D sY (cycleImageSubspace D sY hY f Z) = k then
    (IntegralClosedSubspace.degreeOverImage D sX sY hX hY f Z : ℤ)
  else 0

/-- The multiplicity vanishes unless the integral closed image has δ-dimension `k`. -/
theorem properPushforwardWeightInDimension_eq_zero (sX : X ⟶ D.space) (sY : Y ⟶ D.space)
    (hX : D.IsGood sX) (hY : D.IsGood sY) (f : X ⟶ Y) (k : ℤ)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : deltaDimension D sY (cycleImageSubspace D sY hY f Z) ≠ k) :
    properPushforwardWeightInDimension D sX sY hX hY f k Z = 0 := by
  simp [properPushforwardWeightInDimension, hZ]

/-- The multiplicity is the degree over the integral closed image when that image has
δ-dimension `k`. -/
theorem properPushforwardWeightInDimension_eq (sX : X ⟶ D.space) (sY : Y ⟶ D.space)
    (hX : D.IsGood sX) (hY : D.IsGood sY) (f : X ⟶ Y) (k : ℤ)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : deltaDimension D sY (cycleImageSubspace D sY hY f Z) = k) :
    properPushforwardWeightInDimension D sX sY hX hY f k Z =
      (IntegralClosedSubspace.degreeOverImage D sX sY hX hY f Z : ℤ) := by
  simp [properPushforwardWeightInDimension, hZ]

/-- **Stacks 0EP1, part (2).** The coefficient at an integral closed subspace `Z'` of `Y` of the
proper pushforward of a coefficient family on the integral closed subspaces of `X`: the sum of
`n_Z deg(Z/Z')` over the integral closed subspaces `Z` of `X` with integral closed image
`Z'`. -/
noncomputable def properPushforwardCoeffInDimension (sX : X ⟶ D.space) (sY : Y ⟶ D.space)
    (hX : D.IsGood sX) (hY : D.IsGood sY) (f : X ⟶ Y) (k : ℤ)
    (α : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ)
    (Z' : IntegralClosedSubspace D.site D.base D.base_mem Y) : ℤ :=
  ∑ᶠ Z ∈ (fun Z ↦ cycleImageSubspace D sY hY f Z) ⁻¹' {Z'},
    α Z * properPushforwardWeightInDimension D sX sY hX hY f k Z

/-- The family of point sets tested for local finiteness by the cycle condition. -/
private noncomputable def supportFamily
    (α : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    Set (points D.site D.base D.base_mem X) :=
  if α Z = 0 then ∅ else subspacePointSet D.site D.base D.base_mem X Z.subspace

private theorem supportFamily_eq_empty
    {α : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ}
    {Z : IntegralClosedSubspace D.site D.base D.base_mem X} (h : α Z = 0) :
    supportFamily D α Z = ∅ := by
  simp [supportFamily, h]

private theorem supportFamily_eq
    {α : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ}
    {Z : IntegralClosedSubspace D.site D.base D.base_mem X} (h : α Z ≠ 0) :
    supportFamily D α Z = subspacePointSet D.site D.base D.base_mem X Z.subspace := by
  simp [supportFamily, h]

private theorem isClosed_supportFamily (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (α : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    IsClosed (supportFamily D α Z) := by
  by_cases h : α Z = 0
  · rw [supportFamily_eq_empty D h]
    exact isClosed_empty
  · rw [supportFamily_eq D h]
    exact isClosed_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem hX.1 Z

/-- For a subspace occurring in `α`, the closure of the image of its point set is the point set
of its integral closed image. -/
private theorem closure_image_supportFamily (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (f : X ⟶ Y)
    {α : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ}
    {Z : IntegralClosedSubspace D.site D.base D.base_mem X} (h : α Z ≠ 0) :
    closure (pointsMap D.site D.base D.base_mem X f '' supportFamily D α Z) =
      subspacePointSet D.site D.base D.base_mem Y
        (cycleImageSubspace D sY hY f Z).subspace := by
  rw [supportFamily_eq D h]
  exact (IntegralClosedSubspace.subspacePointSet_closureImage D.site D.base D.base_mem hY.1
    (isDecentSpace_of_isGood D sY hY) f Z).symm

/-- Only finitely many integral closed subspaces occurring in a cycle have a given integral
closed image. -/
theorem finite_integralClosedImage_eq_and_ne_zero (sX : X ⟶ D.space) (sY : Y ⟶ D.space)
    (hX : D.IsGood sX) (hY : D.IsGood sY) (f : X ⟶ Y) (hfB : f ≫ sY = sX)
    (hf : IsProper D.site D.base D.base_mem f) (k : ℤ)
    (α : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ)
    (hα : α ∈ cyclesOfDimension D sX k)
    (Z' : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    {Z | cycleImageSubspace D sY hY f Z = Z' ∧ α Z ≠ 0}.Finite := by
  obtain ⟨hlf, -⟩ := locallyFinite_closure_image_pointsMap D sX hX sY hY hfB hf.2.1.2
    (supportFamily D α) (isClosed_supportFamily D sX hX α) hα.1
  obtain ⟨V, hV, hVfin⟩ := hlf (Z'.ambientGenericPoint D.site D.base D.base_mem)
  refine hVfin.subset ?_
  rintro Z ⟨hZimg, hZne⟩
  refine ⟨Z'.ambientGenericPoint D.site D.base D.base_mem, ?_, mem_of_mem_nhds hV⟩
  change Z'.ambientGenericPoint D.site D.base D.base_mem ∈
    closure (pointsMap D.site D.base D.base_mem X f '' supportFamily D α Z)
  rw [closure_image_supportFamily D sY hY f hZne, hZimg]
  exact ⟨Z'.genericPoint D.site D.base D.base_mem, rfl⟩

/-- A nonzero pushforward coefficient at `Z'` comes from a subspace occurring in `α` with
integral closed image `Z'`. -/
theorem exists_integralClosedImage_eq_of_properPushforwardCoeffInDimension_ne_zero
    (sX : X ⟶ D.space) (sY : Y ⟶ D.space) (hX : D.IsGood sX) (hY : D.IsGood sY) (f : X ⟶ Y)
    (k : ℤ)
    (α : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ)
    (Z' : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (hZ' : properPushforwardCoeffInDimension D sX sY hX hY f k α Z' ≠ 0) :
    ∃ Z, cycleImageSubspace D sY hY f Z = Z' ∧ α Z ≠ 0 := by
  obtain ⟨Z, hZmem, hZne⟩ := exists_ne_zero_of_finsum_mem_ne_zero hZ'
  exact ⟨Z, hZmem, left_ne_zero_of_mul hZne⟩

/-- The proper pushforward of a `k`-cycle is a `k`-cycle. -/
theorem properPushforwardCoeffInDimension_mem_cyclesOfDimension (sX : X ⟶ D.space)
    (sY : Y ⟶ D.space) (hX : D.IsGood sX) (hY : D.IsGood sY) (f : X ⟶ Y) (hfB : f ≫ sY = sX)
    (hf : IsProper D.site D.base D.base_mem f) (k : ℤ)
    (α : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ)
    (hα : α ∈ cyclesOfDimension D sX k) :
    properPushforwardCoeffInDimension D sX sY hX hY f k α ∈ cyclesOfDimension D sY k := by
  obtain ⟨hlf, -⟩ := locallyFinite_closure_image_pointsMap D sX hX sY hY hfB hf.2.1.2
    (supportFamily D α) (isClosed_supportFamily D sX hX α) hα.1
  refine ⟨fun p ↦ ?_, fun Z' hZ' ↦ ?_⟩
  · obtain ⟨V, hV, hVfin⟩ := hlf p
    refine ⟨V, hV, (hVfin.image
      (fun Z ↦ cycleImageSubspace D sY hY f Z)).subset ?_⟩
    rintro Z' ⟨q, hq, hqV⟩
    have hq' : q ∈ (if properPushforwardCoeffInDimension D sX sY hX hY f k α Z' = 0 then
        (∅ : Set (points D.site D.base D.base_mem Y))
      else subspacePointSet D.site D.base D.base_mem Y Z'.subspace) := hq
    have hZ'ne : properPushforwardCoeffInDimension D sX sY hX hY f k α Z' ≠ 0 := by
      intro h
      simp [h] at hq'
    have hqZ' : q ∈ subspacePointSet D.site D.base D.base_mem Y Z'.subspace := by
      simpa [hZ'ne] using hq'
    obtain ⟨Z, hZimg, hZne⟩ :=
      exists_integralClosedImage_eq_of_properPushforwardCoeffInDimension_ne_zero
        D sX sY hX hY f k α Z' hZ'ne
    refine ⟨Z, ⟨q, ?_, hqV⟩, hZimg⟩
    change q ∈ closure (pointsMap D.site D.base D.base_mem X f '' supportFamily D α Z)
    rw [closure_image_supportFamily D sY hY f hZne, hZimg]
    exact hqZ'
  · obtain ⟨Z, hZmem, hZne⟩ := exists_ne_zero_of_finsum_mem_ne_zero hZ'
    have hw := right_ne_zero_of_mul hZne
    have hdim : deltaDimension D sY
        (cycleImageSubspace D sY hY f Z) = k := by
      by_contra h
      exact hw (properPushforwardWeightInDimension_eq_zero D sX sY hX hY f k Z h)
    have himg : cycleImageSubspace D sY hY f Z = Z' := hZmem
    rwa [himg] at hdim

/-- Proper pushforward of cycles of δ-dimension `k` along a proper morphism
`f : X ⟶ Y` of good algebraic spaces over the base: the cycle whose coefficient at `Z'` is the
sum of `n_Z deg(Z/Z')` over the integral closed subspaces `Z` of `X` with integral closed image
`Z'` of δ-dimension `k`. -/
@[stacks 0EP1 "part (2): the pushforward of a k-cycle, as a map Z_k(X) → Z_k(Y)"]
noncomputable def properPushforwardInDimension (sX : X ⟶ D.space) (sY : Y ⟶ D.space)
    (hX : D.IsGood sX) (hY : D.IsGood sY) (f : X ⟶ Y) (hfB : f ≫ sY = sX)
    (hf : IsProper D.site D.base D.base_mem f) (k : ℤ) :
    CycleGroup D sX k → CycleGroup D sY k :=
  fun α ↦ ⟨properPushforwardCoeffInDimension D sX sY hX hY f k α.1,
    properPushforwardCoeffInDimension_mem_cyclesOfDimension D sX sY hX hY f hfB hf k α.1 α.2⟩

/-- The coefficients of a proper pushforward. -/
theorem properPushforwardInDimension_coe (sX : X ⟶ D.space) (sY : Y ⟶ D.space) (hX : D.IsGood sX)
    (hY : D.IsGood sY) (f : X ⟶ Y) (hfB : f ≫ sY = sX)
    (hf : IsProper D.site D.base D.base_mem f) (k : ℤ) (α : CycleGroup D sX k) :
    (properPushforwardInDimension D sX sY hX hY f hfB hf k α).1 =
      properPushforwardCoeffInDimension D sX sY hX hY f k α.1 :=
  rfl

/-! ### The pushforward of the cycle of an integral closed subspace -/

/-- The coefficient of the pushforward of the cycle `[Z]` is the multiplicity of `Z`,
concentrated on the integral closed image of `Z`. -/
theorem properPushforwardCoeffInDimension_cycleCoeff (sX : X ⟶ D.space) (sY : Y ⟶ D.space)
    (hX : D.IsGood sX) (hY : D.IsGood sY) (f : X ⟶ Y) (k : ℤ)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (Z' : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    properPushforwardCoeffInDimension D sX sY hX hY f k (cycleCoeff D Z) Z' =
      cycleCoeff D (cycleImageSubspace D sY hY f Z) Z' *
        properPushforwardWeightInDimension D sX sY hX hY f k Z := by
  have hterm : ∀ V : IntegralClosedSubspace D.site D.base D.base_mem X,
      cycleCoeff D Z V * properPushforwardWeightInDimension D sX sY hX hY f k V =
        cycleCoeff D Z V * properPushforwardWeightInDimension D sX sY hX hY f k Z := by
    intro V
    by_cases h : V = Z
    · rw [h]
    · rw [cycleCoeff_eq_zero D h, zero_mul, zero_mul]
  rw [properPushforwardCoeffInDimension, finsum_mem_congr rfl (fun V _ ↦ hterm V)]
  by_cases himg : cycleImageSubspace D sY hY f Z = Z'
  · have h1 : cycleCoeff D (cycleImageSubspace D sY hY f Z) Z' = 1 := by
      simp [cycleCoeff, himg]
    rw [h1, one_mul]
    refine (finsum_mem_eq_sum_of_subset _ (t := {Z}) ?_ ?_).trans ?_
    · rintro V ⟨-, hV⟩
      refine Finset.mem_coe.2 (Finset.mem_singleton.2 ?_)
      exact eq_of_cycleCoeff_ne_zero D (left_ne_zero_of_mul hV)
    · intro V hV
      have hVZ : V = Z := Finset.mem_singleton.1 (Finset.mem_coe.1 hV)
      change cycleImageSubspace D sY hY f V = Z'
      rwa [hVZ]
    · rw [Finset.sum_singleton, cycleCoeff_self, one_mul]
  · rw [cycleCoeff_eq_zero D (Ne.symm himg), zero_mul]
    refine finsum_mem_eq_zero_of_forall_eq_zero fun V hV ↦ ?_
    have hVimg : cycleImageSubspace D sY hY f V = Z' := hV
    exact mul_eq_zero_of_left
      (cycleCoeff_eq_zero D fun h ↦ himg (by rw [← h]; exact hVimg)) _

/-- The pushforward of the cycle `[Z]` of
an integral closed subspace of δ-dimension `k` is zero when its integral closed image has
smaller δ-dimension. -/
@[stacks 0EP1 "part (1): f_*[Z] = 0 when dim_δ(Z') < k"]
theorem properPushforwardInDimension_cycleOfIntegralClosedSubspace_eq_zero (sX : X ⟶ D.space)
    (sY : Y ⟶ D.space) (hX : D.IsGood sX) (hY : D.IsGood sY) (f : X ⟶ Y) (hfB : f ≫ sY = sX)
    (hf : IsProper D.site D.base D.base_mem f) (k : ℤ)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) (hZ : deltaDimension D sX Z = k)
    (hlt : deltaDimension D sY (cycleImageSubspace D sY hY f Z) < k) :
    properPushforwardInDimension D sX sY hX hY f hfB hf k
        (cycleOfIntegralClosedSubspace D sX k Z hZ) = 0 := by
  refine Subtype.ext (funext fun Z' ↦ ?_)
  rw [properPushforwardInDimension_coe, cycleOfIntegralClosedSubspace_coe,
    properPushforwardCoeffInDimension_cycleCoeff,
    properPushforwardWeightInDimension_eq_zero D sX sY hX hY f k Z (ne_of_lt hlt), mul_zero]
  rfl

/-- The pushforward of the cycle `[Z]` of
an integral closed subspace of δ-dimension `k` whose integral closed image `Z'` again has
δ-dimension `k` is `deg(Z/Z')·[Z']`. -/
@[stacks 0EP1 "part (1): f_*[Z] = deg(Z/Z')·[Z'] when dim_δ(Z') = k"]
theorem properPushforwardInDimension_cycleOfIntegralClosedSubspace (sX : X ⟶ D.space)
    (sY : Y ⟶ D.space) (hX : D.IsGood sX) (hY : D.IsGood sY) (f : X ⟶ Y) (hfB : f ≫ sY = sX)
    (hf : IsProper D.site D.base D.base_mem f) (k : ℤ)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) (hZ : deltaDimension D sX Z = k)
    (hdim : deltaDimension D sY (cycleImageSubspace D sY hY f Z) = k) :
    properPushforwardInDimension D sX sY hX hY f hfB hf k
        (cycleOfIntegralClosedSubspace D sX k Z hZ) =
      (IntegralClosedSubspace.degreeOverImage D sX sY hX hY f Z : ℤ) •
        cycleOfIntegralClosedSubspace D sY k
          (cycleImageSubspace D sY hY f Z) hdim := by
  refine Subtype.ext (funext fun Z' ↦ ?_)
  have hco : ((IntegralClosedSubspace.degreeOverImage D sX sY hX hY f Z : ℤ) •
      cycleOfIntegralClosedSubspace D sY k
        (cycleImageSubspace D sY hY f Z) hdim).1 Z' =
      (IntegralClosedSubspace.degreeOverImage D sX sY hX hY f Z : ℤ) *
        cycleCoeff D (cycleImageSubspace D sY hY f Z) Z' := by
    simp [cycleOfIntegralClosedSubspace_coe]
  rw [properPushforwardInDimension_coe, cycleOfIntegralClosedSubspace_coe,
    properPushforwardCoeffInDimension_cycleCoeff,
    properPushforwardWeightInDimension_eq D sX sY hX hY f k Z hdim, hco,
    mul_comm (cycleCoeff D (cycleImageSubspace D sY hY f Z) Z')]

/-! ### Additivity -/

/-- The proper pushforward of the zero cycle is zero. -/
@[simp]
theorem properPushforwardInDimension_zero (sX : X ⟶ D.space) (sY : Y ⟶ D.space) (hX : D.IsGood sX)
    (hY : D.IsGood sY) (f : X ⟶ Y) (hfB : f ≫ sY = sX)
    (hf : IsProper D.site D.base D.base_mem f) (k : ℤ) :
    properPushforwardInDimension D sX sY hX hY f hfB hf k 0 = 0 := by
  refine Subtype.ext (funext fun Z' ↦ ?_)
  change properPushforwardCoeffInDimension D sX sY hX hY f k (0 : CycleGroup D sX k).1 Z' = 0
  rw [properPushforwardCoeffInDimension]
  exact finsum_mem_eq_zero_of_forall_eq_zero fun V _ ↦ zero_mul _

/-- For a cycle, only finitely many subspaces with a given integral closed image contribute to the
pushforward coefficient. -/
private theorem finite_inter_support (sX : X ⟶ D.space) (sY : Y ⟶ D.space) (hX : D.IsGood sX)
    (hY : D.IsGood sY) (f : X ⟶ Y) (hfB : f ≫ sY = sX)
    (hf : IsProper D.site D.base D.base_mem f) (k : ℤ)
    (α : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ)
    (hα : α ∈ cyclesOfDimension D sX k)
    (Z' : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    ((fun Z ↦ cycleImageSubspace D sY hY f Z) ⁻¹' {Z'} ∩
      Function.support
        fun Z ↦ α Z * properPushforwardWeightInDimension D sX sY hX hY f k Z).Finite := by
  refine (finite_integralClosedImage_eq_and_ne_zero D sX sY hX hY f hfB hf k α hα Z').subset ?_
  rintro Z ⟨hZ, hZs⟩
  exact ⟨hZ, left_ne_zero_of_mul hZs⟩

/-- Proper pushforward is additive. -/
theorem properPushforwardInDimension_add (sX : X ⟶ D.space) (sY : Y ⟶ D.space) (hX : D.IsGood sX)
    (hY : D.IsGood sY) (f : X ⟶ Y) (hfB : f ≫ sY = sX)
    (hf : IsProper D.site D.base D.base_mem f) (k : ℤ) (α β : CycleGroup D sX k) :
    properPushforwardInDimension D sX sY hX hY f hfB hf k (α + β) =
      properPushforwardInDimension D sX sY hX hY f hfB hf k α +
        properPushforwardInDimension D sX sY hX hY f hfB hf k β := by
  refine Subtype.ext (funext fun Z' ↦ ?_)
  change properPushforwardCoeffInDimension D sX sY hX hY f k (α.1 + β.1) Z' =
    properPushforwardCoeffInDimension D sX sY hX hY f k α.1 Z' +
      properPushforwardCoeffInDimension D sX sY hX hY f k β.1 Z'
  rw [properPushforwardCoeffInDimension, properPushforwardCoeffInDimension,
    properPushforwardCoeffInDimension,
    finsum_mem_congr rfl (fun V _ ↦ show (α.1 + β.1) V *
          properPushforwardWeightInDimension D sX sY hX hY f k V =
        α.1 V * properPushforwardWeightInDimension D sX sY hX hY f k V +
          β.1 V * properPushforwardWeightInDimension D sX sY hX hY f k V from add_mul _ _ _),
    finsum_mem_add_distrib' (finite_inter_support D sX sY hX hY f hfB hf k α.1 α.2 Z')
      (finite_inter_support D sX sY hX hY f hfB hf k β.1 β.2 Z')]

/-- Proper pushforward respects negation. -/
theorem properPushforwardInDimension_neg (sX : X ⟶ D.space) (sY : Y ⟶ D.space) (hX : D.IsGood sX)
    (hY : D.IsGood sY) (f : X ⟶ Y) (hfB : f ≫ sY = sX)
    (hf : IsProper D.site D.base D.base_mem f) (k : ℤ) (α : CycleGroup D sX k) :
    properPushforwardInDimension D sX sY hX hY f hfB hf k (-α) =
      -properPushforwardInDimension D sX sY hX hY f hfB hf k α :=
  eq_neg_iff_add_eq_zero.mpr <| by
    rw [add_comm, ← properPushforwardInDimension_add, add_neg_cancel,
      properPushforwardInDimension_zero]

end Pushforward

/-! ### Functoriality -/

section Functoriality

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y W : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The integral closed image of the integral closed image is the integral closed image of the
composite. -/
theorem IntegralClosedSubspace.integralClosedImage_integralClosedImage (sY : Y ⟶ D.space)
    (sW : W ⟶ D.space) (hY : D.IsGood sY) (hW : D.IsGood sW) (f : X ⟶ Y) (g : Y ⟶ W)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    cycleImageSubspace D sW hW g
        (cycleImageSubspace D sY hY f Z) =
      cycleImageSubspace D sW hW (f ≫ g) Z :=
  IntegralClosedSubspace.closureImage_closureImage D.site D.base D.base_mem hY.1
    (isDecentSpace_of_isGood D sY hY) hW.1 (isDecentSpace_of_isGood D sW hW) f g Z

/-- **Stacks 0EP2, the multiplicativity of the multiplicities.** For an integral closed subspace
of δ-dimension `k`, the multiplicity for the composite is the product of the multiplicity for
the second morphism at the integral closed image and the multiplicity for the first. -/
theorem properPushforwardWeightInDimension_comp (sX : X ⟶ D.space) (sY : Y ⟶ D.space)
    (sW : W ⟶ D.space) (hX : D.IsGood sX) (hY : D.IsGood sY) (hW : D.IsGood sW) (f : X ⟶ Y)
    (g : Y ⟶ W)
    (hfB : f ≫ sY = sX) (hgB : g ≫ sW = sY) (k : ℤ)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) (hZ : deltaDimension D sX Z = k) :
    properPushforwardWeightInDimension D sX sW hX hW (f ≫ g) k Z =
      properPushforwardWeightInDimension D sY sW hY hW g k
          (cycleImageSubspace D sY hY f Z) *
        properPushforwardWeightInDimension D sX sY hX hY f k Z := by
  have himg := congrArg (deltaDimension D sW)
    (IntegralClosedSubspace.integralClosedImage_integralClosedImage D sY sW hY hW f g Z)
  by_cases hb : deltaDimension D sY (cycleImageSubspace D sY hY f Z) = k
  · by_cases hc : deltaDimension D sW
        (cycleImageSubspace D sW hW (f ≫ g) Z) = k
    · rw [properPushforwardWeightInDimension_eq D sX sW hX hW (f ≫ g) k Z hc,
        properPushforwardWeightInDimension_eq D sX sY hX hY f k Z hb,
        properPushforwardWeightInDimension_eq D sY sW hY hW g k _
          (himg.trans hc),
        IntegralClosedSubspace.degreeOverImage, IntegralClosedSubspace.degreeOverImage,
        IntegralClosedSubspace.degreeOverImage,
        IntegralClosedSubspace.degreeOverClosureImage_comp D.site D.base D.base_mem hX.1 hY.1
          hW.1 (isDecentSpace_of_isGood D sX hX) (isDecentSpace_of_isGood D sY hY)
          (isDecentSpace_of_isGood D sW hW) f g Z,
        Nat.cast_mul]
    · rw [properPushforwardWeightInDimension_eq_zero D sX sW hX hW (f ≫ g) k Z hc,
        properPushforwardWeightInDimension_eq_zero D sY sW hY hW g k _
          (fun h ↦ hc (himg.symm.trans h)), zero_mul]
  · have hcne : deltaDimension D sW
        (cycleImageSubspace D sW hW (f ≫ g) Z) ≠ k := by
      intro hc
      have h1 := IntegralClosedSubspace.deltaDimension_closureImage_le D sY sW hY hW g hgB
        (cycleImageSubspace D sY hY f Z)
      have h2 := IntegralClosedSubspace.deltaDimension_closureImage_le D sX sY hX hY f hfB Z
      exact hb (le_antisymm (h2.trans_eq hZ) ((himg.trans hc).symm.trans_le h1))
    rw [properPushforwardWeightInDimension_eq_zero D sX sW hX hW (f ≫ g) k Z hcne,
      properPushforwardWeightInDimension_eq_zero D sX sY hX hY f k Z hb, mul_zero]

/-- Proper pushforward of `k`-cycles is functorial: pushing forward along
`f : X ⟶ Y` and then along `g : Y ⟶ W` is pushing forward along the composite. -/
@[stacks 0EP2]
theorem properPushforwardInDimension_comp (sX : X ⟶ D.space) (sY : Y ⟶ D.space) (sW : W ⟶ D.space)
    (hX : D.IsGood sX) (hY : D.IsGood sY) (hW : D.IsGood sW) (f : X ⟶ Y) (g : Y ⟶ W)
    (hfB : f ≫ sY = sX) (hgB : g ≫ sW = sY) (hf : IsProper D.site D.base D.base_mem f)
    (hg : IsProper D.site D.base D.base_mem g) (k : ℤ) (α : CycleGroup D sX k) :
    properPushforwardInDimension D sY sW hY hW g hgB hg k
        (properPushforwardInDimension D sX sY hX hY f hfB hf k α) =
      properPushforwardInDimension D sX sW hX hW (f ≫ g) (by rw [Category.assoc, hgB, hfB])
        (isProper_comp D.site D.base D.base_mem hX.1 hY.1 hW.1 f g hf hg) k α := by
  refine Subtype.ext (funext fun Z'' ↦ ?_)
  have hfin := finite_integralClosedImage_eq_and_ne_zero D sX sW hX hW (f ≫ g)
    (by rw [Category.assoc, hgB, hfB])
    (isProper_comp D.site D.base D.base_mem hX.1 hY.1 hW.1 f g hf hg) k α.1 α.2 Z''
  have hfib : {Z | cycleImageSubspace D sW hW g
      (cycleImageSubspace D sY hY f Z) = Z'' ∧
      α.1 Z * properPushforwardWeightInDimension D sX sY hX hY f k Z ≠ 0}.Finite := by
    refine hfin.subset ?_
    rintro Z ⟨hZ, hZne⟩
    refine ⟨?_, left_ne_zero_of_mul hZne⟩
    rwa [IntegralClosedSubspace.integralClosedImage_integralClosedImage D sY sW hY hW f g Z] at hZ
  have hkey := finsum_fiberwise_mul
    (fun Z ↦ cycleImageSubspace D sY hY f Z)
    (fun Z' ↦ cycleImageSubspace D sW hW g Z')
    (fun Z ↦ α.1 Z * properPushforwardWeightInDimension D sX sY hX hY f k Z)
    (fun Z' ↦ properPushforwardWeightInDimension D sY sW hY hW g k Z') Z'' hfib
  change properPushforwardCoeffInDimension D sY sW hY hW g k
      (properPushforwardCoeffInDimension D sX sY hX hY f k α.1) Z'' =
    properPushforwardCoeffInDimension D sX sW hX hW (f ≫ g) k α.1 Z''
  calc properPushforwardCoeffInDimension D sY sW hY hW g k
          (properPushforwardCoeffInDimension D sX sY hX hY f k α.1) Z''
      = ∑ᶠ Z' ∈ (fun Z' ↦ cycleImageSubspace D sW hW g Z') ⁻¹' {Z''},
          (∑ᶠ Z ∈ (fun Z ↦ cycleImageSubspace D sY hY f Z) ⁻¹' {Z'},
              α.1 Z * properPushforwardWeightInDimension D sX sY hX hY f k Z) *
            properPushforwardWeightInDimension D sY sW hY hW g k Z' := rfl
    _ = ∑ᶠ Z ∈ (fun Z ↦ cycleImageSubspace D sW hW g
            (cycleImageSubspace D sY hY f Z)) ⁻¹' {Z''},
          α.1 Z * properPushforwardWeightInDimension D sX sY hX hY f k Z *
            properPushforwardWeightInDimension D sY sW hY hW g k
              (cycleImageSubspace D sY hY f Z) := hkey
    _ = properPushforwardCoeffInDimension D sX sW hX hW (f ≫ g) k α.1 Z'' := by
        rw [properPushforwardCoeffInDimension]
        refine finsum_mem_congr ?_ ?_
        · ext Z
          simp only [Set.mem_preimage, Set.mem_singleton_iff,
            IntegralClosedSubspace.integralClosedImage_integralClosedImage D sY sW hY hW f g Z]
        · intro Z _
          by_cases hα : α.1 Z = 0
          · rw [hα, zero_mul, zero_mul, zero_mul]
          · rw [properPushforwardWeightInDimension_comp D sX sY sW hX hY hW f g hfB hgB k Z
                (α.2.2 Z hα)]
            ring

end Functoriality

end AlgebraicGeometry.Space

end

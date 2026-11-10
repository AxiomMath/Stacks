module

public import StacksFrontier.AlgebraicGeometry.Chow.CycleAdditivity
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaCoefficients
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalence
public import StacksFrontier.Topology.LocallyFinite.Sigma

/-!
# Iterated cap products with first Chern classes, subspace by subspace

In Situation 0EDT let `X/B` be good and let `ℒ`, `𝒩` be invertible `𝒪_X`-modules. Stacks 0EQZ
asserts that the two iterated cap products

`c₁(ℒ) ∩ c₁(𝒩) ∩ α` and `c₁(𝒩) ∩ c₁(ℒ) ∩ α`

agree in `CH_k(X)` for `α ∈ CH_{k+2}(X)`. Its proof writes `α = ∑ m_j [Z_j]` over a locally
finite family of integral closed subspaces of δ-dimension `k + 2` and reduces, by the
compatibility of the cap product with proper pushforward, to a single integral `Z_j`, where the
key formula (Stacks 0EQX) applies.

This file carries out, at the level of cycles, the part of that reduction which concerns the
locally finite sum. For the cycle-level cap products of Stacks 0EQJ with arbitrary component
rules, the coefficient of `c₁(ℒ) ∩ (c₁(𝒩) ∩ α)` at an integral closed subspace `Z` is
`∑_W n_W (c₁(ℒ) ∩ (c₁(𝒩) ∩ [W]))_Z` for `α = ∑ n_W [W]`, the term of `W` being carried by `W`.
Consequently, if for every integral closed subspace `W` of δ-dimension `k + 2` the difference
`c₁(ℒ) ∩ (c₁(𝒩) ∩ [W]) - c₁(𝒩) ∩ (c₁(ℒ) ∩ [W])` is a locally finite sum of principal divisors on
integral closed subspaces *of `W`*, then for every `α` the difference of the two iterated cap
products is a locally finite sum of principal divisors on integral closed subspaces of `X`: the
combined family is locally finite by Stacks 0EQ8.

## Main results

* `AlgebraicGeometry.Space.firstChernCapCycleMap_firstChernCapCycleMap_apply`: the iterated cap
  product of `α = ∑ n_W [W]` is `∑_W n_W · c₁(ℒ) ∩ (c₁(𝒩) ∩ [W])`, coefficientwise.
* `AlgebraicGeometry.Space.firstChernCapCycleMap_comm_sub_apply`: the same for the difference of
  the two iterated cap products.
* `AlgebraicGeometry.Space.cycleFamilySum_sigma_zsmul_apply`: a locally finite sum of sums
  `∑_j (W_{i,j} → X)_* c_{i,j}` over families carried by a locally finite family of subsets is the
  sum over the combined family.
* `AlgebraicGeometry.Space.canonicalPrincipalDivisorCycleAt_zpow`: `div(f^n) = n · div(f)`.
* `AlgebraicGeometry.Space.exists_cycleFamilySum_eq_firstChernCapCycleMap_comm_sub`: the
  reduction of the commutativity of the two cap products to integral closed subspaces, for any
  class of cycles stable under integer multiples.
* `AlgebraicGeometry.Space.exists_canonicalPrincipalDivisorSum_eq_firstChernCapCycleMap_comm_sub`:
  the same reduction for the principal divisors of invertible rational functions, formed with
  the canonical embeddings of Stacks 0ENK.

## Implementation notes

The source reduces to a single integral subspace by pushing forward along the proper morphism
`∐ Z_j → X`. Here the reduction is the exchange of two locally finite sums, which needs neither
the disjoint union nor proper pushforward; what it needs instead is that the rational equivalence
found for the component `W` lives on subspaces of `W`, which is what makes the union of these
families locally finite. The hypothesis on a component `W` is stated on `X`, for the cycle
`c₁(ℒ) ∩ (c₁(𝒩) ∩ [W])` of `X`; identifying it with the pushforward of the corresponding cycle of
the integral space `W` is the compatibility of the cap product with pushforward along the closed
immersion `W → X`, Stacks 0EQT.

The conclusions are existence statements of the explicit form `∑_j (V_j → X)_* div(f_j)` rather
than statements about a Chow group, so that they apply to whichever reading of rational
equivalence is in use; for the principal divisors of the canonical embeddings they are the
relation of Stacks 0EQ6. The index type of the combined family is `Σ W, J_W`, with `W` ranging
over the integral closed subspaces occurring in `α`, so it lives in the universe `max (u + 1) v`.

## References

* [Stacks Project, Tag 0EQZ](https://stacks.math.columbia.edu/tag/0EQZ)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
* [Stacks Project, Tag 0EQT](https://stacks.math.columbia.edu/tag/0EQT)
* [Stacks Project, Tag 0EQX](https://stacks.math.columbia.edu/tag/0EQX)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
-/

/- Stacks 0EQZ itself is proved in `IteratedFirstChernCapCommutativity.lean`, by
`chowClassCanonical_firstChernCapCycleMap_firstChernCapCycleMap_comm`: that proof establishes the
component statement at an integral closed subspace directly and then sums the components with the
coefficientwise formula `firstChernCapCycleMap_comm_sub_apply` below, so it does not pass through
the packaged reductions at the end of this file. -/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX)

/-! ### Subspaces of a cycle through a given subspace -/

section Through

/-- Only finitely many integral closed subspaces occurring in a cycle contain a given integral
closed subspace `Z`: they all contain the generic point of `Z`, and the subspaces occurring in a
cycle form a locally finite collection. -/
theorem finite_setOf_ne_zero_subspacePointSet_subset {k : ℤ} (α : CycleGroup D sX k)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    {W : IntegralClosedSubspace D.site D.base D.base_mem X | α.1 W ≠ 0 ∧
      subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆
        subspacePointSet D.site D.base D.base_mem X W.subspace}.Finite := by
  set ξ : points D.site D.base D.base_mem X :=
    pointsMap D.site D.base D.base_mem Z.subspace.toFunctor Z.subspace.ι
      (Z.genericPoint D.site D.base D.base_mem)
  have hξZ : ξ ∈ subspacePointSet D.site D.base D.base_mem X Z.subspace := ⟨_, rfl⟩
  obtain ⟨U, hU, hUfin⟩ := α.2.1 ξ
  refine hUfin.subset fun W ⟨hW, hZW⟩ => ⟨ξ, ?_, mem_of_mem_nhds hU⟩
  simpa [hW] using hZW hξZ

end Through

/-! ### The iterated cap product as a sum over the subspaces of the cycle -/

section DoubleCap

variable {k : ℤ} (chernL : FirstChernComponentCycleRule D sX k)
    (chernN : FirstChernComponentCycleRule D sX (k + 1))

/-- If `V` occurs in the component cycle of `W` and `Z` in that of `V`, then `Z ⊆ W`. -/
private theorem subspacePointSet_subset_of_firstChernComponentCycle_ne_zero_trans
    (W V Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hV : (firstChernComponentCycle D sX hX (k + 1) chernN W).1 V ≠ 0)
    (hZ : (firstChernComponentCycle D sX hX k chernL V).1 Z ≠ 0) :
    subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆
      subspacePointSet D.site D.base D.base_mem X W.subspace :=
  (subspacePointSet_subset_of_firstChernComponentCycle_ne_zero D sX hX k chernL V Z hZ).trans
    (subspacePointSet_subset_of_firstChernComponentCycle_ne_zero D sX hX (k + 1) chernN W V hV)

/-- A nonzero coefficient at `Z` of the cap product of the component cycle of `W` comes from a
subspace containing `Z` and contained in `W`. -/
theorem subspacePointSet_subset_of_firstChernCapCycleMap_firstChernComponentCycle_ne_zero
    (W Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : (firstChernCapCycleMap D sX hX k chernL
      (firstChernComponentCycle D sX hX (k + 1) chernN W)).1 Z ≠ 0) :
    subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆
      subspacePointSet D.site D.base D.base_mem X W.subspace := by
  obtain ⟨V, hV, hVZ⟩ := exists_ne_zero_of_firstChernCapCoeff_ne_zero D sX hX k chernL _ Z hZ
  exact subspacePointSet_subset_of_firstChernComponentCycle_ne_zero_trans D sX hX chernL chernN
    W V Z hV hVZ

/-- At a fixed integral closed subspace `Z` only finitely many pairs `(W, V)` contribute to the
iterated cap product `c₁(ℒ) ∩ (c₁(𝒩) ∩ α)`: a contributing pair has `Z ⊆ V ⊆ W` with `W`
occurring in `α`, so `W` is one of finitely many subspaces, and `V` is one of the finitely many
subspaces occurring in the component cycle of `W` and containing `Z`. -/
theorem finite_firstChernCapCycleMap_firstChernCapCycleMap_terms
    (α : CycleGroup D sX (k + 1 + 1)) (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    {p : IntegralClosedSubspace D.site D.base D.base_mem X ×
        IntegralClosedSubspace D.site D.base D.base_mem X |
      α.1 p.1 * (firstChernComponentCycle D sX hX (k + 1) chernN p.1).1 p.2 *
        (firstChernComponentCycle D sX hX k chernL p.2).1 Z ≠ 0}.Finite := by
  refine ((finite_setOf_ne_zero_subspacePointSet_subset D sX α Z).biUnion fun W _ =>
    ((finite_setOf_ne_zero_subspacePointSet_subset D sX
      (firstChernComponentCycle D sX hX (k + 1) chernN W) Z).image
        fun V => (W, V))).subset ?_
  rintro ⟨W, V⟩ hp
  have hV := right_ne_zero_of_mul (left_ne_zero_of_mul hp)
  have hZ := right_ne_zero_of_mul hp
  exact Set.mem_biUnion (x := W) ⟨left_ne_zero_of_mul (left_ne_zero_of_mul hp),
    subspacePointSet_subset_of_firstChernComponentCycle_ne_zero_trans D sX hX chernL chernN
      W V Z hV hZ⟩
    ⟨V, ⟨hV, subspacePointSet_subset_of_firstChernComponentCycle_ne_zero D sX hX k chernL V Z hZ⟩,
      rfl⟩

/-- **The iterated cap product is computed subspace by subspace.** For `α = ∑ n_W [W]` in
`Z_{k+2}(X)` the coefficient of `c₁(ℒ) ∩ (c₁(𝒩) ∩ α)` at `Z` is
`∑_W n_W · (c₁(ℒ) ∩ (c₁(𝒩) ∩ [W]))_Z`, where `c₁(𝒩) ∩ [W]` is the component cycle of `W`.

Both sides are double sums over pairs `(W, V)`, and only finitely many pairs contribute. -/
theorem firstChernCapCycleMap_firstChernCapCycleMap_apply (α : CycleGroup D sX (k + 1 + 1))
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (firstChernCapCycleMap D sX hX k chernL
        (firstChernCapCycleMap D sX hX (k + 1) chernN α)).1 Z =
      ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem X, α.1 W *
        (firstChernCapCycleMap D sX hX k chernL
          (firstChernComponentCycle D sX hX (k + 1) chernN W)).1 Z := by
  simp only [firstChernCapCycleMap_apply, finsum_mul, mul_finsum]
  rw [finsum_comm_of_finite (fun W V =>
      α.1 W * (firstChernComponentCycle D sX hX (k + 1) chernN W).1 V *
        (firstChernComponentCycle D sX hX k chernL V).1 Z)
    (finite_firstChernCapCycleMap_firstChernCapCycleMap_terms D sX hX chernL chernN α Z)]
  refine finsum_congr fun W => finsum_congr fun V => ?_
  ring

end DoubleCap

/-! ### Locally finite sums of sums of pushforwards -/

section FamilySums

variable {I : Type*} {J : I → Type*}
    (W : ∀ i, J i → IntegralClosedSubspace D.site D.base D.base_mem X)

/-- **A locally finite sum of sums `∑ (i_j)_* c_j` is again such a sum.** Let `{T_i}` be a
locally finite collection of subsets of `|X|`, and for each `i` let `{W_{i,j}}_j` be a locally
finite collection of integral closed subspaces contained in `T_i`, with `k`-cycles `c_{i,j}` on
them. Then the combined collection `{W_{i,j}}_{(i,j)}` is locally finite (Stacks 0EQ8) and, for
integers `m_i`, its sum `∑_{(i,j)} (W_{i,j} → X)_*(m_i c_{i,j})` has coefficient
`∑_i m_i (∑_j (W_{i,j} → X)_* c_{i,j})_Z` at every integral closed subspace `Z`. -/
theorem cycleFamilySum_sigma_zsmul_apply {k : ℤ}
    (hfin : LocallyFinite fun p : (i : I) × J i =>
      subspacePointSet D.site D.base D.base_mem X (W p.1 p.2).subspace)
    (hW : ∀ i, LocallyFinite fun j : J i =>
      subspacePointSet D.site D.base D.base_mem X (W i j).subspace)
    (m : I → ℤ) (c : ∀ i j, CycleGroup D ((W i j).subspace.ι ≫ sX) k)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (cycleFamilySum D sX hX (fun p : (i : I) × J i => W p.1 p.2) hfin k
        (fun p => m p.1 • c p.1 p.2)).1 Z =
      ∑ᶠ i : I, m i * (cycleFamilySum D sX hX (W i) (hW i) k (c i)).1 Z := by
  rw [cycleFamilySum_apply,
    Stacks.Chow.finsum_sigma _ (finite_support_cycleFamilyCoeff D sX hX _ hfin k _ Z)]
  refine finsum_congr fun i => ?_
  rw [cycleFamilySum_apply, mul_finsum]
  refine finsum_congr fun j => ?_
  rw [map_zsmul]
  rfl

end FamilySums


/-! ### Integer multiples of a principal divisor -/

section Zpow

variable {Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (hintY : IsIntegralSpace D.site D.base D.base_mem Y)

/-- `div(f^n) = n · div(f)` for the canonical principal divisor of an invertible rational
function on a good integral algebraic space. -/
theorem canonicalPrincipalDivisorCycleAt_zpow
    (f : (rationalFunctions D.site D.base D.base_mem hY.1)ˣ) (n : ℤ) {k : ℤ}
    (hk : deltaDimensionClosed D sY hY Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt)) :
    canonicalPrincipalDivisorCycleAt D sY hY hintY (f ^ n) hk =
      n • canonicalPrincipalDivisorCycleAt D sY hY hintY f hk := by
  refine Subtype.ext (funext fun P => ?_)
  rw [AddSubgroup.coe_zsmul, Pi.smul_apply, smul_eq_mul]
  by_cases hP : codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hY.1 P) = 1
  · rw [canonicalPrincipalDivisorCycleAt_apply_of_codimension_eq_one D sY hY hintY _ hk P hP,
      canonicalPrincipalDivisorCycleAt_apply_of_codimension_eq_one D sY hY hintY _ hk P hP,
      ordRationalFunction, ordRationalFunction, GenericFractionEmbedding.ord_zpow,
      Pi.smul_apply, smul_eq_mul]
  · unfold canonicalPrincipalDivisorCycleAt
    simp only
    rw [principalDivisorCycleCoefficients, principalDivisorCycleCoefficients, dite_eq_right hP,
      dite_eq_right hP, mul_zero]

end Zpow

/-! ### Reduction of the commutativity of the cap products to integral subspaces -/

section Commutativity

variable {k : ℤ} (chernL₀ : FirstChernComponentCycleRule D sX k)
    (chernN₁ : FirstChernComponentCycleRule D sX (k + 1))
    (chernN₀ : FirstChernComponentCycleRule D sX k)
    (chernL₁ : FirstChernComponentCycleRule D sX (k + 1))

/-- The terms `n_W · (c₁(ℒ) ∩ (c₁(𝒩) ∩ [W]))_Z` of the iterated cap product are supported on the
finitely many subspaces occurring in `α` and containing `Z`. -/
theorem hasFiniteSupport_mul_firstChernCapCycleMap_firstChernComponentCycle
    (α : CycleGroup D sX (k + 1 + 1)) (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    Function.HasFiniteSupport fun W : IntegralClosedSubspace D.site D.base D.base_mem X =>
      α.1 W * (firstChernCapCycleMap D sX hX k chernL₀
        (firstChernComponentCycle D sX hX (k + 1) chernN₁ W)).1 Z := by
  refine (finite_setOf_ne_zero_subspacePointSet_subset D sX α Z).subset fun W hW => ?_
  have hW : α.1 W * (firstChernCapCycleMap D sX hX k chernL₀
      (firstChernComponentCycle D sX hX (k + 1) chernN₁ W)).1 Z ≠ 0 := hW
  exact ⟨left_ne_zero_of_mul hW,
    subspacePointSet_subset_of_firstChernCapCycleMap_firstChernComponentCycle_ne_zero D sX hX
      chernL₀ chernN₁ W Z (right_ne_zero_of_mul hW)⟩

/-- The coefficient at `Z` of `c₁(ℒ) ∩ (c₁(𝒩) ∩ α) - c₁(𝒩) ∩ (c₁(ℒ) ∩ α)` is
`∑_W n_W · (c₁(ℒ) ∩ (c₁(𝒩) ∩ [W]) - c₁(𝒩) ∩ (c₁(ℒ) ∩ [W]))_Z` for `α = ∑ n_W [W]`. -/
theorem firstChernCapCycleMap_comm_sub_apply (α : CycleGroup D sX (k + 1 + 1))
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (firstChernCapCycleMap D sX hX k chernL₀ (firstChernCapCycleMap D sX hX (k + 1) chernN₁ α) -
        firstChernCapCycleMap D sX hX k chernN₀
          (firstChernCapCycleMap D sX hX (k + 1) chernL₁ α)).1 Z =
      ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem X, α.1 W *
        (firstChernCapCycleMap D sX hX k chernL₀
            (firstChernComponentCycle D sX hX (k + 1) chernN₁ W) -
          firstChernCapCycleMap D sX hX k chernN₀
            (firstChernComponentCycle D sX hX (k + 1) chernL₁ W)).1 Z := by
  change (firstChernCapCycleMap D sX hX k chernL₀
      (firstChernCapCycleMap D sX hX (k + 1) chernN₁ α)).1 Z -
    (firstChernCapCycleMap D sX hX k chernN₀
      (firstChernCapCycleMap D sX hX (k + 1) chernL₁ α)).1 Z = _
  rw [firstChernCapCycleMap_firstChernCapCycleMap_apply D sX hX chernL₀ chernN₁,
    firstChernCapCycleMap_firstChernCapCycleMap_apply D sX hX chernN₀ chernL₁,
    ← finsum_sub_distrib
      (hasFiniteSupport_mul_firstChernCapCycleMap_firstChernComponentCycle D sX hX chernL₀
        chernN₁ α Z)
      (hasFiniteSupport_mul_firstChernCapCycleMap_firstChernComponentCycle D sX hX chernN₀
        chernL₁ α Z)]
  refine finsum_congr fun W => ?_
  change _ = α.1 W * ((firstChernCapCycleMap D sX hX k chernL₀
      (firstChernComponentCycle D sX hX (k + 1) chernN₁ W)).1 Z -
    (firstChernCapCycleMap D sX hX k chernN₀
      (firstChernComponentCycle D sX hX (k + 1) chernL₁ W)).1 Z)
  ring

/-- **The source's reduction of Stacks 0EQZ to an integral subspace, at the level of cycles.**
Fix, for every integral closed subspace `W ⊆ X`, a class `P(W)` of `k`-cycles on `W` stable under
integer multiples (for instance the principal divisors `div(f)`, `f ∈ R(W)^*`). Suppose that for
every integral closed subspace `W ⊆ X` of δ-dimension `k + 2` the cycle

`c₁(ℒ) ∩ (c₁(𝒩) ∩ [W]) - c₁(𝒩) ∩ (c₁(ℒ) ∩ [W])`

is a sum `∑_j (V_j → X)_* c_j` over a locally finite family of integral closed subspaces
`V_j ⊆ W` of δ-dimension `k + 1`, with `c_j ∈ P(V_j)`. Then for every `α ∈ Z_{k+2}(X)` the cycle

`c₁(ℒ) ∩ (c₁(𝒩) ∩ α) - c₁(𝒩) ∩ (c₁(ℒ) ∩ α)`

is such a sum over a locally finite family of integral closed subspaces of `X`.

The cap products are the cycle-level cap products of Stacks 0EQJ for arbitrary component rules,
the inner ones in degree `k + 1` and the outer ones in degree `k`. The combined family is indexed
by the pairs `(W, j)` with `W` occurring in `α`; it is locally finite by Stacks 0EQ8 because each
`V_j` lies in `W`. -/
theorem exists_cycleFamilySum_eq_firstChernCapCycleMap_comm_sub
    (P : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      CycleGroup D (W.subspace.ι ≫ sX) k → Prop)
    (hP : ∀ (W : IntegralClosedSubspace D.site D.base D.base_mem X) (n : ℤ)
      (c : CycleGroup D (W.subspace.ι ≫ sX) k), P W c → P W (n • c))
    (h : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      deltaDimension D sX W = k + 1 + 1 →
        ∃ (J : Type v) (V : J → IntegralClosedSubspace D.site D.base D.base_mem X)
          (hV : LocallyFinite fun j : J =>
            subspacePointSet D.site D.base D.base_mem X (V j).subspace)
          (c : ∀ j, CycleGroup D ((V j).subspace.ι ≫ sX) k),
          (∀ j, deltaDimension D sX (V j) = k + 1) ∧ (∀ j, P (V j) (c j)) ∧
            (∀ j, subspacePointSet D.site D.base D.base_mem X (V j).subspace ⊆
              subspacePointSet D.site D.base D.base_mem X W.subspace) ∧
            firstChernCapCycleMap D sX hX k chernL₀
                (firstChernComponentCycle D sX hX (k + 1) chernN₁ W) -
              firstChernCapCycleMap D sX hX k chernN₀
                (firstChernComponentCycle D sX hX (k + 1) chernL₁ W) =
              cycleFamilySum D sX hX V hV k c)
    (α : CycleGroup D sX (k + 1 + 1)) :
    ∃ (J : Type (max (u + 1) v)) (V : J → IntegralClosedSubspace D.site D.base D.base_mem X)
      (hV : LocallyFinite fun j : J =>
        subspacePointSet D.site D.base D.base_mem X (V j).subspace)
      (c : ∀ j, CycleGroup D ((V j).subspace.ι ≫ sX) k),
      (∀ j, deltaDimension D sX (V j) = k + 1) ∧ (∀ j, P (V j) (c j)) ∧
        firstChernCapCycleMap D sX hX k chernL₀
            (firstChernCapCycleMap D sX hX (k + 1) chernN₁ α) -
          firstChernCapCycleMap D sX hX k chernN₀
            (firstChernCapCycleMap D sX hX (k + 1) chernL₁ α) =
          cycleFamilySum D sX hX V hV k c := by
  let I : Set (IntegralClosedSubspace D.site D.base D.base_mem X) := {W | α.1 W ≠ 0}
  choose J V hV c hVdim hVP hVW heq using fun W : I => h W.1 (α.2.2 W.1 W.2)
  have hT : LocallyFinite fun W : I =>
      subspacePointSet D.site D.base D.base_mem X W.1.subspace :=
    (α.2.1.comp_injective Subtype.val_injective).subset fun W => by
      simp [show α.1 W.1 ≠ 0 from W.2]
  have hfin := locallyFinite_sigma_of_subset hT hV hVW
  refine ⟨(W : I) × J W, fun p => V p.1 p.2, hfin, fun p => α.1 p.1.1 • c p.1 p.2,
    fun p => hVdim p.1 p.2, fun p => hP _ _ _ (hVP p.1 p.2), ?_⟩
  refine Subtype.ext (funext fun Z => ?_)
  rw [firstChernCapCycleMap_comm_sub_apply D sX hX chernL₀ chernN₁ chernN₀ chernL₁ α Z,
    cycleFamilySum_sigma_zsmul_apply D sX hX V hfin hV (fun W : I => α.1 W.1) c Z]
  simp_rw [← heq]
  refine (finsum_mem_univ _).symm.trans (((finsum_mem_inter_support_eq _ _ _ ?_)).trans
    (finsum_set_coe_eq_finsum_mem I).symm)
  rw [Set.univ_inter]
  exact (Set.inter_eq_right.2 fun W hW => left_ne_zero_of_mul hW).symm

/-- **The source's reduction of Stacks 0EQZ to an integral subspace, for principal divisors.**
Suppose that for every integral closed subspace `W ⊆ X` of δ-dimension `k + 2` the cycle
`c₁(ℒ) ∩ (c₁(𝒩) ∩ [W]) - c₁(𝒩) ∩ (c₁(ℒ) ∩ [W])` is a sum `∑_j (V_j → X)_* div_{V_j}(f_j)` of
principal divisors of invertible rational functions `f_j ∈ R(V_j)^*` over a locally finite
family of integral closed subspaces `V_j ⊆ W` of δ-dimension `k + 1`, the principal divisors
being formed with the canonical embeddings `R(V_j) → Q(𝒪^h)` of Stacks 0ENK. Then for every
`α ∈ Z_{k+2}(X)` the cycle `c₁(ℒ) ∩ (c₁(𝒩) ∩ α) - c₁(𝒩) ∩ (c₁(ℒ) ∩ α)` is such a sum over a
locally finite family of integral closed subspaces of `X`, that is, it is rationally equivalent to
zero in the sense of Stacks 0EQ6. -/
theorem exists_canonicalPrincipalDivisorSum_eq_firstChernCapCycleMap_comm_sub
    (h : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      deltaDimension D sX W = k + 1 + 1 →
        ∃ (J : Type v) (V : J → IntegralClosedSubspace D.site D.base D.base_mem X)
          (hV : LocallyFinite fun j : J =>
            subspacePointSet D.site D.base D.base_mem X (V j).subspace)
          (f : ∀ j, (rationalFunctions D.site D.base D.base_mem
            (isGood_integralClosedSubspace D sX hX (V j)).1)ˣ)
          (hk : ∀ j, deltaDimensionClosed D ((V j).subspace.ι ≫ sX)
            (isGood_integralClosedSubspace D sX hX (V j)) Set.univ isClosed_univ =
              ((k + 1 : ℤ) : EInt)),
          (∀ j, subspacePointSet D.site D.base D.base_mem X (V j).subspace ⊆
              subspacePointSet D.site D.base D.base_mem X W.subspace) ∧
            firstChernCapCycleMap D sX hX k chernL₀
                (firstChernComponentCycle D sX hX (k + 1) chernN₁ W) -
              firstChernCapCycleMap D sX hX k chernN₀
                (firstChernComponentCycle D sX hX (k + 1) chernL₁ W) =
              cycleFamilySum D sX hX V hV k fun j =>
                canonicalPrincipalDivisorCycleAt D ((V j).subspace.ι ≫ sX)
                  (isGood_integralClosedSubspace D sX hX (V j)) (V j).isIntegralSpace (f j)
                  (hk j))
    (α : CycleGroup D sX (k + 1 + 1)) :
    ∃ (J : Type (max (u + 1) v)) (V : J → IntegralClosedSubspace D.site D.base D.base_mem X)
      (hV : LocallyFinite fun j : J =>
        subspacePointSet D.site D.base D.base_mem X (V j).subspace)
      (f : ∀ j, (rationalFunctions D.site D.base D.base_mem
        (isGood_integralClosedSubspace D sX hX (V j)).1)ˣ)
      (hk : ∀ j, deltaDimensionClosed D ((V j).subspace.ι ≫ sX)
        (isGood_integralClosedSubspace D sX hX (V j)) Set.univ isClosed_univ =
          ((k + 1 : ℤ) : EInt)),
      firstChernCapCycleMap D sX hX k chernL₀
          (firstChernCapCycleMap D sX hX (k + 1) chernN₁ α) -
        firstChernCapCycleMap D sX hX k chernN₀
          (firstChernCapCycleMap D sX hX (k + 1) chernL₁ α) =
        cycleFamilySum D sX hX V hV k fun j =>
          canonicalPrincipalDivisorCycleAt D ((V j).subspace.ι ≫ sX)
            (isGood_integralClosedSubspace D sX hX (V j)) (V j).isIntegralSpace (f j) (hk j) := by
  have hdim : ∀ (V : IntegralClosedSubspace D.site D.base D.base_mem X)
      (_ : deltaDimensionClosed D (V.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX V)
        Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt)), deltaDimension D sX V = k + 1 := by
    intro V hk
    rw [deltaDimensionClosed_univ_integralClosedSubspace D sX hX V] at hk
    exact WithBotTop.coe_injective hk
  obtain ⟨J, V, hV, c, -, hc, heq⟩ := exists_cycleFamilySum_eq_firstChernCapCycleMap_comm_sub
    D sX hX chernL₀ chernN₁ chernN₀ chernL₁
    (fun W c => ∃ (f : (rationalFunctions D.site D.base D.base_mem
        (isGood_integralClosedSubspace D sX hX W).1)ˣ)
      (hk : deltaDimensionClosed D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
        Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt)),
      c = canonicalPrincipalDivisorCycleAt D (W.subspace.ι ≫ sX)
        (isGood_integralClosedSubspace D sX hX W) W.isIntegralSpace f hk)
    (fun W n c ⟨f, hk, hcf⟩ => ⟨f ^ n, hk, by
      rw [hcf, canonicalPrincipalDivisorCycleAt_zpow]⟩)
    (fun W hW => by
      obtain ⟨J, V, hV, f, hk, hVW, heq⟩ := h W hW
      exact ⟨J, V, hV, _, fun j => hdim (V j) (hk j), fun j => ⟨f j, hk j, rfl⟩, hVW, heq⟩)
    α
  choose f hk hcf using hc
  obtain rfl : c = fun j => canonicalPrincipalDivisorCycleAt D ((V j).subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D sX hX (V j)) (V j).isIntegralSpace (f j) (hk j) :=
    funext hcf
  exact ⟨J, V, hV, f, hk, heq⟩

end Commutativity

end AlgebraicGeometry.Space

end

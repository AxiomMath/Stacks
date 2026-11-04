module

public import Mathlib.Algebra.BigOperators.Finprod
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.LocalizationSequence

/-!
# Locally finite sums of cycles pushed forward from closed subspaces

In the situation of Stacks 0EDT let `X/B` be good and let `k ∈ ℤ`. Given a locally finite
collection `{W_j ⊆ X}` of integral closed subspaces and, for each `j`, a `k`-cycle `c_j` on
`W_j`, the coefficientwise sum `∑ (i_j)_* c_j` of the pushforwards along the inclusions
`i_j : W_j → X` is a well-defined `k`-cycle on `X`.

This is the construction underlying part (1) of Stacks 0EQ6, where `c_j` is the principal
divisor `div(f_j)` of a nonzero rational function `f_j ∈ R(W_j)^*` on a subspace of
δ-dimension `k + 1`.

## Main definitions

* `AlgebraicGeometry.Space.integralClosedSubspacePushforward`: pushforward of `k`-cycles
  along the inclusion of an integral closed subspace, as a homomorphism of cycle groups.
* `AlgebraicGeometry.Space.cycleFamilySumCoeff`: the coefficient family of the sum.
* `AlgebraicGeometry.Space.cycleFamilySum`: **Stacks 0EQ6, part (1)**, the sum as an element
  of `Z_k(X)`.

## Main results

* `AlgebraicGeometry.Space.subspacePointSet_subset_of_pushforward_ne_zero`: a nonzero
  coefficient of a pushforward sits on a subspace contained in `W`.
* `AlgebraicGeometry.Space.finite_support_cycleFamilyCoeff`: at a fixed integral closed
  subspace only finitely many members of the family contribute, so the defining sum is a
  finite sum.
* `AlgebraicGeometry.Space.cycleFamilySumCoeff_mem_cyclesOfDimension`: **Stacks 0EQ6,
  part (1)**, the sum is a `k`-cycle.

## Implementation notes

The sum is taken with `finsum`, which is the sum over the support when that support is
finite; `AlgebraicGeometry.Space.finite_support_cycleFamilyCoeff` is exactly the statement
that it is. Its proof is the reason the source requires the collection `{W_j}` to be locally
finite, and it is the formal counterpart of the source's remark that the sum makes sense because
`∐ i_j : ∐ W_j → X` is proper: the generic point of a subspace carrying a nonzero coefficient
of `(i_j)_* c_j` lies in `|W_j|`, and a neighbourhood of it meets only finitely many of the
`|W_j|`.

The source states part (1) for `c_j = div(f_j)` with `dim_δ(W_j) = k + 1`, the hypothesis
which makes `div(f_j)` a `k`-cycle. Here the summands are arbitrary `k`-cycles on the `W_j`,
so that hypothesis is not needed and is not imposed; the source's statement is the special
case `c_j = div(f_j)`. The principal divisor of a rational function on an integral algebraic
space (Stacks 0ENP, through the order of vanishing of Stacks 0ENL and the embedding of the
function field into the total ring of fractions of the henselian local ring, Stacks 0ENK) is
`AlgebraicGeometry.Space.principalDivisorCycleCoefficients` at the canonical embeddings
`AlgebraicGeometry.Space.genericFractionEmbedding`.

Pushforward along a closed immersion is `AlgebraicGeometry.Space.cycleGroupClosedPushforward`
of the localization sequence; the hypotheses it needs are read off from the integral closed
subspace, whose inclusion is a closed immersion of algebraic spaces, and from goodness of
`X/B`, which supplies decency of `|X|` and local finiteness of type of the structure
morphism.

## References

* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDZ](https://stacks.math.columbia.edu/tag/0EDZ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-! ### Pushforward along the inclusion of an integral closed subspace -/

/-- Pushforward of `k`-cycles along the inclusion `i : W → X` of an integral closed subspace
of a good algebraic space `X/B`, where `W` is viewed over the base through `i`. -/
def integralClosedSubspacePushforward (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (W : IntegralClosedSubspace D.site D.base D.base_mem X) (k : ℤ) :
    CycleGroup D (W.subspace.ι ≫ sX) k →+ CycleGroup D sX k :=
  cycleGroupClosedPushforward D hX.1 W.isClosedSubspace.1
    (D.isDecentSpace_of_isGood sX hX) W.isClosedSubspace.2 sX hX.2.2 _ rfl k

/-- An integral closed subspace at which a pushforward from `W` has a nonzero coefficient has
its point set contained in that of `W`: the coefficient is nonzero only at the image of an
integral closed subspace of `W`. -/
theorem subspacePointSet_subset_of_pushforward_ne_zero (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (W : IntegralClosedSubspace D.site D.base D.base_mem X) (k : ℤ)
    (c : CycleGroup D (W.subspace.ι ≫ sX) k)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : (integralClosedSubspacePushforward D sX hX W k c).1 Z ≠ 0) :
    subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆
      subspacePointSet D.site D.base D.base_mem X W.subspace := by
  by_cases hex : ∃ Z', IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1
      W.isClosedSubspace.1 (D.isDecentSpace_of_isGood sX hX) W.isClosedSubspace.2 Z' = Z
  · obtain ⟨Z', rfl⟩ := hex
    rw [IntegralClosedSubspace.subspacePointSet_pushforward]
    exact Set.image_subset_range _ _
  · exact absurd (cycleClosedPushforward_apply_of_forall_ne D hX.1 W.isClosedSubspace.1
      (D.isDecentSpace_of_isGood sX hX) W.isClosedSubspace.2 c.1 Z
      fun Z' hZ' => hex ⟨Z', hZ'⟩) hZ

/-- The δ-dimension of an integral closed subspace at which a pushforward of a `k`-cycle has a
nonzero coefficient is `k`. -/
theorem deltaDimension_eq_of_pushforward_ne_zero (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (W : IntegralClosedSubspace D.site D.base D.base_mem X) (k : ℤ)
    (c : CycleGroup D (W.subspace.ι ≫ sX) k)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : (integralClosedSubspacePushforward D sX hX W k c).1 Z ≠ 0) :
    deltaDimension D sX Z = k :=
  (integralClosedSubspacePushforward D sX hX W k c).2.2 Z hZ

/-- The point sets of the integral closed subspaces at which a pushforward of a `k`-cycle has a
nonzero coefficient form a locally finite collection. -/
theorem locallyFinite_pushforward_support (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (W : IntegralClosedSubspace D.site D.base D.base_mem X) (k : ℤ)
    (c : CycleGroup D (W.subspace.ι ≫ sX) k) :
    LocallyFinite fun Z : IntegralClosedSubspace D.site D.base D.base_mem X =>
      if (integralClosedSubspacePushforward D sX hX W k c).1 Z = 0 then ∅
        else subspacePointSet D.site D.base D.base_mem X Z.subspace :=
  (integralClosedSubspacePushforward D sX hX W k c).2.1

/-! ### The sum over a locally finite family -/

variable {J : Type v}

/-- The coefficient family of the sum `∑ (i_j)_* c_j` of the pushforwards of a family of
`k`-cycles `c_j` on a family of integral closed subspaces `W_j ⊆ X`. -/
def cycleFamilySumCoeff (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (W : J → IntegralClosedSubspace D.site D.base D.base_mem X) (k : ℤ)
    (c : ∀ j, CycleGroup D ((W j).subspace.ι ≫ sX) k)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) : ℤ :=
  ∑ᶠ j : J, (integralClosedSubspacePushforward D sX hX (W j) k (c j)).1 Z

/-- A nonzero coefficient of the sum comes from a nonzero coefficient of one of the
summands. -/
theorem exists_pushforward_ne_zero_of_cycleFamilySumCoeff_ne_zero (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (W : J → IntegralClosedSubspace D.site D.base D.base_mem X) (k : ℤ)
    (c : ∀ j, CycleGroup D ((W j).subspace.ι ≫ sX) k)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : cycleFamilySumCoeff D sX hX W k c Z ≠ 0) :
    ∃ j, (integralClosedSubspacePushforward D sX hX (W j) k (c j)).1 Z ≠ 0 := by
  by_contra hall
  exact hZ (finsum_eq_zero_of_forall_eq_zero fun j => not_not.1 (not_exists.1 hall j))

/-- At a fixed integral closed subspace only finitely many members of a locally finite family
contribute to the sum: the generic point of a subspace with a nonzero coefficient lies in the
point set of the corresponding member, and only finitely many members meet a neighbourhood of
it. This is why the collection `{W_j}` is required to be locally finite. -/
theorem finite_support_cycleFamilyCoeff (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (W : J → IntegralClosedSubspace D.site D.base D.base_mem X)
    (hWfin : LocallyFinite fun j : J =>
      subspacePointSet D.site D.base D.base_mem X (W j).subspace)
    (k : ℤ) (c : ∀ j, CycleGroup D ((W j).subspace.ι ≫ sX) k)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (Function.support fun j : J =>
      (integralClosedSubspacePushforward D sX hX (W j) k (c j)).1 Z).Finite := by
  set ξ : points D.site D.base D.base_mem X :=
    pointsMap D.site D.base D.base_mem Z.subspace.toFunctor Z.subspace.ι
      (Z.genericPoint D.site D.base D.base_mem) with hξ
  have hξZ : ξ ∈ subspacePointSet D.site D.base D.base_mem X Z.subspace := ⟨_, rfl⟩
  obtain ⟨V, hV, hVfin⟩ := hWfin ξ
  refine hVfin.subset fun j hj => ?_
  exact ⟨ξ, subspacePointSet_subset_of_pushforward_ne_zero D sX hX (W j) k (c j) Z hj hξZ,
    mem_of_mem_nhds hV⟩

/-- **Stacks 0EQ6, part (1).** The coefficientwise sum `∑ (i_j)_* c_j` of the pushforwards of a
family of `k`-cycles along the inclusions of a locally finite collection of integral closed
subspaces is a `k`-cycle on `X`.

Local finiteness of the collection gives local finiteness of the support: a neighbourhood of a
point meeting only finitely many of the `|W_j|` is shrunk, using the pushforwards from those
finitely many, to one meeting only finitely many point sets of subspaces with a nonzero
coefficient. The δ-dimension of each such subspace is `k` because that holds for the summand
it comes from. -/
@[stacks 0EQ6 "part (1)"]
theorem cycleFamilySumCoeff_mem_cyclesOfDimension (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (W : J → IntegralClosedSubspace D.site D.base D.base_mem X)
    (hWfin : LocallyFinite fun j : J =>
      subspacePointSet D.site D.base D.base_mem X (W j).subspace)
    (k : ℤ) (c : ∀ j, CycleGroup D ((W j).subspace.ι ≫ sX) k) :
    cycleFamilySumCoeff D sX hX W k c ∈ cyclesOfDimension D sX k := by
  refine ⟨fun x => ?_, fun Z hZ => ?_⟩
  · obtain ⟨V, hV, hVfin⟩ := hWfin x
    choose U hU hUfin using fun j : J =>
      locallyFinite_pushforward_support D sX hX (W j) k (c j) x
    set F : Set J := {j : J | (subspacePointSet D.site D.base D.base_mem X
      (W j).subspace ∩ V).Nonempty} with hF
    refine ⟨V ∩ (⋂ j ∈ F, U j),
      Filter.inter_mem hV ((Filter.biInter_mem hVfin).2 fun j _ => hU j), ?_⟩
    refine (hVfin.biUnion fun j _ => hUfin j).subset ?_
    intro Z hZ
    obtain ⟨p, hpZ, hpV⟩ := hZ
    have hne : cycleFamilySumCoeff D sX hX W k c Z ≠ 0 := fun hne => by simp [hne] at hpZ
    have hpZ' : p ∈ subspacePointSet D.site D.base D.base_mem X Z.subspace := by
      simpa [hne] using hpZ
    obtain ⟨j, hj⟩ :=
      exists_pushforward_ne_zero_of_cycleFamilySumCoeff_ne_zero D sX hX W k c Z hne
    have hjF : j ∈ F :=
      ⟨p, subspacePointSet_subset_of_pushforward_ne_zero D sX hX (W j) k (c j) Z hj hpZ',
        hpV.1⟩
    refine Set.mem_iUnion₂.2 ⟨j, hjF, p, ?_, Set.mem_iInter₂.1 hpV.2 j hjF⟩
    simpa [hj] using hpZ'
  · obtain ⟨j, hj⟩ :=
      exists_pushforward_ne_zero_of_cycleFamilySumCoeff_ne_zero D sX hX W k c Z hZ
    exact deltaDimension_eq_of_pushforward_ne_zero D sX hX (W j) k (c j) Z hj

/-- **Stacks 0EQ6, part (1).** The element `∑ (i_j)_* c_j` of `Z_k(X)` determined by a locally
finite collection `{W_j ⊆ X}` of integral closed subspaces and a family of `k`-cycles `c_j` on
them; taking `c_j = div(f_j)` for `f_j ∈ R(W_j)^*` on subspaces of δ-dimension `k + 1` gives
the cycle of the source. -/
@[stacks 0EQ6 "part (1)"]
def cycleFamilySum (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (W : J → IntegralClosedSubspace D.site D.base D.base_mem X)
    (hWfin : LocallyFinite fun j : J =>
      subspacePointSet D.site D.base D.base_mem X (W j).subspace)
    (k : ℤ) (c : ∀ j, CycleGroup D ((W j).subspace.ι ≫ sX) k) : CycleGroup D sX k :=
  ⟨cycleFamilySumCoeff D sX hX W k c,
    cycleFamilySumCoeff_mem_cyclesOfDimension D sX hX W hWfin k c⟩

/-- The coefficient of `∑ (i_j)_* c_j` at an integral closed subspace is the sum of the
coefficients of the pushforwards there. -/
@[simp]
theorem cycleFamilySum_apply (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (W : J → IntegralClosedSubspace D.site D.base D.base_mem X)
    (hWfin : LocallyFinite fun j : J =>
      subspacePointSet D.site D.base D.base_mem X (W j).subspace)
    (k : ℤ) (c : ∀ j, CycleGroup D ((W j).subspace.ι ≫ sX) k)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (cycleFamilySum D sX hX W hWfin k c).1 Z =
      ∑ᶠ j : J, (integralClosedSubspacePushforward D sX hX (W j) k (c j)).1 Z :=
  rfl

end AlgebraicGeometry.Space

end

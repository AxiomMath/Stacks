module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.CycleAdditivity
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalence
public import StacksFrontier.Topology.LocallyFinite.Sigma

/-!
# Infinite sums of rational equivalences

In the situation of Stacks 0EDT let `X/B` be good and let `k ∈ ℤ`. Let `{T_i}_{i ∈ I}` be a
locally finite collection of subsets of `|X|` and let `α_i, β_i ∈ Z_k(X)` be families of
`k`-cycles supported on `T_i`. Then the coefficientwise sums `∑ α_i` and `∑ β_i` are again
`k`-cycles. If moreover `α_i ∼_rat β_i` "on `T_i`", that is if the rational equivalence is
witnessed by a locally finite family `{W_{i, j}, f_{i, j} ∈ R(W_{i, j})^*}_{j ∈ J_i}` of
integral closed subspaces with `|W_{i, j}| ⊆ T_i`, then `∑ α_i ∼_rat ∑ β_i`.

## Main definitions

* `AlgebraicGeometry.Space.locallyFiniteCycleSumCoeff`,
  `AlgebraicGeometry.Space.locallyFiniteCycleSum`: the sum `∑ α_i` of a family of `k`-cycles
  supported on a locally finite collection of subsets of `|X|`.
* `AlgebraicGeometry.Space.RationallyEquivalentOn`: the relation `α ∼_rat β` "on `T`", the
  witnessing subspaces being contained in `T`.

## Main results

* `AlgebraicGeometry.Space.locallyFiniteCycleSumCoeff_mem_cyclesOfDimension`: the sum `∑ α_i`
  is a `k`-cycle.
* `AlgebraicGeometry.Space.rationallyEquivalent_locallyFiniteCycleSum`: **Stacks 0EQ8**, the
  positive claim of the remark: `∑ α_i ∼_rat ∑ β_i` when each `α_i ∼_rat β_i` on `T_i`.

## Implementation notes

The remark's point is that the combined family `{W_{i, j}}_{i ∈ I, j ∈ J_i}` is locally finite,
which is `locallyFinite_sigma_of_subset`; the rational equivalence of the sums is then the
single family indexed by `Σ i, J i`, and the required identity of coefficients is the exchange
of a sum over `Σ i, J i` with the iterated sum, `Stacks.Chow.finsum_sigma`.

The source takes the `T_i` to be closed. Closedness is used nowhere — neither for the sums to
be cycles nor for the rational equivalence — so it is not assumed here.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} {I : Type v}

/-! ### The sum of a family of cycles with locally finite supports -/

/-- The coefficient family of the sum `∑ α_i` of a family of `k`-cycles on `X`. -/
def locallyFiniteCycleSumCoeff (sX : X ⟶ D.space) (k : ℤ) (α : I → CycleGroup D sX k)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) : ℤ :=
  ∑ᶠ i : I, (α i).1 Z

/-- A nonzero coefficient of the sum `∑ α_i` comes from a nonzero coefficient of one of the
summands. -/
theorem exists_ne_zero_of_locallyFiniteCycleSumCoeff_ne_zero (sX : X ⟶ D.space) (k : ℤ)
    (α : I → CycleGroup D sX k) (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : locallyFiniteCycleSumCoeff D sX k α Z ≠ 0) : ∃ i, (α i).1 Z ≠ 0 := by
  by_contra hall
  exact hZ (finsum_eq_zero_of_forall_eq_zero fun i => not_not.1 (not_exists.1 hall i))

/-- At a fixed integral closed subspace only finitely many members of a family of cycles
supported on a locally finite collection of subsets contribute: the generic point of the
subspace lies in the member of the collection carrying each contributing summand. -/
theorem finite_support_locallyFiniteCycleCoeff (sX : X ⟶ D.space) (k : ℤ)
    (T : I → Set (points D.site D.base D.base_mem X)) (hT : LocallyFinite T)
    (α : I → CycleGroup D sX k)
    (hαT : ∀ (i : I) (Z : IntegralClosedSubspace D.site D.base D.base_mem X),
      (α i).1 Z ≠ 0 → subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆ T i)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (Function.support fun i : I => (α i).1 Z).Finite := by
  set ξ : points D.site D.base D.base_mem X :=
    pointsMap D.site D.base D.base_mem Z.subspace.toFunctor Z.subspace.ι
      (Z.genericPoint D.site D.base D.base_mem) with hξ
  have hξZ : ξ ∈ subspacePointSet D.site D.base D.base_mem X Z.subspace := ⟨_, rfl⟩
  obtain ⟨V, hV, hVfin⟩ := hT ξ
  refine hVfin.subset fun i hi => ?_
  exact ⟨ξ, hαT i Z (by simpa [Function.mem_support] using hi) hξZ, mem_of_mem_nhds hV⟩

/-- The coefficientwise sum of a family of `k`-cycles supported on the members of a locally
finite collection of subsets of `|X|` is a `k`-cycle: a neighbourhood of a point meeting only
finitely many of the `T_i` is shrunk, using the supports of those finitely many summands, to one
meeting only finitely many point sets of subspaces with a nonzero coefficient in the sum. -/
theorem locallyFiniteCycleSumCoeff_mem_cyclesOfDimension (sX : X ⟶ D.space) (k : ℤ)
    (T : I → Set (points D.site D.base D.base_mem X)) (hT : LocallyFinite T)
    (α : I → CycleGroup D sX k)
    (hαT : ∀ (i : I) (Z : IntegralClosedSubspace D.site D.base D.base_mem X),
      (α i).1 Z ≠ 0 → subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆ T i) :
    locallyFiniteCycleSumCoeff D sX k α ∈ cyclesOfDimension D sX k := by
  refine ⟨fun x => ?_, fun Z hZ => ?_⟩
  · obtain ⟨V, hV, hVfin⟩ := hT x
    choose U hU hUfin using fun i : I => (α i).2.1 x
    set F : Set I := {i : I | (T i ∩ V).Nonempty} with hF
    refine ⟨V ∩ (⋂ i ∈ F, U i),
      Filter.inter_mem hV ((Filter.biInter_mem hVfin).2 fun i _ => hU i), ?_⟩
    refine (hVfin.biUnion fun i _ => hUfin i).subset ?_
    intro Z hZ
    obtain ⟨p, hpZ, hpV⟩ := hZ
    by_cases hne : locallyFiniteCycleSumCoeff D sX k α Z = 0
    · simp [hne] at hpZ
    have hpZ' : p ∈ subspacePointSet D.site D.base D.base_mem X Z.subspace := by
      simpa [hne] using hpZ
    obtain ⟨i, hi⟩ := exists_ne_zero_of_locallyFiniteCycleSumCoeff_ne_zero D sX k α Z hne
    have hiF : i ∈ F := ⟨p, hαT i Z hi hpZ', hpV.1⟩
    refine Set.mem_iUnion₂.2 ⟨i, hiF, p, ?_, Set.mem_iInter₂.1 hpV.2 i hiF⟩
    simpa [hi] using hpZ'
  · obtain ⟨i, hi⟩ := exists_ne_zero_of_locallyFiniteCycleSumCoeff_ne_zero D sX k α Z hZ
    exact (α i).2.2 Z hi

/-- The sum `∑ α_i` of a family of `k`-cycles supported on the members of a locally finite
collection of subsets of `|X|`, as an element of `Z_k(X)`. -/
def locallyFiniteCycleSum (sX : X ⟶ D.space) (k : ℤ)
    (T : I → Set (points D.site D.base D.base_mem X)) (hT : LocallyFinite T)
    (α : I → CycleGroup D sX k)
    (hαT : ∀ (i : I) (Z : IntegralClosedSubspace D.site D.base D.base_mem X),
      (α i).1 Z ≠ 0 → subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆ T i) :
    CycleGroup D sX k :=
  ⟨locallyFiniteCycleSumCoeff D sX k α,
    locallyFiniteCycleSumCoeff_mem_cyclesOfDimension D sX k T hT α hαT⟩

/-- The coefficient of `∑ α_i` at an integral closed subspace is the sum of the coefficients of
the summands there. -/
@[simp]
theorem locallyFiniteCycleSum_apply (sX : X ⟶ D.space) (k : ℤ)
    (T : I → Set (points D.site D.base D.base_mem X)) (hT : LocallyFinite T)
    (α : I → CycleGroup D sX k)
    (hαT : ∀ (i : I) (Z : IntegralClosedSubspace D.site D.base D.base_mem X),
      (α i).1 Z ≠ 0 → subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆ T i)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (locallyFiniteCycleSum D sX k T hT α hαT).1 Z = ∑ᶠ i : I, (α i).1 Z :=
  rfl

/-! ### Rational equivalence on a subset -/

/-- Two `k`-cycles are *rationally equivalent on* a subset `T` of `|X|` when the rational
equivalence of Stacks 0EQ6 can be witnessed by a family `{W_j, f_j ∈ R(W_j)^*}` of integral
closed subspaces all of whose point sets are contained in `T`. -/
def RationallyEquivalentOn (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ)
    (T : Set (points D.site D.base D.base_mem X)) (α β : CycleGroup D sX k) : Prop :=
  ∃ (J : Type v) (W : J → IntegralClosedSubspace D.site D.base D.base_mem X)
    (hWfin : LocallyFinite fun j : J =>
      subspacePointSet D.site D.base D.base_mem X (W j).subspace)
    (c : ∀ j, CycleGroup D ((W j).subspace.ι ≫ sX) k),
    (∀ j, deltaDimension D sX (W j) = k + 1) ∧
      (∀ j, IsPrincipalDivisorCycle D ((W j).subspace.ι ≫ sX) k (c j)) ∧
        (∀ j, subspacePointSet D.site D.base D.base_mem X (W j).subspace ⊆ T) ∧
          α - β = cycleFamilySum D sX hX W hWfin k c

/-- Cycles rationally equivalent on a subset of `|X|` are rationally equivalent. -/
theorem RationallyEquivalentOn.rationallyEquivalent (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (k : ℤ) (T : Set (points D.site D.base D.base_mem X)) {α β : CycleGroup D sX k}
    (h : RationallyEquivalentOn.{v} D sX hX k T α β) :
    RationallyEquivalent.{v} D sX hX k α β := by
  obtain ⟨J, W, hWfin, c, hWdim, hWprin, -, hsum⟩ := h
  exact ⟨J, W, hWfin, c, hWdim, hWprin, hsum⟩

/-! ### Rational equivalence of the sums -/

/-- **Stacks 0EQ8.** Let `{T_i}_{i ∈ I}` be a locally finite collection of subsets of `|X|` and
let `α_i, β_i ∈ Z_k(X)` be supported on `T_i`. If `α_i ∼_rat β_i` on `T_i` for every `i`, then
`∑ α_i ∼_rat ∑ β_i`: the combined family `{W_{i, j}}_{i ∈ I, j ∈ J_i}` of witnessing subspaces
is locally finite, so it is a single rational equivalence between the two sums. -/
@[stacks 0EQ8 "the remark in full: for alpha_i, beta_i supported on a locally finite family \
T_i with alpha_i ~rat beta_i on T_i, the sums are k-cycles and are rationally equivalent, the \
combined witnessing family being locally finite"]
theorem rationallyEquivalent_locallyFiniteCycleSum (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ)
    (T : I → Set (points D.site D.base D.base_mem X)) (hT : LocallyFinite T)
    (α β : I → CycleGroup D sX k)
    (hαT : ∀ (i : I) (Z : IntegralClosedSubspace D.site D.base D.base_mem X),
      (α i).1 Z ≠ 0 → subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆ T i)
    (hβT : ∀ (i : I) (Z : IntegralClosedSubspace D.site D.base D.base_mem X),
      (β i).1 Z ≠ 0 → subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆ T i)
    (hαβ : ∀ i, RationallyEquivalentOn.{v} D sX hX k (T i) (α i) (β i)) :
    RationallyEquivalent.{v} D sX hX k (locallyFiniteCycleSum D sX k T hT α hαT)
      (locallyFiniteCycleSum D sX k T hT β hβT) := by
  classical
  choose J W hWfin c hWdim hWprin hWT hsum using hαβ
  have hfin : LocallyFinite fun ij : Σ i, J i =>
      subspacePointSet D.site D.base D.base_mem X (W ij.1 ij.2).subspace :=
    locallyFinite_sigma_of_subset hT hWfin hWT
  refine ⟨Σ i, J i, fun ij => W ij.1 ij.2, hfin, fun ij => c ij.1 ij.2,
    fun ij => hWdim ij.1 ij.2, fun ij => hWprin ij.1 ij.2, Subtype.ext (funext fun Z => ?_)⟩
  have hαfin := finite_support_locallyFiniteCycleCoeff D sX k T hT α hαT Z
  have hβfin := finite_support_locallyFiniteCycleCoeff D sX k T hT β hβT Z
  have hsigfin := finite_support_cycleFamilyCoeff D sX hX (fun ij : Σ i, J i => W ij.1 ij.2)
    hfin k (fun ij => c ij.1 ij.2) Z
  have hterm : ∀ i : I, (α i).1 Z - (β i).1 Z =
      ∑ᶠ j : J i, (integralClosedSubspacePushforward D sX hX (W i j) k (c i j)).1 Z := by
    intro i
    simpa using congrArg (fun γ : CycleGroup D sX k => γ.1 Z) (hsum i)
  show (∑ᶠ i : I, (α i).1 Z) - (∑ᶠ i : I, (β i).1 Z) = _
  rw [← finsum_sub_distrib hαfin hβfin, cycleFamilySum_apply]
  exact (finsum_congr hterm).trans (Stacks.Chow.finsum_sigma _ hsigfin).symm

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.InfiniteSumsRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.MaximalDeltaDimension

/-!
# Rational equivalence on a subset of the points

In Situation 0EDT let `X/B` be good and `T ⊆ |X|`. Two `k`-cycles are rationally equivalent on
`T` (`AlgebraicGeometry.Space.RationallyEquivalentOn`) when their difference is a locally finite
sum `∑ (i_j)_* div(f_j)` of principal divisors on integral closed subspaces `W_j` with
`|W_j| ⊆ T`. The cycles rationally equivalent to zero on `T` form a subgroup of `Z_k(X)`, so
rational equivalence on `T` is an equivalence relation compatible with the group structure; it
grows with `T`; and a locally finite sum of rational equivalences on subsets of `T` is one on
`T`, which is the form of Stacks 0EQ8 that keeps track of supports.

The point of tracking the subset is rigidity: if `T` is the point set of an integral closed
subspace `Z` of δ-dimension `k`, then two `k`-cycles rationally equivalent on `T` are equal,
because every integral closed subspace of `X` with point set inside `|Z|` has δ-dimension at
most `k`, while the witnesses of a rational equivalence of `k`-cycles have δ-dimension `k + 1`.

## Main definitions

* `AlgebraicGeometry.Space.PrivateChern.rationalEquivalencesOn`: the subgroup of `k`-cycles
  rationally equivalent to zero on `T`.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.rationallyEquivalentOn_iff_sub_mem`: rational
  equivalence on `T` is congruence modulo that subgroup.
* `AlgebraicGeometry.Space.PrivateChern.RationallyEquivalentOn.mono`: monotonicity in `T`.
* `AlgebraicGeometry.Space.PrivateChern.rationallyEquivalentOn_locallyFiniteCycleSum`:
  Stacks 0EQ8 on a subset.
* `AlgebraicGeometry.Space.PrivateChern.deltaDimension_le_of_subset`: the δ-dimension is
  monotone along inclusions of point sets.
* `AlgebraicGeometry.Space.PrivateChern.eq_of_rationallyEquivalentOn_integralClosedSubspace`:
  rigidity in the top dimension of an integral closed subspace.

## References

* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
* [Stacks Project, Tag 0EDX](https://stacks.math.columbia.edu/tag/0EDX)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space.PrivateChern

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (k : ℤ)

/-! ### The subgroup of cycles rationally equivalent to zero on a subset -/

/-- Two cycles are rationally equivalent on `T` once their difference agrees coefficientwise with
the sum of a family of principal divisors on integral closed subspaces inside `T`. -/
private theorem rationallyEquivalentOn_of_apply_sub_eq
    {T : Set (points D.site D.base D.base_mem X)} {α β : CycleGroup D sX k} {J : Type v}
    {W : J → IntegralClosedSubspace D.site D.base D.base_mem X}
    (hWfin : LocallyFinite fun j : J =>
      subspacePointSet D.site D.base D.base_mem X (W j).subspace)
    {c : ∀ j, CycleGroup D ((W j).subspace.ι ≫ sX) k}
    (hWdim : ∀ j, deltaDimension D sX (W j) = k + 1)
    (hWprin : ∀ j, IsPrincipalDivisorCycle D ((W j).subspace.ι ≫ sX) k (c j))
    (hWT : ∀ j, subspacePointSet D.site D.base D.base_mem X (W j).subspace ⊆ T)
    (h : ∀ Z, α.1 Z - β.1 Z =
      ∑ᶠ j, (integralClosedSubspacePushforward D sX hX (W j) k (c j)).1 Z) :
    RationallyEquivalentOn.{v} D sX hX k T α β :=
  ⟨J, W, hWfin, c, hWdim, hWprin, hWT,
    Subtype.ext (funext fun Z => (h Z).trans (cycleFamilySum_apply D sX hX W hWfin k c Z).symm)⟩

/-- The zero cycle is rationally equivalent to zero on any subset. -/
theorem rationallyEquivalentOn_zero_zero (T : Set (points D.site D.base D.base_mem X)) :
    RationallyEquivalentOn.{v} D sX hX k T 0 0 :=
  rationallyEquivalentOn_of_apply_sub_eq D sX hX k (W := fun j : PEmpty.{v + 1} => nomatch j)
    (locallyFinite_of_finite _) (c := fun j => nomatch j) (fun j => nomatch j)
    (fun j => nomatch j) (fun j => nomatch j) fun _ => by simp [finsum_of_isEmpty]

/-- Sums of cycles rationally equivalent to zero on `T` are rationally equivalent to zero on
`T`. -/
theorem RationallyEquivalentOn.add_zero_zero {T : Set (points D.site D.base D.base_mem X)}
    {α β : CycleGroup D sX k} (hα : RationallyEquivalentOn.{v} D sX hX k T α 0)
    (hβ : RationallyEquivalentOn.{v} D sX hX k T β 0) :
    RationallyEquivalentOn.{v} D sX hX k T (α + β) 0 := by
  obtain ⟨J, W, hWfin, c, hWdim, hWprin, hWT, hWsum⟩ := hα
  obtain ⟨K, V, hVfin, e, hVdim, hVprin, hVT, hVsum⟩ := hβ
  rw [sub_zero] at hWsum hVsum
  have hfin : LocallyFinite fun s : J ⊕ K =>
      subspacePointSet D.site D.base D.base_mem X (Sum.elim W V s).subspace :=
    by convert hWfin.sumElim hVfin using 1; exact (Sum.elim_comp_inl_inr _).symm
  refine rationallyEquivalentOn_of_apply_sub_eq D sX hX k hfin
    (c := fun s => match s with | .inl j => c j | .inr l => e l)
    (fun s => match s with | .inl j => hWdim j | .inr l => hVdim l)
    (fun s => match s with | .inl j => hWprin j | .inr l => hVprin l)
    (fun s => match s with | .inl j => hWT j | .inr l => hVT l) fun Z => ?_
  have hsplit : (fun s : J ⊕ K => (integralClosedSubspacePushforward D sX hX
        (Sum.elim W V s) k (match s with | .inl j => c j | .inr l => e l)).1 Z) =
      Sum.elim (fun j => (integralClosedSubspacePushforward D sX hX (W j) k (c j)).1 Z)
        (fun l => (integralClosedSubspacePushforward D sX hX (V l) k (e l)).1 Z) :=
    (Sum.elim_comp_inl_inr _).symm
  change (α + β).1 Z - 0 = _
  rw [sub_zero, hsplit, Stacks.Chow.finsum_sum_elim _ _
      (finite_support_cycleFamilyCoeff D sX hX W hWfin k c Z)
      (finite_support_cycleFamilyCoeff D sX hX V hVfin k e Z)]
  change α.1 Z + β.1 Z = _
  rw [hWsum, hVsum]
  show (cycleFamilySum D sX hX W hWfin k c).1 Z + (cycleFamilySum D sX hX V hVfin k e).1 Z = _
  rw [cycleFamilySum_apply, cycleFamilySum_apply]

/-- The negative of a cycle rationally equivalent to zero on `T` is rationally equivalent to
zero on `T`. -/
theorem RationallyEquivalentOn.neg_zero {T : Set (points D.site D.base D.base_mem X)}
    {α : CycleGroup D sX k} (hα : RationallyEquivalentOn.{v} D sX hX k T α 0) :
    RationallyEquivalentOn.{v} D sX hX k T (-α) 0 := by
  obtain ⟨J, W, hWfin, c, hWdim, hWprin, hWT, hWsum⟩ := hα
  rw [sub_zero] at hWsum
  refine rationallyEquivalentOn_of_apply_sub_eq D sX hX k hWfin (c := fun j => -c j) hWdim
    (fun j => isPrincipalDivisorCycle_neg D _ k (hWprin j)) hWT fun Z => ?_
  change -α.1 Z - 0 = _
  rw [sub_zero, hWsum]
  show -(cycleFamilySum D sX hX W hWfin k c).1 Z = _
  rw [cycleFamilySum_apply, ← finsum_neg_distrib]
  refine finsum_congr fun j => ?_
  rw [map_neg]
  rfl

/-- The subgroup of `k`-cycles rationally equivalent to zero on a subset `T ⊆ |X|`. -/
def rationalEquivalencesOn (T : Set (points D.site D.base D.base_mem X)) :
    AddSubgroup (CycleGroup D sX k) where
  carrier := {α | RationallyEquivalentOn.{v} D sX hX k T α 0}
  zero_mem' := rationallyEquivalentOn_zero_zero.{v} D sX hX k T
  add_mem' := RationallyEquivalentOn.add_zero_zero.{v} D sX hX k
  neg_mem' := RationallyEquivalentOn.neg_zero.{v} D sX hX k

/-- A `k`-cycle lies in `rationalEquivalencesOn T` if and only if it is rationally equivalent to
zero on `T`. -/
theorem mem_rationalEquivalencesOn {T : Set (points D.site D.base D.base_mem X)}
    {α : CycleGroup D sX k} :
    α ∈ rationalEquivalencesOn.{v} D sX hX k T ↔ RationallyEquivalentOn.{v} D sX hX k T α 0 :=
  Iff.rfl

/-- Rational equivalence on `T` is congruence modulo the cycles rationally equivalent to zero on
`T`. -/
theorem rationallyEquivalentOn_iff_sub_mem {T : Set (points D.site D.base D.base_mem X)}
    {α β : CycleGroup D sX k} :
    RationallyEquivalentOn.{v} D sX hX k T α β ↔
      α - β ∈ rationalEquivalencesOn.{v} D sX hX k T := by
  show _ ↔ RationallyEquivalentOn.{v} D sX hX k T (α - β) 0
  unfold RationallyEquivalentOn
  simp only [sub_zero]

/-- Two `k`-cycles `α` and `β` are rationally equivalent on `T` if and only if `α - β` is
rationally equivalent to zero on `T`. -/
theorem rationallyEquivalentOn_iff_zero {T : Set (points D.site D.base D.base_mem X)}
    {α β : CycleGroup D sX k} :
    RationallyEquivalentOn.{v} D sX hX k T α β ↔
      RationallyEquivalentOn.{v} D sX hX k T (α - β) 0 :=
  rationallyEquivalentOn_iff_sub_mem.{v} D sX hX k

/-- Rational equivalence on `T` is reflexive. -/
theorem rationallyEquivalentOn_refl (T : Set (points D.site D.base D.base_mem X))
    (α : CycleGroup D sX k) : RationallyEquivalentOn.{v} D sX hX k T α α := by
  rw [rationallyEquivalentOn_iff_sub_mem, sub_self]
  exact AddSubgroup.zero_mem _

variable {D sX hX k}

/-- Rational equivalence on `T` is symmetric. -/
theorem RationallyEquivalentOn.symm {T : Set (points D.site D.base D.base_mem X)}
    {α β : CycleGroup D sX k} (h : RationallyEquivalentOn.{v} D sX hX k T α β) :
    RationallyEquivalentOn.{v} D sX hX k T β α := by
  rw [rationallyEquivalentOn_iff_sub_mem] at h ⊢
  rw [← neg_sub]
  exact AddSubgroup.neg_mem _ h

/-- Rational equivalence on `T` is transitive. -/
theorem RationallyEquivalentOn.trans {T : Set (points D.site D.base D.base_mem X)}
    {α β γ : CycleGroup D sX k} (h₁ : RationallyEquivalentOn.{v} D sX hX k T α β)
    (h₂ : RationallyEquivalentOn.{v} D sX hX k T β γ) :
    RationallyEquivalentOn.{v} D sX hX k T α γ := by
  rw [rationallyEquivalentOn_iff_sub_mem] at h₁ h₂ ⊢
  rw [← sub_add_sub_cancel α β γ]
  exact AddSubgroup.add_mem _ h₁ h₂

/-- Rational equivalence on `T` is compatible with addition. -/
theorem RationallyEquivalentOn.add {T : Set (points D.site D.base D.base_mem X)}
    {α β α' β' : CycleGroup D sX k} (h : RationallyEquivalentOn.{v} D sX hX k T α β)
    (h' : RationallyEquivalentOn.{v} D sX hX k T α' β') :
    RationallyEquivalentOn.{v} D sX hX k T (α + α') (β + β') := by
  rw [rationallyEquivalentOn_iff_sub_mem] at h h' ⊢
  rw [add_sub_add_comm]
  exact AddSubgroup.add_mem _ h h'

/-- Rational equivalence on `T` is compatible with subtraction. -/
theorem RationallyEquivalentOn.sub {T : Set (points D.site D.base D.base_mem X)}
    {α β α' β' : CycleGroup D sX k} (h : RationallyEquivalentOn.{v} D sX hX k T α β)
    (h' : RationallyEquivalentOn.{v} D sX hX k T α' β') :
    RationallyEquivalentOn.{v} D sX hX k T (α - α') (β - β') := by
  rw [rationallyEquivalentOn_iff_sub_mem] at h h' ⊢
  rw [sub_sub_sub_comm]
  exact AddSubgroup.sub_mem _ h h'

/-- Rational equivalence on `T` is compatible with integer multiples. -/
theorem RationallyEquivalentOn.zsmul {T : Set (points D.site D.base D.base_mem X)}
    {α β : CycleGroup D sX k} (h : RationallyEquivalentOn.{v} D sX hX k T α β) (n : ℤ) :
    RationallyEquivalentOn.{v} D sX hX k T (n • α) (n • β) := by
  rw [rationallyEquivalentOn_iff_sub_mem] at h ⊢
  rw [← smul_sub]
  exact AddSubgroup.zsmul_mem _ h n

/-- Rational equivalence on `T` implies rational equivalence on any larger subset. -/
theorem RationallyEquivalentOn.mono {T T' : Set (points D.site D.base D.base_mem X)}
    (hTT' : T ⊆ T') {α β : CycleGroup D sX k}
    (h : RationallyEquivalentOn.{v} D sX hX k T α β) :
    RationallyEquivalentOn.{v} D sX hX k T' α β := by
  obtain ⟨J, W, hWfin, c, hWdim, hWprin, hWT, hsum⟩ := h
  exact ⟨J, W, hWfin, c, hWdim, hWprin, fun j => (hWT j).trans hTT', hsum⟩

/-- Rational equivalence to zero on a subset gives rational equivalence to zero. -/
theorem RationallyEquivalentOn.isRationallyEquivalentToZero
    {T : Set (points D.site D.base D.base_mem X)} {α : CycleGroup D sX k}
    (h : RationallyEquivalentOn.{v} D sX hX k T α 0) :
    IsRationallyEquivalentToZero.{v} D sX hX k α := by
  obtain ⟨J, W, hWfin, c, hWdim, hWprin, -, hsum⟩ := h
  rw [sub_zero] at hsum
  exact ⟨J, W, hWfin, c, hWdim, hWprin, hsum⟩

/-- A cycle rationally equivalent to zero is rationally equivalent to zero on the whole of
`|X|`. -/
theorem rationallyEquivalentOn_univ_of_isRationallyEquivalentToZero {α : CycleGroup D sX k}
    (h : IsRationallyEquivalentToZero.{v} D sX hX k α) :
    RationallyEquivalentOn.{v} D sX hX k Set.univ α 0 := by
  obtain ⟨J, W, hWfin, c, hWdim, hWprin, hsum⟩ := h
  exact ⟨J, W, hWfin, c, hWdim, hWprin, fun _ => Set.subset_univ _, by rw [sub_zero]; exact hsum⟩

variable (D sX hX k)

/-! ### Locally finite sums -/

/-- **Stacks 0EQ8, on a subset.** Let `{T_i}` be a locally finite collection of subsets of `|X|`
contained in `T`, and let `α_i, β_i` be `k`-cycles supported on `T_i` with `α_i ∼_rat β_i` on
`T_i`. Then `∑ α_i ∼_rat ∑ β_i` on `T`. -/
theorem rationallyEquivalentOn_locallyFiniteCycleSum {I : Type v}
    (T : Set (points D.site D.base D.base_mem X))
    (Ti : I → Set (points D.site D.base D.base_mem X)) (hT : LocallyFinite Ti)
    (hTi : ∀ i, Ti i ⊆ T) (α β : I → CycleGroup D sX k)
    (hαT : ∀ (i : I) (Z : IntegralClosedSubspace D.site D.base D.base_mem X),
      (α i).1 Z ≠ 0 → subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆ Ti i)
    (hβT : ∀ (i : I) (Z : IntegralClosedSubspace D.site D.base D.base_mem X),
      (β i).1 Z ≠ 0 → subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆ Ti i)
    (hαβ : ∀ i, RationallyEquivalentOn.{v} D sX hX k (Ti i) (α i) (β i)) :
    RationallyEquivalentOn.{v} D sX hX k T (locallyFiniteCycleSum D sX k Ti hT α hαT)
      (locallyFiniteCycleSum D sX k Ti hT β hβT) := by
  classical
  choose J W hWfin c hWdim hWprin hWT hsum using hαβ
  have hfin : LocallyFinite fun ij : Σ i, J i =>
      subspacePointSet D.site D.base D.base_mem X (W ij.1 ij.2).subspace :=
    locallyFinite_sigma_of_subset hT hWfin hWT
  refine rationallyEquivalentOn_of_apply_sub_eq D sX hX k hfin (c := fun ij => c ij.1 ij.2)
    (fun ij => hWdim ij.1 ij.2) (fun ij => hWprin ij.1 ij.2)
    (fun ij => (hWT ij.1 ij.2).trans (hTi ij.1)) fun Z => ?_
  have hαfin := finite_support_locallyFiniteCycleCoeff D sX k Ti hT α hαT Z
  have hβfin := finite_support_locallyFiniteCycleCoeff D sX k Ti hT β hβT Z
  have hsigfin := finite_support_cycleFamilyCoeff D sX hX (fun ij : Σ i, J i => W ij.1 ij.2)
    hfin k (fun ij => c ij.1 ij.2) Z
  have hterm : ∀ i : I, (α i).1 Z - (β i).1 Z =
      ∑ᶠ j : J i, (integralClosedSubspacePushforward D sX hX (W i j) k (c i j)).1 Z := by
    intro i
    simpa using congrArg (fun γ : CycleGroup D sX k => γ.1 Z) (hsum i)
  show (∑ᶠ i : I, (α i).1 Z) - (∑ᶠ i : I, (β i).1 Z) = _
  rw [← finsum_sub_distrib hαfin hβfin]
  exact (finsum_congr hterm).trans (Stacks.Chow.finsum_sigma _ hsigfin).symm

/-! ### Rigidity in the top dimension -/

include hX in
/-- **The δ-dimension is monotone.** An integral closed subspace whose point set lies in that of
another has at most its δ-dimension. -/
theorem deltaDimension_le_of_subset (W Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hWZ : subspacePointSet D.site D.base D.base_mem X W.subspace ⊆
      subspacePointSet D.site D.base D.base_mem X Z.subspace) :
    deltaDimension D sX W ≤ deltaDimension D sX Z := by
  set ξ := pointsMap D.site D.base D.base_mem W.subspace.toFunctor W.subspace.ι
    (W.genericPoint D.site D.base D.base_mem)
  set η := pointsMap D.site D.base D.base_mem Z.subspace.toFunctor Z.subspace.ι
    (Z.genericPoint D.site D.base D.base_mem)
  have hξ : ξ ∈ subspacePointSet D.site D.base D.base_mem X Z.subspace := hWZ ⟨_, rfl⟩
  have hηgen : IsGenericPoint η (subspacePointSet D.site D.base D.base_mem X Z.subspace) :=
    isGenericPoint_pointsMap_genericPoint D.site D.base D.base_mem hX.1 Z
  have hspec : η ⤳ ξ := hηgen.specializes hξ
  have hanti : ∀ ⦃x y : points D.site D.base D.base_mem X⦄, x ⤳ y → x ≠ y →
      inducedDimensionValue D.site D.base D.base_mem D.delta sX y <
        inducedDimensionValue D.site D.base D.base_mem D.delta sX x :=
    lt_inducedDimensionValue_of_specializes D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX) D.isAlgebraicSpace
      (isDecentSpace_of_isAbsolutelyQuasiSeparated D.site D.base D.base_mem D.space
        D.isAlgebraicSpace D.quasiSeparated)
      D.locallyNoetherian D.universallyCatenary D.delta sX hX.2.2
  by_cases h : η = ξ
  · exact le_of_eq (congrArg (D.deltaValue sX) h.symm)
  · exact le_of_lt (hanti hspec h)

/-- **Rigidity in the top dimension.** Let `Z ⊆ X` be an integral closed subspace of
δ-dimension `k`. Two `k`-cycles rationally equivalent on `|Z|` are equal. -/
theorem eq_of_rationallyEquivalentOn_integralClosedSubspace
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) (hZ : deltaDimension D sX Z = k)
    {α β : CycleGroup D sX k}
    (h : RationallyEquivalentOn.{v} D sX hX k
      (subspacePointSet D.site D.base D.base_mem X Z.subspace) α β) : α = β := by
  obtain ⟨J, W, hWfin, c, hWdim, -, hWT, hsum⟩ := h
  have : IsEmpty J := ⟨fun j => by
    have := deltaDimension_le_of_subset D sX hX (W j) Z (hWT j)
    rw [hWdim j, hZ] at this
    omega⟩
  rw [← sub_eq_zero, hsum]
  exact Subtype.ext (funext fun Z => by
    rw [cycleFamilySum_apply, finsum_of_isEmpty]
    rfl)

end AlgebraicGeometry.Space.PrivateChern

end

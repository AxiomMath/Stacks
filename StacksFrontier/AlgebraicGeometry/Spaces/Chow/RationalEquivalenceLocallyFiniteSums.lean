module

public import StacksFrontier.AlgebraicGeometry.Chow.CycleAdditivity
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalenceSums
public import StacksFrontier.Topology.LocallyFinite.Sigma

/-!
# Locally finite sums of cycles rationally equivalent to zero on an algebraic space

In the situation of Stacks 0EDT let `X/B` be good. A `k`-cycle `α` on `X` is rationally
equivalent to zero (Stacks 0EQ6) when it is `∑ (i_j)_* div(f_j)` for a locally finite family of
integral closed subspaces `W_j ⊆ X` of δ-dimension `k + 1` and `f_j ∈ R(W_j)^*`. The sum of two
such cycles is again one, but an *infinite* locally finite sum of cycles each rationally
equivalent to zero need not be (Stacks 0EQ8).

Fix for every integral closed subspace `W ⊆ X` a set `P(W)` of `k`-cycles on `W`. A cycle is a
*sum of members of `P` within* a set `T ⊆ |X|` when it is `∑ (i_j)_* c_j` for a locally finite
family of integral closed subspaces `W_j` with point sets in `T` and `c_j ∈ P(W_j)`. If the
members `β_i` of a family of cycles are such sums within the members `T_i` of a locally finite
family of sets, then every cycle which is coefficientwise `∑ β_i` is one, within `⋃ T_i`.

For `P(W)` the principal divisors of Stacks 0EQ6 on `W` of δ-dimension `k + 1` this is rational
equivalence to zero within `T`.

## Main definitions

* `AlgebraicGeometry.Space.IsCycleFamilySumWithin`: `α` is a locally finite sum of pushforwards
  of members of a prescribed class of cycles on integral closed subspaces inside a given set.

## Main results

* `AlgebraicGeometry.Space.IsCycleFamilySumWithin.add`, `.neg`, `.sub`, `.zsmul`: for a fixed set
  these sums form a subgroup, when the classes are closed under negation.
* `AlgebraicGeometry.Space.isCycleFamilySumWithin_finsum`: the locally finite sum of Stacks 0EQ8,
  with the witnesses in the union of the sets.
* `AlgebraicGeometry.Space.IsCycleFamilySumWithin.isRationallyEquivalentToZeroWithin` and
  `AlgebraicGeometry.Space.IsRationallyEquivalentToZeroWithin.isCycleFamilySumWithin`: rational
  equivalence to zero within a set (`AlgebraicGeometry.Space.IsRationallyEquivalentToZeroWithin`)
  is a sum within it of principal divisors.
* `AlgebraicGeometry.Space.isRationallyEquivalentToZero_finsum_max`: the locally finite sum of
  Stacks 0EQ8, forgetting the set.

## References

* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u v w

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (k : ℤ)

/-! ### Locally finite sums of a prescribed class of cycles -/

/-- Given for every integral closed subspace `W ⊆ X` a set `P W` of `k`-cycles on `W`, a `k`-cycle
`α` on `X` is a *sum of members of `P` within* a set `T ⊆ |X|` when it is a locally finite sum
`∑ (i_j)_* c_j` over integral closed subspaces `W_j` whose point sets lie in `T`, with
`c_j ∈ P W_j`. -/
def IsCycleFamilySumWithin
    (P : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      Set (CycleGroup D (W.subspace.ι ≫ sX) k))
    (α : CycleGroup D sX k) (T : Set (points D.site D.base D.base_mem X)) : Prop :=
  ∃ (J : Type v) (W : J → IntegralClosedSubspace D.site D.base D.base_mem X)
    (hWfin : LocallyFinite fun j : J =>
      subspacePointSet D.site D.base D.base_mem X (W j).subspace)
    (c : ∀ j, CycleGroup D ((W j).subspace.ι ≫ sX) k),
    (∀ j, subspacePointSet D.site D.base D.base_mem X (W j).subspace ⊆ T) ∧
      (∀ j, c j ∈ P (W j)) ∧ α = cycleFamilySum D sX hX W hWfin k c

variable {D sX hX k}
variable {P Q : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
  Set (CycleGroup D (W.subspace.ι ≫ sX) k)}

/-- Enlarging the set preserves being a sum of members of `P` within it. -/
theorem IsCycleFamilySumWithin.mono {α : CycleGroup D sX k}
    {T T' : Set (points D.site D.base D.base_mem X)}
    (h : IsCycleFamilySumWithin.{u, v} D sX hX k P α T) (hTT' : T ⊆ T') :
    IsCycleFamilySumWithin.{u, v} D sX hX k P α T' := by
  obtain ⟨J, W, hWfin, c, hsub, hP, hsum⟩ := h
  exact ⟨J, W, hWfin, c, fun j => (hsub j).trans hTT', hP, hsum⟩

/-- Enlarging the classes of summands preserves being a sum of their members. -/
theorem IsCycleFamilySumWithin.of_subset {α : CycleGroup D sX k}
    {T : Set (points D.site D.base D.base_mem X)}
    (h : IsCycleFamilySumWithin.{u, v} D sX hX k P α T) (hPQ : ∀ W, P W ⊆ Q W) :
    IsCycleFamilySumWithin.{u, v} D sX hX k Q α T := by
  obtain ⟨J, W, hWfin, c, hsub, hP, hsum⟩ := h
  exact ⟨J, W, hWfin, c, hsub, fun j => hPQ _ (hP j), hsum⟩

/-- A cycle whose coefficients are the sums of those of the pushforwards `(i_j)_* c_j` is
`∑ (i_j)_* c_j`. -/
private theorem eq_cycleFamilySum_of_apply {J : Type v} {α : CycleGroup D sX k}
    {W : J → IntegralClosedSubspace D.site D.base D.base_mem X}
    {hWfin : LocallyFinite fun j : J => subspacePointSet D.site D.base D.base_mem X (W j).subspace}
    {c : ∀ j, CycleGroup D ((W j).subspace.ι ≫ sX) k}
    (h : ∀ Z, α.1 Z = ∑ᶠ j : J, (integralClosedSubspacePushforward D sX hX (W j) k (c j)).1 Z) :
    α = cycleFamilySum D sX hX W hWfin k c :=
  Subtype.ext (funext h)

variable (D sX hX k) in
/-- The zero cycle is a sum of members of any classes within any set. -/
theorem isCycleFamilySumWithin_zero (T : Set (points D.site D.base D.base_mem X)) :
    IsCycleFamilySumWithin.{u, v} D sX hX k P 0 T := by
  exact ⟨PEmpty.{v + 1}, (fun j => nomatch j), locallyFinite_of_finite _, (fun j => nomatch j),
    (fun j => nomatch j), (fun j => nomatch j),
    eq_cycleFamilySum_of_apply fun _ => (finsum_of_isEmpty _).symm⟩

variable (D sX hX k) in
/-- The pushforward of one member of `P W`, for an integral closed subspace `W ⊆ X`, is a sum of
members of `P` within `|W|`. -/
theorem isCycleFamilySumWithin_integralClosedSubspacePushforward
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    {c : CycleGroup D (W.subspace.ι ≫ sX) k} (hc : c ∈ P W) :
    IsCycleFamilySumWithin.{u, v} D sX hX k P (integralClosedSubspacePushforward D sX hX W k c)
      (subspacePointSet D.site D.base D.base_mem X W.subspace) := by
  refine ⟨PUnit.{v + 1}, fun _ => W, locallyFinite_of_finite _, fun _ => c, fun _ => subset_rfl,
    fun _ => hc, eq_cycleFamilySum_of_apply fun _ => by rw [finsum_unique]⟩

/-- The sum of two sums of members of `P` within a set is one. -/
theorem IsCycleFamilySumWithin.add {α β : CycleGroup D sX k}
    {T : Set (points D.site D.base D.base_mem X)}
    (hα : IsCycleFamilySumWithin.{u, v} D sX hX k P α T)
    (hβ : IsCycleFamilySumWithin.{u, v} D sX hX k P β T) :
    IsCycleFamilySumWithin.{u, v} D sX hX k P (α + β) T := by
  obtain ⟨J, W, hWfin, c, hWsub, hWP, rfl⟩ := hα
  obtain ⟨K, V, hVfin, e, hVsub, hVP, rfl⟩ := hβ
  have hfin : LocallyFinite fun s : J ⊕ K =>
      subspacePointSet D.site D.base D.base_mem X (Sum.elim W V s).subspace := by
    have hsets : (fun s : J ⊕ K =>
        subspacePointSet D.site D.base D.base_mem X (Sum.elim W V s).subspace) =
        Sum.elim (fun j => subspacePointSet D.site D.base D.base_mem X (W j).subspace)
          (fun l => subspacePointSet D.site D.base D.base_mem X (V l).subspace) :=
      funext fun s => by cases s <;> rfl
    rw [hsets]
    exact hWfin.sumElim hVfin
  refine ⟨J ⊕ K, Sum.elim W V, hfin,
    (fun s => match s with | .inl j => c j | .inr l => e l),
    (fun s => match s with | .inl j => hWsub j | .inr l => hVsub l),
    (fun s => match s with | .inl j => hWP j | .inr l => hVP l),
    eq_cycleFamilySum_of_apply fun Z => ?_⟩
  have hsplit : (fun s : J ⊕ K => (integralClosedSubspacePushforward D sX hX
        (Sum.elim W V s) k (match s with | .inl j => c j | .inr l => e l)).1 Z) =
      Sum.elim (fun j => (integralClosedSubspacePushforward D sX hX (W j) k (c j)).1 Z)
        (fun l => (integralClosedSubspacePushforward D sX hX (V l) k (e l)).1 Z) :=
    funext fun s => by cases s <;> rfl
  rw [hsplit, Stacks.Chow.finsum_sum_elim _ _
    (finite_support_cycleFamilyCoeff D sX hX W hWfin k c Z)
    (finite_support_cycleFamilyCoeff D sX hX V hVfin k e Z)]
  rfl

/-- When the classes `P W` are closed under negation, the negative of a sum of members of `P`
within a set is one. -/
theorem IsCycleFamilySumWithin.neg {α : CycleGroup D sX k}
    {T : Set (points D.site D.base D.base_mem X)}
    (hα : IsCycleFamilySumWithin.{u, v} D sX hX k P α T) (hP : ∀ {W c}, c ∈ P W → -c ∈ P W) :
    IsCycleFamilySumWithin.{u, v} D sX hX k P (-α) T := by
  obtain ⟨J, W, hWfin, c, hWsub, hWP, rfl⟩ := hα
  refine ⟨J, W, hWfin, (fun j => -c j), hWsub, (fun j => hP (hWP j)),
    eq_cycleFamilySum_of_apply fun Z => ?_⟩
  change -∑ᶠ j : J, _ = _
  rw [← finsum_neg_distrib]
  exact finsum_congr fun j => by rw [map_neg]; rfl

/-- When the classes `P W` are closed under negation, the difference of two sums of members of
`P` within a set is one. -/
theorem IsCycleFamilySumWithin.sub {α β : CycleGroup D sX k}
    {T : Set (points D.site D.base D.base_mem X)}
    (hα : IsCycleFamilySumWithin.{u, v} D sX hX k P α T)
    (hβ : IsCycleFamilySumWithin.{u, v} D sX hX k P β T) (hP : ∀ {W c}, c ∈ P W → -c ∈ P W) :
    IsCycleFamilySumWithin.{u, v} D sX hX k P (α - β) T := by
  rw [sub_eq_add_neg]
  exact hα.add (hβ.neg hP)

/-- When the classes `P W` are closed under negation, an integer multiple of a sum of members of
`P` within a set is one. -/
theorem IsCycleFamilySumWithin.zsmul {α : CycleGroup D sX k}
    {T : Set (points D.site D.base D.base_mem X)}
    (hα : IsCycleFamilySumWithin.{u, v} D sX hX k P α T) (hP : ∀ {W c}, c ∈ P W → -c ∈ P W)
    (n : ℤ) : IsCycleFamilySumWithin.{u, v} D sX hX k P (n • α) T := by
  induction n using Int.induction_on with
  | zero => rw [zero_smul]; exact isCycleFamilySumWithin_zero D sX hX k T
  | succ n ih => rw [add_smul, one_smul]; exact ih.add hα
  | pred n ih => rw [sub_smul, one_smul]; exact ih.sub hα hP

variable (D sX hX k) in
/-- Let `{T_i}` be a locally finite family of subsets of `|X|` and let `β_i` be `k`-cycles on
`X`, each a sum of members of `P` within `T_i`. A `k`-cycle `α` which is coefficientwise `∑ β_i`
is a sum of members of `P` within `⋃ T_i`. -/
theorem isCycleFamilySumWithin_finsum {I : Type w}
    (T : I → Set (points D.site D.base D.base_mem X)) (hT : LocallyFinite T)
    (β : I → CycleGroup D sX k)
    (hβ : ∀ i, IsCycleFamilySumWithin.{u, v} D sX hX k P (β i) (T i))
    {α : CycleGroup D sX k} (hα : ∀ Z, α.1 Z = ∑ᶠ i : I, (β i).1 Z) :
    IsCycleFamilySumWithin.{u, max w v} D sX hX k P α (⋃ i, T i) := by
  choose J W hWfin c hsub hP hsum using hβ
  have hfin : LocallyFinite fun ij : (i : I) × J i =>
      subspacePointSet D.site D.base D.base_mem X (W ij.1 ij.2).subspace :=
    locallyFinite_sigma_of_subset hT hWfin hsub
  refine ⟨(i : I) × J i, fun ij => W ij.1 ij.2, hfin, fun ij => c ij.1 ij.2,
    fun ij => (hsub ij.1 ij.2).trans (Set.subset_iUnion T ij.1), fun ij => hP ij.1 ij.2, ?_⟩
  refine eq_cycleFamilySum_of_apply fun Z => ?_
  rw [hα Z, Stacks.Chow.finsum_sigma _
    (finite_support_cycleFamilyCoeff D sX hX (fun ij : (i : I) × J i => W ij.1 ij.2) hfin k
      (fun ij => c ij.1 ij.2) Z)]
  exact finsum_congr fun i => by rw [hsum i, cycleFamilySum_apply]

/-! ### Rational equivalence within a set -/

/-- A sum within `T ⊆ |X|` of principal divisors on integral closed subspaces `W` of
δ-dimension `k + 1` is rationally equivalent to zero within `T`
(`AlgebraicGeometry.Space.IsRationallyEquivalentToZeroWithin`). -/
theorem IsCycleFamilySumWithin.isRationallyEquivalentToZeroWithin {α : CycleGroup D sX k}
    {T : Set (points D.site D.base D.base_mem X)}
    (h : IsCycleFamilySumWithin.{u, v} D sX hX k
      (fun W => {c | IsPrincipalDivisorCycle D (W.subspace.ι ≫ sX) k c ∧
        deltaDimension D sX W = k + 1}) α T) :
    IsRationallyEquivalentToZeroWithin.{v} D sX hX k α T := by
  obtain ⟨J, W, hWfin, c, hsub, hP, hsum⟩ := h
  exact ⟨J, W, hWfin, c, hsub, fun j => (hP j).2, fun j => (hP j).1, hsum⟩

/-- A cycle rationally equivalent to zero within a set is a sum within it of principal divisors
on integral closed subspaces of δ-dimension `k + 1`. -/
theorem IsRationallyEquivalentToZeroWithin.isCycleFamilySumWithin {α : CycleGroup D sX k}
    {T : Set (points D.site D.base D.base_mem X)}
    (h : IsRationallyEquivalentToZeroWithin.{v} D sX hX k α T) :
    IsCycleFamilySumWithin.{u, v} D sX hX k
      (fun W => {c | IsPrincipalDivisorCycle D (W.subspace.ι ≫ sX) k c ∧
        deltaDimension D sX W = k + 1}) α T := by
  obtain ⟨J, W, hWfin, c, hsub, hdim, hprin, hsum⟩ := h
  exact ⟨J, W, hWfin, c, hsub, fun j => ⟨hprin j, hdim j⟩, hsum⟩

/-- The negative of a principal divisor on an integral closed subspace of δ-dimension `k + 1` is
one. -/
theorem neg_mem_principalDivisors {W : IntegralClosedSubspace D.site D.base D.base_mem X}
    {c : CycleGroup D (W.subspace.ι ≫ sX) k}
    (h : c ∈ {c | IsPrincipalDivisorCycle D (W.subspace.ι ≫ sX) k c ∧
      deltaDimension D sX W = k + 1}) :
    -c ∈ {c | IsPrincipalDivisorCycle D (W.subspace.ι ≫ sX) k c ∧
      deltaDimension D sX W = k + 1} :=
  ⟨isPrincipalDivisorCycle_neg (h := h.1), h.2⟩

variable (D sX hX k) in
/-- A cycle which is coefficientwise a locally finite sum of cycles rationally equivalent to
zero within the members of a locally finite family of sets is rationally equivalent to zero. -/
theorem isRationallyEquivalentToZero_finsum_max {I : Type w}
    (T : I → Set (points D.site D.base D.base_mem X)) (hT : LocallyFinite T)
    (β : I → CycleGroup D sX k)
    (hβ : ∀ i, IsRationallyEquivalentToZeroWithin.{v} D sX hX k (β i) (T i))
    {α : CycleGroup D sX k} (hα : ∀ Z, α.1 Z = ∑ᶠ i : I, (β i).1 Z) :
    IsRationallyEquivalentToZero.{max w v} D sX hX k α :=
  (isCycleFamilySumWithin_finsum D sX hX k T hT β (fun i => (hβ i).isCycleFamilySumWithin)
    hα).isRationallyEquivalentToZeroWithin.isRationallyEquivalentToZero

end AlgebraicGeometry.Space

end

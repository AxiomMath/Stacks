module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralGoodSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisorCycleOfGood

/-!
# Rational equivalence and the Chow group at the canonical embeddings of Stacks 0ENK

In the situation of Stacks 0EDT let `X/B` be good and let `k ∈ ℤ`. **Stacks 0EQ6** calls a
`k`-cycle `α ∈ Z_k(X)` *rationally equivalent to zero* when it is a sum

`α = ∑ (i_j)_* div(f_j)`

over a locally finite family `{W_j ⊆ X}` of integral closed subspaces with
`dim_δ(W_j) = k + 1`, with `f_j ∈ R(W_j)^*`; two cycles are *rationally equivalent* when their
difference is rationally equivalent to zero, and `CH_k(X)` is the quotient of `Z_k(X)` by
rational equivalence.

Reading the summand `div(f_j)` requires, at every prime divisor `ξ` of `W_j`, the embedding
`R(W_j) → Q(𝒪^h_{W_j,ξ})` of Stacks 0ENK; the coefficients `ord_ξ(f_j)` depend on it, so a cycle
is the principal divisor of `f_j` only relative to a choice of that embedding. This file reads
the summand at the *canonical* embeddings of Stacks 0ENK, which for the good integral `W_j` are
constructed, not chosen: the summand condition is
`AlgebraicGeometry.Space.IsPrincipalDivisorCycleOfGood`, which pins the embedding to
`AlgebraicGeometry.Space.genericFractionEmbedding` and quantifies nothing but the source's `f_j`.
So the subgroup of cycles rationally equivalent to zero built here consists exactly of the cycles
the source displays, and the quotient by it is the source's `CH_k(X)`.

This file is parts (2), (3) and (4) of Stacks 0EQ6 read that way. Part (1) — that the displayed
sum is a well-defined `k`-cycle — is `AlgebraicGeometry.Space.cycleFamilySum`, and the goodness
and integrality of `W_j` that the canonical embeddings need are not hypotheses here: they are
`AlgebraicGeometry.Space.isGood_integralClosedSubspace` applied to `X/B` good, and the
`isIntegralSpace` field of an integral closed subspace.

## Main definitions

* `AlgebraicGeometry.Space.IsRationallyEquivalentToZeroCanonical`: a `k`-cycle is rationally
  equivalent to zero (Stacks 0EQ6, part (2)).
* `AlgebraicGeometry.Space.rationalEquivalencesCanonical`: the subgroup of `Z_k(X)` of cycles
  rationally equivalent to zero.
* `AlgebraicGeometry.Space.RationallyEquivalentCanonical`: rational equivalence of `k`-cycles
  (Stacks 0EQ6, part (3)).
* `AlgebraicGeometry.Space.chowGroupCanonical`: the Chow group `CH_k(X) = Z_k(X)/∼_rat`
  (Stacks 0EQ6, part (4)).
* `AlgebraicGeometry.Space.chowClassCanonical`: the class map `Z_k(X) → CH_k(X)`.

## Main results

* `AlgebraicGeometry.Space.rationallyEquivalentCanonical_equivalence`: rational equivalence is an
  equivalence relation.
* `AlgebraicGeometry.Space.chowClassCanonical_cycleFamilySum_eq_zero`: the class of a sum
  `∑ (i_j)_* div(f_j)` is zero in `CH_k(X)`.
* `AlgebraicGeometry.Space.chowClassCanonical_eq_iff_rationallyEquivalentCanonical`: two cycles
  have the same class exactly when they are rationally equivalent.
* `AlgebraicGeometry.Space.rationalEquivalencesCanonical_le_rationalEquivalences` and
  `AlgebraicGeometry.Space.chowGroupCanonicalToChowGroup`: the comparison with the reading of
  rational equivalence in which the embedding is quantified existentially.

## Implementation notes

### Comparison with the existentially quantified reading

`AlgebraicGeometry.Space.IsPrincipalDivisorCycle` asks of a summand only that *some* ring map
`R(W) → Q(𝒪^h_{W,ξ})` make its coefficients come out as the orders of vanishing of `f`. The
canonical data of Stacks 0ENK is such a ring map, so the condition used here implies that one,
whence `AlgebraicGeometry.Space.rationalEquivalencesCanonical_le_rationalEquivalences` and the
surjection `AlgebraicGeometry.Space.chowGroupCanonicalToChowGroup`.

The converse of that comparison fails. A ring map `R(W) → Q(𝒪^h_{W,ξ})` unrelated to the
canonical one — the embeddings may moreover be chosen independently at each `W` — gives orders of
vanishing unrelated to those of `f`, so a cycle can satisfy the existential condition without
being a principal divisor. Nothing identifies the cycles counted that way with the ones the
source displays, so the subgroup they generate is in general strictly larger and its quotient is
in general a proper quotient of `CH_k(X)`. Consequently
`AlgebraicGeometry.Space.chowGroupCanonicalToChowGroup` is surjective but is not claimed
injective.

### `f ∈ R(W)^*` is `IsUnit f`

As in `AlgebraicGeometry.Space.IsPrincipalDivisorCycleOfGood`, the source's `f_j ∈ R(W_j)^*` is
read as `IsUnit f_j` in the ring of rational functions of `W_j`. This is what makes the set of
cycles rationally equivalent to zero closed under negation, `div(f⁻¹) = -div(f)` needing an
inverse of `f` itself.

### The quotient is by the set, not by the subgroup it generates

`AlgebraicGeometry.Space.rationalEquivalencesCanonical` has as its carrier exactly the set of
cycles the source calls rationally equivalent to zero: the three closure properties are proved —
the empty family for `0`, the disjoint union of two families for a sum, and the inverse functions
for a negative — so `CH_k(X)` is the honest quotient `Z_k(X)/∼_rat`.

### The index universe

The source's family `{W_j}_{j ∈ J}` has an unrestricted index set; here `J` ranges over a
universe `v` which is a parameter of the definitions.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EQ1](https://stacks.math.columbia.edu/tag/0EQ1)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Rational equivalence at the canonical embeddings -/

section RationalEquivalence

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- A `k`-cycle on a good algebraic space `X/B` is *rationally equivalent to zero* when it is
the cycle `∑ (i_j)_* div(f_j)` of part (1): there is a locally finite family `{W_j ⊆ X}` of
integral closed subspaces with `dim_δ(W_j) = k + 1`, and on each a rational function
`f_j ∈ R(W_j)^*` whose principal divisor `div(f_j)` is the `j`-th summand, the pushforwards
summing to the cycle.

Each `W_j` is good over `B` by `AlgebraicGeometry.Space.isGood_integralClosedSubspace` and
integral by definition, so `div(f_j)` is read at the canonical embeddings
`R(W_j) → Q(𝒪^h_{W_j,ξ})` of Stacks 0ENK and depends on nothing but `f_j`: the summand condition
is `AlgebraicGeometry.Space.IsPrincipalDivisorCycleOfGood`. The sum is
`AlgebraicGeometry.Space.cycleFamilySum`. -/
@[stacks 0EQ6 "part (2): rationally equivalent to zero, the summands being principal divisors \
at the canonical embeddings of Stacks 0ENK. The sum is part (1), \
AlgebraicGeometry.Space.cycleFamilySum; the index type ranges over the universe v"]
def IsRationallyEquivalentToZeroCanonical (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ)
    (α : CycleGroup D sX k) : Prop :=
  ∃ (J : Type v) (W : J → IntegralClosedSubspace D.site D.base D.base_mem X)
    (hWfin : LocallyFinite fun j : J =>
      subspacePointSet D.site D.base D.base_mem X (W j).subspace)
    (c : ∀ j, CycleGroup D ((W j).subspace.ι ≫ sX) k),
    (∀ j, deltaDimension D sX (W j) = k + 1) ∧
      (∀ j, IsPrincipalDivisorCycleOfGood D ((W j).subspace.ι ≫ sX)
        (isGood_integralClosedSubspace D sX hX (W j)) (W j).isIntegralSpace k (c j)) ∧
        α = cycleFamilySum D sX hX W hWfin k c

/-- The zero cycle is rationally equivalent to zero, via the empty family. -/
theorem isRationallyEquivalentToZeroCanonical_zero (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (k : ℤ) : IsRationallyEquivalentToZeroCanonical.{v} D sX hX k 0 := by
  have hcoeff : cycleFamilySumCoeff D sX hX (fun j : PEmpty.{v + 1} => nomatch j) k
      (fun j => nomatch j) = 0 := funext fun _ => finsum_of_isEmpty _
  exact ⟨PEmpty.{v + 1}, (fun j => nomatch j), locallyFinite_of_finite _, (fun j => nomatch j),
    (fun j => nomatch j), (fun j => nomatch j), Subtype.ext hcoeff.symm⟩

/-- The sum of two cycles rationally equivalent to zero is rationally equivalent to zero, via the
disjoint union of the two families. -/
theorem isRationallyEquivalentToZeroCanonical_add (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ)
    {α β : CycleGroup D sX k} (hα : IsRationallyEquivalentToZeroCanonical.{v} D sX hX k α)
    (hβ : IsRationallyEquivalentToZeroCanonical.{v} D sX hX k β) :
    IsRationallyEquivalentToZeroCanonical.{v} D sX hX k (α + β) := by
  obtain ⟨J, W, hWfin, c, hWdim, hWprin, hWsum⟩ := hα
  obtain ⟨K, V, hVfin, e, hVdim, hVprin, hVsum⟩ := hβ
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
    (fun s => match s with | .inl j => hWdim j | .inr l => hVdim l),
    (fun s => match s with | .inl j => hWprin j | .inr l => hVprin l), ?_⟩
  refine Subtype.ext (funext fun Z => ?_)
  have hsplit : (fun s : J ⊕ K => (integralClosedSubspacePushforward D sX hX
        (Sum.elim W V s) k (match s with | .inl j => c j | .inr l => e l)).1 Z) =
      Sum.elim (fun j => (integralClosedSubspacePushforward D sX hX (W j) k (c j)).1 Z)
        (fun l => (integralClosedSubspacePushforward D sX hX (V l) k (e l)).1 Z) :=
    funext fun s => by cases s <;> rfl
  show (α + β).1 Z = _
  rw [cycleFamilySum_apply, hsplit, Stacks.Chow.finsum_sum_elim _ _
      (finite_support_cycleFamilyCoeff D sX hX W hWfin k c Z)
      (finite_support_cycleFamilyCoeff D sX hX V hVfin k e Z), hWsum, hVsum]
  show (cycleFamilySum D sX hX W hWfin k c).1 Z + (cycleFamilySum D sX hX V hVfin k e).1 Z = _
  rw [cycleFamilySum_apply, cycleFamilySum_apply]

/-- The negative of a cycle rationally equivalent to zero is rationally equivalent to zero, via
the inverses of the same rational functions on the same family of subspaces. -/
theorem isRationallyEquivalentToZeroCanonical_neg (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ)
    {α : CycleGroup D sX k} (hα : IsRationallyEquivalentToZeroCanonical.{v} D sX hX k α) :
    IsRationallyEquivalentToZeroCanonical.{v} D sX hX k (-α) := by
  obtain ⟨J, W, hWfin, c, hWdim, hWprin, hWsum⟩ := hα
  refine ⟨J, W, hWfin, (fun j => -c j), hWdim,
    (fun j => isPrincipalDivisorCycleOfGood_neg D _
      (isGood_integralClosedSubspace D sX hX (W j)) (W j).isIntegralSpace k (hWprin j)), ?_⟩
  refine Subtype.ext (funext fun Z => ?_)
  show -α.1 Z = _
  rw [hWsum, cycleFamilySum_apply, cycleFamilySum_apply, ← finsum_neg_distrib]
  refine finsum_congr fun j => ?_
  rw [map_neg]
  rfl

/-- The subgroup of `k`-cycles rationally equivalent to zero. Its carrier is exactly the set of
cycles of the form `∑ (i_j)_* div(f_j)`, the principal divisors being read at the canonical
embeddings of Stacks 0ENK. -/
@[stacks 0EQ6 "part (2): the cycles rationally equivalent to zero, as a subgroup of Z_k(X); the \
carrier is exactly the set of sums of part (1) with div(f) at the canonical embeddings"]
def rationalEquivalencesCanonical (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ) :
    AddSubgroup (CycleGroup D sX k) where
  carrier := {α | IsRationallyEquivalentToZeroCanonical.{v} D sX hX k α}
  zero_mem' := isRationallyEquivalentToZeroCanonical_zero.{v} D sX hX k
  add_mem' := isRationallyEquivalentToZeroCanonical_add.{v} D sX hX k
  neg_mem' := isRationallyEquivalentToZeroCanonical_neg.{v} D sX hX k

/-- Membership in the subgroup of cycles rationally equivalent to zero is being rationally
equivalent to zero. -/
@[simp]
theorem mem_rationalEquivalencesCanonical (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ)
    (α : CycleGroup D sX k) :
    α ∈ rationalEquivalencesCanonical.{v} D sX hX k ↔
      IsRationallyEquivalentToZeroCanonical.{v} D sX hX k α :=
  Iff.rfl

/-- Two `k`-cycles are *rationally equivalent* when their difference is rationally equivalent to
zero. -/
@[stacks 0EQ6 "part (3): α ∼_rat β, defined as α - β being rationally equivalent to zero, for \
the reading of part (2) at the canonical embeddings"]
def RationallyEquivalentCanonical (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ)
    (α β : CycleGroup D sX k) : Prop :=
  IsRationallyEquivalentToZeroCanonical.{v} D sX hX k (α - β)

/-- Rational equivalence is an equivalence relation on `Z_k(X)`. -/
@[stacks 0EQ6 "part (3): ∼_rat is an equivalence relation, from the subgroup property of the \
cycles rationally equivalent to zero"]
theorem rationallyEquivalentCanonical_equivalence (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ) :
    Equivalence (RationallyEquivalentCanonical.{v} D sX hX k) where
  refl α := by
    have h := isRationallyEquivalentToZeroCanonical_zero.{v} D sX hX k
    rwa [← sub_self α] at h
  symm {α β} h := by
    have h' := isRationallyEquivalentToZeroCanonical_neg.{v} D sX hX k h
    rwa [neg_sub] at h'
  trans {α β γ} h h' := by
    have h'' := isRationallyEquivalentToZeroCanonical_add.{v} D sX hX k h h'
    rwa [sub_add_sub_cancel] at h''

end RationalEquivalence

/-! ### The Chow group -/

section ChowGroup

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The *Chow group of `k`-cycles on `X`*, that is the group of `k`-cycles modulo rational
equivalence,

`CH_k(X) = Z_k(X)/∼_rat`,

the quotient of the group of `k`-cycles of a good algebraic space `X/B` by the subgroup of
cycles rationally equivalent to zero. -/
@[stacks 0EQ6 "part (4): CH_k(X) = Z_k(X)/∼_rat, the quotient of Z_k(X) by the subgroup of \
cycles rationally equivalent to zero"]
abbrev chowGroupCanonical (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ) :=
  CycleGroup D sX k ⧸ rationalEquivalencesCanonical.{v} D sX hX k

/-- The class map `Z_k(X) → CH_k(X)`, the quotient homomorphism. -/
@[stacks 0EQ6 "part (4): the class map Z_k(X) → CH_k(X) of the quotient by ∼_rat"]
def chowClassCanonical (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ) :
    CycleGroup D sX k →+ chowGroupCanonical.{v} D sX hX k :=
  QuotientAddGroup.mk' (rationalEquivalencesCanonical.{v} D sX hX k)

/-- A cycle has class zero in `CH_k(X)` exactly when it is rationally equivalent to zero. -/
@[simp]
theorem chowClassCanonical_eq_zero_iff (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ)
    (α : CycleGroup D sX k) :
    chowClassCanonical.{v} D sX hX k α = 0 ↔
      IsRationallyEquivalentToZeroCanonical.{v} D sX hX k α :=
  QuotientAddGroup.eq_zero_iff α

/-- Two cycles have the same class in `CH_k(X)` exactly when they are rationally equivalent. -/
theorem chowClassCanonical_eq_iff_rationallyEquivalentCanonical (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (k : ℤ) (α β : CycleGroup D sX k) :
    chowClassCanonical.{v} D sX hX k α = chowClassCanonical.{v} D sX hX k β ↔
      RationallyEquivalentCanonical.{v} D sX hX k α β := by
  rw [← sub_eq_zero, ← map_sub, chowClassCanonical_eq_zero_iff]
  exact Iff.rfl

/-- The class in `CH_k(X)` of the cycle `∑ (i_j)_* div(f_j)`, a sum of principal divisors on a
locally finite family of integral closed subspaces of δ-dimension `k + 1`, is zero. -/
@[stacks 0EQ6 "parts (2) and (4): the class map kills ∑ (i_j)_* div(f_j), the cycle of part (1); \
proved for the constructed CH_k(X), not assumed"]
theorem chowClassCanonical_cycleFamilySum_eq_zero (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ)
    {J : Type v} (W : J → IntegralClosedSubspace D.site D.base D.base_mem X)
    (hWfin : LocallyFinite fun j : J =>
      subspacePointSet D.site D.base D.base_mem X (W j).subspace)
    (c : ∀ j, CycleGroup D ((W j).subspace.ι ≫ sX) k)
    (hWdim : ∀ j, deltaDimension D sX (W j) = k + 1)
    (hWprin : ∀ j, IsPrincipalDivisorCycleOfGood D ((W j).subspace.ι ≫ sX)
      (isGood_integralClosedSubspace D sX hX (W j)) (W j).isIntegralSpace k (c j)) :
    chowClassCanonical.{v} D sX hX k (cycleFamilySum D sX hX W hWfin k c) = 0 :=
  (chowClassCanonical_eq_zero_iff.{v} D sX hX k _).2 ⟨J, W, hWfin, c, hWdim, hWprin, rfl⟩

/-- An additive operation on `Z_k(X)` which kills every cycle rationally equivalent to zero
factors through `CH_k(X)`. -/
def chowGroupCanonicalLift (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ) {A : Type*}
    [AddCommGroup A] (F : CycleGroup D sX k →+ A)
    (hF : ∀ α : CycleGroup D sX k,
      IsRationallyEquivalentToZeroCanonical.{v} D sX hX k α → F α = 0) :
    chowGroupCanonical.{v} D sX hX k →+ A :=
  QuotientAddGroup.lift (rationalEquivalencesCanonical.{v} D sX hX k) F hF

/-- The descended operation agrees with the original one on the class of a cycle. -/
@[simp]
theorem chowGroupCanonicalLift_chowClassCanonical (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ)
    {A : Type*} [AddCommGroup A] (F : CycleGroup D sX k →+ A)
    (hF : ∀ α : CycleGroup D sX k,
      IsRationallyEquivalentToZeroCanonical.{v} D sX hX k α → F α = 0)
    (α : CycleGroup D sX k) :
    chowGroupCanonicalLift.{v} D sX hX k F hF (chowClassCanonical.{v} D sX hX k α) = F α :=
  rfl

end ChowGroup

/-! ### Comparison with the existentially quantified reading -/

section Comparison

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- A cycle rationally equivalent to zero at the canonical embeddings of Stacks 0ENK is
rationally equivalent to zero in the reading of
`AlgebraicGeometry.Space.IsRationallyEquivalentToZero`, where the embedding on each summand is
quantified existentially.

The converse is not expected: a summand satisfying the existential condition does so through
*some* ring map `R(W) → Q(𝒪^h_{W,ξ})`, chosen independently at each `W`, and the orders of
vanishing it computes need have nothing to do with those of `f` at the canonical embedding. -/
theorem IsRationallyEquivalentToZeroCanonical.isRationallyEquivalentToZero {sX : X ⟶ D.space}
    {hX : D.IsGood sX} {k : ℤ} {α : CycleGroup D sX k}
    (h : IsRationallyEquivalentToZeroCanonical.{v} D sX hX k α) :
    IsRationallyEquivalentToZero.{v} D sX hX k α := by
  obtain ⟨J, W, hWfin, c, hWdim, hWprin, hWsum⟩ := h
  exact ⟨J, W, hWfin, c, hWdim, fun j => (hWprin j).isPrincipalDivisorCycle, hWsum⟩

/-- The subgroup of cycles rationally equivalent to zero at the canonical embeddings of
Stacks 0ENK is contained in the one defined with the embedding quantified existentially. -/
theorem rationalEquivalencesCanonical_le_rationalEquivalences (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (k : ℤ) :
    rationalEquivalencesCanonical.{v} D sX hX k ≤ rationalEquivalences.{v} D sX hX k :=
  fun _ h => h.isRationallyEquivalentToZero

/-- The comparison map from `AlgebraicGeometry.Space.chowGroupCanonical` onto the quotient by
the existentially quantified rational equivalence, induced by the inclusion of subgroups
`AlgebraicGeometry.Space.rationalEquivalencesCanonical_le_rationalEquivalences`. -/
def chowGroupCanonicalToChowGroup (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ) :
    chowGroupCanonical.{v} D sX hX k →+ chowGroup.{v} D sX hX k :=
  chowGroupCanonicalLift.{v} D sX hX k (chowClass.{v} D sX hX k) fun _ h =>
    (chowClass_eq_zero_iff.{v} D sX hX k _).2 h.isRationallyEquivalentToZero

/-- The comparison map carries the class of a cycle to its class. -/
@[simp]
theorem chowGroupCanonicalToChowGroup_chowClassCanonical (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (k : ℤ) (α : CycleGroup D sX k) :
    chowGroupCanonicalToChowGroup.{v} D sX hX k (chowClassCanonical.{v} D sX hX k α) =
      chowClass.{v} D sX hX k α :=
  rfl

/-- The comparison map is surjective. -/
theorem surjective_chowGroupCanonicalToChowGroup (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ) :
    Function.Surjective (chowGroupCanonicalToChowGroup.{v} D sX hX k) := by
  intro x
  obtain ⟨α, hα⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences.{v} D sX hX k) x
  exact ⟨chowClassCanonical.{v} D sX hX k α, hα⟩

end Comparison

end AlgebraicGeometry.Space

end

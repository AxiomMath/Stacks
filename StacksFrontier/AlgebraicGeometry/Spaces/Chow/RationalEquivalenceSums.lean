module

public import StacksFrontier.AlgebraicGeometry.Chow.CycleAdditivity
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalence
public import StacksFrontier.Topology.LocallyFinite.Sigma
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackRationalEquivalence

/-!
# Locally finite sums of rational equivalences, and maps that descend to the Chow group

In the situation of Stacks 0EDT let `X/B` be good. A `k`-cycle on `X` is rationally equivalent
to zero, in the sense of part (2) of Stacks 0EQ6, when it is a sum `∑ (i_j)_* div(f_j)` over a
*locally finite* family `{W_j ⊆ X}` of integral closed subspaces of δ-dimension `k + 1`. Two
facts about that notion are needed by every argument which produces a rational equivalence one
piece at a time and then reassembles the pieces, and neither is in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalence`:

1. a locally finite sum of cycles each rationally equivalent to zero is rationally equivalent to
   zero — the subgroup `AlgebraicGeometry.Space.rationalEquivalences` is closed under *finite*
   sums, which is not enough when the family of pieces is infinite;
2. an additive map on cycle groups which carries the cycles rationally equivalent to zero to
   cycles rationally equivalent to zero respects rational equivalence, and therefore descends to
   a homomorphism of the Chow groups of Stacks 0EQ6, part (4).

Point (1) is the content of Stacks 0EQ8 (Remark 82.15.3), which the proofs of Stacks 0EQB,
0EQC and 0EQY all appeal to; point (2) is the step those three lemmas share once the piecewise
statement has been established.

Local finiteness of the combined family does *not* follow from local finiteness of each piece's
family together with local finiteness of the family of pieces: the subspaces `W_{j,i}`
presenting the `j`-th rational equivalence can be much larger than the support of the `j`-th
cycle, and nothing stops infinitely many of them from passing through one point of `|X|`. So the
hypothesis is carried explicitly, through the refinement
`AlgebraicGeometry.Space.IsRationallyEquivalentToZeroWithin` which remembers a subset of `|X|`
containing the whole presenting family. This is the algebraic-space counterpart of
`Stacks.Chow.IsRationallyEquivalentToZeroWithin` of
`StacksFrontier.AlgebraicGeometry.Chow.CycleAdditivity`, from which this file also takes the
reindexing `Stacks.Chow.finsum_sigma`.

## Main definitions

* `AlgebraicGeometry.Space.IsRationallyEquivalentToZeroWithin`: rational equivalence to zero
  witnessed by a family of integral closed subspaces whose point sets lie in a given subset of
  `|X|`.
* `AlgebraicGeometry.Space.chowGroupHomOfCycleHom`: the homomorphism `CH_m(Y) → CH_n(X)` induced
  by a homomorphism `Z_m(Y) → Z_n(X)` of cycle groups which carries cycles rationally equivalent
  to zero to cycles rationally equivalent to zero.

## Main results

* `AlgebraicGeometry.Space.IsRationallyEquivalentToZeroWithin.mono` and
  `AlgebraicGeometry.Space.IsRationallyEquivalentToZeroWithin.isRationallyEquivalentToZero`:
  the carrier may be enlarged, and forgotten.
* `AlgebraicGeometry.Space.isRationallyEquivalentToZeroWithin_univ_iff`: the carrier `|X|` says
  nothing, so the refinement really is one.
* `AlgebraicGeometry.Space.isRationallyEquivalentToZeroWithin_finsum` and
  `AlgebraicGeometry.Space.isRationallyEquivalentToZero_finsum`: **Stacks 0EQ8**
  (Remark 82.15.3), a cycle which is coefficientwise the locally finite sum of cycles each
  rationally equivalent to zero within the members of a locally finite family of subsets of
  `|X|` is itself rationally equivalent to zero.
* `AlgebraicGeometry.Space.rationallyEquivalent_cycleHom`: a homomorphism of cycle groups which
  kills rational equivalence to zero respects rational equivalence.
* `AlgebraicGeometry.Space.chowGroupHomOfCycleHom_chowClass`: the induced map on Chow groups
  takes the class of `α` to the class of its image, which is what makes it the descent of the
  given map and not some other homomorphism.

## Implementation notes

The index universe `v` of the presenting families is the one of
`AlgebraicGeometry.Space.IsRationallyEquivalentToZero`, hence of
`AlgebraicGeometry.Space.chowGroup`; the combined family of
`AlgebraicGeometry.Space.isRationallyEquivalentToZeroWithin_finsum` is indexed by the sigma type
`Σ j, K j` of the index types of the pieces, which lies in the same universe, so the conclusion
is a rational equivalence of the same kind as the hypotheses.

Neither of the two facts the sigma-indexed reassembly rests on is proved again here: local
finiteness of the combined family is `locallyFinite_sigma_of_subset` of
`StacksFrontier.Topology.LocallyFinite.Sigma`, which is where Stacks 0EQ8 is registered, and
finiteness of the support of the combined sum at a fixed integral closed subspace is
`AlgebraicGeometry.Space.finite_support_cycleFamilyCoeff` applied to that family.

No tag is registered here. Stacks 0EQ8 already has its registration in
`StacksFrontier.Topology.LocallyFinite.Sigma`, and point (2) is a step inside the proofs of
Stacks 0EQB, 0EQC and 0EQY, none of which it proves on its own: each of those lemmas needs,
besides this descent, the geometric input that its cycle-level operation really does kill a
principal divisor cycle pushed forward from an integral closed subspace.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
* [Stacks Project, Tag 0EQB](https://stacks.math.columbia.edu/tag/0EQB)
* [Stacks Project, Tag 0EQC](https://stacks.math.columbia.edu/tag/0EQC)
* [Stacks Project, Tag 0EQY](https://stacks.math.columbia.edu/tag/0EQY)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace Stacks.Chow

/-! ### Exchanging two locally finite sums -/

/-- Multiplying a finitely supported `finsum` of integers by a constant may be done
termwise. -/
theorem finsum_mul_of_finite_support {ι : Type*} (g : ι → ℤ) (b : ℤ)
    (h : (Function.support g).Finite) : (∑ᶠ i : ι, g i) * b = ∑ᶠ i : ι, g i * b := by
  classical
  have hsub : Function.support (fun i : ι => g i * b) ⊆ (h.toFinset : Set ι) := fun i hi => by
    simp only [Set.Finite.coe_toFinset, Function.mem_support]
    exact left_ne_zero_of_mul hi
  rw [finsum_eq_sum_of_support_subset g (s := h.toFinset) (by simp),
    finsum_eq_sum_of_support_subset _ hsub, Finset.sum_mul]

end Stacks.Chow

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Rational equivalence to zero with a prescribed carrier -/

section Within

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- **A refinement of part (2) of Stacks 0EQ6.** A `k`-cycle on a good algebraic space `X/B` is
*rationally equivalent to zero within* a subset `T` of `|X|` when the family `{W_j}` of integral
closed subspaces presenting its rational equivalence to zero can be taken with every `|W_j|`
inside `T`.

The extra information is what makes rational equivalence to zero stable under locally finite
sums: a locally finite family of carriers forces the union of the presenting families to be
locally finite, which the bare statement of part (2) of Stacks 0EQ6 does not. -/
def IsRationallyEquivalentToZeroWithin (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ)
    (α : CycleGroup D sX k) (T : Set (points D.site D.base D.base_mem X)) : Prop :=
  ∃ (J : Type v) (W : J → IntegralClosedSubspace D.site D.base D.base_mem X)
    (hWfin : LocallyFinite fun j : J =>
      subspacePointSet D.site D.base D.base_mem X (W j).subspace)
    (c : ∀ j, CycleGroup D ((W j).subspace.ι ≫ sX) k),
    (∀ j, subspacePointSet D.site D.base D.base_mem X (W j).subspace ⊆ T) ∧
      (∀ j, deltaDimension D sX (W j) = k + 1) ∧
        (∀ j, IsPrincipalDivisorCycle D ((W j).subspace.ι ≫ sX) k (c j)) ∧
          α = cycleFamilySum D sX hX W hWfin k c

/-- Enlarging the carrier preserves rational equivalence to zero within it. -/
theorem IsRationallyEquivalentToZeroWithin.mono {D : BaseSpaceDimensionSituation.{u}}
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} {sX : X ⟶ D.space}
    {hX : D.IsGood sX} {k : ℤ} {α : CycleGroup D sX k}
    {T T' : Set (points D.site D.base D.base_mem X)}
    (h : IsRationallyEquivalentToZeroWithin.{v} D sX hX k α T) (hT : T ⊆ T') :
    IsRationallyEquivalentToZeroWithin.{v} D sX hX k α T' := by
  obtain ⟨J, W, hWfin, c, hsub, hdim, hprin, hsum⟩ := h
  exact ⟨J, W, hWfin, c, fun j => (hsub j).trans hT, hdim, hprin, hsum⟩

/-- Forgetting the carrier of a rational equivalence to zero gives part (2) of Stacks 0EQ6. -/
theorem IsRationallyEquivalentToZeroWithin.isRationallyEquivalentToZero
    {D : BaseSpaceDimensionSituation.{u}}
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} {sX : X ⟶ D.space}
    {hX : D.IsGood sX} {k : ℤ} {α : CycleGroup D sX k}
    {T : Set (points D.site D.base D.base_mem X)}
    (h : IsRationallyEquivalentToZeroWithin.{v} D sX hX k α T) :
    IsRationallyEquivalentToZero.{v} D sX hX k α := by
  obtain ⟨J, W, hWfin, c, -, hdim, hprin, hsum⟩ := h
  exact ⟨J, W, hWfin, c, hdim, hprin, hsum⟩

/-- Rational equivalence to zero in the sense of part (2) of Stacks 0EQ6 is rational equivalence
to zero within the whole of `|X|`: the carrier carries no information when it is everything. -/
theorem isRationallyEquivalentToZeroWithin_univ_iff (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ)
    (α : CycleGroup D sX k) :
    IsRationallyEquivalentToZeroWithin.{v} D sX hX k α Set.univ ↔
      IsRationallyEquivalentToZero.{v} D sX hX k α := by
  refine ⟨fun h => h.isRationallyEquivalentToZero, fun h => ?_⟩
  obtain ⟨J, W, hWfin, c, hdim, hprin, hsum⟩ := h
  exact ⟨J, W, hWfin, c, fun _ => Set.subset_univ _, hdim, hprin, hsum⟩

/-- The zero cycle is rationally equivalent to zero within any subset, via the empty family. -/
theorem isRationallyEquivalentToZeroWithin_zero (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ)
    (T : Set (points D.site D.base D.base_mem X)) :
    IsRationallyEquivalentToZeroWithin.{v} D sX hX k 0 T := by
  have hcoeff : cycleFamilySumCoeff D sX hX (fun j : PEmpty.{v + 1} => nomatch j) k
      (fun j => nomatch j) = 0 := funext fun _ => finsum_of_isEmpty _
  exact ⟨PEmpty.{v + 1}, (fun j => nomatch j), locallyFinite_of_finite _, (fun j => nomatch j),
    (fun j => nomatch j), (fun j => nomatch j), (fun j => nomatch j), Subtype.ext hcoeff.symm⟩

end Within

/-! ### Locally finite sums of cycles rationally equivalent to zero -/

section Finsum

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- **Stacks 0EQ8 (Remark 82.15.3).** A `k`-cycle which is coefficientwise the locally finite sum
of `k`-cycles `β j`, each rationally equivalent to zero within a subset `E j` of `|X|`, is
rationally equivalent to zero within the union of the `E j`, provided the family `E` is locally
finite.

The carriers are what make the combined family of presenting subspaces locally finite: a point
of `|X|` has a neighbourhood meeting only finitely many `E j`, hence only finitely many of the
families presenting the `β j`, and each of those families is itself locally finite. That is
`locallyFinite_sigma_of_subset`, where Stacks 0EQ8 is registered. The sum over the combined
family, indexed by the sigma type of the index types of the pieces, is the iterated sum by
`Stacks.Chow.finsum_sigma`. -/
theorem isRationallyEquivalentToZeroWithin_finsum (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ)
    {J : Type v} (β : J → CycleGroup D sX k)
    (E : J → Set (points D.site D.base D.base_mem X)) (hE : LocallyFinite E)
    (hβ : ∀ j, IsRationallyEquivalentToZeroWithin.{v} D sX hX k (β j) (E j))
    {α : CycleGroup D sX k}
    (hα : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
      α.1 Z = ∑ᶠ j : J, (β j).1 Z) :
    IsRationallyEquivalentToZeroWithin.{v} D sX hX k α (⋃ j, E j) := by
  choose K W hWfin c hsub hdim hprin hsum using hβ
  have hVfin : LocallyFinite fun s : (j : J) × K j =>
      subspacePointSet D.site D.base D.base_mem X (W s.1 s.2).subspace :=
    locallyFinite_sigma_of_subset hE hWfin hsub
  refine ⟨(j : J) × K j, fun s => W s.1 s.2, hVfin, fun s => c s.1 s.2,
    fun s => (hsub s.1 s.2).trans (Set.subset_iUnion E s.1), fun s => hdim s.1 s.2,
    fun s => hprin s.1 s.2, Subtype.ext (funext fun Z => ?_)⟩
  have hterm : ∀ j : J, (β j).1 Z =
      ∑ᶠ i : K j, (integralClosedSubspacePushforward D sX hX (W j i) k (c j i)).1 Z := fun j => by
    rw [hsum j]
    exact cycleFamilySum_apply D sX hX (W j) (hWfin j) k (c j) Z
  rw [hα Z, finsum_congr hterm]
  exact (Stacks.Chow.finsum_sigma (fun s : (j : J) × K j =>
    (integralClosedSubspacePushforward D sX hX (W s.1 s.2) k (c s.1 s.2)).1 Z)
    (finite_support_cycleFamilyCoeff D sX hX (fun s : (j : J) × K j => W s.1 s.2) hVfin k
      (fun s => c s.1 s.2) Z)).symm

/-- **Stacks 0EQ8 (Remark 82.15.3).** A `k`-cycle which is coefficientwise the locally finite sum
of `k`-cycles each rationally equivalent to zero within the members of a locally finite family
of subsets of `|X|` is rationally equivalent to zero.

This is the locally finite form of `AlgebraicGeometry.Space.isRationallyEquivalentToZero_add`,
which is the case of a two-element index type and needs no carriers. -/
theorem isRationallyEquivalentToZero_finsum (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ)
    {J : Type v} (β : J → CycleGroup D sX k)
    (E : J → Set (points D.site D.base D.base_mem X)) (hE : LocallyFinite E)
    (hβ : ∀ j, IsRationallyEquivalentToZeroWithin.{v} D sX hX k (β j) (E j))
    {α : CycleGroup D sX k}
    (hα : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
      α.1 Z = ∑ᶠ j : J, (β j).1 Z) :
    IsRationallyEquivalentToZero.{v} D sX hX k α :=
  (isRationallyEquivalentToZeroWithin_finsum.{v} D sX hX k β E hE hβ
    hα).isRationallyEquivalentToZero

end Finsum

/-! ### Descending a homomorphism of cycle groups to the Chow groups -/

section Descent

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- A homomorphism `φ : Z_m(Y) → Z_n(X)` of cycle groups which carries cycles rationally
equivalent to zero to cycles rationally equivalent to zero respects rational equivalence:
`α ∼_rat β` gives `φ(α) ∼_rat φ(β)`, because `φ(α) - φ(β) = φ(α - β)`.

This is the step shared by Stacks 0EQB, 0EQC and 0EQY once the operation in question has been
shown to kill rational equivalence to zero. -/
theorem rationallyEquivalent_cycleHom (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (m n : ℤ) (φ : CycleGroup D sY m →+ CycleGroup D sX n)
    (hφ : ∀ γ : CycleGroup D sY m, IsRationallyEquivalentToZero.{v} D sY hY m γ →
      IsRationallyEquivalentToZero.{v} D sX hX n (φ γ))
    {α β : CycleGroup D sY m} (h : RationallyEquivalent.{v} D sY hY m α β) :
    RationallyEquivalent.{v} D sX hX n (φ α) (φ β) := by
  have hsub := hφ (α - β) h
  rwa [map_sub] at hsub

/-- The homomorphism `CH_m(Y) → CH_n(X)` of Chow groups induced by a homomorphism
`φ : Z_m(Y) → Z_n(X)` of cycle groups which carries cycles rationally equivalent to zero to
cycles rationally equivalent to zero.

The Chow groups are the constructed ones, `AlgebraicGeometry.Space.chowGroup` of part (4) of
Stacks 0EQ6, and the map is the one induced on the quotients; no Chow group is assumed. -/
def chowGroupHomOfCycleHom (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (m n : ℤ) (φ : CycleGroup D sY m →+ CycleGroup D sX n)
    (hφ : ∀ γ : CycleGroup D sY m, IsRationallyEquivalentToZero.{v} D sY hY m γ →
      IsRationallyEquivalentToZero.{v} D sX hX n (φ γ)) :
    chowGroup.{v} D sY hY m →+ chowGroup.{v} D sX hX n :=
  QuotientAddGroup.map (rationalEquivalences.{v} D sY hY m) (rationalEquivalences.{v} D sX hX n)
    φ fun γ hγ => hφ γ hγ

/-- The induced map on Chow groups takes the class of a cycle to the class of its image. -/
@[simp]
theorem chowGroupHomOfCycleHom_chowClass (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) (m n : ℤ) (φ : CycleGroup D sY m →+ CycleGroup D sX n)
    (hφ : ∀ γ : CycleGroup D sY m, IsRationallyEquivalentToZero.{v} D sY hY m γ →
      IsRationallyEquivalentToZero.{v} D sX hX n (φ γ)) (α : CycleGroup D sY m) :
    chowGroupHomOfCycleHom.{v} D sX hX sY hY m n φ hφ (chowClass.{v} D sY hY m α) =
      chowClass.{v} D sX hX n (φ α) :=
  rfl

end Descent

end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalenceCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalenceSums

/-!
# Locally finite sums of rational equivalences at the canonical embeddings of Stacks 0ENK

In the situation of Stacks 0EDT let `X/B` be good.  A `k`-cycle on `X` is rationally equivalent
to zero in the sense of part (2) of Stacks 0EQ6 when it is a sum `∑ (i_j)_* div(f_j)` over a
*locally finite* family `{W_j ⊆ X}` of integral closed subspaces of δ-dimension `k + 1`.  Reading
each summand `div(f_j)` requires the embedding `R(W_j) → Q(𝒪^h_{W_j,ξ})` of Stacks 0ENK, and
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalenceCanonical` reads it at the
*canonical* embedding, which for the good integral `W_j` is constructed rather than chosen: the
summand condition there is `AlgebraicGeometry.Space.IsPrincipalDivisorCycleOfGood`, and the
resulting `AlgebraicGeometry.Space.chowGroupCanonical` is the source's `CH_k(X)`.

This file refines that notion at the canonical embeddings by remembering a subset of `|X|`
containing the whole presenting family, and proves the locally finite reassembly of Stacks 0EQ8
for it: a locally finite sum of cycles rationally equivalent to zero within the members of a
locally finite family of subsets of `|X|` is rationally equivalent to zero.

## Main definitions

* `AlgebraicGeometry.Space.IsRationallyEquivalentToZeroWithinCanonical`: rational equivalence to
  zero at the canonical embeddings of Stacks 0ENK, witnessed by a family of integral closed
  subspaces whose point sets lie in a given subset of `|X|`.

## Main results

* `AlgebraicGeometry.Space.IsRationallyEquivalentToZeroWithinCanonical.mono` and
  `IsRationallyEquivalentToZeroWithinCanonical.isRationallyEquivalentToZeroCanonical`: the
  carrier may be enlarged, and forgotten.
* `AlgebraicGeometry.Space.isRationallyEquivalentToZeroWithinCanonical_univ_iff`: rational
  equivalence to zero within `|X|` is rational equivalence to zero.
* `AlgebraicGeometry.Space.isRationallyEquivalentToZeroWithinCanonical_zero`: the zero cycle,
  via the empty family.
* `AlgebraicGeometry.Space.isRationallyEquivalentToZeroWithinCanonical_finsum` and
  `AlgebraicGeometry.Space.isRationallyEquivalentToZeroCanonical_finsum`: Stacks 0EQ8 at the
  canonical embeddings — a cycle which is coefficientwise the locally finite sum of cycles each
  rationally equivalent to zero within the members of a locally finite family of subsets of `|X|`
  is itself rationally equivalent to zero.
* `IsRationallyEquivalentToZeroWithinCanonical.isRationallyEquivalentToZeroWithin`: the
  comparison with the existentially quantified reading, at a fixed carrier.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQ8](https://stacks.math.columbia.edu/tag/0EQ8)
* [Stacks Project, Tag 0EQY](https://stacks.math.columbia.edu/tag/0EQY)
* [Stacks Project, Tag 0ER9](https://stacks.math.columbia.edu/tag/0ER9)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Rational equivalence to zero at the canonical embeddings, with a prescribed carrier -/

section Within

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- A `k`-cycle on a good algebraic space `X/B` is *rationally equivalent to zero within* a
subset `T` of `|X|` when the family `{W_j}` of integral closed subspaces presenting its rational
equivalence to zero can be taken with every `|W_j|` inside `T`.

This is `AlgebraicGeometry.Space.IsRationallyEquivalentToZeroWithin` with the summand condition
replaced by `AlgebraicGeometry.Space.IsPrincipalDivisorCycleOfGood`, which pins the embedding
`R(W_j) → Q(𝒪^h_{W_j,ξ})` of Stacks 0ENK to the canonical one of
`AlgebraicGeometry.Space.genericFractionEmbedding` and quantifies nothing but the source's `f_j`;
the goodness and integrality the canonical embedding needs are
`AlgebraicGeometry.Space.isGood_integralClosedSubspace` and the `isIntegralSpace` field of an
integral closed subspace, so they are not hypotheses. -/
def IsRationallyEquivalentToZeroWithinCanonical (sX : X ⟶ D.space) (hX : D.IsGood sX) (k : ℤ)
    (α : CycleGroup D sX k) (T : Set (points D.site D.base D.base_mem X)) : Prop :=
  ∃ (J : Type v) (W : J → IntegralClosedSubspace D.site D.base D.base_mem X)
    (hWfin : LocallyFinite fun j : J =>
      subspacePointSet D.site D.base D.base_mem X (W j).subspace)
    (c : ∀ j, CycleGroup D ((W j).subspace.ι ≫ sX) k),
    (∀ j, subspacePointSet D.site D.base D.base_mem X (W j).subspace ⊆ T) ∧
      (∀ j, deltaDimension D sX (W j) = k + 1) ∧
        (∀ j, IsPrincipalDivisorCycleOfGood D ((W j).subspace.ι ≫ sX)
          (isGood_integralClosedSubspace D sX hX (W j)) (W j).isIntegralSpace k (c j)) ∧
          α = cycleFamilySum D sX hX W hWfin k c

/-- Enlarging the carrier preserves rational equivalence to zero within it. -/
theorem IsRationallyEquivalentToZeroWithinCanonical.mono {D : BaseSpaceDimensionSituation.{u}}
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} {sX : X ⟶ D.space}
    {hX : D.IsGood sX} {k : ℤ} {α : CycleGroup D sX k}
    {T T' : Set (points D.site D.base D.base_mem X)}
    (h : IsRationallyEquivalentToZeroWithinCanonical.{v} D sX hX k α T) (hT : T ⊆ T') :
    IsRationallyEquivalentToZeroWithinCanonical.{v} D sX hX k α T' := by
  obtain ⟨J, W, hWfin, c, hsub, hdim, hprin, hsum⟩ := h
  exact ⟨J, W, hWfin, c, fun j => (hsub j).trans hT, hdim, hprin, hsum⟩

/-- Forgetting the carrier of a rational equivalence to zero at the canonical embeddings gives
part (2) of Stacks 0EQ6 in the reading of
`AlgebraicGeometry.Space.IsRationallyEquivalentToZeroCanonical`. -/
theorem IsRationallyEquivalentToZeroWithinCanonical.isRationallyEquivalentToZeroCanonical
    {D : BaseSpaceDimensionSituation.{u}}
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} {sX : X ⟶ D.space}
    {hX : D.IsGood sX} {k : ℤ} {α : CycleGroup D sX k}
    {T : Set (points D.site D.base D.base_mem X)}
    (h : IsRationallyEquivalentToZeroWithinCanonical.{v} D sX hX k α T) :
    IsRationallyEquivalentToZeroCanonical.{v} D sX hX k α := by
  obtain ⟨J, W, hWfin, c, -, hdim, hprin, hsum⟩ := h
  exact ⟨J, W, hWfin, c, hdim, hprin, hsum⟩

/-- Rational equivalence to zero at the canonical embeddings is rational equivalence to zero
within the whole of `|X|`: the carrier carries no information when it is everything. -/
theorem isRationallyEquivalentToZeroWithinCanonical_univ_iff (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (k : ℤ) (α : CycleGroup D sX k) :
    IsRationallyEquivalentToZeroWithinCanonical.{v} D sX hX k α Set.univ ↔
      IsRationallyEquivalentToZeroCanonical.{v} D sX hX k α := by
  refine ⟨fun h => h.isRationallyEquivalentToZeroCanonical, fun h => ?_⟩
  obtain ⟨J, W, hWfin, c, hdim, hprin, hsum⟩ := h
  exact ⟨J, W, hWfin, c, fun _ => Set.subset_univ _, hdim, hprin, hsum⟩

/-- The zero cycle is rationally equivalent to zero within any subset, via the empty family. -/
theorem isRationallyEquivalentToZeroWithinCanonical_zero (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (k : ℤ) (T : Set (points D.site D.base D.base_mem X)) :
    IsRationallyEquivalentToZeroWithinCanonical.{v} D sX hX k 0 T := by
  have hcoeff : cycleFamilySumCoeff D sX hX (fun j : PEmpty.{v + 1} => nomatch j) k
      (fun j => nomatch j) = 0 := funext fun _ => finsum_of_isEmpty _
  exact ⟨PEmpty.{v + 1}, (fun j => nomatch j), locallyFinite_of_finite _, (fun j => nomatch j),
    (fun j => nomatch j), (fun j => nomatch j), (fun j => nomatch j), Subtype.ext hcoeff.symm⟩

/-- A rational equivalence to zero within a carrier at the canonical embeddings of Stacks 0ENK
is one in the reading `AlgebraicGeometry.Space.IsRationallyEquivalentToZeroWithin`, where the
embedding on each summand is quantified existentially: the canonical data is a witness for that
existential, summand by summand, by
`AlgebraicGeometry.Space.IsPrincipalDivisorCycleOfGood.isPrincipalDivisorCycle`. -/
theorem IsRationallyEquivalentToZeroWithinCanonical.isRationallyEquivalentToZeroWithin
    {D : BaseSpaceDimensionSituation.{u}}
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} {sX : X ⟶ D.space}
    {hX : D.IsGood sX} {k : ℤ} {α : CycleGroup D sX k}
    {T : Set (points D.site D.base D.base_mem X)}
    (h : IsRationallyEquivalentToZeroWithinCanonical.{v} D sX hX k α T) :
    IsRationallyEquivalentToZeroWithin.{v} D sX hX k α T := by
  obtain ⟨J, W, hWfin, c, hsub, hdim, hprin, hsum⟩ := h
  exact ⟨J, W, hWfin, c, hsub, hdim, fun j => (hprin j).isPrincipalDivisorCycle, hsum⟩

end Within

/-! ### Locally finite sums of cycles rationally equivalent to zero -/

section Finsum

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- **Stacks 0EQ8 at the canonical embeddings of Stacks 0ENK.**  A `k`-cycle which is
coefficientwise the locally finite sum of `k`-cycles `β j`, each rationally equivalent to zero
within a subset `E j` of `|X|`, is rationally equivalent to zero within the union of the `E j`,
provided the family `E` is locally finite. -/
theorem isRationallyEquivalentToZeroWithinCanonical_finsum (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (k : ℤ) {J : Type v} (β : J → CycleGroup D sX k)
    (E : J → Set (points D.site D.base D.base_mem X)) (hE : LocallyFinite E)
    (hβ : ∀ j, IsRationallyEquivalentToZeroWithinCanonical.{v} D sX hX k (β j) (E j))
    {α : CycleGroup D sX k}
    (hα : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
      α.1 Z = ∑ᶠ j : J, (β j).1 Z) :
    IsRationallyEquivalentToZeroWithinCanonical.{v} D sX hX k α (⋃ j, E j) := by
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

/-- **Stacks 0EQ8 at the canonical embeddings of Stacks 0ENK.**  A `k`-cycle which is
coefficientwise the locally finite sum of `k`-cycles each rationally equivalent to zero within the
members of a locally finite family of subsets of `|X|` is rationally equivalent to zero. -/
theorem isRationallyEquivalentToZeroCanonical_finsum (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (k : ℤ) {J : Type v} (β : J → CycleGroup D sX k)
    (E : J → Set (points D.site D.base D.base_mem X)) (hE : LocallyFinite E)
    (hβ : ∀ j, IsRationallyEquivalentToZeroWithinCanonical.{v} D sX hX k (β j) (E j))
    {α : CycleGroup D sX k}
    (hα : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
      α.1 Z = ∑ᶠ j : J, (β j).1 Z) :
    IsRationallyEquivalentToZeroCanonical.{v} D sX hX k α :=
  (isRationallyEquivalentToZeroWithinCanonical_finsum.{v} D sX hX k β E hE hβ
    hα).isRationallyEquivalentToZeroCanonical

end Finsum

end AlgebraicGeometry.Space

end

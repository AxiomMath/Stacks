module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyClosedPoints
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersectionLeadingTerm

/-!
# Points meeting every irreducible component, and the strict inequality they give

The last step of the proof of Stacks 0B0E turns a non-strict dimension inequality into a strict
one. Having chosen, for each closed subvariety `T_i`, closed points `x_{it} ∈ T_i ∩ Z` with at
least one in each irreducible component of `T_i ∩ Z`, the source argues: an irreducible component
`V` of `T_i ∩ Z_j` contained in `T_i ∩ Z` and containing none of the `x_{it}` has
`dim V < dim (Z ∩ T_i)`.

The reason is that a closed irreducible subset of a closed set `S`, of the same dimension as `S`,
is *maximal* among the closed irreducible subsets of `S` — an irreducible component of `S` — and
every component carries one of the chosen points. So a closed irreducible subset of `S` carrying
none of them cannot have the dimension of `S`, and having at most that dimension, has less.

The subset is not assumed irreducible, because the set the strictness clause applies this to is
an intersection of three closed sets. The inequality is then read off the chains directly: every
chain of closed irreducible subsets of `A` is a chain of closed irreducible subsets of `S` whose
last stage, carrying none of the chosen points, is not maximal, so a strictly larger one can be
appended and no chain of `A` is a longest chain of `S`.

## Main results

* `AlgebraicGeometry.eq_of_isIrreducible_subset_of_topologicalKrullDim_eq`: a closed irreducible
  subset of a closed set `S`, of the same finite dimension as `S`, is maximal among the closed
  irreducible subsets of `S`.
* `AlgebraicGeometry.topologicalKrullDim_lt_of_forall_notMem`: the strict inequality, for a
  closed subset of a nonempty closed set containing none of a family of points which meets every
  maximal closed irreducible subset.
* `AlgebraicGeometry.exists_finite_isClosed_forall_maximal_exists_mem`: the points themselves —
  on a Noetherian Jacobson space every closed subset carries a finite set of closed points of the
  ambient space meeting each of its maximal closed irreducible subsets.

## Implementation notes

**Why maximality rather than `irreducibleComponents`.** The components of `S` are the maximal
irreducible subsets of the subspace `↥S`, and the statements of this module are about subsets of
the ambient space, as the source's are. Maximality is therefore spelled out — "every closed
irreducible `C` with `B ⊆ C ⊆ S` equals `B`" — rather than written as membership of
`irreducibleComponents ↥S`, so that no consumer has to transport a subvariety of `𝐏(V)` into a
subspace to use these. The transport is done once, inside the proofs, through
`isIrreducible_preimage_subtypeVal` and `topologicalKrullDim_preimage_val` of
`StacksFrontier.Topology.Dimension.ClosedSubsetDimension` and
`StacksFrontier.Topology.Dimension.Krull`.

**Finiteness of the dimension** is a hypothesis of
`AlgebraicGeometry.mem_irreducibleComponents_of_topologicalKrullDim_eq`, which is what the
maximality rests on, and it is not automatic: the argument compares the height of the subset with
the Krull dimension of the ambient subspace, and an infinite dimension makes that comparison
vacuous. For a closed subset of a variety it holds, the dimension being bounded by that of the
variety.

**The choice of the points.** `AlgebraicGeometry.exists_isClosed_singleton_mem` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyClosedPoints` supplies a
point of a nonempty closed subset of a Jacobson space which is closed in the ambient space; the
components of a closed subset of a Noetherian space are finite in number, which is what makes
the collection of chosen points finite, as the source's "finitely many closed points `x_{it}`"
requires. Which component a chosen point belongs to is not recorded: the conclusion is the one
the source uses, that each maximal closed irreducible subset contains at least one of them.

## References

* [Stacks Project, Tag 0B0E](https://stacks.math.columbia.edu/tag/0B0E)
-/

@[expose] public section

open Set TopologicalSpace

namespace AlgebraicGeometry

variable {X : Type*} [TopologicalSpace X]

/-- A subset of a subset `S` is contained in `D` once its preimage in `↥S` is. -/
private theorem subset_of_preimage_val_subset {α : Type*} {S B D : Set α} (hBS : B ⊆ S)
    (h : (Subtype.val ⁻¹' B : Set ↥S) ⊆ Subtype.val ⁻¹' D) : B ⊆ D :=
  fun y hy => h (a := ⟨y, hBS hy⟩) hy

/-- A closed irreducible subset of a closed subspace `↥S` is a closed irreducible subset of `X`. -/
private theorem isIrreducible_and_isClosed_image_val {S : Set X} (hS : IsClosed S) {W : Set ↥S}
    (hirr : IsIrreducible W) (hcl : IsClosed W) :
    IsIrreducible (Subtype.val '' W) ∧ IsClosed (Subtype.val '' W) :=
  ⟨hirr.image _ continuous_subtype_val.continuousOn, hS.isClosedMap_subtype_val _ hcl⟩

/-- **A closed irreducible subset of a closed set, of the same dimension, is an irreducible
component of it.** Let `S` be closed and let `A ⊆ S` be closed and irreducible with
`dim A = dim S < ⊤`. Then every closed irreducible `B` with `A ⊆ B ⊆ S` equals `A`.

This is `AlgebraicGeometry.mem_irreducibleComponents_of_topologicalKrullDim_eq` read in the
subspace `S`, with the component expressed by its maximality among subsets of the ambient
space. -/
public theorem eq_of_isIrreducible_subset_of_topologicalKrullDim_eq {S A B : Set X}
    (_hScl : IsClosed S) (hAcl : IsClosed A) (hAirr : IsIrreducible A) (hAS : A ⊆ S)
    (hfin : topologicalKrullDim ↥A < ⊤)
    (hdim : topologicalKrullDim ↥A = topologicalKrullDim ↥S)
    (hBirr : IsIrreducible B) (hAB : A ⊆ B) (hBS : B ⊆ S) :
    B = A := by
  have hcomp : (Subtype.val ⁻¹' A : Set ↥S) ∈ irreducibleComponents ↥S := by
    refine mem_irreducibleComponents_of_topologicalKrullDim_eq
      (isIrreducible_preimage_subtypeVal hAirr hAS) (hAcl.preimage continuous_subtype_val) ?_ ?_
    all_goals rwa [topologicalKrullDim_preimage_val S A hAS]
  have hle : (Subtype.val ⁻¹' B : Set ↥S) ⊆ (Subtype.val ⁻¹' A : Set ↥S) :=
    hcomp.2 (isIrreducible_preimage_subtypeVal hBirr hBS) (Set.preimage_mono hAB)
  exact Set.Subset.antisymm (subset_of_preimage_val_subset hBS hle) hAB

/-- **The strict inequality of the last step of Stacks 0B0E.** Let `S` be a nonempty closed
subset of finite dimension and let `x : ι → X` be points such that every maximal closed
irreducible subset of `S` — every irreducible component of `S` — contains one of them. Then a
closed subset of `S` containing none of them has dimension strictly less than that of `S`.

With `S = T_i ∩ Z`, the `x` the source's `x_{it}` and the subset `W ∩ Z_j ∩ T_i`, this is
`dim (W ∩ Z_j ∩ T_i) < dim (Z ∩ T_i)`.

`A` is not assumed irreducible: the set the strictness clause of Stacks 0B0E applies this to is
an intersection of three closed sets and has no reason to be. `S.Nonempty` is then needed, and
is what irreducibility of `A` used to supply: for `S = ∅` the hypotheses hold vacuously with
`A = ∅` while the conclusion `⊥ < ⊥` is false. -/
public theorem topologicalKrullDim_lt_of_forall_notMem {S A : Set X} {ι : Type*} {x : ι → X}
    (hScl : IsClosed S) (hAcl : IsClosed A) (hAS : A ⊆ S) (hSne : S.Nonempty)
    (hfin : topologicalKrullDim ↥S < ⊤)
    (hmeet : ∀ B : Set X, IsClosed B → IsIrreducible B → B ⊆ S →
      (∀ C : Set X, IsIrreducible C → B ⊆ C → C ⊆ S → C = B) → ∃ i, x i ∈ B)
    (hnot : ∀ i, x i ∉ A) :
    topologicalKrullDim ↥A < topologicalKrullDim ↥S := by
  obtain ⟨p, hp⟩ := hSne
  have hA' : IsClosed ((Subtype.val : ↥S → X) ⁻¹' A) := hAcl.preimage continuous_subtype_val
  let : Nonempty (IrreducibleCloseds ↥S) :=
    ⟨⟨closure {(⟨p, hp⟩ : ↥S)}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  let : FiniteDimensionalOrder (IrreducibleCloseds ↥S) :=
    Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top.mpr
      ⟨Order.krullDim_ne_bot_iff.mpr inferInstance, ne_of_lt hfin⟩
  rw [← topologicalKrullDim_preimage_val S A hAS]
  show Order.krullDim (IrreducibleCloseds ↥((Subtype.val : ↥S → X) ⁻¹' A)) <
    Order.krullDim (IrreducibleCloseds ↥S)
  rw [Order.krullDim_eq_length_of_finiteDimensionalOrder (α := IrreducibleCloseds ↥S)]
  refine Order.krullDim_lt_coe_iff.mpr fun l ↦ ?_
  let e : IrreducibleCloseds ↥((Subtype.val : ↥S → X) ⁻¹' A) ↪o IrreducibleCloseds ↥S :=
    OrderEmbedding.ofMapLEIff
      (fun W ↦ ⟨Subtype.val '' (W : Set ↥((Subtype.val : ↥S → X) ⁻¹' A)),
        (isIrreducible_and_isClosed_image_val hA' W.isIrreducible W.isClosed).1,
        (isIrreducible_and_isClosed_image_val hA' W.isIrreducible W.isClosed).2⟩)
      (fun _ _ ↦ Set.image_subset_image_iff Subtype.val_injective)
  -- the last stage of the embedded chain, read as a closed irreducible subset of `A` in `X`
  obtain ⟨B, hBeq, hBirr, hBcl, hBS, hBA⟩ : ∃ B : Set X,
      Subtype.val '' (((l.map e e.strictMono).last : IrreducibleCloseds ↥S) : Set ↥S) = B ∧
        IsIrreducible B ∧ IsClosed B ∧ B ⊆ S ∧ B ⊆ A := by
    have hBic := isIrreducible_and_isClosed_image_val hScl
      (l.map e e.strictMono).last.isIrreducible (l.map e e.strictMono).last.isClosed
    refine ⟨_, rfl, hBic.1, hBic.2, Subtype.coe_image_subset S _, ?_⟩
    have hlastval : (((l.map e e.strictMono).last : IrreducibleCloseds ↥S) : Set ↥S) =
        Subtype.val '' ((l.last : IrreducibleCloseds ↥((Subtype.val : ↥S → X) ⁻¹' A)) :
          Set ↥((Subtype.val : ↥S → X) ⁻¹' A)) := rfl
    rintro _ ⟨z, hz, rfl⟩
    rw [hlastval] at hz
    obtain ⟨w, -, rfl⟩ := hz
    exact w.2
  have hBmem : ∀ z ∈ (((l.map e e.strictMono).last : IrreducibleCloseds ↥S) : Set ↥S),
      (z : X) ∈ B := fun z hz => hBeq ▸ ⟨z, hz, rfl⟩
  -- `B` carries none of the chosen points, so it is not maximal: something is strictly larger
  obtain ⟨C, hCirr, hBC, hCS, hCB⟩ : ∃ C : Set X, IsIrreducible C ∧ B ⊆ C ∧ C ⊆ S ∧ C ≠ B := by
    by_contra hcon
    simp only [not_exists, not_and, not_ne_iff] at hcon
    obtain ⟨i, hi⟩ := hmeet B hBcl hBirr hBS fun C h₁ h₂ h₃ => hcon C h₁ h₂ h₃
    exact hnot i (hBA hi)
  have hC'S : closure C ⊆ S := hScl.closure_subset_iff.mpr hCS
  have hlt : (l.map e e.strictMono).last <
      (⟨(Subtype.val : ↥S → X) ⁻¹' closure C,
        isIrreducible_preimage_subtypeVal hCirr.closure hC'S,
        isClosed_closure.preimage continuous_subtype_val⟩ : IrreducibleCloseds ↥S) := by
    refine lt_of_le_not_ge (fun z hz => subset_closure (hBC (hBmem z hz))) fun hge => hCB ?_
    exact Set.Subset.antisymm (subset_closure.trans
      (subset_of_preimage_val_subset hC'S fun w hw => hBmem w (hge hw))) hBC
  exact Nat.lt_of_succ_le
    (LTSeries.longestOf_is_longest ((l.map e e.strictMono).snoc _ hlt))

/-- **The points `x_{it}` of Stacks 0B0E.** On a Noetherian Jacobson space every closed subset
`S` carries a finite set of points, each closed in the ambient space, such that every maximal
closed irreducible subset of `S` contains one of them.

This is the source's "for every `i` pick closed points `x_{it} ∈ T_i ∩ Z`, at least one in each
irreducible component of `T_i ∩ Z`". -/
public theorem exists_finite_isClosed_forall_maximal_exists_mem [JacobsonSpace X]
    [NoetherianSpace X] {S : Set X} (hScl : IsClosed S) :
    ∃ t : Set X, t.Finite ∧ t ⊆ S ∧ (∀ y ∈ t, IsClosed ({y} : Set X)) ∧
      ∀ B : Set X, IsClosed B → IsIrreducible B → B ⊆ S →
        (∀ C : Set X, IsIrreducible C → B ⊆ C → C ⊆ S → C = B) → ∃ y ∈ t, y ∈ B := by
  classical
  have hfincomp : (irreducibleComponents ↥S).Finite := NoetherianSpace.finite_irreducibleComponents
  have : Finite ↥(irreducibleComponents ↥S) := hfincomp.to_subtype
  -- a closed point of the ambient space in each component, read as a subset of `X`
  have hpoint : ∀ A : ↥(irreducibleComponents ↥S),
      ∃ z ∈ Subtype.val '' (A : Set ↥S), IsClosed ({z} : Set X) := by
    intro A
    refine exists_isClosed_singleton_mem (A.2.1.nonempty.image _) ?_
    exact hScl.isClosedEmbedding_subtypeVal.isClosedMap _
      (isClosed_of_mem_irreducibleComponents _ A.2)
  choose y hymem hyclosed using hpoint
  refine ⟨Set.range y, Set.finite_range y, ?_, ?_, ?_⟩
  · rintro _ ⟨A, rfl⟩
    exact Subtype.coe_image_subset S _ (hymem A)
  · rintro _ ⟨A, rfl⟩
    exact hyclosed A
  · intro B hBcl hBirr hBS hBmax
    obtain ⟨A, hA, hBA⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
      (Subtype.val ⁻¹' B : Set ↥S) (isIrreducible_preimage_subtypeVal hBirr hBS)
    have hvalA : Subtype.val '' A ⊆ S := Subtype.coe_image_subset S A
    have hBvalA : B ⊆ Subtype.val '' A :=
      subset_of_preimage_val_subset hBS fun w hw => ⟨w, hBA hw, rfl⟩
    have heq : Subtype.val '' A = B :=
      hBmax _ (hA.1.image _ continuous_subtype_val.continuousOn) hBvalA hvalA
    exact ⟨y ⟨A, hA⟩, ⟨⟨A, hA⟩, rfl⟩, heq ▸ hymem ⟨A, hA⟩⟩

end AlgebraicGeometry

end

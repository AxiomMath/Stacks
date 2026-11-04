module

public import Mathlib.AlgebraicGeometry.Limits

/-! # A finite affine one-hypercover of a quasi-compact quasi-separated scheme

A quasi-compact scheme is covered by finitely many affine opens; if it is moreover
quasi-separated, the intersection of two of them is again quasi-compact and so is itself covered
by finitely many affine opens. Together these give the *one-hypercover* data of a quasi-compact
quasi-separated scheme by affine opens: finitely many affine opens covering the scheme, together
with, for each pair, finitely many affine opens covering their intersection.

## Main results

* `Stacks.QcqsOneHypercover.exists_finite_affine_oneHypercover_opens`: the data described above.

## Implementation notes

The second index type `ν` is a single finite type, not one per pair: the finite subcovers chosen
for the pairs are indexed by finite sets of points of `S`, and `ν` is the subtype attached to
their union, with the opens chosen for a pair but indexed by a point outside its own finite set
taken to be the empty open, which is affine (`AlgebraicGeometry.isAffineOpen_bot`).

Both coverings are stated as equalities of opens: `⨆ k, U k = ⊤` and `⨆ m, V k l m = U k ⊓ U l`;
the inclusions `V k l m ≤ U k ⊓ U l` are also stated separately.

Quasi-compactness of `S` is the hypothesis `CompactSpace` and quasi-separatedness is
`QuasiSeparatedSpace`.

## References

* [Stacks 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks 01OX](https://stacks.math.columbia.edu/tag/01OX)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.QcqsOneHypercover

/-- On a quasi-compact quasi-separated scheme `S` there are finitely many affine opens `U k`
covering `S` and, for each pair `(k, l)`, finitely many affine opens `V k l m` contained in
`U k ⊓ U l` and covering it. -/
theorem exists_finite_affine_oneHypercover_opens (S : Scheme.{u}) [CompactSpace S]
    [QuasiSeparatedSpace S] :
    ∃ (κ ν : Type u) (_ : Finite κ) (_ : Finite ν) (U : κ → S.Opens)
      (V : κ → κ → ν → S.Opens),
      (∀ k, IsAffineOpen (U k)) ∧ (∀ k l m, IsAffineOpen (V k l m)) ∧
        (⨆ k, U k) = ⊤ ∧ (∀ k l m, V k l m ≤ U k ⊓ U l) ∧
          ∀ k l, (⨆ m, V k l m) = U k ⊓ U l := by
  classical
  have hpt : ∀ x : S, ∃ U : S.Opens, IsAffineOpen U ∧ x ∈ U := by
    intro x
    obtain ⟨-, ⟨W, hW, rfl⟩, hxW, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨W, hW, hxW⟩
  choose U0 hU0aff hU0mem using hpt
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : S => (U0 x : Set S))
    (fun x => (U0 x).isOpen) fun x _ => Set.mem_iUnion.2 ⟨x, hU0mem x⟩
  set K := {x : S // x ∈ t}
  set U : K → S.Opens := fun k => U0 k.1
  have hUaff : ∀ k, IsAffineOpen (U k) := fun k => hU0aff k.1
  have hUtop : (⨆ k, U k) = ⊤ := by
    refine TopologicalSpace.Opens.ext (Set.eq_univ_of_univ_subset ?_)
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy⟩, hxy⟩
  have hinter : ∀ k l : K, IsCompact ((U k ⊓ U l : S.Opens) : Set S) := fun k l =>
    QuasiSeparatedSpace.inter_isCompact _ _ (U k).isOpen (hUaff k).isCompact
      (U l).isOpen (hUaff l).isCompact
  have hV : ∀ (k l : K) (y : S), ∃ V : S.Opens,
      IsAffineOpen V ∧ V ≤ U k ⊓ U l ∧ (y ∈ (U k ⊓ U l : S.Opens) → y ∈ V) := by
    intro k l y
    by_cases hy : y ∈ (U k ⊓ U l : S.Opens)
    · obtain ⟨-, ⟨V, hVaff, rfl⟩, hyV, hVsub⟩ :=
        S.isBasis_affineOpens.exists_subset_of_mem_open hy (U k ⊓ U l).isOpen
      exact ⟨V, hVaff, hVsub, fun _ => hyV⟩
    · exact ⟨⊥, isAffineOpen_bot S, bot_le, fun h => absurd h hy⟩
  choose V0 hV0aff hV0le hV0mem using hV
  have hfin : ∀ k l : K, ∃ s : Finset S,
      ((U k ⊓ U l : S.Opens) : Set S) ⊆ ⋃ y ∈ s, (V0 k l y : Set S) := fun k l =>
    (hinter k l).elim_finite_subcover (fun y : S => (V0 k l y : Set S))
      (fun y => (V0 k l y).isOpen) fun y hy => Set.mem_iUnion.2 ⟨y, hV0mem k l y hy⟩
  choose tt htt using hfin
  set T : Finset S := Finset.univ.biUnion fun p : K × K => tt p.1 p.2
  refine ⟨K, {y : S // y ∈ T}, inferInstance, inferInstance,
    U, fun k l m => V0 k l m.1, hUaff, fun k l m => hV0aff k l m.1, hUtop,
    fun k l m => hV0le k l m.1, fun k l => le_antisymm (iSup_le fun m => hV0le k l m.1) ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (htt k l hx)
  have hyT : y ∈ T := Finset.mem_biUnion.2 ⟨(k, l), Finset.mem_univ _, hy⟩
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hyT⟩, hxy⟩

end Stacks.QcqsOneHypercover

end

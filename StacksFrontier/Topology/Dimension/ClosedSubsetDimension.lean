module

public import Mathlib.Topology.KrullDimension

/-!
# The dimension of a closed subset from the closures of its points

On a quasi-sober space the dimension of a closed subset `S` is controlled by the dimensions of
the closures of the points of `S`: a chain of irreducible closed subsets of `S` lies inside the
closure of the generic point of its largest member, and that generic point is a point of `S`.

## Main results

* `isIrreducible_preimage_subtypeVal` — an irreducible subset of `X` contained in a subset `T`
  stays irreducible when read in the subspace `T`.
* `topologicalKrullDim_le_of_forall_closure` — if every point `x` of a closed subset `S` of a
  quasi-sober space satisfies `dim(closure {x}) ≤ d`, then `dim(S) ≤ d`.
-/

@[expose] public section

open Order Set TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

/-- An irreducible subset `Z` of `X` contained in a subset `T` remains irreducible when read in
the subspace `T`: the opens of `T` are the restrictions of the opens of `X`, and the point of `Z`
produced by irreducibility in `X` lies in `T`. -/
theorem isIrreducible_preimage_subtypeVal {T Z : Set X} (hZ : IsIrreducible Z) (hZT : Z ⊆ T) :
    IsIrreducible (Subtype.val ⁻¹' Z : Set T) := by
  obtain ⟨z, hz⟩ := hZ.nonempty
  refine ⟨⟨⟨z, hZT hz⟩, hz⟩, ?_⟩
  rintro U V hU hV ⟨a, haZ, haU⟩ ⟨b, hbZ, hbV⟩
  obtain ⟨U', hU', rfl⟩ := isOpen_induced_iff.1 hU
  obtain ⟨V', hV', rfl⟩ := isOpen_induced_iff.1 hV
  obtain ⟨c, hcZ, hcU, hcV⟩ := hZ.2 U' V' hU' hV' ⟨a.1, haZ, haU⟩ ⟨b.1, hbZ, hbV⟩
  exact ⟨⟨c, hZT hcZ⟩, hcZ, hcU, hcV⟩

omit [TopologicalSpace X] in
/-- A subset of `T` is recovered from the points of `T` lying over it. -/
private theorem image_preimage_subtypeVal {T A : Set X} (hAT : A ⊆ T) :
    Subtype.val '' (Subtype.val ⁻¹' A : Set T) = A := by
  rw [Set.image_preimage_eq_inter_range, Subtype.range_coe_subtype]
  exact Set.inter_eq_self_of_subset_left hAT

/-- **The dimension of a closed subset is bounded by the dimensions of the closures of its
points.** Let `X` be quasi-sober and let `S ⊆ X` be closed. If `dim(closure {x}) ≤ d` for every
`x ∈ S`, then `dim(S) ≤ d`.

A chain of irreducible closed subsets of `S` is a chain of irreducible closed subsets of `X`; its
largest member is the closure of a point `ξ`, which lies in `S`, and the whole chain restricts to
a chain of the same length in that closure. -/
theorem topologicalKrullDim_le_of_forall_closure [QuasiSober X] {S : Set X} (hS : IsClosed S)
    {d : WithBot ℕ∞} (h : ∀ x ∈ S, topologicalKrullDim (closure ({x} : Set X)) ≤ d) :
    topologicalKrullDim S ≤ d := by
  rw [topologicalKrullDim, Order.krullDim]
  refine iSup_le fun p => ?_
  -- the members of the chain, read as subsets of `X`
  set W : Fin (p.length + 1) → Set X := fun i => Subtype.val '' (p.toFun i : Set S)
  have hWirr : ∀ i, IsIrreducible (W i) := fun i =>
    (p.toFun i).isIrreducible.image _ continuous_subtype_val.continuousOn
  have hWcl : ∀ i, IsClosed (W i) := fun i =>
    hS.isClosedEmbedding_subtypeVal.isClosedMap _ (p.toFun i).isClosed
  -- the largest member is the closure of one of its points
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober (hWirr (Fin.last p.length)) (hWcl (Fin.last p.length))
  have hWT : ∀ i, W i ⊆ closure ({ξ} : Set X) := fun i =>
    (Set.image_mono (SetLike.coe_subset_coe.2 (p.monotone (Fin.le_last i)))).trans hξ.def.ge
  refine le_trans ?_ (h ξ (Subtype.coe_image_subset S _ hξ.mem))
  rw [topologicalKrullDim, Order.krullDim]
  -- the chain restricted to that closure
  let F : Fin (p.length + 1) → IrreducibleCloseds (closure ({ξ} : Set X)) := fun i =>
    ⟨Subtype.val ⁻¹' W i, isIrreducible_preimage_subtypeVal (hWirr i) (hWT i),
      (hWcl i).preimage continuous_subtype_val⟩
  have hFmono : StrictMono F := by
    refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    have hlt := p.step i
    have hne : W i.castSucc ≠ W i.succ := fun hEq =>
      hlt.ne (SetLike.coe_injective (Set.image_injective.2 Subtype.coe_injective hEq))
    refine lt_of_le_of_ne (SetLike.coe_subset_coe.1 fun z hz =>
      Set.image_mono (SetLike.coe_subset_coe.2 hlt.le) hz) fun hEq => hne ?_
    rw [← image_preimage_subtypeVal (hWT i.castSucc), ← image_preimage_subtypeVal (hWT i.succ)]
    exact congrArg (Subtype.val '' ·) (SetLike.coe_set_eq.2 hEq)
  exact le_iSup_of_le (LTSeries.mk p.length F hFmono) le_rfl

end

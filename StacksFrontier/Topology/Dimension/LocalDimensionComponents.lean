module

public import Mathlib.Topology.NoetherianSpace
public import StacksFrontier.Topology.Dimension.ClosedSubsetDimension
public import StacksFrontier.Topology.Dimension.Krull
public import StacksFrontier.Topology.Dimension.MaximalPointDrop
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The local dimension at a point is attained on an irreducible component through it

Let `X` be a topological space and `x ∈ X` a point with a Noetherian open neighbourhood — which
is what local Noetherianity of `X` provides at every point. Then some irreducible component `T`
of `X` containing `x` satisfies

`dim_x(T) = dim_x(X)`,

so that the dimension of `X` at `x` is the maximum of the dimensions at `x` of the irreducible
components of `X` through `x`.

The inequality `dim_x(T) ≤ dim_x(X)` is `topologicalKrullDimAt_le_of_isEmbedding` and needs no
hypothesis at all. For the other one, a Noetherian space has finitely many irreducible
components; deleting those that miss `x`, and intersecting with one neighbourhood of `x` per
remaining component on which that component's local dimension is already attained, leaves an
open neighbourhood `W` of `x` covered by finitely many closed sets, one inside each of those
neighbourhoods. The dimension of a space carrying such a cover is bounded by the dimensions of
the members of the cover, so `dim(W) ≤ max_T dim_x(T)`, while `dim_x(X) ≤ dim(W)` because `W` is
one of the neighbourhoods the infimum defining `dim_x(X)` runs over.

## Main results

* `length_le_topologicalKrullDim_of_forall_subset`: a chain of irreducible closed subsets all of
  whose members lie in a subset `T` has length at most `dim(T)`.
* `topologicalKrullDim_le_of_finite_isClosed_cover`: the dimension of a space covered by finitely
  many closed subsets is bounded by the dimensions of the members of the cover.
* `closure_image_mem_irreducibleComponents_of_isOpen`: the closure of an irreducible component of
  an open subspace is an irreducible component of the ambient space.
* `topologicalKrullDimAt_closure_image_eq_of_isOpen`: and it has the same local dimension there.
* `exists_mem_irreducibleComponents_topologicalKrullDimAt_eq`: the attainment, which is the
  middle equality `dim_u(U) = sup_T dim_u(T)` in the proof of **Stacks 0DRZ**.

## Implementation notes

The Noetherian neighbourhood is carried as `(hN : IsOpen N) (hxN : x ∈ N) [NoetherianSpace ↥N]`,
the shape `StacksFrontier.Topology.Dimension.MaximalPointDrop` already uses and exactly what
`TopologicalSpace.IsLocallyNoetherianSpace` unfolds to at a point; no predicate for local
Noetherianity is needed, and this module stays independent of the files that define one.

The argument itself is run on a Noetherian space, in
`exists_mem_irreducibleComponents_topologicalKrullDimAt_eq_of_noetherianSpace`, and then
transported to the neighbourhood: this keeps the components free of a second layer of subtypes.
Transporting is what the two lemmas on components of an open subspace are for.

The components through the point are indexed by the subtype of the set of them rather than by a
`Finset`, so that the neighbourhood chosen for each comes from a single `choose`; the subtype is
finite because a Noetherian space has finitely many irreducible components.
-/

@[expose] public section

open Set TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

/-! ### Chains inside a subset -/

omit [TopologicalSpace X] in
/-- Two subsets of `T` with the same preimage in the subspace `T` are equal. -/
private theorem eq_of_preimage_subtypeVal_eq {T A A' : Set X} (hA : A ⊆ T) (hA' : A' ⊆ T)
    (h : (Subtype.val ⁻¹' A : Set T) = Subtype.val ⁻¹' A') : A = A' := by
  ext a
  exact ⟨fun ha => (Set.ext_iff.1 h ⟨a, hA ha⟩).1 ha, fun ha => (Set.ext_iff.1 h ⟨a, hA' ha⟩).2 ha⟩

/-- **A chain of irreducible closed subsets inside a subset is a chain of the subspace.** If
every member of a chain of irreducible closed subsets of `X` lies in `T`, then the chain
restricts to a chain of the same length in the subspace `T`, so its length is at most
`dim(T)`. -/
theorem length_le_topologicalKrullDim_of_forall_subset
    (p : LTSeries (IrreducibleCloseds X)) {T : Set X}
    (hpT : ∀ i, (p.toFun i : Set X) ⊆ T) :
    (p.length : WithBot ℕ∞) ≤ topologicalKrullDim T := by
  rw [topologicalKrullDim, Order.krullDim]
  let F : Fin (p.length + 1) → IrreducibleCloseds T := fun i =>
    ⟨Subtype.val ⁻¹' (p.toFun i : Set X),
      isIrreducible_preimage_subtypeVal (p.toFun i).isIrreducible (hpT i),
      (p.toFun i).isClosed.preimage continuous_subtype_val⟩
  have hFmono : StrictMono F := by
    refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    have hlt : p.toFun i.castSucc < p.toFun i.succ := p.step i
    have hne : F i.castSucc ≠ F i.succ := fun hEq =>
      hlt.ne (SetLike.coe_injective (eq_of_preimage_subtypeVal_eq (hpT i.castSucc) (hpT i.succ)
        (SetLike.coe_set_eq.2 hEq)))
    exact lt_of_le_of_ne
      (SetLike.coe_subset_coe.1 fun z hz => SetLike.coe_subset_coe.2 hlt.le hz) hne
  exact le_iSup_of_le (LTSeries.mk p.length F hFmono) le_rfl

/-- **The dimension of a space covered by finitely many closed subsets is bounded by theirs.**
The top member of a chain of irreducible closed subsets is irreducible, hence contained in one
member of the cover, and then so is the whole chain. -/
@[ega "0 14.1.4" "(ii)", ega "0 14.1.7" "partial"]
theorem topologicalKrullDim_le_of_finite_isClosed_cover
    {𝒞 : Set (Set X)} (hfin : 𝒞.Finite) (hclosed : ∀ C ∈ 𝒞, IsClosed C)
    (hcover : ∀ y : X, ∃ C ∈ 𝒞, y ∈ C) {d : WithBot ℕ∞}
    (hdim : ∀ C ∈ 𝒞, topologicalKrullDim C ≤ d) :
    topologicalKrullDim X ≤ d := by
  classical
  rw [topologicalKrullDim, Order.krullDim]
  refine iSup_le fun p => ?_
  obtain ⟨C, hCmem, hpC⟩ := isIrreducible_iff_sUnion_isClosed.mp
    (p.toFun (Fin.last p.length)).isIrreducible hfin.toFinset
    (fun C hC => hclosed C (hfin.mem_toFinset.mp hC))
    (by
      rw [hfin.coe_toFinset]
      exact fun y _ => mem_sUnion.2 (hcover y))
  rw [hfin.mem_toFinset] at hCmem
  refine le_trans (length_le_topologicalKrullDim_of_forall_subset p fun j => ?_) (hdim C hCmem)
  exact (SetLike.coe_subset_coe.2 (LTSeries.monotone p (Fin.le_last j))).trans hpC

/-! ### The attainment on a Noetherian space -/

/-- The local dimension of a subset `S` at a point is the dimension of the trace on `S` of some
open neighbourhood of that point. -/
theorem exists_isOpen_topologicalKrullDim_inter_le {Y : Type*} [TopologicalSpace Y]
    (S : Set Y) {y : Y} (hy : y ∈ S) :
    ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧
      topologicalKrullDim ↥(S ∩ V) ≤ topologicalKrullDimAt S ⟨y, hy⟩ := by
  obtain ⟨⟨O, hyO, hO, hOdim⟩, -⟩ := topologicalKrullDimAt_isLeast S ⟨y, hy⟩
  obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.1 hO
  refine ⟨V, hV, hyO, ?_⟩
  rw [hOdim, ← Subtype.preimage_coe_self_inter S V,
    topologicalKrullDim_preimage_val S (S ∩ V) Set.inter_subset_left]

/-- A point lying on no irreducible component that misses `y` has `y` in its irreducible
component. -/
theorem mem_irreducibleComponent_of_notMem_biUnion {Y : Type*} [TopologicalSpace Y] {y z : Y}
    (hz : z ∉ ⋃ D ∈ {D : Set Y | D ∈ irreducibleComponents Y ∧ y ∉ D}, D) :
    y ∈ irreducibleComponent z := by
  by_contra hnot
  exact hz (mem_iUnion₂.2 ⟨_, ⟨irreducibleComponent_mem_irreducibleComponents z, hnot⟩,
    mem_irreducibleComponent⟩)

/-- **On a Noetherian space the local dimension at a point is attained on an irreducible
component through it.** -/
theorem exists_mem_irreducibleComponents_topologicalKrullDimAt_eq_of_noetherianSpace
    {Y : Type*} [TopologicalSpace Y] [NoetherianSpace Y] (y : Y) :
    ∃ D, ∃ _ : D ∈ irreducibleComponents Y, ∃ hyD : y ∈ D,
      topologicalKrullDimAt ↥D ⟨y, hyD⟩ = topologicalKrullDimAt Y y := by
  classical
  -- the components through `y`, a finite nonempty family
  have hfin : {D : Set Y | D ∈ irreducibleComponents Y ∧ y ∈ D}.Finite :=
    NoetherianSpace.finite_irreducibleComponents.subset fun D hD => hD.1
  have hmem : irreducibleComponent y ∈ {D : Set Y | D ∈ irreducibleComponents Y ∧ y ∈ D} :=
    ⟨irreducibleComponent_mem_irreducibleComponents y, mem_irreducibleComponent⟩
  have hFinite : Finite ↥{D : Set Y | D ∈ irreducibleComponents Y ∧ y ∈ D} := hfin
  -- the local dimension at `y` of a subset through `y`, extended by `⊥` to every subset so that
  -- the finite maximum may be taken over the set of components rather than over its subtype
  set loc : Set Y → WithBot ℕ∞ :=
    fun D => if h : y ∈ D then topologicalKrullDimAt ↥D ⟨y, h⟩ else ⊥
  have hlocval : ∀ (D : Set Y) (h : y ∈ D), loc D = topologicalKrullDimAt ↥D ⟨y, h⟩ :=
    fun D h => dif_pos h
  obtain ⟨D₀, hD₀mem, hD₀max⟩ := Set.exists_max_image
    {D : Set Y | D ∈ irreducibleComponents Y ∧ y ∈ D} loc hfin ⟨_, hmem⟩
  -- a neighbourhood of `y` on which each of them already attains its local dimension
  choose V hVopen hyV hVdim using fun D : ↥{D : Set Y | D ∈ irreducibleComponents Y ∧ y ∈ D} =>
    exists_isOpen_topologicalKrullDim_inter_le D.1 D.2.2
  -- delete the components that miss `y`, and intersect with those neighbourhoods
  have hBadclosed : IsClosed (⋃ D ∈ {D : Set Y | D ∈ irreducibleComponents Y ∧ y ∉ D}, D) :=
    (NoetherianSpace.finite_irreducibleComponents.subset
      fun D (hD : D ∈ {D : Set Y | D ∈ irreducibleComponents Y ∧ y ∉ D}) =>
        hD.1).isClosed_biUnion fun D hD => isClosed_of_mem_irreducibleComponents D hD.1
  set W : Set Y :=
    (⋂ D : ↥{D : Set Y | D ∈ irreducibleComponents Y ∧ y ∈ D}, V D) \
      ⋃ D ∈ {D : Set Y | D ∈ irreducibleComponents Y ∧ y ∉ D}, D
  have hWopen : IsOpen W := (isOpen_iInter_of_finite hVopen).sdiff hBadclosed
  have hyW : y ∈ W := ⟨Set.mem_iInter.2 hyV, fun hbad => by
    obtain ⟨D, ⟨-, hyD⟩, hyD'⟩ := Set.mem_iUnion₂.1 hbad
    exact hyD hyD'⟩
  -- `W` is covered by the traces on it of the components through `y`
  have hWcover : ∀ z : ↥W, ∃ C ∈ Set.range
      (fun D : ↥{D : Set Y | D ∈ irreducibleComponents Y ∧ y ∈ D} =>
        (Subtype.val ⁻¹' D.1 : Set ↥W)), z ∈ C := fun z =>
    ⟨_, ⟨⟨_, irreducibleComponent_mem_irreducibleComponents _,
      mem_irreducibleComponent_of_notMem_biUnion z.2.2⟩, rfl⟩,
      (mem_irreducibleComponent : (z : Y) ∈ irreducibleComponent (z : Y))⟩
  have hWbound : topologicalKrullDim ↥W ≤ topologicalKrullDimAt ↥D₀ ⟨y, hD₀mem.2⟩ := by
    refine topologicalKrullDim_le_of_finite_isClosed_cover (Set.finite_range _) ?_ hWcover ?_
    · rintro C ⟨D, rfl⟩
      exact (isClosed_of_mem_irreducibleComponents D.1 D.2.1).preimage continuous_subtype_val
    · rintro C ⟨D, rfl⟩
      show topologicalKrullDim ↥(Subtype.val ⁻¹' D.1 : Set ↥W) ≤
        topologicalKrullDimAt ↥D₀ ⟨y, hD₀mem.2⟩
      rw [← Subtype.preimage_coe_inter_self W D.1,
        topologicalKrullDim_preimage_val W (D.1 ∩ W) Set.inter_subset_right]
      refine le_trans (topologicalKrullDim_le_of_subset ?_) ((hVdim D).trans ?_)
      · exact fun z hz => ⟨hz.1, Set.mem_iInter.1 hz.2.1 D⟩
      · rw [← hlocval D.1 D.2.2, ← hlocval D₀ hD₀mem.2]
        exact hD₀max D.1 D.2
  exact ⟨D₀, hD₀mem.1, hD₀mem.2, le_antisymm
    (topologicalKrullDimAt_le_of_isEmbedding Topology.IsEmbedding.subtypeVal _)
    (((topologicalKrullDimAt_isLeast Y y).2 ⟨W, hyW, hWopen, rfl⟩).trans hWbound)⟩

/-! ### Components of an open subspace -/

section OpenSubspace

variable {N : Set X} (hN : IsOpen N)

include hN

/-- **The closure of an irreducible component of an open subspace is an irreducible component.**
A larger irreducible subset of `X` meets `N` in an irreducible subset of the subspace `N`
containing the given component, hence equal to it; and an irreducible set lies in the closure of
its intersection with any open set it meets. -/
@[ega "0 2.1.6" "partial"]
theorem closure_image_mem_irreducibleComponents_of_isOpen
    {D : Set N} (hD : D ∈ irreducibleComponents N) :
    closure (Subtype.val '' D) ∈ irreducibleComponents X := by
  have himg : IsIrreducible (Subtype.val '' D : Set X) :=
    hD.1.image _ continuous_subtype_val.continuousOn
  refine ⟨isIrreducible_iff_closure.mpr himg, fun Z hZ hsub => ?_⟩
  have hZN : (Z ∩ N).Nonempty := by
    obtain ⟨w, hw⟩ := hD.1.nonempty
    exact ⟨(w : X), hsub (subset_closure ⟨w, hw, rfl⟩), w.2⟩
  have hirrZN : IsIrreducible (Subtype.val ⁻¹' Z : Set N) := by
    have h₁ : IsIrreducible (Z ∩ N) := ⟨hZN, hZ.isPreirreducible.inter_of_isOpen hN⟩
    rw [← Subtype.preimage_coe_inter_self N Z]
    exact isIrreducible_preimage_subtypeVal h₁ fun _ h => h.2
  have hDsub : D ⊆ (Subtype.val ⁻¹' Z : Set N) := fun w hw =>
    hsub (subset_closure ⟨w, hw, rfl⟩)
  have hDeq : D = (Subtype.val ⁻¹' Z : Set N) := Set.Subset.antisymm hDsub (hD.2 hirrZN hDsub)
  refine (subset_closure_inter_of_isPreirreducible_of_isOpen hZ.isPreirreducible hN hZN).trans ?_
  refine closure_mono fun z hz => ⟨⟨z, hz.2⟩, ?_, rfl⟩
  rw [hDeq]
  exact hz.1

omit hN in
/-- **An irreducible component of a subspace is the ambient component it generates, read back in
the subspace.** The component is closed in the subspace, so it is the preimage of its own
closure. -/
theorem image_eq_inter_closure_image_of_mem_irreducibleComponents
    {D : Set N} (hD : D ∈ irreducibleComponents N) :
    (Subtype.val '' D : Set X) = closure (Subtype.val '' D) ∩ N := by
  have hDclosed : IsClosed D := isClosed_of_mem_irreducibleComponents D hD
  refine Set.Subset.antisymm (fun z hz => ⟨subset_closure hz, ?_⟩) fun z hz => ?_
  · obtain ⟨w, -, rfl⟩ := hz
    exact w.2
  · obtain ⟨hzcl, hzN⟩ := hz
    have hclmem : (⟨z, hzN⟩ : ↥N) ∈ closure D := by
      rw [mem_closure_iff]
      intro U hU hzU
      obtain ⟨U', hU', rfl⟩ := isOpen_induced_iff.1 hU
      obtain ⟨c, hcU', w, hwD, rfl⟩ := mem_closure_iff.1 hzcl U' hU' hzU
      exact ⟨w, hcU', hwD⟩
    exact ⟨⟨z, hzN⟩, hDclosed.closure_subset hclmem, rfl⟩

/-- **An irreducible component of an open subspace has the same local dimension as the ambient
component it generates.** It is an open subset of that component, and homeomorphic to its own
image. -/
theorem topologicalKrullDimAt_closure_image_eq_of_isOpen
    {D : Set N} (hD : D ∈ irreducibleComponents N) {w : ↥N} (hwD : w ∈ D) :
    topologicalKrullDimAt ↥(closure (Subtype.val '' D)) ⟨(w : X), subset_closure ⟨w, hwD, rfl⟩⟩ =
      topologicalKrullDimAt ↥D ⟨w, hwD⟩ := by
  have himg := image_eq_inter_closure_image_of_mem_irreducibleComponents hD
  have hsubset : (Subtype.val '' D : Set X) ⊆ closure (Subtype.val '' D) := subset_closure
  have hopen : Topology.IsOpenEmbedding
      (Set.inclusion hsubset : (Subtype.val '' D : Set X) → ↥(closure (Subtype.val '' D))) := by
    refine ⟨Topology.IsEmbedding.inclusion _, ?_⟩
    rw [Set.range_inclusion]
    have hset : {z : ↥(closure (Subtype.val '' D)) | (z : X) ∈ (Subtype.val '' D : Set X)} =
        Subtype.val ⁻¹' N := by
      ext z
      exact ⟨fun h => (himg.subset h).2, fun h => himg.symm.subset ⟨z.2, h⟩⟩
    rw [hset]
    exact hN.preimage continuous_subtype_val
  have hpt : (hN.isOpenEmbedding_subtypeVal.isEmbedding.homeomorphImage D) ⟨w, hwD⟩ =
      (⟨(w : X), ⟨w, hwD, rfl⟩⟩ : (Subtype.val '' D : Set X)) := Subtype.ext rfl
  calc topologicalKrullDimAt ↥(closure (Subtype.val '' D))
          ⟨(w : X), subset_closure ⟨w, hwD, rfl⟩⟩
      = topologicalKrullDimAt (Subtype.val '' D : Set X) ⟨(w : X), ⟨w, hwD, rfl⟩⟩ :=
        hopen.topologicalKrullDimAt_eq ⟨(w : X), ⟨w, hwD, rfl⟩⟩
    _ = topologicalKrullDimAt ↥D ⟨w, hwD⟩ := by
        rw [topologicalKrullDimAt_eq_of_homeomorph
          (hN.isOpenEmbedding_subtypeVal.isEmbedding.homeomorphImage D) ⟨w, hwD⟩, hpt]

end OpenSubspace

/-! ### The attainment -/

/-- **The local dimension at a point is attained on an irreducible component through it.** Let
`x` be a point of a topological space `X` having a Noetherian open neighbourhood. Then some
irreducible component `T` of `X` through `x` satisfies `dim_x(T) = dim_x(X)`; equivalently,
`dim_x(X)` is the maximum of `dim_x(T)` over the irreducible components `T` through `x`, since
the inequality `dim_x(T) ≤ dim_x(X)` holds for every closed subset `T` through `x`.

This is the middle equality `dim_u(U) = sup_T dim_u(T)` in the proof of **Stacks 0DRZ**, in the
form that proof uses it: the supremum over the irreducible components of `U` through `u` is
attained at one of them. -/
theorem exists_mem_irreducibleComponents_topologicalKrullDimAt_eq
    {x : X} {N : Set X} (hN : IsOpen N) (hxN : x ∈ N) [NoetherianSpace ↥N] :
    ∃ T, ∃ _ : T ∈ irreducibleComponents X, ∃ hxT : x ∈ T,
      topologicalKrullDimAt ↥T ⟨x, hxT⟩ = topologicalKrullDimAt X x := by
  obtain ⟨D, hD, hxD, hDdim⟩ :=
    exists_mem_irreducibleComponents_topologicalKrullDimAt_eq_of_noetherianSpace
      (⟨x, hxN⟩ : ↥N)
  refine ⟨closure (Subtype.val '' D), closure_image_mem_irreducibleComponents_of_isOpen hN hD,
    subset_closure ⟨⟨x, hxN⟩, hxD, rfl⟩, ?_⟩
  rw [topologicalKrullDimAt_closure_image_eq_of_isOpen hN hD hxD, hDdim]
  exact (hN.isOpenEmbedding_subtypeVal.topologicalKrullDimAt_eq ⟨x, hxN⟩).symm

end

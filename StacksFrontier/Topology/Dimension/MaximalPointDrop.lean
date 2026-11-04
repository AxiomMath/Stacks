module

public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober
public import StacksFrontier.Topology.Dimension.Krull

/-!
# The dimension drops at a maximal point of a closed subset

Let `W` be a closed subset of a topological space `T` and let `x` be a point of `W` which is
*maximal in `W`* for specialization: no point of `W` other than `x` specializes to `x`. If `x` is
*not* maximal in `T`, so that some other point `z` of `T` specializes to `x`, then the local
dimension of `W` at `x` is strictly smaller than the local dimension of `T` at `x`.

The reason is that near `x` the set `W` is contained in `closure {x}`: in a Noetherian
neighbourhood of `x` only finitely many irreducible pieces of `W` occur, and each of them whose
closure contains `x` is `closure {x}` by maximality. The point `z` lies in every neighbourhood
of `x`, so `closure {z}` meets that neighbourhood in an irreducible set strictly larger than
`W`, and every chain of irreducible closed subsets of `W` extends by one step along it.

Dually, at a point maximal in the whole of `T` the local dimension of a closed subset containing
it equals the local dimension of `T`, because such a point has a whole neighbourhood inside its
own closure.

## Main results

* `IsPreirreducible.inter_of_isOpen`: the intersection of a preirreducible set with an open set
  is preirreducible.
* `topologicalKrullDim_inter_le_pred_of_not_subset`: a relatively closed proper nonempty subset
  of an irreducible set of dimension at most `n` has dimension at most `n - 1`, and `1 ≤ n`.
* `exists_isOpen_inter_subset_closure_singleton`: near a maximal point `x` of a closed set `W`,
  `W` is contained in `closure {x}`.
* `exists_le_topologicalKrullDimAt_of_specializes`: **the dimension drop.**
* `topologicalKrullDimAt_subtype_eq_of_isMax`: the local dimension of a closed subset at a point
  maximal in the ambient space is the local dimension of the ambient space.
* `exists_specializes_forall_specializes_imp_eq`: every point of a closed set is a
  specialization of a point of that set which is maximal in it.

## Implementation notes

Maximality for specialization is written out as `∀ y ∈ W, y ⤳ x → y = x` rather than through
`closure {x} ∈ irreducibleComponents W`, which would force every statement through a subtype
coercion; on a quasi-sober `T₀` space the two agree. This matches the convention of
`StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.LocallyPrincipal`.

The decomposition of a closed set into finitely many irreducible pieces is taken inside the
Noetherian subspace and pushed forward along `Subtype.val`, which preserves irreducibility but
not closedness; closures are taken afterwards, which is harmless because the generic point of
the closure of a subset of `W` still lies in `W`.

The irreducible set along which the chain is extended is produced abstractly, by an `obtain`
listing exactly the four properties of `closure {z} ∩ V` that the argument uses; this keeps the
subsequent rewriting away from the intersection's definitional unfolding.
-/

@[expose] public section

open TopologicalSpace

universe u

variable {T : Type*} [TopologicalSpace T]

/-- The intersection of a preirreducible set with an open set is preirreducible: two open sets
meeting the intersection meet it simultaneously, because their intersections with the open set
meet the preirreducible set. -/
public theorem IsPreirreducible.inter_of_isOpen {C V : Set T} (hC : IsPreirreducible C)
    (hV : IsOpen V) : IsPreirreducible (C ∩ V) := by
  rintro u v hu hv ⟨a, ⟨haC, haV⟩, hau⟩ ⟨b, ⟨hbC, hbV⟩, hbv⟩
  obtain ⟨p, hpC, hp⟩ := hC (V ∩ u) (V ∩ v) (hV.inter hu) (hV.inter hv)
    ⟨a, haC, haV, hau⟩ ⟨b, hbC, hbV, hbv⟩
  exact ⟨p, ⟨hpC, hp.1.1⟩, hp.1.2, hp.2.2⟩

/-- A chain of irreducible closed subsets of `C ∩ F`, for `F` closed and `C` irreducible not
contained in `F`, extends by one step: namely by `C` itself, which is not contained in `F`. -/
private theorem succ_le_topologicalKrullDim_of_not_subset {C F : Set T} (hC : IsIrreducible C)
    (hF : IsClosed F) (hCF : ¬ C ⊆ F) (p : LTSeries (IrreducibleCloseds ↥(C ∩ F))) :
    ((p.length + 1 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim ↥C := by
  have hsub : C ∩ F ⊆ C := Set.inter_subset_left
  have hinc : Topology.IsInducing (Set.inclusion hsub) :=
    (Topology.IsEmbedding.inclusion hsub).isInducing
  have : IrreducibleSpace ↥C := isIrreducible_iff_irreducibleSpace.mp hC
  let G : IrreducibleCloseds ↥(C ∩ F) → IrreducibleCloseds ↥C :=
    IrreducibleCloseds.map (Set.inclusion hsub) hinc.continuous
  have hG : StrictMono G := IrreducibleCloseds.map_strictMono_of_isInducing hinc
  let top : IrreducibleCloseds ↥C :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ ↥C, isClosed_univ⟩
  have hFset : IsClosed {q : ↥C | (q : T) ∈ F} := hF.preimage continuous_subtype_val
  obtain ⟨c, hcC, hcF⟩ := Set.not_subset.mp hCF
  have hlt : G p.last < top := by
    refine lt_of_le_of_ne (fun q _ => Set.mem_univ q) fun h => ?_
    have hc : (⟨c, hcC⟩ : ↥C) ∈ (G p.last : Set ↥C) := by
      rw [h]
      exact Set.mem_univ _
    have hle : (G p.last : Set ↥C) ⊆ {q : ↥C | (q : T) ∈ F} := by
      refine (IsClosed.closure_subset_iff hFset).mpr ?_
      rintro _ ⟨w, -, rfl⟩
      exact w.2.2
    exact hcF (hle hc)
  have hq := Order.LTSeries.length_le_krullDim ((p.map G hG).snoc top hlt)
  have hlen : ((p.map G hG).snoc top hlt).length = p.length + 1 := by
    simp [RelSeries.snoc, RelSeries.append, RelSeries.singleton]
  rw [hlen] at hq
  simpa [topologicalKrullDim] using hq

/-- A relatively closed subset of an irreducible set `C` of dimension at most `n`, which is
nonempty and not all of `C`, has dimension at most `n - 1`; and `1 ≤ n`, since already the
trivial chain extends by one step. -/
public theorem topologicalKrullDim_inter_le_pred_of_not_subset {C F : Set T}
    (hC : IsIrreducible C) (hF : IsClosed F) (hCF : ¬ C ⊆ F) (hne : (C ∩ F).Nonempty) {n : ℕ}
    (hn : topologicalKrullDim ↥C ≤ (n : WithBot ℕ∞)) :
    1 ≤ n ∧ topologicalKrullDim ↥(C ∩ F) ≤ ((n - 1 : ℕ) : WithBot ℕ∞) := by
  have key : ∀ p : LTSeries (IrreducibleCloseds ↥(C ∩ F)), p.length + 1 ≤ n := fun p => by
    exact_mod_cast WithBot.coe_le_coe.mp
      ((succ_le_topologicalKrullDim_of_not_subset hC hF hCF p).trans hn)
  have h1 : 1 ≤ n := by
    obtain ⟨c, hc⟩ := hne
    have hz := key (RelSeries.singleton _
      (⟨closure {(⟨c, hc⟩ : ↥(C ∩ F))}, isIrreducible_singleton.closure, isClosed_closure⟩))
    simp only [RelSeries.singleton] at hz
    omega
  refine ⟨h1, ?_⟩
  rw [topologicalKrullDim, Order.krullDim]
  refine iSup_le fun p => ?_
  exact WithBot.coe_le_coe.mpr (by exact_mod_cast Nat.le_sub_one_of_lt (key p))

/-- **Near a maximal point of a closed set, the set is contained in the closure of that point.**
If `x ∈ W` is such that no other point of the closed set `W` specializes to `x`, and `x` has a
Noetherian open neighbourhood `N`, then some open neighbourhood `V ⊆ N` of `x` satisfies
`W ∩ V ⊆ closure {x}`.

The Noetherian subspace `W ∩ N` is a finite union of irreducible pieces; the closure of a piece
whose closure contains `x` has a generic point which lies in `W` and specializes to `x`, hence
equals `x` by maximality. Removing the closures of the remaining pieces leaves the required
neighbourhood. -/
public theorem exists_isOpen_inter_subset_closure_singleton [QuasiSober T] {W : Set T}
    (hW : IsClosed W) {x : T} (hmax : ∀ y ∈ W, y ⤳ x → y = x) {N : Set T}
    (hN : IsOpen N) (hxN : x ∈ N) [NoetherianSpace ↥N] :
    ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ N ∧ W ∩ V ⊆ closure {x} := by
  have : NoetherianSpace ↥(W ∩ N) :=
    NoetherianSpace.of_subset (W := N) Set.inter_subset_right
  obtain ⟨S, hSf, -, hSi, hSU⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible
      (α := ↥(W ∩ N)) (s := Set.univ) isClosed_univ
  set A : Set ↥(W ∩ N) → Set T := fun Y => closure (Subtype.val '' Y) with hA
  have hAsub : ∀ Y : Set ↥(W ∩ N), A Y ⊆ W := by
    intro Y
    exact hW.closure_subset_iff.mpr
      (Set.image_subset_iff.mpr fun q _ => (q.2 : (q : T) ∈ W ∩ N).1)
  have hkey : ∀ Y ∈ S, x ∈ A Y → A Y ⊆ closure {x} := by
    intro Y hY hxA
    have hirr : IsIrreducible (Subtype.val '' Y) :=
      (hSi Y hY).image _ continuous_subtype_val.continuousOn
    have hgen : closure {hirr.genericPoint} = A Y := hirr.genericPoint_closure_eq
    have hmemW : hirr.genericPoint ∈ W := hAsub Y (hgen ▸ subset_closure rfl)
    have hsp : hirr.genericPoint ⤳ x := specializes_iff_mem_closure.mpr (hgen ▸ hxA)
    rw [← hgen, hmax _ hmemW hsp]
  have hbadf : {Y ∈ S | x ∉ A Y}.Finite := hSf.subset fun _ h => h.1
  have hKclosed : IsClosed (⋃ Y ∈ {Y ∈ S | x ∉ A Y}, A Y) :=
    hbadf.isClosed_biUnion fun _ _ => isClosed_closure
  refine ⟨N ∩ (⋃ Y ∈ {Y ∈ S | x ∉ A Y}, A Y)ᶜ, hN.inter hKclosed.isOpen_compl,
    ⟨hxN, ?_⟩, fun _ h => h.1, ?_⟩
  · intro hmem
    obtain ⟨Y, hY, hxY⟩ := Set.mem_iUnion₂.mp hmem
    exact hY.2 hxY
  · rintro w ⟨hwW, hwN, hwK⟩
    have hwmem : (⟨w, hwW, hwN⟩ : ↥(W ∩ N)) ∈ (Set.univ : Set ↥(W ∩ N)) := Set.mem_univ _
    rw [hSU] at hwmem
    obtain ⟨Y, hY, hwY⟩ := hwmem
    have hwA : w ∈ A Y := subset_closure ⟨_, hwY, rfl⟩
    have hxAY : x ∈ A Y := by
      by_contra hx
      exact hwK (Set.mem_iUnion₂.mpr ⟨Y, ⟨hY, hx⟩, hwA⟩)
    exact hkey Y hY hxAY hwA

/-- **The dimension drops at a maximal point of a closed subset.** Let `W` be a closed subset of
a quasi-sober space, let `x ∈ W` be maximal in `W` for specialization, and suppose some point
`z ≠ x` specializes to `x`. If the local dimension of the ambient space at `x` is at most `n`,
then `1 ≤ n` and the local dimension of `W` at `x` is at most `n - 1`.

This is the step of Stacks 053R which says that at a generic point `x` of an irreducible
component of `Z_s` which is not a generic point of an irreducible component of `X_s` one has
`dim_x(Z_s) ≤ d - 1`. -/
public theorem exists_le_topologicalKrullDimAt_of_specializes [QuasiSober T] {W : Set T}
    (hW : IsClosed W) {x : T} (hxW : x ∈ W) (hmax : ∀ y ∈ W, y ⤳ x → y = x) {z : T}
    (hz : z ⤳ x) (hzx : z ≠ x) {N : Set T} (hN : IsOpen N) (hxN : x ∈ N)
    [NoetherianSpace ↥N] {n : ℕ} (hn : topologicalKrullDimAt T x ≤ (n : WithBot ℕ∞)) :
    ∃ k : ℕ, k + 1 ≤ n ∧ topologicalKrullDimAt ↥W ⟨x, hxW⟩ ≤ (k : WithBot ℕ∞) := by
  obtain ⟨⟨V₀, hxV₀, hV₀, hdim⟩, -⟩ := topologicalKrullDimAt_isLeast T x
  obtain ⟨V₁, hV₁, hxV₁, -, hWV₁⟩ :=
    exists_isOpen_inter_subset_closure_singleton hW hmax hN hxN
  obtain ⟨V, hVopen, hxV, hVV₀, hWV⟩ :
      ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ V₀ ∧ W ∩ V ⊆ closure {x} :=
    ⟨V₀ ∩ V₁, hV₀.inter hV₁, ⟨hxV₀, hxV₁⟩, Set.inter_subset_left,
      fun w hw => hWV₁ ⟨hw.1, hw.2.2⟩⟩
  have hVdim : topologicalKrullDim ↥V ≤ (n : WithBot ℕ∞) :=
    le_trans (Topology.IsEmbedding.inclusion hVV₀).isInducing.topologicalKrullDim_le (hdim ▸ hn)
  have hzV : z ∈ V := by
    obtain ⟨p, hpV, hpz⟩ := mem_closure_iff.mp (specializes_iff_mem_closure.mp hz) V hVopen hxV
    exact hpz ▸ hpV
  obtain ⟨C, hCirr, hzC, hCV, hWVC⟩ :
      ∃ C : Set T, IsIrreducible C ∧ z ∈ C ∧ C ⊆ V ∧ W ∩ V ⊆ C :=
    ⟨closure {z} ∩ V, ⟨⟨z, subset_closure rfl, hzV⟩,
        isIrreducible_singleton.closure.isPreirreducible.inter_of_isOpen hVopen⟩,
      ⟨subset_closure rfl, hzV⟩, Set.inter_subset_right,
      fun w hw => ⟨specializes_iff_closure_subset.mp hz (hWV hw), hw.2⟩⟩
  have hCdim : topologicalKrullDim ↥C ≤ (n : WithBot ℕ∞) :=
    le_trans (Topology.IsEmbedding.inclusion hCV).isInducing.topologicalKrullDim_le hVdim
  have hCW : ¬ C ⊆ W := fun h => hzx (hmax z (h hzC) hz)
  have hxC : x ∈ C := hWVC ⟨hxW, hxV⟩
  obtain ⟨h1, hdrop⟩ :=
    topologicalKrullDim_inter_le_pred_of_not_subset hCirr hW hCW ⟨x, hxC, hxW⟩ hCdim
  refine ⟨n - 1, by omega, ?_⟩
  have hopenemb : Topology.IsOpenEmbedding
      (Set.inclusion (Set.inter_subset_right : C ∩ W ⊆ W)) := by
    refine ⟨Topology.IsEmbedding.inclusion _, ?_⟩
    rw [Set.range_inclusion, show {q : ↥W | (q : T) ∈ C ∩ W} = Subtype.val ⁻¹' V from
      Set.ext fun q => ⟨fun h => hCV h.1, fun h => ⟨hWVC ⟨q.2, h⟩, q.2⟩⟩]
    exact hVopen.preimage continuous_subtype_val
  have hxCW : x ∈ C ∩ W := ⟨hxC, hxW⟩
  calc topologicalKrullDimAt ↥W ⟨x, hxW⟩
      = topologicalKrullDimAt ↥(C ∩ W) ⟨x, hxCW⟩ :=
        hopenemb.topologicalKrullDimAt_eq ⟨x, hxCW⟩
    _ ≤ topologicalKrullDim ↥(C ∩ W) := topologicalKrullDimAt_le_topologicalKrullDim _
    _ ≤ ((n - 1 : ℕ) : WithBot ℕ∞) := hdrop

/-- At a point maximal in the whole space for specialization, the local dimension of a closed
subset containing it is the local dimension of the space: such a point has an open neighbourhood
contained in its own closure, hence in the subset. -/
public theorem topologicalKrullDimAt_subtype_eq_of_isMax [QuasiSober T] {x : T}
    (hmax : ∀ y : T, y ⤳ x → y = x) {N : Set T} (hN : IsOpen N) (hxN : x ∈ N)
    [NoetherianSpace ↥N] {W : Set T} (hW : IsClosed W) (hxW : x ∈ W) :
    topologicalKrullDimAt ↥W ⟨x, hxW⟩ = topologicalKrullDimAt T x := by
  obtain ⟨V, hVopen, hxV, -, hVsub⟩ :=
    exists_isOpen_inter_subset_closure_singleton (W := Set.univ) isClosed_univ
      (fun y _ hy => hmax y hy) hN hxN
  have hVclosure : V ⊆ closure {x} := fun v hv => hVsub ⟨Set.mem_univ v, hv⟩
  have hVW : V ⊆ W := hVclosure.trans (hW.closure_subset_iff.mpr (by simpa using hxW))
  have hembW : Topology.IsOpenEmbedding (Set.inclusion hVW) :=
    ⟨Topology.IsEmbedding.inclusion _, by
      rw [Set.range_inclusion]
      exact hVopen.preimage continuous_subtype_val⟩
  calc topologicalKrullDimAt ↥W ⟨x, hxW⟩
      = topologicalKrullDimAt ↥V ⟨x, hxV⟩ := hembW.topologicalKrullDimAt_eq ⟨x, hxV⟩
    _ = topologicalKrullDimAt T x :=
      (hVopen.isOpenEmbedding_subtypeVal.topologicalKrullDimAt_eq ⟨x, hxV⟩).symm

/-- **A proper nonempty closed subset of an irreducible space is not a union of irreducible
components.** An irreducible space has exactly one irreducible component, the whole space, which
is not contained in a proper subset; so the union in question is empty.

This records that "is set theoretically a union of irreducible components of the ambient space",
the conclusion of Stacks 053R, is a genuine constraint on a closed set and not automatic: it
fails for every proper nonempty closed subset of an irreducible space. -/
public theorem ne_sUnion_irreducibleComponents_of_ne_univ [IrreducibleSpace T] (W : Set T)
    (hne : W.Nonempty) (hW : W ≠ Set.univ) :
    W ≠ ⋃₀ {C : Set T | C ∈ irreducibleComponents T ∧ C ⊆ W} := by
  have hempty : {C : Set T | C ∈ irreducibleComponents T ∧ C ⊆ W} = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun C hC => ?_
    have hCuniv : C = Set.univ := by
      simpa [irreducibleComponents_eq_singleton] using hC.1
    exact hW (Set.univ_subset_iff.mp (hCuniv ▸ hC.2))
  rw [hempty, Set.sUnion_empty]
  exact hne.ne_empty

/-- Every point of a closed subset of a quasi-sober `T₀` space is a specialization of a point of
that subset which is maximal in it for specialization, namely of the generic point of the
irreducible component of the subset through it. -/
public theorem exists_specializes_forall_specializes_imp_eq [QuasiSober T] [T0Space T]
    {W : Set T} (hW : IsClosed W) {y : T} (hy : y ∈ W) :
    ∃ ξ ∈ W, ξ ⤳ y ∧ ∀ w ∈ W, w ⤳ ξ → w = ξ := by
  have : QuasiSober ↥W := hW.isClosedEmbedding_subtypeVal.quasiSober
  have hZirr : IsIrreducible (irreducibleComponent (⟨y, hy⟩ : ↥W)) :=
    isIrreducible_irreducibleComponent
  have hζZ : closure {hZirr.genericPoint} = irreducibleComponent (⟨y, hy⟩ : ↥W) :=
    hZirr.closure_genericPoint isClosed_irreducibleComponent
  refine ⟨(hZirr.genericPoint : T), hZirr.genericPoint.2, ?_, ?_⟩
  · exact (specializes_iff_mem_closure.mpr
      (hζZ ▸ mem_irreducibleComponent)).map continuous_subtype_val
  · intro w hw hwζ
    have hw' : (⟨w, hw⟩ : ↥W) ⤳ hZirr.genericPoint :=
      Topology.IsInducing.subtypeVal.specializes_iff.mp hwζ
    have hsub : irreducibleComponent (⟨y, hy⟩ : ↥W) ⊆ closure {(⟨w, hw⟩ : ↥W)} :=
      hζZ ▸ specializes_iff_closure_subset.mp hw'
    have heq : closure {(⟨w, hw⟩ : ↥W)} = irreducibleComponent (⟨y, hy⟩ : ↥W) :=
      Set.Subset.antisymm
        ((irreducibleComponent_mem_irreducibleComponents (⟨y, hy⟩ : ↥W)).2
          isIrreducible_singleton.closure hsub) hsub
    have hback : hZirr.genericPoint ⤳ (⟨w, hw⟩ : ↥W) :=
      specializes_iff_mem_closure.mpr (by rw [hζZ, ← heq]; exact subset_closure rfl)
    exact congrArg Subtype.val (hw'.antisymm hback).eq

end

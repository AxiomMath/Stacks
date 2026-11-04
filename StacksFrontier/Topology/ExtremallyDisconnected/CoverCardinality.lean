module

public import StacksFrontier.Topology.ExtremallyDisconnected.Cover
public import StacksFrontier.Topology.Compactification.CardinalityBound

/-!
# The size of a minimal extremally disconnected cover

Let `X` be a quasi-compact Hausdorff space and let `π : X' → X` be a *minimal* extremally
disconnected cover in the sense of `StacksFrontier.Topology.ExtremallyDisconnected.Cover`, i.e. a
continuous surjection from a quasi-compact Hausdorff extremally disconnected space such that no
proper closed subset of `X'` surjects onto `X`. If `κ` is a cardinal with `#X ≤ κ`, then
`#X' ≤ 2 ^ (2 ^ κ)`.

The argument is the one in the Stacks project: pick a set-theoretic section `s : X → X'` of `π`
and put `S = range s`. Minimality forces `S` to be dense in `X'`, because `closure S` is a closed
subset whose image is already all of `X`. Now `#X' ≤ #P(P(S))` by Stacks 0909, and `#S = #X ≤ κ`.

Two deliberate deviations from the source:

* The statement is **conditional on being given a minimal cover**. The existence result
  `exists_extremallyDisconnected_cover` (Stacks 090D) produces a cover via `Ultrafilter X` but does
  not assert that it is minimal, so no minimal cover is available to instantiate this with; and the
  tag is anyway a statement *about* the minimal cover rather than an existence claim.
* Stacks assumes `κ` infinite. That hypothesis is **not needed** for the inequality — the proof
  only uses `#X ≤ κ` and monotonicity of `κ ↦ 2 ^ κ`. It is retained (as the unused `_hκ`) to
  keep the statement literally that of the source.

## Main results

* `dense_of_minimal_cover`: in a minimal cover, any subset of `X'` surjecting onto `X` is dense.
* `minimal_cover_card_le` (Stacks 090E): the cardinality bound `#X' ≤ 2 ^ (2 ^ κ)`.
-/

@[expose] public section

open Function Set

universe u

/-- If no proper closed subset of `X'` surjects onto `X` under `π`, then any subset `S ⊆ X'` with
`π '' S = univ` is dense: `closure S` is a closed subset whose image is all of `X`, hence is not
proper. -/
lemma dense_of_minimal_cover {X X' : Type u} [TopologicalSpace X']
    {π : X' → X} (π_min : ∀ E : Set X', IsClosed E → E ≠ univ → π '' E ≠ univ)
    {S : Set X'} (hS : π '' S = univ) : Dense S := by
  rw [dense_iff_closure_eq]
  by_contra h
  exact π_min (closure S) isClosed_closure h
    (eq_univ_of_subset (image_mono subset_closure) hS)

/-- **Stacks 090E.** Let `X` be a quasi-compact Hausdorff space and let `π : X' → X` be a minimal
quasi-compact Hausdorff extremally disconnected cover of `X`, minimality meaning that no proper
closed subset of `X'` surjects onto `X`. If `#X ≤ κ` then `#X' ≤ 2 ^ (2 ^ κ)`.

The infiniteness hypothesis `_hκ` on `κ` is present only to match the source; it is not used. -/
@[stacks 090E]
theorem minimal_cover_card_le
    {X X' : Type u}
    [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace X'] [CompactSpace X'] [T2Space X'] [ExtremallyDisconnected X']
    {π : X' → X} (π_surj : Function.Surjective π)
    (π_min : ∀ E : Set X', IsClosed E → E ≠ univ → π '' E ≠ univ)
    {κ : Cardinal.{u}} (_hκ : Cardinal.aleph0 ≤ κ) (hX : Cardinal.mk X ≤ κ) :
    Cardinal.mk X' ≤ (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ) := by
  -- A set-theoretic section `s` of `π`, and the subset `range s` it cuts out.
  obtain ⟨s, hs⟩ := π_surj.hasRightInverse
  -- `range s` surjects onto `X` because `π ∘ s = id`, so it is dense by minimality.
  have hrange : DenseRange ((↑) : range s → X') := by
    rw [DenseRange, Subtype.range_coe]
    exact dense_of_minimal_cover π_min
      (eq_univ_of_forall fun x => ⟨s x, mem_range_self x, hs x⟩)
  -- Stacks 0909 applied to the inclusion `range s → X'`, which is continuous with dense range;
  -- and `range s` is in bijection with `X`, since `s` is injective.
  calc Cardinal.mk X' ≤ Cardinal.mk (Set (Set (range s))) :=
        mk_le_mk_set_set_of_denseRange _ continuous_subtype_val hrange
    _ = (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ Cardinal.mk (range s)) := by
        rw [Cardinal.mk_set, Cardinal.mk_set]
    _ ≤ (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ) :=
        Cardinal.power_le_power_left two_ne_zero
          (Cardinal.power_le_power_left two_ne_zero
            ((Cardinal.mk_range_eq s hs.injective).trans_le hX))

end

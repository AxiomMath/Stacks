module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Proper.ClosedProjection

/-!
# Quasi-compactness via closed projections: the two Bourbaki ingredients

Stacks Lemma 005P says that a topological space `X` is quasi-compact exactly when the projection
`Z × X → Z` is a closed map for every topological space `Z`; it is
`compactSpace_iff_forall_isClosedMap_fst`. Stacks Remark 005Q records that this lemma is the
combination of two results of Bourbaki (General Topology, I, p. 75, Lemme 1 and p. 76,
Corollaire 1). This file states those two directions separately and recovers the equivalence as
their combination.

## Main results

* `isClosedMap_fst_of_compactSpace_and_compactSpace_of_forall_isClosedMap_fst`: the two
  directions of Lemma 005P, stated separately. A quasi-compact `X` has closed projections
  `Z × X → Z` for every `Z` in any universe, and conversely closedness of these projections for
  every `Z` in the universe of `X` forces `X` to be quasi-compact.
* `compactSpace_iff_isClosedMap_fst`: their combination, the equivalence of Lemma 005P for
  spaces in `Type`.
-/

@[expose] public section

universe u v

/-- The two ingredients of Stacks Lemma 005P, which Stacks Remark 005Q attributes to Bourbaki
(General Topology, I, p. 75, Lemme 1 and p. 76, Corollaire 1).

1. If `X` is quasi-compact, then for every topological space `Z` (in any universe) the
   projection `Prod.fst : Z × X → Z` is a closed map.
2. Conversely, if the projection `Prod.fst : Z × X → Z` is a closed map for every topological
   space `Z` in the universe of `X`, then `X` is quasi-compact.

Lemma 005P (`compactSpace_iff_forall_isClosedMap_fst`) is their combination, as the remark
says; see `compactSpace_iff_isClosedMap_fst`. -/
@[stacks 005Q "the remark is bibliographic: it says Lemma 005P combines two results of \
Bourbaki. Formalized as the two directions of 005P stated separately, the forward one for every \
universe of `Z`; their combination is `compactSpace_iff_isClosedMap_fst`."]
theorem isClosedMap_fst_of_compactSpace_and_compactSpace_of_forall_isClosedMap_fst
    (X : Type u) [TopologicalSpace X] :
    (CompactSpace X →
        ∀ (Z : Type v) [TopologicalSpace Z], IsClosedMap (Prod.fst : Z × X → Z)) ∧
      ((∀ (Z : Type u) [TopologicalSpace Z], IsClosedMap (Prod.fst : Z × X → Z)) →
        CompactSpace X) :=
  ⟨fun _ _ _ => isClosedMap_fst_of_compactSpace,
    (compactSpace_iff_forall_isClosedMap_fst X).2⟩

/-- A topological space `X : Type` is quasi-compact (`CompactSpace X`) if and only if, for every
topological space `Z : Type`, the first projection `Prod.fst : Z × X → Z` is a closed map. This is
the universe-`0` case of Stacks Lemma 005P (`compactSpace_iff_forall_isClosedMap_fst`), obtained
here by combining the two directions of
`isClosedMap_fst_of_compactSpace_and_compactSpace_of_forall_isClosedMap_fst`, as Stacks
Remark 005Q describes. -/
theorem compactSpace_iff_isClosedMap_fst (X : Type) [TopologicalSpace X] :
    CompactSpace X ↔
      ∀ (Z : Type) [TopologicalSpace Z], IsClosedMap (Prod.fst : Z × X → Z) :=
  let h := isClosedMap_fst_of_compactSpace_and_compactSpace_of_forall_isClosedMap_fst.{0, 0} X
  ⟨h.1, h.2⟩

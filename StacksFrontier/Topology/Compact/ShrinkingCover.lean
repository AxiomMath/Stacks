module

public import Mathlib.Topology.Compactness.Compact

/-!
# Shrinking an open cover of a separated quasi-compact subset (Stacks 0CY5)

Let `Z` be a quasi-compact subset of a topological space `X` any two distinct points of which
can be separated by disjoint opens *of `X`* (no separation axiom is imposed on `X` itself, and
`Z` need not be closed). Let `U : I → Set X` be an open cover of `Z`, let `p : ℕ`, and for
every `(p+1)`-tuple `σ : Fin (p+1) → I` let `W σ` be an open set with `W σ ⊆ ⋂ k, U (σ k)`
which agrees with `⋂ k, U (σ k)` on `Z`. The tag produces an open cover `V : I → Set X` of `Z`
refining `U` with two extra properties: `closure (V i) ∩ Z ⊆ U i`, and — this is the point —
`⋂ k, V (σ k) ⊆ W σ` for *every* tuple `σ`, on the nose rather than only after intersecting
with `Z`.

The construction has three stages.

* **Pointwise shrinking.** For `x ∈ Z ∩ U`, the set `Z \ U` is quasi-compact and misses `x`,
  so finitely many separating neighbourhoods of its points suffice; intersecting the
  complementary neighbourhoods of `x` with `U` gives an open `V ∋ x` inside `U` whose closure
  meets `Z` only inside `U`. Quasi-compactness of `Z` then assembles these into an initial
  cover `V₀` with `closure (V₀ i) ∩ Z ⊆ U i`.
* **The shrink operation.** `TopologicalSpace.shrinkOp` fixes one tuple `σ`: it replaces
  `V (σ k)` by the union of `V (σ k) ∩ W σ` with the part of `V (σ k)` outside the closures of
  the other `V (σ l)`. A point in every `V' (σ k)` but outside `W σ` would have to avoid its
  own closures, which is impossible, so afterwards `⋂ k, V' (σ k) ⊆ W σ`; and the trace on `Z`
  is unchanged, because on `Z` the set `W σ` already *is* `⋂ k, U (σ k)`.
* **Iteration.** `TopologicalSpace.iterateShrink` folds the shrink operation over a *list* of
  tuples. Where the source inducts on `p`, this formalization reduces `I` to a finite subcover
  and then iterates over the (finite) list of all `(p+1)`-tuples, which keeps the invariants —
  openness, refinement, closure control, unchanged trace on `Z`, and the already-handled
  tuples — in a single induction over the list. Indices outside the finite subcover are
  finally assigned `∅`, for which every required property is trivial.
-/

@[expose] public section

namespace TopologicalSpace

/-- Pointwise shrinking. If `x ∈ Z ∩ U` and distinct points of the quasi-compact set `Z` can
be separated by disjoint opens of `X`, then `x` has an open neighbourhood `V ⊆ U` whose closure
meets `Z` only inside `U`: separate `x` from each point of the quasi-compact `Z \ U`, take a
finite subcover, and intersect `U` with the corresponding neighbourhoods of `x`. -/
private lemma exists_isOpen_closure_inter_subset
    {X : Type*} [TopologicalSpace X]
    (Z : Set X) (hZ : IsCompact Z)
    (hSep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
      ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B)
    (U : Set X) (hU : IsOpen U) (x : X) (hxZ : x ∈ Z) (hxU : x ∈ U) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ closure V ∩ Z ⊆ U := by
  -- `K` is the compact set of "bad" points of `Z`.
  set K := Z \ U
  have hKcompact : IsCompact K := hZ.diff hU
  -- Separate `x` from every bad point.
  have hSepK : ∀ y ∈ K, ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B :=
    fun y hy => hSep x hxZ y hy.1 fun h => hy.2 (h ▸ hxU)
  choose A B hAopen hBopen hxA hyB hDisj using hSepK
  obtain ⟨t, ht⟩ := hKcompact.elim_nhds_subcover' B fun y hy => (hBopen y hy).mem_nhds (hyB y hy)
  refine ⟨U ∩ ⋂ (y : K) (_ : y ∈ t), A y.1 y.2, ?_, ?_, ?_, ?_⟩
  · exact hU.inter (isOpen_biInter_finset fun y _ => hAopen y.1 y.2)
  · exact ⟨hxU, Set.mem_iInter₂.mpr (fun y _ => hxA y.1 y.2)⟩
  · exact Set.inter_subset_left
  · intro z ⟨hzClos, hzZ⟩
    by_contra hzU
    obtain ⟨⟨y, hyK⟩, hyt, hzBy⟩ := Set.mem_iUnion₂.mp (ht (⟨hzZ, hzU⟩ : z ∈ K))
    have hVsubAy : U ∩ ⋂ (y' : K) (_ : y' ∈ t), A y'.1 y'.2 ⊆ A y hyK := fun w hw =>
      Set.mem_iInter₂.mp hw.2 ⟨y, hyK⟩ hyt
    have hClosAsubBc : closure (A y hyK) ⊆ (B y hyK)ᶜ :=
      closure_minimal (Set.disjoint_left.mp (hDisj y hyK)) (hBopen y hyK).isClosed_compl
    exact hClosAsubBc (closure_mono hVsubAy hzClos) hzBy

/-- One step of the shrink operation for a single tuple `σ`: the index `j` is replaced by
`V j` intersected with, for every `k` with `σ k = j`, the union of `V (σ k) ∩ W σ` and the part
of `V (σ k)` lying outside the closures of the other `V (σ l)`. -/
noncomputable def shrinkOp {X : Type*} [TopologicalSpace X] {I : Type*} [Fintype I]
    (p : ℕ) (W : (Fin (p + 1) → I) → Set X) (σ : Fin (p + 1) → I) (V : I → Set X) : I → Set X :=
  fun j => V j ∩ ⋂ (k : {k : Fin (p+1) // σ k = j}),
    ((V (σ k) ∩ W σ) ∪ (V (σ k) \ ⋂ (l : {l : Fin (p+1) // l ≠ k}), closure (V (σ l.1))))

/-- Fold `TopologicalSpace.shrinkOp` over a list of tuples, shrinking for each in turn. -/
noncomputable def iterateShrink {X : Type*} [TopologicalSpace X] {I : Type*} [Fintype I]
    (p : ℕ) (W : (Fin (p + 1) → I) → Set X) (tuples : List (Fin (p + 1) → I))
    (V₀ : I → Set X) : I → Set X :=
  tuples.foldl (fun V σ => shrinkOp p W σ V) V₀

/-- Shrinking for a tuple `σ` does not change the trace on `Z`: a point of `V i ∩ Z` outside
`W σ` fails to lie in some `U (σ t)` — because on `Z` the set `W σ` is `⋂ k, U (σ k)` — and the
closure condition then keeps it out of `closure (V (σ t))`, putting it in the second disjunct. -/
private lemma shrinkOp_inter_eq
    {X : Type*} [TopologicalSpace X]
    (Z : Set X) (p : ℕ) (I : Type*) [Fintype I]
    (U : I → Set X)
    (V : I → Set X)
    (hVU : ∀ i, V i ⊆ U i)
    (hClos : ∀ i, closure (V i) ∩ Z ⊆ U i)
    (W : (Fin (p + 1) → I) → Set X)
    (hWinter : ∀ σ, W σ ∩ Z = (⋂ k, U (σ k)) ∩ Z)
    (σ : Fin (p + 1) → I) (i : I) :
    shrinkOp p W σ V i ∩ Z = V i ∩ Z := by
  ext x
  simp only [Set.mem_inter_iff]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · intro ⟨hxVi, hxZ⟩
    refine ⟨⟨hxVi, ?_⟩, hxZ⟩
    apply Set.mem_iInter.mpr
    intro ⟨k, hk⟩
    have hxVsk : x ∈ V (σ k) := hk ▸ hxVi
    by_cases hxW : x ∈ W σ
    · exact Set.mem_union_left _ ⟨hxVsk, hxW⟩
    · refine Set.mem_union_right _ ⟨hxVsk, fun hxInter => ?_⟩
      obtain ⟨t, hxt⟩ : ∃ t, x ∉ U (σ t) := by
        by_contra! h
        exact hxW ((Set.ext_iff.mp (hWinter σ) x).mpr ⟨Set.mem_iInter.mpr h, hxZ⟩).1
      have htk : t ≠ k := by
        rintro rfl
        exact hxt (hVU _ hxVsk)
      exact hxt (hClos (σ t) ⟨Set.mem_iInter.mp hxInter ⟨t, htk⟩, hxZ⟩)

/-- After shrinking for the tuple `σ`, the intersection `⋂ k, V' (σ k)` really is inside
`W σ`: a point outside `W σ` would have to lie in every `V (σ k)`, hence in every
`closure (V (σ l))`, contradicting the second disjunct it was forced into. -/
private lemma iInter_shrinkOp_subset
    {X : Type*} [TopologicalSpace X]
    (p : ℕ) (I : Type*) [Fintype I]
    (V : I → Set X)
    (W : (Fin (p + 1) → I) → Set X)
    (σ : Fin (p + 1) → I) :
    (⋂ k, shrinkOp p W σ V (σ k)) ⊆ W σ := by
  intro x hx
  by_contra hxnW
  have hxSk := fun k : Fin (p + 1) =>
    Set.mem_iInter.mp (Set.mem_iInter.mp hx k).2 ⟨k, rfl⟩
  have hxDiff : ∀ k : Fin (p + 1),
      x ∈ V (σ k) \ ⋂ (l : {l : Fin (p+1) // l ≠ k}), closure (V (σ l.1)) := by
    intro k
    cases hxSk k with
    | inl h => exact absurd h.2 hxnW
    | inr h => exact h
  exact (hxDiff 0).2 (Set.mem_iInter.mpr fun l => subset_closure (hxDiff l.1).1)

private lemma shrinkOp_subset {X : Type*} [TopologicalSpace X] {I : Type*} [Fintype I]
    (p : ℕ) (W : (Fin (p + 1) → I) → Set X) (σ : Fin (p + 1) → I) (V : I → Set X) (j : I) :
    shrinkOp p W σ V j ⊆ V j :=
  Set.inter_subset_left

private lemma iterateShrink_subset {X : Type*} [TopologicalSpace X] {I : Type*} [Fintype I]
    (p : ℕ) (W : (Fin (p + 1) → I) → Set X) (tuples : List (Fin (p + 1) → I))
    (V₀ : I → Set X) (j : I) :
    iterateShrink p W tuples V₀ j ⊆ V₀ j := by
  unfold iterateShrink
  induction tuples generalizing V₀ with
  | nil => exact Set.Subset.rfl
  | cons σ rest ih =>
    simp only [List.foldl_cons]
    exact (ih (shrinkOp p W σ V₀)).trans (shrinkOp_subset p W σ V₀ j)

private lemma isOpen_shrinkOp {X : Type*} [TopologicalSpace X] {I : Type*} [Fintype I]
    (p : ℕ) (W : (Fin (p + 1) → I) → Set X) (hW : ∀ σ, IsOpen (W σ))
    (σ : Fin (p + 1) → I) (V : I → Set X) (hV : ∀ i, IsOpen (V i)) (j : I) :
    IsOpen (shrinkOp p W σ V j) := by
  unfold shrinkOp
  exact (hV j).inter <| isOpen_iInter_of_finite fun k =>
    ((hV _).inter (hW σ)).union ((hV _).sdiff (isClosed_iInter fun _ => isClosed_closure))

/-- The invariants preserved by iterated shrinking: openness, refinement of `U`, the closure
condition, the trace on `Z`, and the intersection condition for every tuple already processed.
-/
private lemma iterateShrink_spec
    {X : Type*} [TopologicalSpace X]
    (Z : Set X) (p : ℕ) (I : Type*) [Fintype I]
    (U : I → Set X)
    (W : (Fin (p + 1) → I) → Set X) (hW : ∀ σ, IsOpen (W σ))
    (hWinter : ∀ σ, W σ ∩ Z = (⋂ k, U (σ k)) ∩ Z)
    (tuples : List (Fin (p + 1) → I))
    (V₀ : I → Set X)
    (hV₀open : ∀ i, IsOpen (V₀ i))
    (hV₀sub : ∀ i, V₀ i ⊆ U i)
    (hV₀clos : ∀ i, closure (V₀ i) ∩ Z ⊆ U i) :
    let Vf := iterateShrink p W tuples V₀
    (∀ i, IsOpen (Vf i)) ∧
    (∀ i, Vf i ⊆ U i) ∧
    (∀ i, closure (Vf i) ∩ Z ⊆ U i) ∧
    (∀ i, Vf i ∩ Z = V₀ i ∩ Z) ∧
    (∀ σ ∈ tuples, (⋂ k, Vf (σ k)) ⊆ W σ) := by
  simp only [show iterateShrink p W tuples V₀ = tuples.foldl (fun V σ => shrinkOp p W σ V) V₀ from
      rfl]
  induction tuples generalizing V₀ with
  | nil =>
    simp only [List.foldl_nil, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
    exact ⟨hV₀open, hV₀sub, hV₀clos⟩
  | cons σ₀ tl ih =>
    simp only [List.foldl_cons]
    have hV_mid_open : ∀ i, IsOpen (shrinkOp p W σ₀ V₀ i) :=
      fun i => isOpen_shrinkOp p W hW σ₀ V₀ hV₀open i
    have hV_mid_sub : ∀ i, shrinkOp p W σ₀ V₀ i ⊆ U i := fun i =>
      (shrinkOp_subset p W σ₀ V₀ i).trans (hV₀sub i)
    have hV_mid_clos : ∀ i, closure (shrinkOp p W σ₀ V₀ i) ∩ Z ⊆ U i := fun i x hx =>
      hV₀clos i ⟨closure_mono (shrinkOp_subset p W σ₀ V₀ i) hx.1, hx.2⟩
    obtain ⟨hIH1, hIH2, hIH3, hIH4, hIH5⟩ :=
      ih (shrinkOp p W σ₀ V₀) hV_mid_open hV_mid_sub hV_mid_clos
    refine ⟨hIH1, hIH2, hIH3, ?_, ?_⟩
    · exact fun i => (hIH4 i).trans <| shrinkOp_inter_eq Z p I U V₀ hV₀sub hV₀clos W hWinter σ₀ i
    · intro σ hσ
      rw [List.mem_cons] at hσ
      cases hσ with
      | inl heq =>
        subst heq
        calc ⋂ k, List.foldl (fun V σ' => shrinkOp p W σ' V) (shrinkOp p W σ V₀) tl (σ k)
            ⊆ ⋂ k, shrinkOp p W σ V₀ (σ k) :=
              Set.iInter_mono (fun k => iterateShrink_subset p W tl (shrinkOp p W σ V₀) (σ k))
          _ ⊆ W σ := iInter_shrinkOp_subset p I V₀ W σ
      | inr hmem =>
        exact hIH5 σ hmem

/-- The initial family: pointwise shrinking at each point of `Z`, then a finite subcover.
It satisfies everything the tag asks for except the intersection condition. -/
private lemma exists_isOpen_cover_closure_inter_subset
    {X : Type*} [TopologicalSpace X]
    (Z : Set X) (hZ : IsCompact Z)
    (hSep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
      ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B)
    (I : Type*)
    (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (hCover : Z ⊆ ⋃ i, U i) :
    ∃ V₀ : I → Set X,
      (∀ i, IsOpen (V₀ i)) ∧ (Z ⊆ ⋃ i, V₀ i) ∧
      (∀ i, V₀ i ⊆ U i) ∧ (∀ i, closure (V₀ i) ∩ Z ⊆ U i) := by
  classical
  -- Choose an index and a shrunken neighbourhood at each point of `Z`.
  have hShrink : ∀ x ∈ Z, ∃ (i : I) (N : Set X),
      IsOpen N ∧ x ∈ N ∧ N ⊆ U i ∧ closure N ∩ Z ⊆ U i := by
    intro x hxZ
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hCover hxZ)
    exact ⟨i, exists_isOpen_closure_inter_subset Z hZ hSep (U i) (hU i) x hxZ hxi⟩
  choose idx N hNo hxN hNU hNcl using hShrink
  obtain ⟨t, ht⟩ := hZ.elim_nhds_subcover' N fun x hx => (hNo x hx).mem_nhds (hxN x hx)
  -- Group the chosen neighbourhoods by the index they were chosen for.
  refine ⟨fun i => ⋃ j ∈ t.filter (fun j : Z => idx j.1 j.2 = i), N j.1 j.2, ?_, ?_, ?_, ?_⟩
  · exact fun i => isOpen_biUnion fun j _ => hNo j.1 j.2
  · intro z hz
    obtain ⟨j, hjt, hzNj⟩ := Set.mem_iUnion₂.mp (ht hz)
    exact Set.mem_iUnion.mpr
      ⟨idx j.1 j.2, Set.mem_iUnion₂.mpr ⟨j, Finset.mem_filter.mpr ⟨hjt, rfl⟩, hzNj⟩⟩
  · intro i x hx
    obtain ⟨j, hjf, hxN⟩ := Set.mem_iUnion₂.mp hx
    rw [← (Finset.mem_filter.mp hjf).2]
    exact hNU j.1 j.2 hxN
  · intro i x ⟨hxcl, hxZ⟩
    rw [Finset.closure_biUnion (t.filter (fun j : Z => idx j.1 j.2 = i))
      (fun j => N j.1 j.2)] at hxcl
    obtain ⟨j, hjf, hxclj⟩ := Set.mem_iUnion₂.mp hxcl
    rw [← (Finset.mem_filter.mp hjf).2]
    exact hNcl j.1 j.2 ⟨hxclj, hxZ⟩

/-- The statement for a finite index type: build the initial family, then iterate the shrink
operation over the list of *all* `(p+1)`-tuples, which is finite. -/
private theorem exists_isOpen_refinement_of_finite
    {X : Type*} [TopologicalSpace X]
    (Z : Set X) (hZ : IsCompact Z)
    (hSep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
      ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B)
    (p : ℕ) (I : Type*) [Finite I]
    (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (W : (Fin (p + 1) → I) → Set X) (hW : ∀ σ, IsOpen (W σ))
    (hCover : Z ⊆ ⋃ i, U i)
    (hWinter : ∀ σ, W σ ∩ Z = (⋂ k, U (σ k)) ∩ Z) :
    ∃ V : I → Set X,
      (∀ i, IsOpen (V i)) ∧
      (Z ⊆ ⋃ i, V i) ∧
      (∀ i, V i ⊆ U i) ∧
      (∀ i, closure (V i) ∩ Z ⊆ U i) ∧
      (∀ σ : Fin (p + 1) → I, ⋂ k, V (σ k) ⊆ W σ) := by
  let : Fintype I := Fintype.ofFinite I
  obtain ⟨V₀, hV₀open, hV₀cover, hV₀sub, hV₀clos⟩ :=
    exists_isOpen_cover_closure_inter_subset Z hZ hSep I U hU hCover
  let tuples := (Finset.univ : Finset (Fin (p + 1) → I)).toList
  let Vf := iterateShrink p W tuples V₀
  obtain ⟨hVfopen, hVfsub, hVfclos, hVftrace, hVfinter⟩ :=
    iterateShrink_spec Z p I U W hW hWinter tuples V₀ hV₀open hV₀sub hV₀clos
  refine ⟨Vf, hVfopen, ?_, hVfsub, hVfclos, ?_⟩
  · -- The trace on `Z` is unchanged, and `V₀` covers `Z`.
    intro z hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hV₀cover hz)
    exact Set.mem_iUnion.mpr ⟨i, ((Set.ext_iff.mp (hVftrace i) z).mpr ⟨hi, hz⟩).1⟩
  · -- Every tuple occurs in `tuples`, which lists all of them.
    exact fun σ => hVfinter σ (Finset.mem_toList.mpr (Finset.mem_univ σ))

/-- **Stacks 0CY5.** Let `Z` be a quasi-compact subset of a topological space `X` whose
distinct points can be separated by disjoint opens of `X`, let `U : I → Set X` be an open
cover of `Z`, and for each `(p+1)`-tuple `σ` of indices let `W σ` be an open set contained in
`⋂ k, U (σ k)` and agreeing with it on `Z`. Then `Z` has an open cover `V : I → Set X` with
`V i ⊆ U i`, with `closure (V i) ∩ Z ⊆ U i`, and with `⋂ k, V (σ k) ⊆ W σ` for every `σ`.

The reduction to the finite case is by extracting a finite subcover of `Z` and extending the
resulting family by `∅` outside it. -/
@[stacks 0CY5]
theorem exists_isOpen_refinement_of_isCompact_of_pairwiseSeparated
    {X : Type*} [TopologicalSpace X]
    (Z : Set X) (hZ : IsCompact Z)
    (hSep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y →
      ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B)
    (p : ℕ) (I : Type*)
    (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (W : (Fin (p + 1) → I) → Set X) (hW : ∀ σ, IsOpen (W σ))
    (hCover : Z ⊆ ⋃ i, U i)
    (hWinter : ∀ σ, W σ ∩ Z = (⋂ k, U (σ k)) ∩ Z) :
    ∃ V : I → Set X,
      (∀ i, IsOpen (V i)) ∧
      (Z ⊆ ⋃ i, V i) ∧
      (∀ i, V i ⊆ U i) ∧
      (∀ i, closure (V i) ∩ Z ⊆ U i) ∧
      (∀ σ : Fin (p + 1) → I, ⋂ k, V (σ k) ⊆ W σ) := by
  classical
  obtain ⟨s, hs⟩ := hZ.elim_finite_subcover U hU hCover
  -- Restrict everything to the finite subcover, apply the finite case, then extend by `∅`.
  let J := {i // i ∈ s}
  let U_J : J → Set X := fun j => U j.val
  let W_J : (Fin (p + 1) → J) → Set X := fun τ => W (fun k => (τ k).val)
  have hCover_J : Z ⊆ ⋃ j : J, U_J j := by
    intro z hz
    obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp (hs hz)
    exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hzi⟩
  obtain ⟨V_J, hVJ_open, hVJ_cover, hVJ_sub, hVJ_clos, hVJ_inter⟩ :=
    exists_isOpen_refinement_of_finite Z hZ hSep p J U_J (fun j => hU j.val) W_J
      (fun τ => hW _) hCover_J fun τ => hWinter (fun k => (τ k).val)
  let V : I → Set X := fun i => if hi : i ∈ s then V_J ⟨i, hi⟩ else ∅
  have hV : ∀ i (hi : i ∈ s), V i = V_J ⟨i, hi⟩ := fun i hi => dite_eq_left hi
  refine ⟨V, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ s
    · exact hV i hi ▸ hVJ_open ⟨i, hi⟩
    · simp [V, hi]
  · intro z hz
    obtain ⟨⟨j, hj⟩, hjz⟩ := Set.mem_iUnion.mp (hVJ_cover hz)
    exact Set.mem_iUnion.mpr ⟨j, hV j hj ▸ hjz⟩
  · intro i x hx
    by_cases hi : i ∈ s
    · exact hVJ_sub ⟨i, hi⟩ (hV i hi ▸ hx)
    · simp [V, hi] at hx
  · intro i x ⟨hxcl, hxZ⟩
    by_cases hi : i ∈ s
    · rw [hV i hi] at hxcl
      exact hVJ_clos ⟨i, hi⟩ ⟨hxcl, hxZ⟩
    · simp [V, hi] at hxcl
  · intro σ
    by_cases hall : ∀ k, σ k ∈ s
    · -- All indices of `σ` survive the reduction.
      intro x hx
      exact hVJ_inter (fun k => ⟨σ k, hall k⟩) (Set.mem_iInter.mpr fun k =>
        hV _ (hall k) ▸ Set.mem_iInter.mp hx k)
    · -- Some index of `σ` was dropped, so the intersection is empty.
      obtain ⟨k, hk⟩ := not_forall.mp hall
      intro x hx
      simpa [V, hk] using Set.mem_iInter.mp hx k

end TopologicalSpace

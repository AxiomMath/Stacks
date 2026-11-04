module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

@[expose] public section

/-
# Problem: Shrinking an open covering (Stacks Project, Tag 09UX)

Let $X$ be a Hausdorff and locally quasi-compact topological space (in the
Stacks Project sense: every point has a quasi-compact neighborhood).  Let
$Z \subseteq X$ be a quasi-compact subset (necessarily closed in $X$ since
$X$ is Hausdorff).  Suppose given:
* an integer $p \ge 0$,
* a set $I$,
* for every $i \in I$, an open subset $U_i \subseteq X$,
* for every $(p+1)$-tuple $(i_0, \ldots, i_p) \in I^{p+1}$, an open subset
  $W_{i_0 \ldots i_p} \subseteq U_{i_0} \cap \cdots \cap U_{i_p}$,
such that
  (1) $Z \subseteq \bigcup_{i \in I} U_i$,
  (2) for every $(p+1)$-tuple, $W_{i_0 \ldots i_p} \cap Z = U_{i_0} \cap
      \cdots \cap U_{i_p} \cap Z$.
Then there exist open subsets $V_i \subseteq X$ such that
  (a) $Z \subseteq \bigcup_{i \in I} V_i$,
  (b) $\overline{V_i} \subseteq U_i$ for every $i$,
  (c) $V_{i_0} \cap \cdots \cap V_{i_p} \subseteq W_{i_0 \ldots i_p}$ for
      every $(p+1)$-tuple.
-/

-- Background and context (as comments)
--
-- The relevant notions used in the lemma correspond to the following
-- Mathlib classes / predicates:
--
-- * Hausdorff space: `T2Space`.
-- * Quasi-compact subset: `IsCompact` (Mathlib's `IsCompact` builds in no
--   separation axiom, matching the Stacks Project convention).
-- * Locally quasi-compact space (Stacks, Tag 005H): every point has a
--   quasi-compact neighborhood.  This is `WeaklyLocallyCompactSpace`.
--   (Mathlib's `LocallyCompactSpace` requires a basis of compact
--   neighborhoods, which is equivalent under Hausdorff.)
-- * Closure of a subset $A \subseteq X$: `closure A`.
--
-- A `(p+1)`-tuple of elements of $I$ is encoded as a function
-- `Fin (p+1) → I`.

open Set Topology

-- Main Definition(s)
--
-- The definitions involved (Hausdorff, quasi-compact, locally quasi-compact,
-- closure) are the standard Mathlib ones (`T2Space`, `IsCompact`,
-- `WeaklyLocallyCompactSpace`, `closure`).  No new definitions are needed.

-- Main Statement(s)

/-! ## Helper lemmas -/

/-- In a T2 + WeaklyLocallyCompact space (hence regular), for any open U and x ∈ U,
there exists an open V with x ∈ V, closure V compact, and closure V ⊆ U.

Proof strategy: Use `exists_compact_mem_nhds` to get a compact neighborhood K of x.
Then K° ∩ U is an open neighborhood of x. By regularity (`hasBasis_nhds_closure`),
find V open with x ∈ V and closure V ⊆ K° ∩ U. Since closure V ⊆ K and K is compact
in a T2 space, closure V is compact. -/
lemma exists_open_compact_closure_subset
    {X : Type*} [TopologicalSpace X] [T2Space X] [WeaklyLocallyCompactSpace X]
    {U : Set X} (hU : IsOpen U) {x : X} (hx : x ∈ U) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ IsCompact (closure V) ∧ closure V ⊆ U := by
  obtain ⟨V, hV_open, hxV, hcl_sub, hcl_compact⟩ :=
    exists_open_between_and_isCompact_closure isCompact_singleton hU (singleton_subset_iff.mpr hx)
  exact ⟨V, hV_open, hxV (mem_singleton x), hcl_compact, hcl_sub⟩

/-- Given a compact Z covered by open sets U_i in a T2 + WeaklyLocallyCompact space,
produce a finite collection of open sets (indexed by Fin n) with compact closures
contained in the respective U_i, that still covers Z.

Proof strategy: For each z ∈ Z, use `exists_open_compact_closure_subset` to get
V_z open with z ∈ V_z, closure V_z compact, closure V_z ⊆ U_{i(z)} for some i(z).
The {V_z}_{z∈Z} form an open cover of Z. By compactness (`IsCompact.elim_finite_subcover`),
extract a finite subcover indexed by some finite set, then re-index by Fin n. -/
lemma exists_finite_subcover_with_compact_closure
    {X : Type*} [TopologicalSpace X] [T2Space X] [WeaklyLocallyCompactSpace X]
    {Z : Set X} (hZ : IsCompact Z) {I : Type*}
    (U : I → Set X) (hU : ∀ i, IsOpen (U i)) (hcov : Z ⊆ ⋃ i, U i) :
    ∃ (n : ℕ) (idx : Fin n → I) (V0 : Fin n → Set X),
      (∀ j, IsOpen (V0 j)) ∧
      (∀ j, IsCompact (closure (V0 j))) ∧
      (∀ j, closure (V0 j) ⊆ U (idx j)) ∧
      (Z ⊆ ⋃ j, V0 j) := by
  -- For each `x ∈ Z`, pick `i` with `x ∈ U i`, then use `exists_open_compact_closure_subset`.
  have h_local : ∀ x ∈ Z, ∃ i : I, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      IsCompact (closure V) ∧ closure V ⊆ U i := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov hx)
    exact ⟨i, exists_open_compact_closure_subset (hU i) hi⟩
  choose ix Vx hVx_open hx_mem hVx_compact hVx_sub using h_local
  -- Compactness of `Z` gives a finite subcover, re-indexed by `Fin n` through `t.toList`.
  set S : Z → Set X := fun z => Vx z.1 z.2
  obtain ⟨t, ht⟩ := hZ.elim_finite_subcover S (fun z => hVx_open z.1 z.2)
    fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hx_mem x hx⟩
  set L := t.toList
  set n := L.length
  refine ⟨n, fun j => ix (L.get j).1 (L.get j).2, fun j => Vx (L.get j).1 (L.get j).2,
    fun j => hVx_open _ _, fun j => hVx_compact _ _, fun j => hVx_sub _ _, fun x hx => ?_⟩
  obtain ⟨z, hz_mem, hx_Sz⟩ := mem_iUnion₂.mp (ht hx)
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp (Finset.mem_toList.mpr hz_mem)
  exact mem_iUnion.mpr ⟨j, hj ▸ hx_Sz⟩

/-- For a single tuple τ : Fin (p+1) → Fin n, the compact set
(⋂ k, closure (V0 (τ k))) \ W (idx ∘ τ) is disjoint from Z.
We can find an open N containing Z such that (⋂ k, closure (V0 (τ k))) ∩ N ⊆ W (idx ∘ τ).

Proof strategy: Let C = (⋂ k, closure (V0 (τ k))) \ W (idx ∘ τ).
- C is compact: it's a closed subset (W is open) of the compact set ⋂ k, closure (V0 (τ k))
  (finite intersection of compact sets in T2).
- C ∩ Z = ∅: If x ∈ C ∩ Z, then x ∈ ⋂ k, closure (V0 (τ k)) ⊆ ⋂ k, U (idx (τ k))
  = ⋂ k, U ((idx ∘ τ) k), so x ∈ (⋂ k, U ((idx∘τ) k)) ∩ Z = W (idx∘τ) ∩ Z by `hint`.
  But x ∉ W (idx∘τ) by definition of C, contradiction.
- By `SeparatedNhds.of_isCompact_isCompact` (T2 separation of disjoint compact sets),
  there exist disjoint open sets M ⊇ C and N ⊇ Z.
- Then (⋂ k, closure (V0 (τ k))) ∩ N ⊆ W (idx ∘ τ): if x is in both, x ∉ M (disjoint from N),
  so x ∉ C, meaning x ∈ W (idx∘τ). -/
lemma separation_for_single_tuple
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {Z : Set X} (hZ : IsCompact Z)
    {p : ℕ} {I : Type*}
    (U : I → Set X)
    (W : (Fin (p + 1) → I) → Set X) (hW : ∀ σ, IsOpen (W σ))
    (hint : ∀ σ, W σ ∩ Z = (⋂ k, U (σ k)) ∩ Z)
    {n : ℕ} (idx : Fin n → I) (V0 : Fin n → Set X)
    (hV0_compact : ∀ j, IsCompact (closure (V0 j)))
    (hV0_sub : ∀ j, closure (V0 j) ⊆ U (idx j))
    (τ : Fin (p + 1) → Fin n) :
    ∃ (N : Set X), IsOpen N ∧ Z ⊆ N ∧
      (⋂ k, closure (V0 (τ k))) ∩ N ⊆ W (idx ∘ τ) := by
  set C := (⋂ k, closure (V0 (τ k))) \ W (idx ∘ τ)
  -- `C` is a closed subset of the compact `closure (V0 (τ 0))`, minus an open set.
  have hC_compact : IsCompact C :=
    ((hV0_compact (τ 0)).of_isClosed_subset (isClosed_iInter fun _ => isClosed_closure)
      (iInter_subset (fun k => closure (V0 (τ k))) 0)).diff (hW _)
  have hCZ : Disjoint C Z := Set.disjoint_left.mpr fun x hxC hxZ => by
    have hx : x ∈ (⋂ k, U ((idx ∘ τ) k)) ∩ Z :=
      ⟨mem_iInter.mpr fun k => hV0_sub (τ k) (mem_iInter.mp hxC.1 k), hxZ⟩
    rw [← hint (idx ∘ τ)] at hx
    exact hxC.2 hx.1
  -- Separate the disjoint compact sets `C` and `Z` (Hausdorff); the open set around `Z` works.
  obtain ⟨s, t, -, ht, hCs, hZt, hst⟩ := SeparatedNhds.of_isCompact_isCompact hC_compact hZ hCZ
  refine ⟨t, ht, hZt, fun x hx => ?_⟩
  by_contra hxW
  exact Set.disjoint_left.mp hst (hCs ⟨hx.1, hxW⟩) hx.2

/-- The refinement step: intersect each V0 j with finitely many open neighborhoods
of Z (one per tuple) to ensure the tuple intersection property.

This lemma is fully proved from `separation_for_single_tuple`:
- Define V1 j = V0 j ∩ ⋂ τ, N_τ where N_τ are from separation_for_single_tuple.
- Since Fin (p+1) → Fin n is finite, V1 j is a finite intersection of open sets, hence open.
- V1 j ⊆ V0 j trivially.
- Z ⊆ ⋃ j, V1 j because Z ⊆ each N_τ and Z ⊆ ⋃ j, V0 j.
- For the tuple property: if x ∈ ⋂ k, V1 (τ k), then x ∈ ⋂ k, V0 (τ k) ⊆ ⋂ k, closure(V0(τ k)),
  and x ∈ N_τ, so x ∈ W(idx∘τ) by the separation property. -/
lemma refine_for_tuple_constraints
    {X : Type*} [TopologicalSpace X] [T2Space X] [WeaklyLocallyCompactSpace X]
    {Z : Set X} (hZ : IsCompact Z)
    {p : ℕ} {I : Type*}
    (U : I → Set X)
    (W : (Fin (p + 1) → I) → Set X) (hW : ∀ σ, IsOpen (W σ))
    (hint : ∀ σ, W σ ∩ Z = (⋂ k, U (σ k)) ∩ Z)
    {n : ℕ} (idx : Fin n → I) (V0 : Fin n → Set X)
    (hV0_open : ∀ j, IsOpen (V0 j))
    (hV0_compact : ∀ j, IsCompact (closure (V0 j)))
    (hV0_sub : ∀ j, closure (V0 j) ⊆ U (idx j))
    (hV0_cov : Z ⊆ ⋃ j, V0 j) :
    ∃ (V1 : Fin n → Set X),
      (∀ j, IsOpen (V1 j)) ∧
      (∀ j, V1 j ⊆ V0 j) ∧
      (Z ⊆ ⋃ j, V1 j) ∧
      (∀ (τ : Fin (p + 1) → Fin n),
        (⋂ k, V1 (τ k)) ⊆ W (idx ∘ τ)) := by
  choose N hN_open hN_Z hN_sub using fun τ =>
    separation_for_single_tuple hZ U W hW hint idx V0 hV0_compact hV0_sub τ
  -- `V1 j = V0 j ∩ ⋂ τ, N τ`: a finite intersection, since `Fin (p + 1) → Fin n` is finite.
  refine ⟨fun j => V0 j ∩ ⋂ (τ : Fin (p + 1) → Fin n), N τ,
    fun j => (hV0_open j).inter (isOpen_iInter_of_finite hN_open),
    fun j => inter_subset_left, fun x hx => ?_, fun τ x hx => ?_⟩
  · obtain ⟨j, hj⟩ := mem_iUnion.mp (hV0_cov hx)
    exact mem_iUnion.mpr ⟨j, hj, mem_iInter.mpr fun τ => hN_Z τ hx⟩
  · have hx_mem : ∀ k, x ∈ V0 (τ k) ∩ ⋂ (τ' : Fin (p + 1) → Fin n), N τ' :=
      fun k => mem_iInter.mp hx k
    exact hN_sub τ ⟨mem_iInter.mpr fun k => subset_closure (hx_mem k).1,
      mem_iInter.mp (hx_mem 0).2 τ⟩

/-- Assembly step: define V_i = ⋃ {V1 j | idx j = i} and verify all conditions.

Proof strategy:
- V i = ⋃ (j : Fin n) (h : idx j = i), V1 j. This is a finite union of open sets, hence open.
- Z ⊆ ⋃ i, V i: For x ∈ Z, get j with x ∈ V1 j from hV1_cov. Then x ∈ V (idx j).
- closure (V i) ⊆ U i: Since V i = ⋃ (j with idx j = i) V1 j is a finite union,
  closure (V i) = ⋃ (j with idx j = i) closure (V1 j). Each closure (V1 j) ⊆ closure (V0 j) ⊆ U
  (idx j) = U i.
- ⋂ k, V (σ k) ⊆ W σ: If x ∈ ⋂ k, V (σ k), then for each k there exists j_k with
  idx j_k = σ k and x ∈ V1 j_k. Set τ = (j_0, ..., j_p). Then x ∈ ⋂ k, V1 (τ k)
  and idx ∘ τ = σ, so x ∈ W (idx ∘ τ) = W σ by hV1_tuple. -/
lemma assemble_covering
    {X : Type*} [TopologicalSpace X]
    {Z : Set X} {I : Type*} {n : ℕ}
    (U : I → Set X) (idx : Fin n → I) (V1 : Fin n → Set X) (V0 : Fin n → Set X)
    (hV1_open : ∀ j, IsOpen (V1 j))
    (hV1_sub_V0 : ∀ j, V1 j ⊆ V0 j)
    (hV0_sub : ∀ j, closure (V0 j) ⊆ U (idx j))
    (hV1_cov : Z ⊆ ⋃ j, V1 j)
    {p : ℕ} (W : (Fin (p + 1) → I) → Set X)
    (hV1_tuple : ∀ (τ : Fin (p + 1) → Fin n), (⋂ k, V1 (τ k)) ⊆ W (idx ∘ τ)) :
    ∃ V : I → Set X,
      (∀ i, IsOpen (V i)) ∧
      Z ⊆ ⋃ i, V i ∧
      (∀ i, closure (V i) ⊆ U i) ∧
      (∀ σ : Fin (p + 1) → I, (⋂ k, V (σ k)) ⊆ W σ) := by
  refine ⟨fun i => ⋃ (j : Fin n) (_ : idx j = i), V1 j,
    fun i => isOpen_iUnion fun j => isOpen_iUnion fun _ => hV1_open j, fun x hx => ?_,
    fun i => ?_, fun σ x hx => ?_⟩
  · obtain ⟨j, hj⟩ := mem_iUnion.mp (hV1_cov hx)
    exact mem_iUnion.mpr ⟨idx j, mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨rfl, hj⟩⟩⟩
  · calc closure (⋃ (j : Fin n) (_ : idx j = i), V1 j)
        ⊆ closure (⋃ (j : Fin n) (_ : idx j = i), V0 j) :=
          closure_mono (iUnion₂_mono fun j _ => hV1_sub_V0 j)
      _ = ⋃ (j : Fin n), closure (⋃ (_ : idx j = i), V0 j) := closure_iUnion_of_finite _
      _ ⊆ U i := iUnion_subset fun j => by
          by_cases h : idx j = i
          · simpa [h] using hV0_sub j
          · simp [h]
  · -- For each `k`, `x ∈ V1 (τ k)` for some `τ k` with `idx (τ k) = σ k`.
    simp only [mem_iInter, mem_iUnion] at hx
    choose τ hτ_eq hτ_mem using hx
    have h_comp : idx ∘ τ = σ := funext hτ_eq
    rw [← h_comp]
    exact hV1_tuple τ (mem_iInter.mpr hτ_mem)

/--
Stacks Project, Tag 09UX (Shrinking an open covering).

Let `X` be a Hausdorff and locally quasi-compact (in the Stacks Project sense,
i.e. weakly locally compact) topological space.  Let `Z ⊆ X` be a compact
subset.  Given an open cover `U : I → Set X` of `Z`, and for each
`(p+1)`-tuple `σ : Fin (p+1) → I` an open subset
`W σ ⊆ ⋂ k, U (σ k)` satisfying
`W σ ∩ Z = (⋂ k, U (σ k)) ∩ Z`, there exist open subsets `V : I → Set X`
with `Z ⊆ ⋃ i, V i`, `closure (V i) ⊆ U i` for every `i`, and
`⋂ k, V (σ k) ⊆ W σ` for every `(p+1)`-tuple `σ`.
-/
@[stacks 09UX]
theorem shrinking_open_covering
    {X : Type*} [TopologicalSpace X] [T2Space X] [WeaklyLocallyCompactSpace X]
    {Z : Set X} (hZ : IsCompact Z)
    {p : ℕ} {I : Type*}
    (U : I → Set X) (hU : ∀ i, IsOpen (U i))
    (W : (Fin (p + 1) → I) → Set X) (hW : ∀ σ, IsOpen (W σ))
    (hcov : Z ⊆ ⋃ i, U i)
    (hint : ∀ σ, W σ ∩ Z = (⋂ k, U (σ k)) ∩ Z) :
    ∃ V : I → Set X,
      (∀ i, IsOpen (V i)) ∧
      Z ⊆ ⋃ i, V i ∧
      (∀ i, closure (V i) ⊆ U i) ∧
      (∀ σ : Fin (p + 1) → I, ⋂ k, V (σ k) ⊆ W σ) := by
  -- Step 1: Get finite subcover with compact closures
  obtain ⟨n, idx, V0, hV0_open, hV0_compact, hV0_sub, hV0_cov⟩ :=
    exists_finite_subcover_with_compact_closure hZ U hU hcov
  -- Step 2: Refine for tuple constraints
  obtain ⟨V1, hV1_open, hV1_sub, hV1_cov, hV1_tuple⟩ :=
    refine_for_tuple_constraints hZ U W hW hint idx V0
      hV0_open hV0_compact hV0_sub hV0_cov
  -- Step 3: Assemble V : I → Set X from V1 : Fin n → Set X
  exact assemble_covering U idx V1 V0 hV1_open hV1_sub hV0_sub hV1_cov W hV1_tuple


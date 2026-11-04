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
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.ShrinkingLemma
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Refining an open cover of a compact Hausdorff space

Let `(U i)` be an open cover of a compact Hausdorff space `X` and let `(W i k)` be, for each
`(p + 1)`-tuple `i` of indices, an open cover of `⋂ a, U (i a)`. Then there is an open cover
`(V j)` of `X` together with a map `α` of index sets such that `closure (V j) ⊆ U (α j)` and
every `(p + 1)`-fold intersection `⋂ a, V (j a)` is either empty or contained in a single
`W (α ∘ j) k`.

## Main definitions

* `J_idx`: the index type of the refined cover.
* `vTerm`: the open set intersected in for one `(p + 1)`-tuple of indices.
* `vSet`: the members of the refined cover.
* `α_map`: the map from the refined index type to the original one.

## Main results

* `exists_cover_closure_subset_and_refines`: such a refinement exists.
-/

@[expose] public section

open Set Topology

/-- Given an open cover `(U i)_{i : I}` of a compact Hausdorff space `X`, there is an open
cover `(V i)_{i : I}` indexed by the same set `I` with `closure (V i) ⊆ U i` for all `i`. -/
lemma relatively_compact_refinement_helper
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    {I : Type*} (U : I → Set X) (hUopen : ∀ i, IsOpen (U i))
    (hUcov : ⋃ i, U i = Set.univ) :
    ∃ V : I → Set X, (∀ i, IsOpen (V i)) ∧ (⋃ i, V i = Set.univ) ∧
      (∀ i, closure (V i) ⊆ U i) := by
  classical
  obtain ⟨J, hJ⟩ : ∃ J : Finset I, (Set.univ : Set X) ⊆ ⋃ i ∈ J, U i :=
    isCompact_univ.elim_finite_subcover U hUopen hUcov.ge
  set U' : I → Set X := fun i => if i ∈ J then U i else ∅
  have hU'_subset (i) : U' i ⊆ U i := by by_cases h : i ∈ J <;> simp [U', h]
  have hU'_open (i) : IsOpen (U' i) := by by_cases h : i ∈ J <;> simp [U', h, hUopen i]
  have hU'_cov : ⋃ i, U' i = Set.univ := by
    refine eq_univ_of_univ_subset fun x hx => ?_
    obtain ⟨i, hiJ, hxU⟩ := mem_iUnion₂.mp (hJ hx)
    exact mem_iUnion.mpr ⟨i, by simp [U', hiJ, hxU]⟩
  have hU'_pointFinite (x : X) : {i | x ∈ U' i}.Finite :=
    (J : Set I).toFinite.subset fun i hi => by
      by_contra hiJ
      simp [U', Finset.mem_coe.not.mp hiJ] at hi
  obtain ⟨V, hVcov, hVopen, hVcl⟩ :=
    exists_iUnion_eq_closure_subset hU'_open hU'_pointFinite hU'_cov
  exact ⟨V, hVopen, hVcov, fun i => (hVcl i).trans (hU'_subset i)⟩

/-- Compactness gives a finite enumeration `f : Fin n → I` of an open subcover,
with `n ≥ 1` when `X` is nonempty. -/
lemma fin_enum_cover_exists
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    {I : Type*} (U : I → Set X) (hUopen : ∀ i, IsOpen (U i))
    (hUcov : ⋃ i, U i = Set.univ) :
    ∃ (n : ℕ) (f : Fin n → I), 1 ≤ n ∧ ⋃ k, U (f k) = Set.univ := by
  obtain ⟨S, hS⟩ : ∃ S : Finset I, (Set.univ : Set X) ⊆ ⋃ i ∈ S, U i :=
    isCompact_univ.elim_finite_subcover U hUopen hUcov.ge
  have hSne : S.Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty X›
    obtain ⟨i, hiS, _⟩ := mem_iUnion₂.mp (hS (mem_univ x))
    exact ⟨i, hiS⟩
  let e : Fin S.card ≃ S := S.equivFin.symm
  refine ⟨S.card, fun k => (e k).val, hSne.card_pos, eq_univ_of_forall fun x => ?_⟩
  obtain ⟨i, hiS, hxU⟩ := mem_iUnion₂.mp (hS (mem_univ x))
  refine mem_iUnion.mpr ⟨e.symm ⟨i, hiS⟩, ?_⟩
  simpa [e] using hxU

/-- For each `(p + 1)`-tuple `t` of indices in the finite enumeration, the closed set
`⋂ a, closure (A (t a))` is covered by finitely many of the sets `W (f ∘ t) k`, enumerated by
`Fin m`. When `K (f ∘ t)` is empty the covering forces `⋂ a, closure (A (t a)) = ∅` and
`m = 0`. -/
lemma tuple_enum_subcover_exists
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {I : Type*} (U : I → Set X)
    (p n : ℕ) (f : Fin n → I)
    (A : Fin n → Set X)
    (hAcl : ∀ i, closure (A i) ⊆ U (f i))
    {K : (Fin (p + 1) → I) → Type*}
    (W : ∀ (i : Fin (p + 1) → I), K i → Set X)
    (hWopen : ∀ i k, IsOpen (W i k))
    (hWcov : ∀ i, (⋂ a, U (i a)) = ⋃ k, W i k)
    (t : Fin (p + 1) → Fin n) :
    ∃ (m : ℕ) (enum : Fin m → K (f ∘ t)),
      ∀ x, (∀ a, x ∈ closure (A (t a))) → ∃ k : Fin m, x ∈ W (f ∘ t) (enum k) := by
  classical
  set Y : Set X := ⋂ a, closure (A (t a)) with hYdef
  have hYcomp : IsCompact Y :=
    (isClosed_iInter fun _ => isClosed_closure).isCompact
  have hYcov : Y ⊆ ⋃ k, W (f ∘ t) k := fun x hx => by
    rw [← hWcov]
    exact mem_iInter.mpr fun a => hAcl (t a) (mem_iInter.mp hx a)
  obtain ⟨S, hS⟩ := hYcomp.elim_finite_subcover (fun k : K (f ∘ t) => W (f ∘ t) k)
    (fun k => hWopen _ k) hYcov
  refine ⟨S.card, fun i => (S.equivFin.symm i).1, fun x hx => ?_⟩
  obtain ⟨k, hkS, hxw⟩ := mem_iUnion₂.mp (hS (hYdef ▸ mem_iInter.mpr hx))
  exact ⟨S.equivFin ⟨k, hkS⟩, by simpa using hxw⟩

/-- The constructed index type for Stacks 09UW. A pair `⟨i0, s⟩` where
`i0 : Fin n` is the outer label and `s` assigns to each `(p+1)`-tuple `t`
starting at `i0` a choice in `Fin (max (m t) 1)`. The use of `max (m t) 1`
ensures `J` is inhabited whenever `n ≥ 1`, even when some `m t = 0`. -/
def J_idx (n p : ℕ) (m : (Fin (p + 1) → Fin n) → ℕ) : Type :=
  Σ i0 : Fin n, ∀ t : {t : Fin (p + 1) → Fin n // t 0 = i0}, Fin (max (m t.1) 1)

/-- Auxiliary: cast `k : Fin (max (m t) 1)` to `Fin (m t)`, given `0 < m t`.
This is a non-dependent helper so that uses of `vTerm` reduce cleanly. -/
def finMaxCast {n : ℕ} (h : 0 < n) (k : Fin (max n 1)) : Fin n :=
  ⟨k.1, by have hcast : k.1 < max n 1 := k.2; omega⟩

/-- Non-dependent term used in the definition of `vSet`. For a tuple `t` with
`m t ≥ 1`, it returns `(⋂_a closure (A (t a)))ᶜ ∪ W (...)`. For `m t = 0`, it
returns `Set.univ`. -/
def vTerm {X : Type*} [TopologicalSpace X] {I : Type*}
    (p n : ℕ) (f : Fin n → I) (A : Fin n → Set X)
    {K : (Fin (p + 1) → I) → Type*}
    (W : ∀ (i : Fin (p + 1) → I), K i → Set X)
    (m : (Fin (p + 1) → Fin n) → ℕ)
    (enum : ∀ t : Fin (p + 1) → Fin n, Fin (m t) → K (f ∘ t))
    (t : Fin (p + 1) → Fin n) (k : Fin (max (m t) 1)) : Set X :=
  if h : 0 < m t then
    (⋂ a, closure (A (t a)))ᶜ ∪ W (f ∘ t) (enum t (finMaxCast h k))
  else Set.univ

/-- On a tuple `t` with `0 < m t`, the set `vTerm t k` is the union of the complement of
`⋂ a, closure (A (t a))` with the `k`-th prescribed open `W (f ∘ t) (enum t k)`. -/
lemma vTerm_of_pos {X : Type*} [TopologicalSpace X] {I : Type*}
    (p n : ℕ) (f : Fin n → I) (A : Fin n → Set X)
    {K : (Fin (p + 1) → I) → Type*}
    (W : ∀ (i : Fin (p + 1) → I), K i → Set X)
    (m : (Fin (p + 1) → Fin n) → ℕ)
    (enum : ∀ t : Fin (p + 1) → Fin n, Fin (m t) → K (f ∘ t))
    (t : Fin (p + 1) → Fin n) (k : Fin (max (m t) 1)) (h : 0 < m t) :
    vTerm p n f A W m enum t k =
      (⋂ a, closure (A (t a)))ᶜ ∪ W (f ∘ t) (enum t (finMaxCast h k)) :=
  dite_eq_left h

/-- On a tuple `t` with `m t = 0`, the set `vTerm t k` is all of `X`. -/
lemma vTerm_of_nonpos {X : Type*} [TopologicalSpace X] {I : Type*}
    (p n : ℕ) (f : Fin n → I) (A : Fin n → Set X)
    {K : (Fin (p + 1) → I) → Type*}
    (W : ∀ (i : Fin (p + 1) → I), K i → Set X)
    (m : (Fin (p + 1) → Fin n) → ℕ)
    (enum : ∀ t : Fin (p + 1) → Fin n, Fin (m t) → K (f ∘ t))
    (t : Fin (p + 1) → Fin n) (k : Fin (max (m t) 1)) (h : ¬ 0 < m t) :
    vTerm p n f A W m enum t k = Set.univ :=
  dite_eq_right h

/-- The constructed open set for `j = ⟨i0, s⟩`. For each `(p+1)`-tuple `t`
starting at `i0`, the term `vTerm t (s t)` is intersected in. -/
def vSet {X : Type*} [TopologicalSpace X] {I : Type*}
    (p n : ℕ) (f : Fin n → I) (A : Fin n → Set X)
    {K : (Fin (p + 1) → I) → Type*}
    (W : ∀ (i : Fin (p + 1) → I), K i → Set X)
    (m : (Fin (p + 1) → Fin n) → ℕ)
    (enum : ∀ t : Fin (p + 1) → Fin n, Fin (m t) → K (f ∘ t))
    (j : J_idx n p m) : Set X :=
  A j.1 ∩ ⋂ t : {t : Fin (p + 1) → Fin n // t 0 = j.1},
    vTerm p n f A W m enum t.1 (j.2 t)

/-- The constructed map `J → I` sending `⟨i0, s⟩` to `f i0`. -/
def α_map {I : Type*} (p n : ℕ) (f : Fin n → I)
    (m : (Fin (p + 1) → Fin n) → ℕ)
    (j : J_idx n p m) : I := f j.1

/-- Each `vTerm t k` is open. -/
lemma vTerm_isOpen
    {X : Type*} [TopologicalSpace X] {I : Type*}
    (p n : ℕ) (f : Fin n → I) (A : Fin n → Set X)
    {K : (Fin (p + 1) → I) → Type*}
    (W : ∀ (i : Fin (p + 1) → I), K i → Set X)
    (hWopen : ∀ i k, IsOpen (W i k))
    (m : (Fin (p + 1) → Fin n) → ℕ)
    (enum : ∀ t : Fin (p + 1) → Fin n, Fin (m t) → K (f ∘ t))
    (t : Fin (p + 1) → Fin n) (k : Fin (max (m t) 1)) :
    IsOpen (vTerm p n f A W m enum t k) := by
  by_cases h : 0 < m t
  · rw [vTerm_of_pos p n f A W m enum t k h]
    exact (isClosed_iInter fun _ => isClosed_closure).isOpen_compl.union (hWopen _ _)
  · rw [vTerm_of_nonpos p n f A W m enum t k h]
    exact isOpen_univ

/-- Each `V j` is open. -/
lemma vSet_isOpen
    {X : Type*} [TopologicalSpace X] {I : Type*}
    (p n : ℕ) (f : Fin n → I) (A : Fin n → Set X)
    (hAopen : ∀ i, IsOpen (A i))
    {K : (Fin (p + 1) → I) → Type*}
    (W : ∀ (i : Fin (p + 1) → I), K i → Set X)
    (hWopen : ∀ i k, IsOpen (W i k))
    (m : (Fin (p + 1) → Fin n) → ℕ)
    (enum : ∀ t : Fin (p + 1) → Fin n, Fin (m t) → K (f ∘ t)) :
    ∀ j : J_idx n p m, IsOpen (vSet p n f A W m enum j) := fun j =>
  (hAopen j.1).inter <| isOpen_iInter_of_finite fun t =>
    vTerm_isOpen p n f A W hWopen m enum t.1 (j.2 t)

/-- The open sets `V j` cover the whole space (when `X` is nonempty so that
`n ≥ 1` and `A` is a shrinking of an open cover). -/
lemma vSet_covers
    {X : Type*} [TopologicalSpace X] {I : Type*}
    (p n : ℕ) (f : Fin n → I) (A : Fin n → Set X)
    (hAcov : ⋃ i, A i = Set.univ)
    {K : (Fin (p + 1) → I) → Type*}
    (W : ∀ (i : Fin (p + 1) → I), K i → Set X)
    (m : (Fin (p + 1) → Fin n) → ℕ)
    (enum : ∀ t : Fin (p + 1) → Fin n, Fin (m t) → K (f ∘ t))
    (henum : ∀ t x, (∀ a, x ∈ closure (A (t a))) →
                    ∃ k : Fin (m t), x ∈ W (f ∘ t) (enum t k)) :
    ⋃ j : J_idx n p m, vSet p n f A W m enum j = Set.univ := by
  classical
  refine eq_univ_of_forall fun x => ?_
  obtain ⟨i0, hxi0⟩ : ∃ i, x ∈ A i := mem_iUnion.mp (hAcov ▸ mem_univ x)
  -- Build `s`: for each starting tuple `t`, pick a witness in `Fin (max (m t) 1)`.
  let s : ∀ t : {t : Fin (p + 1) → Fin n // t 0 = i0}, Fin (max (m t.1) 1) := fun t => by
    by_cases h : 0 < m t.1
    · -- `m t ≥ 1`. Distinguish whether `x ∈ ⋂_a closure (A (t a))`.
      by_cases hx : ∀ a, x ∈ closure (A (t.1 a))
      · -- Use the henum witness.
        refine ⟨(henum t.1 x hx).choose.1, ?_⟩
        have := (henum t.1 x hx).choose.2
        omega
      · exact ⟨0, by omega⟩
    · -- `m t = 0`. `max 0 1 = 1`; pick the unique element.
      exact ⟨0, by omega⟩
  refine mem_iUnion.mpr ⟨⟨i0, s⟩, hxi0, mem_iInter.mpr fun t => ?_⟩
  by_cases h : 0 < m t.1
  · have hVeq : vTerm p n f A W m enum t.1 (s t) =
        (⋂ a, closure (A (t.1 a)))ᶜ ∪
          W (f ∘ t.1) (enum t.1 (finMaxCast h (s t))) :=
      vTerm_of_pos p n f A W m enum t.1 (s t) h
    rw [hVeq]
    by_cases hx : ∀ a, x ∈ closure (A (t.1 a))
    · -- Use the henum witness.
      have hxw : x ∈ W (f ∘ t.1) (enum t.1 (henum t.1 x hx).choose) :=
        (henum t.1 x hx).choose_spec
      have hsval : (s t).1 = (henum t.1 x hx).choose.1 := by
        show (s t).val = _
        simp only [s]
        rw [dite_eq_left h, dite_eq_left hx]
      have heq : finMaxCast h (s t) = (henum t.1 x hx).choose := Fin.ext hsval
      have hxInW : x ∈ W (f ∘ t.1) (enum t.1 (finMaxCast h (s t))) := by
        rw [heq]; exact hxw
      exact Set.mem_union_right _ hxInW
    · have hxIn : x ∈ (⋂ a, closure (A (t.1 a)))ᶜ := by
        rw [mem_compl_iff, mem_iInter]
        exact hx
      exact Set.mem_union_left _ hxIn
  · -- vTerm reduces to univ in this branch.
    have hVeq : vTerm p n f A W m enum t.1 (s t) = Set.univ :=
      vTerm_of_nonpos p n f A W m enum t.1 (s t) h
    exact hVeq ▸ mem_univ x

/-- For each `j`, `closure (V j) ⊆ U (α j)`. -/
lemma vSet_closure
    {X : Type*} [TopologicalSpace X] {I : Type*}
    (p n : ℕ) (f : Fin n → I) (A : Fin n → Set X)
    (U : I → Set X) (hAcl : ∀ i, closure (A i) ⊆ U (f i))
    {K : (Fin (p + 1) → I) → Type*}
    (W : ∀ (i : Fin (p + 1) → I), K i → Set X)
    (m : (Fin (p + 1) → Fin n) → ℕ)
    (enum : ∀ t : Fin (p + 1) → Fin n, Fin (m t) → K (f ∘ t)) :
    ∀ j : J_idx n p m,
      closure (vSet p n f A W m enum j) ⊆ U (α_map p n f m j) := fun j =>
  (closure_mono Set.inter_subset_left).trans (hAcl j.1)

/-- For any `(p + 1)`-tuple `j : Fin (p + 1) → J_idx n p m`, either `⋂ a, vSet (j a)` is
empty or it is contained in `W (α ∘ j) k` for some `k`. -/
lemma vSet_intersection
    {X : Type*} [TopologicalSpace X] {I : Type*}
    (p n : ℕ) (f : Fin n → I) (A : Fin n → Set X)
    {K : (Fin (p + 1) → I) → Type*}
    (W : ∀ (i : Fin (p + 1) → I), K i → Set X)
    (m : (Fin (p + 1) → Fin n) → ℕ)
    (enum : ∀ t : Fin (p + 1) → Fin n, Fin (m t) → K (f ∘ t))
    (henum : ∀ t x, (∀ a, x ∈ closure (A (t a))) →
                    ∃ k : Fin (m t), x ∈ W (f ∘ t) (enum t k)) :
    ∀ (j : Fin (p + 1) → J_idx n p m),
      (⋂ a, vSet p n f A W m enum (j a)) = ∅ ∨
        ∃ k : K (fun a => α_map p n f m (j a)),
          (⋂ a, vSet p n f A W m enum (j a)) ⊆
            W (fun a => α_map p n f m (j a)) k := by
  intro j
  set t : Fin (p + 1) → Fin n := fun a => (j a).1 with ht_def
  let τ : {u : Fin (p + 1) → Fin n // u 0 = (j 0).1} := ⟨t, rfl⟩
  have hxcl {x} (hx : x ∈ ⋂ a, vSet p n f A W m enum (j a)) (a) : x ∈ closure (A (t a)) :=
    subset_closure (mem_iInter.mp hx a).1
  by_cases hmt : 0 < m t
  · -- Standard case: `m t ≥ 1`, extract the witness from `(j 0).2 τ`.
    right
    refine ⟨enum t (finMaxCast hmt ((j 0).2 τ)), fun x hx => ?_⟩
    have hxV0_τ : x ∈ vTerm p n f A W m enum t ((j 0).2 τ) :=
      mem_iInter.mp (mem_iInter.mp hx 0).2 τ
    rw [vTerm_of_pos p n f A W m enum t ((j 0).2 τ) hmt] at hxV0_τ
    exact hxV0_τ.resolve_left fun h => h (mem_iInter.mpr (hxcl hx))
  · -- Degenerate case: `m t = 0`. Apply `henum t x` to any `x` in `⋂_a V (j a)`
    -- to get a witness in `Fin 0`, contradicting that `Fin 0` is empty.
    left
    refine eq_empty_of_forall_notMem fun x hx => ?_
    obtain ⟨k, _⟩ := henum t x (hxcl hx)
    have : k.1 < m t := k.2
    omega

/-- **Stacks 09UW**.
Let `(U i)` be an open cover of a compact Hausdorff space `X` and let `(W i k)` be, for each
`(p + 1)`-tuple `i` of indices, an open cover of `⋂ a, U (i a)`. Then `X` has an open cover
`(V j)` together with a map `α` of index sets such that `closure (V j) ⊆ U (α j)` and, for
every `(p + 1)`-tuple `j`, the intersection `⋂ a, V (j a)` is either empty or contained in
some `W (α ∘ j) k`.

The final clause is a disjunction because `K (α ∘ j)` may be empty; in that case
`⋂ a, U (α (j a))` is empty by hypothesis, so no `k` exists, and `⋂ a, V (j a)` is empty
too. -/
@[stacks 09UW]
theorem exists_cover_closure_subset_and_refines
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    {I : Type*}
    (U : I → Set X)
    (hUopen : ∀ i, IsOpen (U i))
    (hUcov : ⋃ i, U i = Set.univ)
    (p : ℕ)
    {K : (Fin (p + 1) → I) → Type*}
    (W : ∀ (i : Fin (p + 1) → I), K i → Set X)
    (hWopen : ∀ i k, IsOpen (W i k))
    (hWcov : ∀ i, (⋂ a, U (i a)) = ⋃ k, W i k) :
    ∃ (J : Type) (V : J → Set X) (α : J → I),
      (∀ j, IsOpen (V j)) ∧
      (⋃ j, V j = Set.univ) ∧
      (∀ j, closure (V j) ⊆ U (α j)) ∧
      (∀ (j : Fin (p + 1) → J),
        (⋂ a, V (j a)) = ∅ ∨
          ∃ k : K (fun a => α (j a)), (⋂ a, V (j a)) ⊆ W (fun a => α (j a)) k) := by
  classical
  by_cases hX : Nonempty X
  · -- Nonempty case. `I` is nonempty by `hUcov`; build via finite enumeration.
    obtain ⟨n, f, _hn, hUcov_f⟩ := fin_enum_cover_exists U hUopen hUcov
    obtain ⟨A, hAopen, hAcov, hAcl⟩ :=
      relatively_compact_refinement_helper (U ∘ f)
        (fun i => hUopen (f i)) hUcov_f
    choose m enum henum using fun t : Fin (p + 1) → Fin n =>
      tuple_enum_subcover_exists U p n f A hAcl W hWopen hWcov t
    refine ⟨J_idx n p m, vSet p n f A W m enum,
      α_map p n f m,
      vSet_isOpen p n f A hAopen W hWopen m enum,
      vSet_covers p n f A hAcov W m enum henum,
      vSet_closure p n f A U hAcl W m enum,
      vSet_intersection p n f A W m enum henum⟩
  · -- Empty case. `X` is empty, so take `J := Empty` with everything trivial.
    rw [not_nonempty_iff] at hX
    refine ⟨Empty, Empty.elim, Empty.elim, ?_, ?_, ?_, ?_⟩
    · exact fun j => j.elim
    · exact eq_univ_of_forall isEmptyElim
    · exact fun j => j.elim
    · intro j; exact (j 0).elim


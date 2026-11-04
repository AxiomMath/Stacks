module

public import StacksFrontier.Topology.Dimension.Catenary
public import Mathlib.Order.CompletePartialOrder
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Catenary spaces and additivity of codimension

For irreducible closed subsets `Y ⊆ Y'` of a topological space `X`, the codimension of `Y` in
`Y'` is the supremum of the lengths of chains `Y = Y₀ ⊊ Y₁ ⊊ ⋯ ⊊ Y_e = Y'` of irreducible closed
subsets, and `X` is catenary when every such codimension is finite and computed by every maximal
chain. This file proves that `X` is catenary exactly when all these codimensions are finite and
codimension is additive along triples `Y ⊆ Y' ⊆ Y''`.

The notions themselves — `IrreducibleClosedsCodim.topCodim`,
`IrreducibleClosedsCodim.IsMaximalChain` and `IrreducibleClosedsCodim.IsCatenarySpace` — live in
`StacksFrontier.Topology.Dimension.Catenary`, the definition tag they formalize.

## Main results

* `isCatenarySpace_iff_codim_additive`: a space is catenary iff codimension is everywhere finite
  and additive on triples.
* `topCodim_eq_one_of_covby`: covering pairs have codimension `1`.
* `exists_maximalChain_length_eq_topCodim`: a finite codimension is realized by a maximal chain.
-/

@[expose] public section

open TopologicalSpace

open IrreducibleClosedsCodim

/-! ### Chains realizing the codimension -/

/-- If `Y ≤ Y'`, there exists a chain from `Y` to `Y'`. -/
lemma exists_chain_of_le {X : Type*} [TopologicalSpace X]
    (Y Y' : IrreducibleCloseds X) (hYY' : Y ≤ Y') :
    ∃ p : LTSeries (IrreducibleCloseds X), p.head = Y ∧ p.last = Y' := by
  rcases eq_or_lt_of_le hYY' with h | h
  · refine ⟨RelSeries.singleton _ Y, ?_, ?_⟩
    · exact RelSeries.head_singleton _
    · rw [RelSeries.last_singleton]; exact h
  · refine ⟨(RelSeries.singleton _ Y).snoc Y' (by simpa using h), ?_, ?_⟩
    · simp
    · simp

/-- A supremum in `ℕ∞` over a nonempty index type is attained whenever it is not `⊤`. -/
lemma ENat.iSup_attained_of_ne_top {α : Type*} [Nonempty α] (f : α → ℕ∞)
    (h : ⨆ a, f a ≠ ⊤) : ∃ a, f a = ⨆ a, f a := by
  by_contra h_attain
  push Not at h_attain
  set s := ⨆ a, f a with hs_def
  have h_le : ∀ a, f a ≤ s := fun a => le_iSup f a
  have h_lt : ∀ a, f a < s := fun a => lt_of_le_of_ne (h_le a) (h_attain a)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, s = (n : ℕ∞) :=
    ⟨_, ((ENat.ne_top_iff_exists).mp h).choose_spec.symm⟩
  have h_succ : ∀ a, f a + 1 ≤ (n : ℕ∞) := fun a =>
    Order.add_one_le_of_lt (hn ▸ h_lt a)
  have h_sup_le : ⨆ a, (f a + 1) ≤ (n : ℕ∞) := iSup_le h_succ
  have h_sup_eq : ⨆ a, (f a + 1) = s + 1 := by
    rw [← ENat.iSup_add]
  rw [h_sup_eq, hn] at h_sup_le
  exact absurd h_sup_le (by exact_mod_cast (Nat.lt_succ_self n).not_ge)

/-- If `topCodim Y Y' ≠ ⊤` and `Y ≤ Y'`, the supremum defining `topCodim` is
attained. -/
lemma exists_chain_length_eq_topCodim {X : Type*} [TopologicalSpace X]
    (Y Y' : IrreducibleCloseds X) (hYY' : Y ≤ Y')
    (h : topCodim Y Y' ≠ ⊤) :
    ∃ p : LTSeries (IrreducibleCloseds X), p.head = Y ∧ p.last = Y' ∧
      (p.length : ℕ∞) = topCodim Y Y' := by
  obtain ⟨p₀, hh₀, hl₀⟩ := exists_chain_of_le Y Y' hYY'
  have : Nonempty
      { p : LTSeries (IrreducibleCloseds X) // p.head = Y ∧ p.last = Y' } :=
    ⟨⟨p₀, hh₀, hl₀⟩⟩
  obtain ⟨⟨q, hqh, hql⟩, hq⟩ :=
    ENat.iSup_attained_of_ne_top
      (fun p : { p : LTSeries (IrreducibleCloseds X) // p.head = Y ∧ p.last = Y' } =>
        (p.1.length : ℕ∞)) h
  exact ⟨q, hqh, hql, hq⟩

/-- Given a chain from `Y` to `Y'` and an intermediate element strictly between
two consecutive entries, we can insert it to produce a strictly longer chain
with the same endpoints. -/
lemma exists_longer_chain_of_btw {X : Type*} [TopologicalSpace X]
    (Y Y' : IrreducibleCloseds X) (p : LTSeries (IrreducibleCloseds X))
    (hp1 : p.head = Y) (hp2 : p.last = Y')
    (i : Fin p.length) (Z : IrreducibleCloseds X)
    (hZ1 : p i.castSucc < Z) (hZ2 : Z < p i.succ) :
    ∃ q : LTSeries (IrreducibleCloseds X),
      q.head = Y ∧ q.last = Y' ∧ q.length = p.length + 1 := by
  refine ⟨p.insertNth i Z hZ1 hZ2, ?_, ?_, ?_⟩
  · show (p.insertNth i Z hZ1 hZ2).head = Y
    rw [show (p.insertNth i Z hZ1 hZ2).head = p.head from rfl, hp1]
  · rw [LTSeries.last_insertNth p i Z hZ1 hZ2, hp2]
  · rfl

/-- A chain of length equal to `topCodim Y Y'` (when finite) is a maximal
chain. -/
lemma isMaximalChain_of_length_eq_topCodim {X : Type*} [TopologicalSpace X]
    (Y Y' : IrreducibleCloseds X) (p : LTSeries (IrreducibleCloseds X))
    (hp1 : p.head = Y) (hp2 : p.last = Y')
    (hlen : (p.length : ℕ∞) = topCodim Y Y') :
    IsMaximalChain p Y Y' := by
  refine ⟨hp1, hp2, ?_⟩
  intro i
  by_contra hncov
  have hlt : p i.castSucc < p i.succ := p.step i
  have hbtw : ∃ Z, p i.castSucc < Z ∧ Z < p i.succ := by
    unfold CovBy at hncov
    push Not at hncov
    exact hncov hlt
  obtain ⟨Z, hZ1, hZ2⟩ := hbtw
  obtain ⟨q, hq1, hq2, hqlen⟩ :=
    exists_longer_chain_of_btw Y Y' p hp1 hp2 i Z hZ1 hZ2
  have hbound : (q.length : ℕ∞) ≤ topCodim Y Y' :=
    length_le_topCodim Y Y' q hq1 hq2
  rw [hqlen, ← hlen] at hbound
  -- ((p.length + 1 : ℕ) : ℕ∞) ≤ (p.length : ℕ∞)
  -- but p.length is finite (it's a ℕ), so p.length + 1 ≤ p.length is impossible.
  have : (p.length + 1 : ℕ) ≤ p.length := by exact_mod_cast hbound
  omega

/-- There exists a maximal chain of length equal to `topCodim Y Y'`. -/
lemma exists_maximalChain_length_eq_topCodim {X : Type*} [TopologicalSpace X]
    (Y Y' : IrreducibleCloseds X) (hYY' : Y ≤ Y') (h : topCodim Y Y' ≠ ⊤) :
    ∃ p : LTSeries (IrreducibleCloseds X),
      IsMaximalChain p Y Y' ∧ (p.length : ℕ∞) = topCodim Y Y' := by
  obtain ⟨p, hp1, hp2, hlen⟩ := exists_chain_length_eq_topCodim Y Y' hYY' h
  exact ⟨p, isMaximalChain_of_length_eq_topCodim Y Y' p hp1 hp2 hlen, hlen⟩

/-- Concatenating a maximal chain from `Y` to `Y'` with a maximal chain from `Y'` to `Y''` gives
a maximal chain from `Y` to `Y''`, whose length is the sum of the two lengths. -/
lemma isMaximalChain_smash {X : Type*} [TopologicalSpace X]
    (Y Y' Y'' : IrreducibleCloseds X)
    (p₁ p₂ : LTSeries (IrreducibleCloseds X))
    (h₁ : IsMaximalChain p₁ Y Y') (h₂ : IsMaximalChain p₂ Y' Y'') :
    ∃ p : LTSeries (IrreducibleCloseds X),
      IsMaximalChain p Y Y'' ∧ p.length = p₁.length + p₂.length := by
  obtain ⟨hh1, hl1, hcov1⟩ := h₁
  obtain ⟨hh2, hl2, hcov2⟩ := h₂
  have hconnect : p₁.last = p₂.head := hl1.trans hh2.symm
  refine ⟨p₁.smash p₂ hconnect, ?_, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [RelSeries.head_smash]; exact hh1
  · rw [RelSeries.last_smash]; exact hl2
  · intro i
    -- index i : Fin (p₁.length + p₂.length); split via Fin.addCases
    refine Fin.addCases (motive := fun i => (p₁.smash p₂ hconnect) i.castSucc ⋖
        (p₁.smash p₂ hconnect) i.succ) ?_ ?_ i
    · intro j
      have := hcov1 j
      rw [RelSeries.smash_castAdd, RelSeries.smash_succ_castAdd]
      exact this
    · intro j
      have := hcov2 j
      rw [RelSeries.smash_natAdd, RelSeries.smash_succ_natAdd]
      exact this

/-- In a catenary space, `topCodim Y Y'` is finite for all irreducible closed `Y ≤ Y'`. -/
lemma topCodim_ne_top_of_catenary {X : Type*} [TopologicalSpace X]
    (hX : IsCatenarySpace X) (Y Y' : IrreducibleCloseds X) (hYY' : Y ≤ Y') :
    topCodim Y Y' ≠ ⊤ :=
  (hX Y Y' hYY').1

/-- In a catenary space, codimension is additive along a triple `Y ≤ Y' ≤ Y''` of irreducible
closed subsets. -/
@[ega "0 14.3.2" "Direction (a) ⇒ (b)"]
lemma topCodim_additive_of_catenary {X : Type*} [TopologicalSpace X]
    (hX : IsCatenarySpace X) (Y Y' Y'' : IrreducibleCloseds X)
    (h1 : Y ≤ Y') (h2 : Y' ≤ Y'') :
    topCodim Y Y'' = topCodim Y Y' + topCodim Y' Y'' := by
  have hYY'' : Y ≤ Y'' := h1.trans h2
  have hf1 : topCodim Y Y' ≠ ⊤ := (hX Y Y' h1).1
  have hf2 : topCodim Y' Y'' ≠ ⊤ := (hX Y' Y'' h2).1
  obtain ⟨p₁, hmax1, hlen1⟩ :=
    exists_maximalChain_length_eq_topCodim Y Y' h1 hf1
  obtain ⟨p₂, hmax2, hlen2⟩ :=
    exists_maximalChain_length_eq_topCodim Y' Y'' h2 hf2
  obtain ⟨p, hmaxp, hlenp⟩ :=
    isMaximalChain_smash Y Y' Y'' p₁ p₂ hmax1 hmax2
  have hp : (p.length : ℕ∞) = topCodim Y Y'' :=
    (hX Y Y'' hYY'').2 p hmaxp
  rw [hlenp] at hp
  push_cast at hp
  rw [← hlen1, ← hlen2]
  exact hp.symm

/-! ### Codimension from finiteness and additivity -/

/-- An `LTSeries` whose head equals its last has length zero. -/
lemma ltseries_length_eq_zero_of_head_eq_last {α : Type*} [Preorder α]
    (p : LTSeries α) (h : p.head = p.last) : p.length = 0 := by
  by_contra hne
  have hpos : 0 < p.length := Nat.pos_of_ne_zero hne
  have hlt : (⟨0, Nat.zero_lt_succ _⟩ : Fin (p.length + 1)) <
      ⟨p.length, Nat.lt_succ_self _⟩ := hpos
  have hmono := p.strictMono hlt
  have h1 : p ⟨0, Nat.zero_lt_succ _⟩ = p.head := rfl
  have h2 : p ⟨p.length, Nat.lt_succ_self _⟩ = p.last := rfl
  rw [h1, h2] at hmono
  exact absurd h hmono.ne

/-- If every chain from `Y` to `Y'` has length at most `n`, then `topCodim Y Y' ≤ n`. -/
private lemma topCodim_le_of_forall_length_le {X : Type*} [TopologicalSpace X]
    (Y Y' : IrreducibleCloseds X) (n : ℕ)
    (h : ∀ p : LTSeries (IrreducibleCloseds X), p.head = Y → p.last = Y' → p.length ≤ n) :
    topCodim Y Y' ≤ n :=
  iSup_le fun ⟨p, hhead, hlast⟩ => by exact_mod_cast h p hhead hlast

/-- Codimension of an irreducible closed subset within itself is `0`. -/
lemma topCodim_self_eq_zero {X : Type*} [TopologicalSpace X]
    (Y : IrreducibleCloseds X) : topCodim Y Y = 0 :=
  le_antisymm
    (topCodim_le_of_forall_length_le Y Y 0 fun p hhead hlast =>
      (ltseries_length_eq_zero_of_head_eq_last p (hhead.trans hlast.symm)).le)
    bot_le

/-- Lower bound: if `Y < Z`, then `1 ≤ topCodim Y Z`. -/
lemma one_le_topCodim_of_lt {X : Type*} [TopologicalSpace X]
    (Y Z : IrreducibleCloseds X) (h : Y < Z) :
    (1 : ℕ∞) ≤ topCodim Y Z := by
  let p : LTSeries (IrreducibleCloseds X) :=
    { length := 1
      toFun := fun i => if i = 0 then Y else Z
      step := by
        intro i
        match i with
        | ⟨0, _⟩ => simpa using h }
  have hhead : p.head = Y := rfl
  have hlast : p.last = Z := rfl
  have hlen : p.length = 1 := rfl
  have hbound : (p.length : ℕ∞) ≤ topCodim Y Z :=
    length_le_topCodim Y Z p hhead hlast
  simpa [hlen] using hbound

/-- Upper bound: if `Y ⋖ Z`, any chain from `Y` to `Z` has length at most 1. -/
lemma length_le_one_of_covby_chain {X : Type*} [TopologicalSpace X]
    (Y Z : IrreducibleCloseds X) (h : Y ⋖ Z)
    (p : LTSeries (IrreducibleCloseds X))
    (hhead : p.head = Y) (hlast : p.last = Z) :
    p.length ≤ 1 := by
  by_contra hcontra
  push Not at hcontra
  -- The entry at index `1` lies strictly between `Y` and `Z`, contradicting `Y ⋖ Z`.
  have h₁ : p.head < p.toFun ⟨1, by omega⟩ := p.strictMono (by simp [Fin.lt_def])
  have h₂ : p.toFun ⟨1, by omega⟩ < p.last := p.strictMono (by simpa [Fin.lt_def] using hcontra)
  exact h.2 (hhead ▸ h₁) (hlast ▸ h₂)

/-- Upper bound: if `Y ⋖ Z`, then `topCodim Y Z ≤ 1`. -/
lemma topCodim_le_one_of_covby {X : Type*} [TopologicalSpace X]
    (Y Z : IrreducibleCloseds X) (h : Y ⋖ Z) :
    topCodim Y Z ≤ 1 :=
  topCodim_le_of_forall_length_le Y Z 1 (length_le_one_of_covby_chain Y Z h)

/-- If `Y ⋖ Z` then `topCodim Y Z = 1`. -/
lemma topCodim_eq_one_of_covby {X : Type*} [TopologicalSpace X]
    (Y Z : IrreducibleCloseds X) (h : Y ⋖ Z) :
    topCodim Y Z = 1 :=
  le_antisymm (topCodim_le_one_of_covby Y Z h) (one_le_topCodim_of_lt Y Z h.1)

/-- If `IsMaximalChain p Y Y'` and `p.length = 0`, then `Y = Y'`. -/
lemma eq_of_isMaximalChain_length_zero {X : Type*} [TopologicalSpace X]
    (Y Y' : IrreducibleCloseds X) (p : LTSeries (IrreducibleCloseds X))
    (hmax : IsMaximalChain p Y Y') (hlen : p.length = 0) : Y = Y' := by
  obtain ⟨hh, hl, _⟩ := hmax
  rw [← hh, ← hl]
  unfold RelSeries.head RelSeries.last
  congr 1
  ext
  simp [hlen]

/-- Index-shift: a covering relation in the tail comes from a covering relation
in the original chain. -/
lemma covby_tail_of_covby {α : Type*} [Preorder α]
    (p : LTSeries α) (hne : p.length ≠ 0)
    (hcov : ∀ i : Fin p.length, p.toFun i.castSucc ⋖ p.toFun i.succ)
    (i : Fin (p.tail hne).length) :
    (p.tail hne).toFun i.castSucc ⋖ (p.tail hne).toFun i.succ := by
  -- (p.tail hne).length = p.length - 1, so i.1 < p.length - 1, hence i.1 + 1 < p.length, and the
  -- two entries of the tail at `i` are the entries of `p` at the shifted index.
  have hil : i.1 < p.length - 1 := by simpa only [RelSeries.tail_length] using i.2
  exact hcov ⟨i.1 + 1, by omega⟩

/-- A maximal chain of positive length decomposes as `Y ⋖ Z` plus a maximal
chain from `Z` to `Y'`. -/
lemma isMaximalChain_tail {X : Type*} [TopologicalSpace X]
    (Y Y' : IrreducibleCloseds X) (p : LTSeries (IrreducibleCloseds X))
    (hmax : IsMaximalChain p Y Y') (m : ℕ) (hlen : p.length = m + 1) :
    ∃ (Z : IrreducibleCloseds X) (q : LTSeries (IrreducibleCloseds X)),
      Y ⋖ Z ∧ IsMaximalChain q Z Y' ∧ q.length = m := by
  obtain ⟨hhead, hlast, hcov⟩ := hmax
  have hne : p.length ≠ 0 := by omega
  refine ⟨(p.tail hne).head, p.tail hne, ?_, ⟨rfl, ?_, ?_⟩, ?_⟩
  · rw [RelSeries.head_tail]
    -- (p.tail hne).head = p 1; we need Y ⋖ p 1
    have hi := hcov ⟨0, by omega⟩
    have h0 : p.toFun (Fin.castSucc (⟨0, by omega⟩ : Fin p.length)) = Y := by
      rw [← hhead]; rfl
    have h1eq : p.toFun (Fin.succ (⟨0, by omega⟩ : Fin p.length))
              = p.toFun (1 : Fin (p.length + 1)) := by
      congr 1
      apply Fin.ext
      rw [Fin.val_succ, Fin.val_mk, zero_add, Fin.val_one']
      exact (Nat.mod_eq_of_lt (by omega)).symm
    rw [h0] at hi
    rw [h1eq] at hi
    exact hi
  · rw [RelSeries.last_tail]; exact hlast
  · intro i
    exact covby_tail_of_covby p hne hcov i
  · rw [RelSeries.tail_length]
    omega

/-- ENat arithmetic: if `x ≠ ⊤` and `(k+1 : ℕ∞) = 1 + x` then `x = k`. -/
lemma enat_one_add_eq_succ_cancel (x : ℕ∞) (k : ℕ) (hne : x ≠ ⊤)
    (h : ((k + 1 : ℕ) : ℕ∞) = 1 + x) : x = (k : ℕ∞) := by
  obtain ⟨n, rfl⟩ := WithTop.ne_top_iff_exists.mp hne
  have h2 : ((k + 1 : ℕ) : ℕ∞) = ((1 + n : ℕ) : ℕ∞) := by
    rw [h]; push_cast; rfl
  have h3 : k + 1 = 1 + n := by exact_mod_cast h2
  have hnk : n = k := by omega
  rw [hnk]
  rfl

/-- If codimension is finite and additive, then every maximal chain from `Y` to `Y'` has length
at least `topCodim Y Y'`. -/
lemma length_ge_of_isMaximalChain {X : Type*} [TopologicalSpace X]
    (hAdd : ∀ Y Y' Y'' : IrreducibleCloseds X, Y ≤ Y' → Y' ≤ Y'' →
        topCodim Y Y'' = topCodim Y Y' + topCodim Y' Y'')
    (hFin : ∀ Y Y' : IrreducibleCloseds X, Y ≤ Y' → topCodim Y Y' ≠ ⊤)
    (n : ℕ) :
    ∀ (Y Y' : IrreducibleCloseds X) (p : LTSeries (IrreducibleCloseds X)),
      Y ≤ Y' → topCodim Y Y' = (n : ℕ∞) → IsMaximalChain p Y Y' →
        (n : ℕ∞) ≤ (p.length : ℕ∞) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Y Y' p _ hcod hmax
    rcases n with _ | k
    · exact_mod_cast Nat.zero_le _
    · -- Show p.length ≥ 1
      have hpos : p.length ≠ 0 := by
        intro h0
        have hYY : Y = Y' := eq_of_isMaximalChain_length_zero Y Y' p hmax h0
        subst hYY
        rw [topCodim_self_eq_zero] at hcod
        norm_cast at hcod
      obtain ⟨m, hm⟩ : ∃ m, p.length = m + 1 := ⟨p.length - 1, by omega⟩
      obtain ⟨Z, q, hYZ, hmaxq, hqlen⟩ := isMaximalChain_tail Y Y' p hmax m hm
      have hYZcod : topCodim Y Z = 1 := topCodim_eq_one_of_covby Y Z hYZ
      have hZY' : Z ≤ Y' := by
        obtain ⟨hqhead, hqlast, -⟩ := hmaxq
        exact hqhead ▸ hqlast ▸ q.head_le_last
      have hYZle : Y ≤ Z := le_of_lt hYZ.1
      have hadd : topCodim Y Y' = topCodim Y Z + topCodim Z Y' :=
        hAdd Y Z Y' hYZle hZY'
      rw [hYZcod, hcod] at hadd
      have hne : topCodim Z Y' ≠ ⊤ := hFin Z Y' hZY'
      have hZcod : topCodim Z Y' = (k : ℕ∞) :=
        enat_one_add_eq_succ_cancel (topCodim Z Y') k hne hadd
      have hk_lt : k < k + 1 := Nat.lt_succ_self k
      have hq_ge := ih k hk_lt Z Y' q hZY' hZcod hmaxq
      rw [hqlen] at hq_ge
      rw [hm]
      have h2 : (k : ℕ∞) + 1 ≤ (m : ℕ∞) + 1 := by
        have := add_le_add_right hq_ge (1 : ℕ∞)
        simpa [add_comm] using this
      push_cast
      exact h2

/-- If codimension is finite and additive, then every maximal chain from `Y` to `Y'` has length
exactly `topCodim Y Y'`. -/
@[ega "0 14.3.2" "Direction (b) ⇒ (a)"]
lemma length_eq_topCodim_of_isMaximalChain
    {X : Type*} [TopologicalSpace X]
    (hFin : ∀ Y Y' : IrreducibleCloseds X, Y ≤ Y' → topCodim Y Y' ≠ ⊤)
    (hAdd : ∀ Y Y' Y'' : IrreducibleCloseds X, Y ≤ Y' → Y' ≤ Y'' →
        topCodim Y Y'' = topCodim Y Y' + topCodim Y' Y'')
    (Y Y' : IrreducibleCloseds X) (hYY' : Y ≤ Y')
    (p : LTSeries (IrreducibleCloseds X)) (hmax : IsMaximalChain p Y Y') :
    (p.length : ℕ∞) = topCodim Y Y' := by
  have hup : (p.length : ℕ∞) ≤ topCodim Y Y' := by
    obtain ⟨hhead, hlast, -⟩ := hmax
    exact length_le_topCodim Y Y' p hhead hlast
  have hne : topCodim Y Y' ≠ ⊤ := hFin Y Y' hYY'
  obtain ⟨n, hn⟩ : ∃ n : ℕ, topCodim Y Y' = (n : ℕ∞) := by
    cases hcase : topCodim Y Y' with
    | top => exact (hne hcase).elim
    | coe m => exact ⟨m, by simp⟩
  have hlow : (n : ℕ∞) ≤ (p.length : ℕ∞) :=
    length_ge_of_isMaximalChain hAdd hFin n Y Y' p hYY' hn hmax
  rw [hn] at hup ⊢
  exact le_antisymm hup hlow

/-! ### Main theorem -/

/-- **Stacks 02I6**.
A topological space `X` is catenary iff for every pair of irreducible closed subsets `Y ⊆ Y'`
the codimension is finite, and for every triple `Y ⊆ Y' ⊆ Y''` of irreducible closed subsets we
have the additivity formula `topCodim Y Y'' = topCodim Y Y' + topCodim Y' Y''`. -/
@[stacks 02I6, ega "0 14.3.2"]
theorem isCatenarySpace_iff_codim_additive (X : Type*) [TopologicalSpace X] :
    IsCatenarySpace X ↔
      (∀ Y Y' : IrreducibleCloseds X, Y ≤ Y' → topCodim Y Y' ≠ ⊤) ∧
      (∀ Y Y' Y'' : IrreducibleCloseds X, Y ≤ Y' → Y' ≤ Y'' →
        topCodim Y Y'' = topCodim Y Y' + topCodim Y' Y'') := by
  refine ⟨fun hX => ⟨topCodim_ne_top_of_catenary hX, topCodim_additive_of_catenary hX⟩, ?_⟩
  rintro ⟨hFin, hAdd⟩ Y Y' hYY'
  exact ⟨hFin Y Y' hYY',
    fun p hmax => length_eq_topCodim_of_isMaximalChain hFin hAdd Y Y' hYY' p hmax⟩

module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.Order.RelSeries
public import Mathlib.Topology.Sets.Closeds
public import StacksCore.Tactic.StacksAttribute

/-!
# Catenary topological spaces

A topological space `X` is *catenary* if for every pair of irreducible closed subsets `T ⊆ T'`
the codimension `codim(T, T')` is finite and every maximal chain of irreducible closed subsets
from `T` to `T'` has length equal to that codimension.

Chains are `LTSeries` in the lattice `TopologicalSpace.IrreducibleCloseds X`, `topCodim` is a
supremum in `ℕ∞`, and non-refinability of a chain is the covering relation `⋖`.
`LTSeries.length` counts *steps*, so a chain with `e` steps has `e + 1` members and
`codim(T, T') = e` for a maximal one.

## Main definitions

* `IrreducibleClosedsCodim.topCodim`: the codimension of one irreducible closed subset in
  another, valued in `ℕ∞`.
* `IrreducibleClosedsCodim.IsMaximalChain`: a chain from `Y` to `Y'` all of whose consecutive
  pairs are covering pairs, so that it admits no refinement.
* `IrreducibleClosedsCodim.IsCatenarySpace`: the space is catenary.
* `TopologicalSpace.IsIrreducibleChain` and `TopologicalSpace.IsIrreducibleChain.IsMaximal`: the
  *unbundled* encoding of a chain, as a `List (Set X)` of irreducible closed sets strictly
  increasing under `⊂` with prescribed first and last elements.

## Main results

* `IrreducibleClosedsCodim.topCodim_eq_iSup_head_last`: `topCodim` written as an iterated
  conditional supremum instead of a supremum over a subtype.
* `IrreducibleClosedsCodim.isCatenarySpace_iff_isIrreducibleChain`: `IsCatenarySpace` agrees with
  the unbundled formulation over `List (Set X)` chains, where `n + 1` list members correspond
  to `n` steps of an `LTSeries`.
-/

@[expose] public section

/-- Splicing an element into an `LTSeries` leaves its first term unchanged. -/
lemma LTSeries.head_insertNth {α : Type*} [Preorder α] (p : LTSeries α) (i : Fin p.length)
    (a : α) (h₁ : p i.castSucc < a) (h₂ : a < p i.succ) :
    (p.insertNth i a h₁ h₂).head = p.head := by
  dsimp only [RelSeries.head, RelSeries.insertNth]
  rw [Fin.insertNth_apply_below (by simp [Fin.lt_def])]
  simp

/-- Splicing an element into an `LTSeries` leaves its last term unchanged. -/
lemma LTSeries.last_insertNth {α : Type*} [Preorder α] (p : LTSeries α) (i : Fin p.length)
    (a : α) (h₁ : p i.castSucc < a) (h₂ : a < p i.succ) :
    (p.insertNth i a h₁ h₂).last = p.last := by
  dsimp only [RelSeries.last, RelSeries.insertNth]
  rw [Fin.insertNth_apply_above (by simp [Fin.lt_def])]
  simp [Fin.last]

namespace TopologicalSpace

/-- A chain of irreducible closed subsets from `T` to `T'`: a strictly increasing
list `c` (under `⊂`) of irreducible closed sets with first element `T` and last
element `T'`. -/
@[ega "0 14.1.1"]
def IsIrreducibleChain {X : Type*} [TopologicalSpace X] (T T' : Set X)
    (c : List (Set X)) : Prop :=
  c.IsChain (· ⊂ ·) ∧ (∀ S ∈ c, IsIrreducible S ∧ IsClosed S) ∧
    c.head? = some T ∧ c.getLast? = some T'

/-- A chain is *maximal* when it cannot be refined: no irreducible closed set lies strictly
between two consecutive members. -/
def IsIrreducibleChain.IsMaximal {X : Type*} [TopologicalSpace X]
    (c : List (Set X)) : Prop :=
  c.IsChain (fun A B => ¬ ∃ S : Set X, IsIrreducible S ∧ IsClosed S ∧ A ⊂ S ∧ S ⊂ B)

end TopologicalSpace

open TopologicalSpace

namespace IrreducibleClosedsCodim

variable {X : Type*} [TopologicalSpace X]

/-- The codimension of an irreducible closed subset `Y` inside an irreducible
closed subset `Y'`, defined as the supremum (in `ℕ∞`) of the lengths of chains
`Y = Y₀ ⊊ Y₁ ⊊ ⋯ ⊊ Y_e = Y'` of irreducible closed subsets. -/
@[ega "0 14.2.1" "special case"]
noncomputable def topCodim (Y Y' : IrreducibleCloseds X) : ℕ∞ :=
  ⨆ p : { p : LTSeries (IrreducibleCloseds X) // p.head = Y ∧ p.last = Y' },
    (p.1.length : ℕ∞)

/-- An `LTSeries` of irreducible closed subsets is a *maximal chain* from `Y`
to `Y'` if it starts at `Y`, ends at `Y'`, and every consecutive pair is a
covering pair (so the chain cannot be refined by inserting an additional
irreducible closed subset). -/
@[ega "0 14.3.1"]
def IsMaximalChain (p : LTSeries (IrreducibleCloseds X))
    (Y Y' : IrreducibleCloseds X) : Prop :=
  p.head = Y ∧ p.last = Y' ∧ ∀ i : Fin p.length, p i.castSucc ⋖ p i.succ

/-- A topological space `X` is *catenary* if for every pair of irreducible closed subsets
`Y ⊆ Y'`, the codimension `topCodim Y Y'` is finite and every *maximal* chain of irreducible
closed subsets from `Y` to `Y'` has length equal to it. -/
@[stacks 02I1]
def IsCatenarySpace (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ Y Y' : IrreducibleCloseds X, Y ≤ Y' →
    topCodim Y Y' ≠ ⊤ ∧
    ∀ p : LTSeries (IrreducibleCloseds X),
      IsMaximalChain p Y Y' → (p.length : ℕ∞) = topCodim Y Y'

/-! ### The supremum defining `topCodim` -/

/-- `topCodim` as an iterated conditional supremum over all chains, rather than a supremum over
the subtype of chains with prescribed endpoints. -/
theorem topCodim_eq_iSup_head_last (Y Y' : IrreducibleCloseds X) :
    topCodim Y Y' =
      ⨆ (p : LTSeries (IrreducibleCloseds X)) (_ : p.head = Y) (_ : p.last = Y'),
        (p.length : ℕ∞) := by
  rw [topCodim, iSup_subtype]
  exact iSup_congr fun p => by rw [iSup_and]

/-- Any chain from `Y` to `Y'` has length at most `topCodim Y Y'`. -/
theorem length_le_topCodim (Y Y' : IrreducibleCloseds X)
    (p : LTSeries (IrreducibleCloseds X)) (hp1 : p.head = Y) (hp2 : p.last = Y') :
    (p.length : ℕ∞) ≤ topCodim Y Y' :=
  le_iSup
    (f := fun q : { q : LTSeries (IrreducibleCloseds X) //
                      q.head = Y ∧ q.last = Y' } => (q.1.length : ℕ∞))
    ⟨p, hp1, hp2⟩

/-- `topCodim Y Y'` is bounded by `n` exactly when every chain from `Y` to `Y'` is. -/
theorem topCodim_le_iff {Y Y' : IrreducibleCloseds X} {n : ℕ∞} :
    topCodim Y Y' ≤ n ↔ ∀ p : LTSeries (IrreducibleCloseds X),
      p.head = Y → p.last = Y' → (p.length : ℕ∞) ≤ n := by
  rw [topCodim_eq_iSup_head_last]
  simp [iSup_le_iff]

/-- If `e` reflects and preserves `≤`, and every irreducible closed subset below `e Y'` is in the
image of `e`, then `topCodim (e Y) (e Y') = topCodim Y Y'`. -/
theorem topCodim_eq_of_le_iff {X' : Type*} [TopologicalSpace X']
    (e : IrreducibleCloseds X → IrreducibleCloseds X')
    (hle : ∀ a b : IrreducibleCloseds X, e a ≤ e b ↔ a ≤ b)
    (Y Y' : IrreducibleCloseds X)
    (hsurj : ∀ Z : IrreducibleCloseds X', Z ≤ e Y' → ∃ W, e W = Z) :
    topCodim (e Y) (e Y') = topCodim Y Y' := by
  have hinj : Function.Injective e := fun a b hab =>
    le_antisymm ((hle a b).mp hab.le) ((hle b a).mp hab.ge)
  have he : StrictMono e := fun a b hab =>
    lt_of_le_of_ne ((hle a b).mpr hab.le) fun h => hab.ne (hinj h)
  have hlt : ∀ a b : IrreducibleCloseds X, e a < e b → a < b := fun a b hab =>
    lt_of_le_of_ne ((hle a b).mp hab.le) fun h => hab.ne (by rw [h])
  refine le_antisymm (topCodim_le_iff.mpr fun q hqh hql => ?_)
    (topCodim_le_iff.mpr fun p hph hpl => ?_)
  · have hmem : ∀ i, ∃ W, e W = q i := fun i =>
      hsurj (q i) (hql ▸ q.monotone (Fin.le_last i))
    choose W hW using hmem
    have hWmono : StrictMono W := fun i j hij =>
      hlt _ _ (by rw [hW i, hW j]; exact q.strictMono hij)
    have hq'h : (LTSeries.mk q.length W hWmono).head = Y :=
      hinj ((hW 0).trans hqh)
    have hq'l : (LTSeries.mk q.length W hWmono).last = Y' :=
      hinj ((hW _).trans hql)
    simpa using length_le_topCodim Y Y' _ hq'h hq'l
  · simpa using length_le_topCodim (e Y) (e Y') (p.map e he) (by simp [hph]) (by simp [hpl])

/-- Maximality of a chain, spelled out as "no irreducible closed subset fits strictly between
two consecutive members" instead of by the covering relation. -/
theorem isMaximalChain_iff_forall_not_btwn (p : LTSeries (IrreducibleCloseds X))
    (Y Y' : IrreducibleCloseds X) :
    IsMaximalChain p Y Y' ↔ p.head = Y ∧ p.last = Y' ∧
      ∀ i : Fin p.length, ¬ ∃ Z : IrreducibleCloseds X, p i.castSucc < Z ∧ Z < p i.succ := by
  refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun i => ?_
  exact ⟨fun hcov ⟨Z, h1, h2⟩ => hcov.2 h1 h2, fun h => ⟨p.step i, fun Z h1 h2 => h ⟨Z, h1, h2⟩⟩⟩

/-! ### From list chains to bundled chains

The two encodings of a chain of irreducible closed subsets are matched up here. A list chain with
`c.length` members corresponds to an `LTSeries` of length `c.length - 1`, since `LTSeries.length`
counts steps rather than members. -/

variable {T T' : Set X} {c : List (Set X)}

/-- A chain of irreducible closed subsets from `T` to `T'` is nonempty. -/
theorem ne_nil_of_isIrreducibleChain (h : IsIrreducibleChain T T' c) : c ≠ [] := by
  rintro rfl
  simpa using h.2.2.1

/-- A chain of irreducible closed subsets from `T` to `T'` has positive length. -/
theorem length_pos_of_isIrreducibleChain (h : IsIrreducibleChain T T' c) : 0 < c.length :=
  List.length_pos_iff.mpr (ne_nil_of_isIrreducibleChain h)

/-- The bundled chain attached to a list chain of irreducible closed subsets. -/
def ofIrreducibleChain (h : IsIrreducibleChain T T' c) :
    LTSeries (IrreducibleCloseds X) where
  length := c.length - 1
  toFun := fun i =>
    ⟨c[(i : ℕ)]'(by have := i.isLt; have := length_pos_of_isIrreducibleChain h; omega),
      (h.2.1 _ (List.getElem_mem _)).1, (h.2.1 _ (List.getElem_mem _)).2⟩
  step := fun i => by
    have := i.isLt
    have := length_pos_of_isIrreducibleChain h
    exact List.isChain_iff_getElem.mp h.1 (i : ℕ) (by omega)

/-- A list chain of `c.length` members becomes an `LTSeries` of `c.length - 1` steps. -/
theorem length_ofIrreducibleChain (h : IsIrreducibleChain T T' c) :
    (ofIrreducibleChain h).length + 1 = c.length := by
  have := length_pos_of_isIrreducibleChain h
  dsimp only [ofIrreducibleChain]
  omega

/-- The first member of the bundled chain `ofIrreducibleChain h` has underlying set `T`. -/
theorem coe_head_ofIrreducibleChain (h : IsIrreducibleChain T T' c) :
    ((ofIrreducibleChain h).head : Set X) = T := by
  have hne := ne_nil_of_isIrreducibleChain h
  show c[0]'(length_pos_of_isIrreducibleChain h) = T
  rw [List.getElem_zero]
  exact Option.some_inj.mp ((List.head?_eq_some_head hne).symm.trans h.2.2.1)

/-- The last member of the bundled chain `ofIrreducibleChain h` has underlying set `T'`. -/
theorem coe_last_ofIrreducibleChain (h : IsIrreducibleChain T T' c) :
    ((ofIrreducibleChain h).last : Set X) = T' := by
  have hne := ne_nil_of_isIrreducibleChain h
  show c[c.length - 1]'(by have := length_pos_of_isIrreducibleChain h; omega) = T'
  rw [← List.getLast_eq_getElem hne]
  exact Option.some_inj.mp ((List.getLast?_eq_some_getLast hne).symm.trans h.2.2.2)

/-- The first member of the bundled chain `ofIrreducibleChain h` is `T`. -/
theorem head_ofIrreducibleChain (h : IsIrreducibleChain T T' c)
    (hTirr : IsIrreducible T) (hTcl : IsClosed T) :
    (ofIrreducibleChain h).head = ⟨T, hTirr, hTcl⟩ :=
  IrreducibleCloseds.ext (coe_head_ofIrreducibleChain h)

/-- The last member of the bundled chain `ofIrreducibleChain h` is `T'`. -/
theorem last_ofIrreducibleChain (h : IsIrreducibleChain T T' c)
    (hT'irr : IsIrreducible T') (hT'cl : IsClosed T') :
    (ofIrreducibleChain h).last = ⟨T', hT'irr, hT'cl⟩ :=
  IrreducibleCloseds.ext (coe_last_ofIrreducibleChain h)

/-- Maximality of a list chain gives the covering relation between the consecutive members of the
bundled chain it becomes. -/
theorem covBy_ofIrreducibleChain (h : IsIrreducibleChain T T' c)
    (hmax : IsIrreducibleChain.IsMaximal c) (i : Fin (ofIrreducibleChain h).length) :
    (ofIrreducibleChain h) i.castSucc ⋖ (ofIrreducibleChain h) i.succ := by
  have hlen := length_ofIrreducibleChain h
  have hi := i.isLt
  exact ⟨(ofIrreducibleChain h).step i, fun Z hZ1 hZ2 =>
    List.isChain_iff_getElem.mp hmax (i : ℕ) (by omega)
      ⟨(Z : Set X), Z.isIrreducible', Z.isClosed', hZ1, hZ2⟩⟩

/-! ### From bundled chains to list chains -/

/-- The list of underlying sets of a bundled chain of irreducible closed subsets. -/
def toSetChain (p : LTSeries (IrreducibleCloseds X)) : List (Set X) :=
  p.toList.map (fun Z : IrreducibleCloseds X => (Z : Set X))

/-- The list `toSetChain p` has `p.length + 1` members. -/
@[simp] theorem length_toSetChain (p : LTSeries (IrreducibleCloseds X)) :
    (toSetChain p).length = p.length + 1 := by simp [toSetChain]

/-- The `i`-th member of `toSetChain p` is the underlying set of the `i`-th member of `p`. -/
theorem getElem_toSetChain (p : LTSeries (IrreducibleCloseds X)) (i : ℕ)
    (hi : i < p.length + 1) :
    (toSetChain p)[i]'(by simpa using hi) = (p ⟨i, hi⟩ : Set X) := by
  simp only [toSetChain, List.getElem_map]
  congr 1
  exact RelSeries.toList_getElem p (by simpa using hi)

/-- Consecutive members of `toSetChain p` are strictly increasing under inclusion. -/
theorem isChain_toSetChain (p : LTSeries (IrreducibleCloseds X)) :
    (toSetChain p).IsChain (· ⊂ ·) := by
  rw [toSetChain, List.isChain_map]
  exact (RelSeries.isChain_toList p).imp fun a b hab => hab

/-- The list `toSetChain p` is a chain of irreducible closed subsets from the underlying set of
`p.head` to that of `p.last`. -/
theorem isIrreducibleChain_toSetChain (p : LTSeries (IrreducibleCloseds X)) :
    IsIrreducibleChain (p.head : Set X) (p.last : Set X) (toSetChain p) := by
  refine ⟨isChain_toSetChain p, ?_, ?_, ?_⟩
  · intro S hS
    obtain ⟨Z, -, rfl⟩ := List.mem_map.mp hS
    exact ⟨Z.isIrreducible', Z.isClosed'⟩
  · rw [toSetChain, List.head?_map, List.head?_eq_some_head p.toList_ne_nil,
      RelSeries.head_toList]
    rfl
  · rw [toSetChain, List.getLast?_map,
      List.getLast?_eq_some_getLast p.toList_ne_nil, RelSeries.getLast_toList]
    rfl

/-- If each member of `p` is covered by the next, then the list chain `toSetChain p` is maximal. -/
theorem isMaximal_toSetChain {p : LTSeries (IrreducibleCloseds X)}
    (hcov : ∀ i : Fin p.length, p i.castSucc ⋖ p i.succ) :
    IsIrreducibleChain.IsMaximal (toSetChain p) := by
  rw [IsIrreducibleChain.IsMaximal, List.isChain_iff_getElem]
  intro i hi
  rw [length_toSetChain] at hi
  rw [getElem_toSetChain p i (by omega), getElem_toSetChain p (i + 1) (by omega)]
  rintro ⟨S, hSirr, hScl, h1, h2⟩
  exact (hcov ⟨i, by omega⟩).2
    (show _ < (⟨S, hSirr, hScl⟩ : IrreducibleCloseds X) from h1)
    (show (⟨S, hSirr, hScl⟩ : IrreducibleCloseds X) < _ from h2)

/-! ### The unbundled characterisation of catenarity -/

/-- `X` is catenary exactly when, for every pair of irreducible closed subsets `T ⊆ T'`, there is
an `n` bounding the length of every list chain of irreducible closed sets from `T` to `T'` by
`n + 1` members and equal to the number of members of every *maximal* such chain. -/
theorem isCatenarySpace_iff_isIrreducibleChain :
    IsCatenarySpace X ↔
      ∀ T T' : Set X, IsIrreducible T → IsClosed T → IsIrreducible T' → IsClosed T' → T ⊆ T' →
        ∃ n : ℕ,
          (∀ c : List (Set X), IsIrreducibleChain T T' c → c.length ≤ n + 1) ∧
          (∀ c : List (Set X), IsIrreducibleChain T T' c →
            IsIrreducibleChain.IsMaximal c → c.length = n + 1) := by
  constructor
  · intro hX T T' hTirr hTcl hT'irr hT'cl hTT'
    obtain ⟨hfin, hmaxlen⟩ := hX ⟨T, hTirr, hTcl⟩ ⟨T', hT'irr, hT'cl⟩ hTT'
    obtain ⟨n, hn⟩ : ∃ n : ℕ, topCodim (⟨T, hTirr, hTcl⟩ : IrreducibleCloseds X)
        ⟨T', hT'irr, hT'cl⟩ = (n : ℕ∞) :=
      (WithTop.ne_top_iff_exists.mp hfin).imp fun _ h => h.symm
    refine ⟨n, fun c hc => ?_, fun c hc hcmax => ?_⟩
    · rw [← length_ofIrreducibleChain hc, Nat.add_le_add_iff_right, ← ENat.coe_le_coe, ← hn]
      exact length_le_topCodim _ _ _ (head_ofIrreducibleChain hc hTirr hTcl)
        (last_ofIrreducibleChain hc hT'irr hT'cl)
    · rw [← length_ofIrreducibleChain hc, Nat.add_right_cancel_iff, ← ENat.coe_inj, ← hn]
      exact hmaxlen _ ⟨head_ofIrreducibleChain hc hTirr hTcl,
        last_ofIrreducibleChain hc hT'irr hT'cl, covBy_ofIrreducibleChain hc hcmax⟩
  · intro hA Y Y' hYY'
    obtain ⟨n, hbound, hmaxlen⟩ :=
      hA Y Y' Y.isIrreducible' Y.isClosed' Y'.isIrreducible' Y'.isClosed' hYY'
    have hle : topCodim Y Y' ≤ (n : ℕ∞) := topCodim_le_iff.mpr fun p hph hpl => by
      have hc := isIrreducibleChain_toSetChain p
      rw [hph, hpl] at hc
      exact_mod_cast (by simpa using hbound _ hc : p.length ≤ n)
    refine ⟨fun htop => by simp [htop] at hle, fun p hmax => ?_⟩
    have hc := isIrreducibleChain_toSetChain p
    rw [hmax.1, hmax.2.1] at hc
    have hplen : p.length = n := by simpa using hmaxlen _ hc (isMaximal_toSetChain hmax.2.2)
    exact le_antisymm (length_le_topCodim Y Y' p hmax.1 hmax.2.1) (by rw [hplen]; exact hle)

end IrreducibleClosedsCodim

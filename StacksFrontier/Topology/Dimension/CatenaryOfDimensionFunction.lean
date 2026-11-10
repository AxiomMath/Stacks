module

public import StacksFrontier.Topology.Dimension.Catenary
public import StacksFrontier.Topology.Dimension.DimensionFunctionCatenary
public import StacksFrontier.Topology.Dimension.SpecializingSurjection
public import StacksFrontier.Topology.Sober.Defs
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Algebra.Order.Star.Int
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
# Sober spaces with a dimension function are catenary

A topological space is *catenary* when for every pair of irreducible closed subsets `T ⊆ T'` the
codimension of `T` in `T'` is finite and every maximal chain of irreducible closed subsets from `T`
to `T'` has that length. A sober space carrying a dimension function `δ` is catenary, and the
codimension of `closure {y}` in `closure {x}` along a specialization `x ⤳ y` is `δ x - δ y`.

## Main definitions

* `IsDimensionFunctionForCatenary`: a function `X → ℤ` dropping strictly along non-trivial
  specializations and by exactly one along immediate ones.
* `IsClosedIrreducibleChain`: a strictly increasing chain of irreducible closed subsets from `Y` to
  `Y'`, indexed by `Fin (e + 1)`.
* `IsMaximalFinChain`: such a chain with no irreducible closed subset strictly between two
  consecutive members.
* `ofClosedIrreducibleChain`: the `LTSeries` of irreducible closed subsets attached to such a
  chain.

## Main results

* `codim_closure_singleton_eq_delta_diff`: the codimension formula
  `topCodim (closure {y}) (closure {x}) = (δ x - δ y).toNat`.
* `isCatenary_of_isSober_of_dim`: a sober space with a dimension function is catenary.
* `isCatenarySpace_and_topCodim_eq_of_isDimensionFunction`: the conjunction of the two.

## References

* [Stacks Project, Tag 02IA](https://stacks.math.columbia.edu/tag/02IA)
-/

@[expose] public section

open TopologicalSpace.IrreducibleCloseds (closureSingleton coe_closureSingleton)

variable {X : Type*} [TopologicalSpace X]

/-! ## Definitions -/

/-- A dimension function on `X`: `δ` drops strictly along non-trivial specializations and by
exactly one along immediate specializations. -/
@[sga "6 X 1.6"]
structure IsDimensionFunctionForCatenary (δ : X → ℤ) : Prop where
  strict_spec : ∀ ⦃x y : X⦄, x ⤳ y → x ≠ y → δ y < δ x
  immediate : ∀ ⦃x y : X⦄, TopologicalSpace.IsImmediateSpecialization x y → δ x = δ y + 1

/-- A strictly increasing sequence `Y = Y₀ ⊊ Y₁ ⊊ ⋯ ⊊ Yₑ = Y'` of irreducible closed subsets of
`X`. -/
@[ega "0 14.1.1"]
structure IsClosedIrreducibleChain (e : ℕ) (f : Fin (e + 1) → Set X)
    (Y Y' : Set X) : Prop where
  first : f 0 = Y
  last : f (Fin.last e) = Y'
  isClosed : ∀ i, IsClosed (f i)
  isIrreducible : ∀ i, IsIrreducible (f i)
  strictMono : StrictMono f

/-- A maximal chain from `Y` to `Y'`: a chain of irreducible closed subsets with no irreducible
closed subset strictly between two consecutive members. -/
def IsMaximalFinChain (e : ℕ) (f : Fin (e + 1) → Set X) (Y Y' : Set X) : Prop :=
  IsClosedIrreducibleChain e f Y Y' ∧
    ∀ i : Fin e, ¬ ∃ Z : Set X,
      IsClosed Z ∧ IsIrreducible Z ∧
      (f i.castSucc ⊂ Z) ∧ (Z ⊂ f i.succ)

/-! ## `Fin`-indexed chains and `LTSeries` -/

/-- The canonical bundled chain attached to a `Fin`-indexed chain of irreducible closed sets. -/
def ofClosedIrreducibleChain {e : ℕ} {f : Fin (e + 1) → Set X} {Y Y' : Set X}
    (h : IsClosedIrreducibleChain e f Y Y') :
    LTSeries (TopologicalSpace.IrreducibleCloseds X) where
  length := e
  toFun := fun i => ⟨f i, h.isIrreducible i, h.isClosed i⟩
  step := fun _ => h.strictMono Fin.castSucc_lt_succ

/-- The bundled chain `ofClosedIrreducibleChain h` has length `e`. -/
@[simp] lemma length_ofClosedIrreducibleChain {e : ℕ} {f : Fin (e + 1) → Set X} {Y Y' : Set X}
    (h : IsClosedIrreducibleChain e f Y Y') : (ofClosedIrreducibleChain h).length = e := rfl

/-- The first member of `ofClosedIrreducibleChain h` is `Y`. -/
lemma head_ofClosedIrreducibleChain {e : ℕ} {f : Fin (e + 1) → Set X} {Y Y' : Set X}
    (h : IsClosedIrreducibleChain e f Y Y') (hYirr : IsIrreducible Y) (hYcl : IsClosed Y) :
    (ofClosedIrreducibleChain h).head = ⟨Y, hYirr, hYcl⟩ :=
  TopologicalSpace.IrreducibleCloseds.ext h.first

/-- The last member of `ofClosedIrreducibleChain h` is `Y'`. -/
lemma last_ofClosedIrreducibleChain {e : ℕ} {f : Fin (e + 1) → Set X} {Y Y' : Set X}
    (h : IsClosedIrreducibleChain e f Y Y') (hY'irr : IsIrreducible Y') (hY'cl : IsClosed Y') :
    (ofClosedIrreducibleChain h).last = ⟨Y', hY'irr, hY'cl⟩ :=
  TopologicalSpace.IrreducibleCloseds.ext h.last

/-- Conversely, the underlying sets of a bundled chain form a `Fin`-indexed chain. -/
lemma isClosedIrreducibleChain_coe (p : LTSeries (TopologicalSpace.IrreducibleCloseds X))
    {Y Y' : Set X} (hY : (p.head : Set X) = Y) (hY' : (p.last : Set X) = Y') :
    IsClosedIrreducibleChain p.length (fun i => (p i : Set X)) Y Y' where
  first := hY
  last := hY'
  isClosed := fun i => (p i).isClosed'
  isIrreducible := fun i => (p i).isIrreducible'
  strictMono := fun _ _ hij => p.strictMono hij

/-- If every consecutive pair of a bundled chain is a covering pair, then its underlying sets form
a maximal `Fin`-indexed chain. -/
lemma isMaximalFinChain_coe (p : LTSeries (TopologicalSpace.IrreducibleCloseds X))
    {Y Y' : Set X} (hY : (p.head : Set X) = Y) (hY' : (p.last : Set X) = Y')
    (hcov : ∀ i : Fin p.length, p i.castSucc ⋖ p i.succ) :
    IsMaximalFinChain p.length (fun i => (p i : Set X)) Y Y' := by
  refine ⟨isClosedIrreducibleChain_coe p hY hY', fun i => ?_⟩
  rintro ⟨Z, hZcl, hZirr, h1, h2⟩
  exact (hcov i).2
    (show _ < (⟨Z, hZirr, hZcl⟩ : TopologicalSpace.IrreducibleCloseds X) from h1)
    (show (⟨Z, hZirr, hZcl⟩ : TopologicalSpace.IrreducibleCloseds X) < _ from h2)

/-! ## Closures of singletons -/

/-- The closure of a singleton is irreducible. -/
@[ega "0 2.1.2"]
lemma isIrreducible_closure_singleton (x : X) :
    IsIrreducible (closure ({x} : Set X)) :=
  isIrreducible_singleton.closure

/-- A point is the generic point of the closure of its singleton. -/
lemma isGenericPoint_closure_singleton_self (x : X) :
    IsGenericPoint x (closure ({x} : Set X)) := rfl

/-- Specialization in terms of singleton-closure containment. -/
@[ega "0 2.1.2", sga "4 IV 4.2.2"]
lemma specializes_iff_closure_singleton_subset (x y : X) :
    x ⤳ y ↔ closure ({y} : Set X) ⊆ closure ({x} : Set X) :=
  specializes_iff_closure_subset

/-- Closure containment gives the reverse specialization. -/
@[sga "4 IV 4.2.2" "partial"]
lemma specializes_of_closure_singleton_subset (t t' : X)
    (hsub : closure ({t} : Set X) ⊆ closure ({t'} : Set X)) : t' ⤳ t :=
  specializes_iff_closure_subset.mpr hsub

/-- In a sober space, every irreducible closed subset is the closure of a unique point. -/
lemma sober_unique_generic_singleton (hSober : StacksSober X)
    (Z : Set X) (hZcl : IsClosed Z) (hZirr : IsIrreducible Z) :
    ∃! x : X, closure ({x} : Set X) = Z := by
  obtain ⟨ξ, ⟨-, hξ⟩, huniq⟩ := hSober Z hZirr hZcl
  exact ⟨ξ, hξ.symm, fun y hy ↦ huniq y ⟨hy ▸ subset_closure rfl, hy.symm⟩⟩

/-- In a sober space, if `closure {w} = closure {y}` then `w = y`. -/
lemma eq_of_closure_singleton_eq (hSober : StacksSober X)
    (y w : X) (hw : closure ({w} : Set X) = closure ({y} : Set X)) : w = y := by
  obtain ⟨z, _, hz_uniq⟩ :=
    sober_unique_generic_singleton hSober (closure ({y} : Set X))
      (isClosed_closure) (isIrreducible_closure_singleton y)
  exact (hz_uniq w hw).trans (hz_uniq y rfl).symm

/-- Strict singleton-closure containment gives strict specialization. -/
lemma specializes_and_ne_of_closure_ssubset (a b : X)
    (h : closure ({a} : Set X) ⊂ closure ({b} : Set X)) : b ⤳ a ∧ a ≠ b :=
  ⟨specializes_iff_mem_closure.mpr (h.1 (subset_closure rfl)), fun hab ↦ h.ne (by rw [hab])⟩

/-! ## Generic-point extraction along a chain -/

/-- In a sober space, every chain `f` of irreducible closed sets admits a choice of generic points
`w : Fin (e+1) → X` with `closure {w i} = f i`. -/
lemma exists_generic_point_function (hSober : StacksSober X)
    (e : ℕ) (f : Fin (e + 1) → Set X) (Y Y' : Set X)
    (hchain : IsClosedIrreducibleChain e f Y Y') :
    ∃ w : Fin (e + 1) → X, ∀ i, closure ({w i} : Set X) = f i := by
  choose w hw using fun i =>
    (sober_unique_generic_singleton hSober (f i)
      (hchain.isClosed i) (hchain.isIrreducible i)).exists
  exact ⟨w, hw⟩

/-! ## Upper bound: a chain from `closure {y}` to `closure {x}` has length at most `δ x - δ y` -/

/-- Telescoping for integer sequences indexed by `Fin (e + 1)`. -/
lemma telescope_int_seq (e : ℕ) (g : Fin (e + 1) → ℤ)
    (h : ∀ i : Fin e, g i.succ = g i.castSucc + 1) :
    g (Fin.last e) = g 0 + e := by
  induction e with
  | zero => simp
  | succ n ih =>
    have hlast : (Fin.last (n + 1) : Fin (n + 2)) = (Fin.last n : Fin (n + 1)).succ := by
      ext; simp
    rw [hlast, h (Fin.last n)]
    have key := ih (g ∘ Fin.castSucc) (fun i => by
      simpa [Fin.castSucc_succ] using h i.castSucc)
    simp only [Function.comp_apply, Fin.castSucc_zero] at key
    rw [key]
    push_cast
    ring

/-- A chain from `closure {y}` to `closure {x}` in a sober space has generic points `w i` with
`w 0 = y` and `w (Fin.last e) = x`. -/
private lemma exists_generic_points_of_chain (hSober : StacksSober X) (x y : X)
    (e : ℕ) (f : Fin (e + 1) → Set X)
    (hchain : IsClosedIrreducibleChain e f (closure ({y} : Set X)) (closure ({x} : Set X))) :
    ∃ w : Fin (e + 1) → X,
      (∀ i, closure ({w i} : Set X) = f i) ∧ w 0 = y ∧ w (Fin.last e) = x := by
  obtain ⟨w, hw⟩ := exists_generic_point_function hSober e f _ _ hchain
  exact ⟨w, hw, eq_of_closure_singleton_eq hSober y _ (by rw [hw 0, hchain.first]),
    eq_of_closure_singleton_eq hSober x _ (by rw [hw, hchain.last])⟩

/-- Any chain from `closure {y}` to `closure {x}` has length `≤ δ x - δ y`. -/
lemma chain_length_le_delta_diff (hSober : StacksSober X) (δ : X → ℤ)
    (hδ : IsDimensionFunctionForCatenary δ) (x y : X)
    (e : ℕ) (f : Fin (e + 1) → Set X)
    (hchain : IsClosedIrreducibleChain e f (closure ({y} : Set X))
      (closure ({x} : Set X))) :
    (e : ℤ) ≤ δ x - δ y := by
  obtain ⟨z, hz, hz0, hzlast⟩ := exists_generic_points_of_chain hSober x y e f hchain
  have hstep : ∀ i : Fin e, δ (z i.castSucc) + 1 ≤ δ (z i.succ) := fun i ↦ by
    obtain ⟨hsp, hne⟩ := specializes_and_ne_of_closure_ssubset (z i.castSucc) (z i.succ)
      (by rw [hz i.castSucc, hz i.succ]; exact hchain.strictMono Fin.castSucc_lt_succ)
    have := hδ.strict_spec hsp hne.symm
    omega
  have hbound : ∀ i : Fin (e + 1), δ (z 0) + (i.val : ℤ) ≤ δ (z i) := by
    intro i
    induction i using Fin.induction with
    | zero => simp
    | succ j ih =>
      have hs := hstep j
      have hval : ((j.succ).val : ℤ) = (j.castSucc.val : ℤ) + 1 := by
        simp [Fin.val_succ]
      omega
  have hfinal := hbound (Fin.last e)
  rw [hz0, hzlast, Fin.val_last] at hfinal
  omega

/-! ## Steps of a maximal chain are immediate specializations -/

/-- In a sober space, for a maximal chain `f` of irreducible closed sets, each consecutive step
`(w i.succ, w i.castSucc)` between its generic points is an immediate specialization. -/
lemma consecutive_immediate_specialization (hSober : StacksSober X)
    (e : ℕ) (f : Fin (e + 1) → Set X) (Y Y' : Set X)
    (hmax : IsMaximalFinChain e f Y Y')
    (w : Fin (e + 1) → X) (hw : ∀ i, closure ({w i} : Set X) = f i)
    (i : Fin e) :
    TopologicalSpace.IsImmediateSpecialization (w i.succ) (w i.castSucc) := by
  obtain ⟨hchain, hnoMid⟩ := hmax
  obtain ⟨hspec, hne⟩ := specializes_and_ne_of_closure_ssubset (w i.castSucc) (w i.succ)
    (by rw [hw i.castSucc, hw i.succ]; exact hchain.strictMono Fin.castSucc_lt_succ)
  refine ⟨hspec, fun h => hne h.symm, fun z h1 h2 ↦ ?_⟩
  by_contra! hz
  have hz_in_succ := (specializes_iff_closure_singleton_subset _ _).mp h1
  have hcast_in_z := (specializes_iff_closure_singleton_subset _ _).mp h2
  refine hnoMid i ⟨closure ({z} : Set X), isClosed_closure,
    isIrreducible_closure_singleton z, ?_, ?_⟩
  · rw [← hw i.castSucc]
    exact ⟨hcast_in_z, fun h ↦ hz.2 (eq_of_closure_singleton_eq hSober _ _ (h.antisymm hcast_in_z))⟩
  · rw [← hw i.succ]
    exact ⟨hz_in_succ, fun h ↦ hz.1 (eq_of_closure_singleton_eq hSober _ _ (hz_in_succ.antisymm h))⟩

/-- A maximal chain from `closure {y}` to `closure {x}` has length `δ x - δ y`. -/
lemma maximal_chain_length_eq (hSober : StacksSober X) (δ : X → ℤ)
    (hδ : IsDimensionFunctionForCatenary δ) (x y : X)
    (e : ℕ) (f : Fin (e + 1) → Set X)
    (hmax : IsMaximalFinChain e f (closure ({y} : Set X)) (closure ({x} : Set X))) :
    (e : ℤ) = δ x - δ y := by
  obtain ⟨w, hw, hw0, hwlast⟩ := exists_generic_points_of_chain hSober x y e f hmax.1
  have htel := telescope_int_seq e (fun i => δ (w i)) fun i ↦
    hδ.immediate (consecutive_immediate_specialization hSober e f _ _ hmax w hw i)
  rw [hw0, hwlast] at htel
  linarith

/-! ## Existence of a maximal chain of length `(δ x - δ y).toNat` -/

/-- The constant chain of length `0` from `closure {x}` to itself. -/
private lemma exists_trivial_chain (x : X) :
    ∃ f : Fin (0 + 1) → Set X,
      IsClosedIrreducibleChain 0 f (closure ({x} : Set X)) (closure ({x} : Set X)) := by
  refine ⟨fun _ => closure ({x} : Set X),
          { first := rfl
            last := rfl
            isClosed := fun _ => isClosed_closure
            isIrreducible := fun _ => isIrreducible_closure_singleton x
            strictMono := ?_ }⟩
  intro a b hab
  have ha : (a : ℕ) < 1 := a.isLt
  have hb : (b : ℕ) < 1 := b.isLt
  have hab' : (a : ℕ) < (b : ℕ) := hab
  omega

/-- A length-1 chain `closure {y} ⊊ closure {x}` when `x ⤳ y` and `x ≠ y`. -/
private lemma exists_length_one_chain (hSober : StacksSober X)
    (x y : X) (hxy : x ⤳ y) (hne : x ≠ y) :
    ∃ f : Fin (1 + 1) → Set X,
      IsClosedIrreducibleChain 1 f (closure ({y} : Set X)) (closure ({x} : Set X)) := by
  refine ⟨fun i => if i = 0 then closure ({y} : Set X) else closure ({x} : Set X), ?_⟩
  have hssub : closure ({y} : Set X) ⊂ closure ({x} : Set X) :=
    ((specializes_iff_closure_singleton_subset _ _).mp hxy).ssubset_of_ne fun heq ↦
      hne (eq_of_closure_singleton_eq hSober x y heq).symm
  refine
    { first := by simp
      last := by simp [Fin.last]
      isClosed := fun i ↦ by by_cases h : i = 0 <;> simp [h]
      isIrreducible := fun i ↦ by
        by_cases h : i = 0 <;> simp [h, isIrreducible_closure_singleton]
      strictMono := ?_ }
  · intro a b hab
    have ha : (a : ℕ) < 2 := a.isLt
    have hb : (b : ℕ) < 2 := b.isLt
    have hab' : (a : ℕ) < (b : ℕ) := hab
    have ha0 : (a : ℕ) = 0 := by omega
    have hb1 : (b : ℕ) = 1 := by omega
    have hae : a = 0 := by ext; simp [ha0]
    have hbe : b ≠ 0 := by intro h; rw [h] at hb1; simp at hb1
    simp only [Nat.reduceAdd, hae, Fin.isValue, ↓reduceIte, hbe]
    exact hssub

/-- Set of chain lengths from `closure {y}` to `closure {x}`. -/
private def chainLengthSet (X : Type*) [TopologicalSpace X] (x y : X) : Set ℕ :=
  {e : ℕ | ∃ f : Fin (e + 1) → Set X, IsClosedIrreducibleChain e f
            (closure ({y} : Set X)) (closure ({x} : Set X))}

/-- If `f` is a chain of length `m` from `Y` to `Y'` and `Z` is an irreducible closed set strictly
between `f i.castSucc` and `f i.succ`, then there is a chain of length `m + 1` from `Y` to `Y'`. -/
private lemma insert_into_chain (Y Y' : Set X) (m : ℕ) (f : Fin (m + 1) → Set X)
    (hf : IsClosedIrreducibleChain m f Y Y') (i : Fin m) (Z : Set X)
    (hZcl : IsClosed Z) (hZirr : IsIrreducible Z)
    (hZ_sup : f i.castSucc ⊂ Z) (hZ_sub : Z ⊂ f i.succ) :
    ∃ g : Fin (m + 1 + 1) → Set X, IsClosedIrreducibleChain (m + 1) g Y Y' := by
  refine ⟨_, isClosedIrreducibleChain_coe ((ofClosedIrreducibleChain hf).insertNth i
    ⟨Z, hZirr, hZcl⟩ hZ_sup hZ_sub) ?_ ?_⟩
  · exact (congrArg (fun T : TopologicalSpace.IrreducibleCloseds X => (T : Set X))
      (LTSeries.head_insertNth (ofClosedIrreducibleChain hf) i ⟨Z, hZirr, hZcl⟩
        hZ_sup hZ_sub)).trans hf.first
  · exact (congrArg (fun T : TopologicalSpace.IrreducibleCloseds X => (T : Set X))
      (LTSeries.last_insertNth (ofClosedIrreducibleChain hf) i ⟨Z, hZirr, hZcl⟩
        hZ_sup hZ_sub)).trans hf.last

/-- Every chain from `closure {y}` to `closure {x}` has length at most `(δ x - δ y).toNat`. -/
private lemma mem_chainLengthSet_le_toNat (hSober : StacksSober X) (δ : X → ℤ)
    (hδ : IsDimensionFunctionForCatenary δ) (x y : X) {k : ℕ}
    (hk : k ∈ chainLengthSet X x y) : k ≤ (δ x - δ y).toNat := by
  obtain ⟨g, hg⟩ := hk
  have := chain_length_le_delta_diff hSober δ hδ x y k g hg
  omega

/-- A chain from `closure {y}` to `closure {x}` of maximal length among all such chains is a
maximal chain. -/
private lemma isMaximalFinChain_of_forall_mem_le (x y : X) (m : ℕ) (f : Fin (m + 1) → Set X)
    (hf : IsClosedIrreducibleChain m f (closure ({y} : Set X)) (closure ({x} : Set X)))
    (hle : ∀ k ∈ chainLengthSet X x y, k ≤ m) :
    IsMaximalFinChain m f (closure ({y} : Set X)) (closure ({x} : Set X)) := by
  refine ⟨hf, ?_⟩
  intro i ⟨Z, hZcl, hZirr, hZ_sup, hZ_sub⟩
  obtain ⟨g, hg⟩ := insert_into_chain _ _ m f hf i Z hZcl hZirr hZ_sup hZ_sub
  have := hle (m + 1) ⟨g, hg⟩
  omega

/-- In a sober space with a dimension function `δ`, for any `x ⤳ y` there is a chain from
`closure {y}` to `closure {x}` of length `(δ x - δ y).toNat`. -/
lemma exists_chain_of_length_delta_diff (hSober : StacksSober X) (δ : X → ℤ)
    (hδ : IsDimensionFunctionForCatenary δ) (x y : X) (hxy : x ⤳ y) :
    ∃ f : Fin ((δ x - δ y).toNat + 1) → Set X,
      IsClosedIrreducibleChain (δ x - δ y).toNat f
        (closure ({y} : Set X)) (closure ({x} : Set X)) := by
  classical
  by_cases hxy_eq : x = y
  · subst hxy_eq
    rw [show (δ x - δ x).toNat = 0 by simp]
    exact exists_trivial_chain x
  · have h₁ : 1 ∈ chainLengthSet X x y := exists_length_one_chain hSober x y hxy hxy_eq
    obtain ⟨m, hmmem, hmle⟩ : ∃ m ∈ chainLengthSet X x y, ∀ k ∈ chainLengthSet X x y, k ≤ m :=
      ⟨Nat.findGreatest (· ∈ chainLengthSet X x y) (δ x - δ y).toNat,
        Nat.findGreatest_spec (mem_chainLengthSet_le_toNat hSober δ hδ x y h₁) h₁,
        fun k hk => Nat.le_findGreatest (mem_chainLengthSet_le_toNat hSober δ hδ x y hk) hk⟩
    obtain ⟨f, hf⟩ := hmmem
    have hmeq : (m : ℤ) = δ x - δ y :=
      maximal_chain_length_eq hSober δ hδ x y m f
        (isMaximalFinChain_of_forall_mem_le x y m f hf hmle)
    rw [show (δ x - δ y).toNat = m by omega]
    exact ⟨f, hf⟩

/-! ## The codimension formula and catenarity -/

/-- The codimension of `closure {y}` in `closure {x}` along a specialization `x ⤳ y` is
`δ x - δ y`. -/
lemma codim_closure_singleton_eq_delta_diff (hSober : StacksSober X)
    (δ : X → ℤ) (hδ : IsDimensionFunctionForCatenary δ) (x y : X) (hxy : x ⤳ y) :
    IrreducibleClosedsCodim.topCodim (closureSingleton y) (closureSingleton x)
      = ((δ x - δ y).toNat : ℕ∞) := by
  apply le_antisymm
  · rw [IrreducibleClosedsCodim.topCodim_le_iff]
    intro p hph hpl
    have hc := isClosedIrreducibleChain_coe p (by rw [hph]) (by rw [hpl])
    have h1 : (p.length : ℤ) ≤ δ x - δ y :=
      chain_length_le_delta_diff hSober δ hδ x y p.length _ hc
    exact_mod_cast (show p.length ≤ (δ x - δ y).toNat by omega)
  · obtain ⟨f, hf⟩ := exists_chain_of_length_delta_diff hSober δ hδ x y hxy
    exact IrreducibleClosedsCodim.length_le_topCodim
      (closureSingleton y) (closureSingleton x) (ofClosedIrreducibleChain hf)
      (head_ofClosedIrreducibleChain hf _ _) (last_ofClosedIrreducibleChain hf _ _)

/-- A sober space with a dimension function is catenary. -/
@[sga "6 X 1.6" "more general"]
lemma isCatenary_of_isSober_of_dim (hSober : StacksSober X) (δ : X → ℤ)
    (hδ : IsDimensionFunctionForCatenary δ) :
    IrreducibleClosedsCodim.IsCatenarySpace X := by
  intro T T' hTT'
  obtain ⟨y, hy, _⟩ :=
    sober_unique_generic_singleton hSober T T.isClosed' T.isIrreducible'
  obtain ⟨x, hx, _⟩ :=
    sober_unique_generic_singleton hSober T' T'.isClosed' T'.isIrreducible'
  have hTeq : closureSingleton y = T := TopologicalSpace.IrreducibleCloseds.ext hy
  have hT'eq : closureSingleton x = T' := TopologicalSpace.IrreducibleCloseds.ext hx
  have hsub : closure ({y} : Set X) ⊆ closure ({x} : Set X) := by
    rw [hy, hx]; exact hTT'
  have hxy : x ⤳ y := specializes_of_closure_singleton_subset y x hsub
  have hcod := codim_closure_singleton_eq_delta_diff hSober δ hδ x y hxy
  rw [hTeq, hT'eq] at hcod
  refine ⟨by rw [hcod]; exact (ENat.natCast_lt_top _).ne, fun p hp => ?_⟩
  obtain ⟨hphead, hplast, hpmax⟩ := hp
  have hmax : IsMaximalFinChain p.length (fun i => (p i : Set X))
      (closure ({y} : Set X)) (closure ({x} : Set X)) :=
    isMaximalFinChain_coe p (by rw [hphead, ← hy]) (by rw [hplast, ← hx]) hpmax
  have heeq : (p.length : ℤ) = δ x - δ y :=
    maximal_chain_length_eq hSober δ hδ x y p.length _ hmax
  rw [hcod, show (δ x - δ y).toNat = p.length by omega]

/-! ## The main statement -/

/-- A sober topological space `X` admitting a dimension function `δ` is catenary, and for every
specialization `x ⤳ y` we have `codim(closure {y}, closure {x}) = δ x - δ y`. -/
@[stacks 02IA]
theorem isCatenarySpace_and_topCodim_eq_of_isDimensionFunction (X : Type*) [TopologicalSpace X]
    (hSober : StacksSober X) (δ : X → ℤ) (hδ : IsDimensionFunctionForCatenary δ) :
    IrreducibleClosedsCodim.IsCatenarySpace X ∧
      ∀ x y : X, x ⤳ y →
        IrreducibleClosedsCodim.topCodim (closureSingleton y) (closureSingleton x)
          = ((δ x - δ y).toNat : ℕ∞) :=
  ⟨isCatenary_of_isSober_of_dim hSober δ hδ,
   fun x y hxy => codim_closure_singleton_eq_delta_diff hSober δ hδ x y hxy⟩

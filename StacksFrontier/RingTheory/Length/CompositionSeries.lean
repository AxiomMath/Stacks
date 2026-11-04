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

/-!
# Maximal chains of submodules and composition series

A maximal chain `0 = M_0 ⊂ M_1 ⊂ … ⊂ M_n = M` of submodules of an `R`-module `M` gives a
composition series of `M`: consecutive members cover one another, so every successive
subquotient `M_{i+1} / M_i` is a simple `R`-module, isomorphic to `R ⧸ 𝔪` for a maximal ideal
`𝔪`, and `n` is the length of `M`.
-/

@[expose] public section

/-- The `i`-th successive subquotient `M_{i+1} / M_i` of a chain `M'` of
submodules of `M`. -/
abbrev subQuot {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
    {n : ℕ} (M' : Fin (n + 1) → Submodule R M) (i : Fin n) : Type _ :=
  (M' i.succ) ⧸ ((M' i.castSucc).submoduleOf (M' i.succ))

/-- A *maximal chain* of submodules of `M` of length `n` is a strictly
increasing chain `M_0 ⊂ M_1 ⊂ … ⊂ M_n` with `M_0 = ⊥`, `M_n = ⊤` such that
no submodule strictly lies between any two consecutive members of the chain. -/
structure IsMaximalChainPrime {R : Type*} [Ring R] {M : Type*}
    [AddCommGroup M] [Module R M] {n : ℕ} (M' : Fin (n + 1) → Submodule R M) :
    Prop where
  strictMono : StrictMono M'
  bot : M' 0 = ⊥
  top : M' (Fin.last n) = ⊤
  no_refinement : ∀ (i : Fin n) (N : Submodule R M),
    M' i.castSucc ≤ N → N ≤ M' i.succ → N = M' i.castSucc ∨ N = M' i.succ

/-- For a maximal chain `M'`, consecutive members satisfy the `CovBy` relation
`M' i.castSucc ⋖ M' i.succ`. -/
lemma maximalChain_covBy {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
    {n : ℕ} {M' : Fin (n + 1) → Submodule R M} (hchain : IsMaximalChainPrime M')
    (i : Fin n) : M' i.castSucc ⋖ M' i.succ := by
  refine ⟨hchain.strictMono (Fin.castSucc_lt_succ (i := i)), ?_⟩
  intro N hN1 hN2
  rcases hchain.no_refinement i N hN1.le hN2.le with hEq | hEq
  · exact (lt_irrefl _ (hEq ▸ hN1))
  · exact (lt_irrefl _ (hEq ▸ hN2))

/-- Each successive quotient of a maximal chain is a simple `R`-module. -/
lemma subQuot_isSimpleModule_of_maximalChain
    {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
    {n : ℕ} {M' : Fin (n + 1) → Submodule R M} (hchain : IsMaximalChainPrime M')
    (i : Fin n) : IsSimpleModule R (subQuot M' i) := by
  have hcov := maximalChain_covBy hchain i
  have hle : M' i.castSucc ≤ M' i.succ := hcov.le
  exact (covBy_iff_quot_is_simple hle).mp hcov

/-- Build a `CompositionSeries (Submodule R M)` from a maximal chain.  The
length is `n`, the underlying function is `M'`, and the step relation on
`Submodule R M` is `CovBy`. -/
def compositionSeriesOfMaximalChain
    {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
    {n : ℕ} (M' : Fin (n + 1) → Submodule R M) (hchain : IsMaximalChainPrime M') :
    CompositionSeries (Submodule R M) :=
  ⟨n, M', fun i => maximalChain_covBy hchain i⟩

/-- The composition series built from a maximal chain has head `⊥`. -/
lemma compositionSeriesOfMaximalChain_head
    {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
    {n : ℕ} (M' : Fin (n + 1) → Submodule R M) (hchain : IsMaximalChainPrime M') :
    (compositionSeriesOfMaximalChain M' hchain).head = ⊥ :=
  hchain.bot

/-- The composition series built from a maximal chain has last `⊤`. -/
lemma compositionSeriesOfMaximalChain_last
    {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
    {n : ℕ} (M' : Fin (n + 1) → Submodule R M) (hchain : IsMaximalChainPrime M') :
    (compositionSeriesOfMaximalChain M' hchain).last = ⊤ :=
  hchain.top

/-- The composition series built from a maximal chain has length `n`. -/
lemma compositionSeriesOfMaximalChain_length
    {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
    {n : ℕ} (M' : Fin (n + 1) → Submodule R M) (hchain : IsMaximalChainPrime M') :
    (compositionSeriesOfMaximalChain M' hchain).length = n := rfl

/-! ### Main statements (parts (1)–(3) of Stacks 00J3) -/

/-- **Stacks 00J3** (parts 1, 2, 3). For a finite-length `R`-module `M` and a
maximal chain `0 = M_0 ⊂ M_1 ⊂ … ⊂ M_n = M` of submodules, we have

* `n = length_R(M)` (length is well-defined on maximal chains);
* each successive quotient `M_{i+1}/M_i` is simple;
* each successive quotient is isomorphic to `R/𝔪` for some maximal ideal `𝔪`.

Part (4) of Stacks 00J3, which counts the indices `i` with `𝔪_i = 𝔪` in terms of the length
of a localization, is not covered by this statement. -/
@[stacks 00J3]
theorem length_eq_and_subQuot_isSimpleModule_and_exists_quot_maximal
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {n : ℕ} (M' : Fin (n + 1) → Submodule R M) (hchain : IsMaximalChainPrime M') :
    ((compositionSeriesOfMaximalChain M' hchain).length : ℕ∞)
        = Module.length R M ∧
      (∀ i : Fin n, IsSimpleModule R (subQuot M' i)) ∧
      (∀ i : Fin n, ∃ (𝔪 : Ideal R) (_ : 𝔪.IsMaximal),
        Nonempty (subQuot M' i ≃ₗ[R] R ⧸ 𝔪)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Part (1): length of the chain equals `Module.length R M`.
    have hhead := compositionSeriesOfMaximalChain_head M' hchain
    have hlast := compositionSeriesOfMaximalChain_last M' hchain
    have hlen := Module.length_compositionSeries
      (compositionSeriesOfMaximalChain M' hchain) hhead hlast
    exact_mod_cast hlen
  · -- Part (2): each successive quotient is simple.
    intro i
    exact subQuot_isSimpleModule_of_maximalChain hchain i
  · -- Part (3): each successive quotient is `R / 𝔪` for some maximal `𝔪`.
    intro i
    have hsimple : IsSimpleModule R (subQuot M' i) :=
      subQuot_isSimpleModule_of_maximalChain hchain i
    obtain ⟨𝔪, hmax, he⟩ := isSimpleModule_iff_quot_maximal.mp hsimple
    exact ⟨𝔪, hmax, he⟩


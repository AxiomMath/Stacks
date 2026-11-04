module

public import StacksCore.Tactic.StacksAttribute
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

/-!
# Modules of infinite length over a local ring

Let `R` be a commutative local ring with maximal ideal `m` and let `M` be an `R`-module. If
`m ^ n M ≠ 0` for every `n`, then `M` has infinite length; equivalently, a module of finite
length is killed by some power of `m`.
-/

@[expose] public section

open Module

/-- An ideal kills a submodule `N` iff it kills `N` regarded as a module. -/
private theorem smul_top_eq_bot_iff_smul_eq_bot {R : Type*} [CommRing R] (I : Ideal R)
    {M : Type*} [AddCommGroup M] [Module R M] (N : Submodule R M) :
    I • (⊤ : Submodule R N) = ⊥ ↔ I • N = ⊥ := by
  rw [← (Submodule.map_injective_of_injective N.injective_subtype).eq_iff,
    Submodule.map_smul'', Submodule.map_subtype_top, Submodule.map_bot]

/-- The maximal ideal of a local ring annihilates a simple module. -/
private theorem max_smul_simple (R : Type*) [CommRing R] [IsLocalRing R]
    (S : Type*) [AddCommGroup S] [Module R S] [IsSimpleModule R S] :
    IsLocalRing.maximalIdeal R • (⊤ : Submodule R S) = ⊥ := by
  have hmax : (Module.annihilator R S).IsMaximal := IsSimpleModule.annihilator_isMaximal
  have heq : Module.annihilator R S = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal hmax
  rw [← heq, eq_bot_iff, Submodule.smul_le]
  intro r hr n _
  rw [Module.mem_annihilator] at hr
  simp [hr]

/-- A module of finite length over a local ring `R` is annihilated by some power of the
maximal ideal of `R`. -/
theorem exists_pow_maximalIdeal_smul_eq_bot_of_isFiniteLength (R : Type*) [CommRing R]
    [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] (h : IsFiniteLength R M) :
    ∃ n : ℕ, IsLocalRing.maximalIdeal R ^ n • (⊤ : Submodule R M) = ⊥ := by
  induction h with
  | of_subsingleton =>
    refine ⟨0, ?_⟩
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    rw [Subsingleton.elim (⊤ : Submodule R _) ⊥]
  | @of_simple_quotient M _ _ N _ hfin ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    set m := IsLocalRing.maximalIdeal R with hm
    -- `m • ⊤_M ≤ N`, because `m` annihilates the simple quotient `M/N`.
    have hmle : m • (⊤ : Submodule R M) ≤ N := by
      have hsimple : m • (⊤ : Submodule R (M ⧸ N)) = ⊥ := max_smul_simple R (M ⧸ N)
      have hmap : Submodule.map N.mkQ (m • (⊤ : Submodule R M)) = ⊥ := by
        rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ, hsimple]
      rw [← Submodule.ker_mkQ N, ← Submodule.comap_bot]
      rw [← Submodule.map_le_iff_le_comap, hmap]
    -- `m^n • N = ⊥`, transported from the inductive hypothesis on `N`.
    have hN : m ^ n • N = ⊥ := (smul_top_eq_bot_iff_smul_eq_bot _ N).mp hn
    -- Conclude `m^(n+1) • ⊤_M = ⊥`.
    rw [le_antisymm_iff]
    refine ⟨?_, bot_le⟩
    calc m ^ (n + 1) • (⊤ : Submodule R M)
        = m ^ n • (m • (⊤ : Submodule R M)) := by rw [pow_succ, Submodule.mul_smul]
      _ ≤ m ^ n • N := Submodule.smul_mono (le_refl _) hmle
      _ = ⊥ := hN

/-- **Stacks 00IW.** For a local ring `R` with maximal ideal `m`, if the `R`-module `M` has
finite length then `m ^ n M = 0` for some `n ≥ 0`. -/
@[stacks 00IW]
theorem exists_pow_maximalIdeal_smul_eq_bot_of_length_lt_top
    (R : Type*) [CommRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M]
    (h : Module.length R M < ⊤) :
    ∃ n : ℕ, IsLocalRing.maximalIdeal R ^ n • (⊤ : Submodule R M) = ⊥ := by
  have hfin : IsFiniteLength R M := by
    rw [← Module.length_ne_top_iff]
    exact ne_of_lt h
  exact exists_pow_maximalIdeal_smul_eq_bot_of_isFiniteLength R M hfin

/-- For a local ring `R` with maximal ideal `m`, if `m ^ n M ≠ 0` for every `n ≥ 0` then the
length of the `R`-module `M` is `∞`. -/
theorem length_eq_top_of_forall_pow_maximalIdeal_smul_ne_bot
    (R : Type*) [CommRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M]
    (h : ∀ n : ℕ, IsLocalRing.maximalIdeal R ^ n • (⊤ : Submodule R M) ≠ ⊥) :
    Module.length R M = ⊤ := by
  by_contra hne
  have hlt : Module.length R M < ⊤ := lt_of_le_of_ne le_top hne
  obtain ⟨n, hn⟩ := exists_pow_maximalIdeal_smul_eq_bot_of_length_lt_top R M hlt
  exact h n hn

-- ===== merged from StacksDraft.Ch10.Sec52.Tag00J0 =====

/-!
# Finite length of a module killed by a power of a finitely generated maximal ideal

Let `R` be a commutative ring with a finitely generated maximal ideal `m`, and let `M` be a
finite `R`-module with `m ^ n • M = 0` for some `n`. Then `M` has finite length over `R`. The
argument is an induction on `n` along the short exact sequences
`0 → m • M → M → M ⧸ m • M → 0`, whose two outer terms are killed by `m ^ n` and by `m`
respectively; a module killed by `m` is a finite-dimensional vector space over the residue
field `R ⧸ m`.
-/

@[expose] public section

universe u v

/-- When `M` carries compatible `R`- and `(R⧸m)`-module structures, the lattices of
`R`-submodules and `(R⧸m)`-submodules of `M` are order-isomorphic. -/
def submoduleOrderIsoOfScalarTower
    {R : Type*} [CommRing R] (m : Ideal R)
    {M : Type*} [AddCommGroup M] [Module R M] [Module (R ⧸ m) M]
    [IsScalarTower R (R ⧸ m) M] :
    Submodule (R ⧸ m) M ≃o Submodule R M where
  toFun := Submodule.restrictScalars R
  invFun N :=
    { carrier := N
      add_mem' := N.add_mem
      zero_mem' := N.zero_mem
      smul_mem' := fun r x hx => by
        obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
        rw [show (Ideal.Quotient.mk m s : R ⧸ m) • x = s • x from
          IsScalarTower.algebraMap_smul (R ⧸ m) s x]
        exact N.smul_mem s hx }
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_rel_iff' := ⟨fun h _ hx => h hx, fun h _ hx => h hx⟩

/-- If a maximal ideal `m` annihilates the finite module `M`, then `M` has finite length:
pass to `R⧸m`, a field, where length agrees with finite vector-space dimension. -/
@[ega "0 16.2.1" "finite length of M/mM"]
lemma length_lt_top_of_isMaximal_smul_top_eq_bot
    {R : Type*} [CommRing R] (m : Ideal R) [m.IsMaximal]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hbot : m • (⊤ : Submodule R M) = ⊥) :
    Module.length R M < ⊤ := by
  have htor : Module.IsTorsionBySet R M (m : Set R) := fun x r => by
    have h : r.val • x ∈ m • (⊤ : Submodule R M) :=
      Submodule.smul_mem_smul r.property Submodule.mem_top
    rw [hbot] at h
    simpa using h
  let : Field (R ⧸ m) := Ideal.Quotient.field m
  let : Module (R ⧸ m) M := htor.module
  have : IsScalarTower R (R ⧸ m) M := htor.isScalarTower
  have : Module.Finite (R ⧸ m) M := Module.Finite.of_restrictScalars_finite R (R ⧸ m) M
  have hlen : Module.length R M = Module.length (R ⧸ m) M := by
    unfold Module.length
    congr 1
    exact (Order.krullDim_eq_of_orderIso (submoduleOrderIsoOfScalarTower m)).symm
  rw [hlen, Module.length_eq_finrank (R ⧸ m) M]
  exact WithTop.coe_lt_top _

/-- `m` annihilates the quotient `M ⧸ (m • ⊤)`. -/
lemma smul_top_quotient_eq_bot
    {R : Type*} [CommRing R] (m : Ideal R)
    {M : Type*} [AddCommGroup M] [Module R M] :
    m • (⊤ : Submodule R (M ⧸ (m • (⊤ : Submodule R M)))) = ⊥ := by
  rw [eq_bot_iff]
  refine Submodule.smul_le.mpr fun a ha q _ => ?_
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (m • (⊤ : Submodule R M)) q
  rw [Submodule.mem_bot, ← map_smul]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.smul_mem_smul ha trivial)

/-- If `m ^ n • ⊤_M = 0` for a finitely generated maximal ideal `m`, then the finite `R`-module
`M` has finite length. -/
@[ega "0 16.1.10" "special case",
  ega "0 16.2.1" "finite length of M/q^nM",
  sga "6 X 1.1.2" "special case"]
lemma length_lt_top_of_pow_smul_top
    {R : Type u} [CommRing R]
    (m : Ideal R) [m.IsMaximal] (hm : m.FG)
    (n : ℕ) :
    ∀ {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M],
      m ^ n • (⊤ : Submodule R M) = ⊥ → Module.length R M < ⊤ := by
  induction n with
  | zero =>
    intros M _ _ _ hn
    rw [pow_zero, Submodule.one_smul] at hn
    rw [← Module.length_top, hn]
    simp [Module.length_eq_zero]
  | succ n ih =>
    intros M _ _ _ hn
    set N : Submodule R M := m • (⊤ : Submodule R M)
    have : Module.Finite R N :=
      Module.Finite.iff_fg.mpr ((Module.finite_def.mp inferInstance).smul hm)
    have : Module.Finite R (M ⧸ N) := Module.Finite.quotient R N
    have hlenN : Module.length R N < ⊤ := by
      apply ih
      rw [smul_top_eq_bot_iff_smul_eq_bot, ← hn, pow_succ, mul_smul]
    have hlenQ : Module.length R (M ⧸ N) < ⊤ :=
      length_lt_top_of_isMaximal_smul_top_eq_bot m (smul_top_quotient_eq_bot m)
    rw [Module.length_eq_add_of_exact N.subtype N.mkQ
      (Submodule.injective_subtype N) (Submodule.mkQ_surjective N)
      (LinearMap.exact_subtype_mkQ N)]
    exact ENat.add_lt_top.mpr ⟨hlenN, hlenQ⟩

/-- **Stacks 00J0.** Let `R` be a commutative ring with finitely generated maximal ideal `m`.
If `M` is a finite `R`-module with `m ^ n • M = 0` for some `n`, then `length_R M < ∞`. -/
@[stacks 00J0]
theorem length_lt_top_of_pow_smul_eq_bot
    {R : Type*} [CommRing R]
    (m : Ideal R) [m.IsMaximal] (hm : m.FG)
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (n : ℕ) (hn : m ^ n • (⊤ : Submodule R M) = ⊥) :
    Module.length R M < ⊤ :=
  length_lt_top_of_pow_smul_top m hm n hn


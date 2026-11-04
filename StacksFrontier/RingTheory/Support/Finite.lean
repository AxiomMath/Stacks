module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Support.Basic
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.PicardGroup
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
public import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Support
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Sheaves.Presheaf

/-!
# The support of a finite module as a union of closed sets

Let `A` be a commutative Noetherian ring and `M` a finite `A`-module. Choose a
filtration `0 = M₀ ⊆ M₁ ⊆ ⋯ ⊆ M_n = M` with `M_{i+1} / Mᵢ ≅ A / 𝔭ᵢ` for primes
`𝔭ᵢ`. The main result is `Supp(M) = ⋃ᵢ V(𝔭ᵢ)`; in particular each `𝔭ᵢ` lies in
`Supp(M)`.

The notions used are Mathlib's: `Module.support A M ⊆ PrimeSpectrum A` is the
set of primes `𝔭` at which the localization of `M` is nonzero;
`PrimeSpectrum.zeroLocus s` is the set of primes containing `s`, so for an ideal
`I` it is `V(I) = {𝔭 | I ⊆ 𝔭}`; and
`Submodule.IsQuotientEquivQuotientPrime N₁ N₂` says that `N₁ ≤ N₂` and
`N₂ ⧸ N₁` is isomorphic to `A ⧸ p` for some prime `p`. The filtration itself is
packaged as a `RelSeries` for that relation with `s.head = ⊥` and `s.last = ⊤`.

## Indexing

The series `s` has `s.length` steps and `s.length + 1` vertices. The primes are
indexed by the steps `i : Fin s.length`; step `i` relates the vertex
`i.castSucc` to the vertex `i.succ`, matching the inclusion `Mᵢ ⊆ M_{i+1}` whose
quotient is `A ⧸ 𝔭ᵢ`.
-/

@[expose] public section

/-- The support of a module isomorphic to `R ⧸ I` is the zero locus `V(I)`. -/
private theorem support_eq_zeroLocus_of_equiv_quotient {R : Type*} [CommRing R] {N : Type*}
    [AddCommGroup N] [Module R N] {I : Ideal R} (e : N ≃ₗ[R] R ⧸ I) :
    Module.support R N = PrimeSpectrum.zeroLocus (I : Set R) := by
  rw [e.support_eq, Module.support_eq_zeroLocus, Ideal.annihilator_quotient]

open Module PrimeSpectrum in
/-- Core step (Stacks 00L3 applied to a single inclusion `N₁ ≤ N₂` whose
quotient is `A / 𝔭`): the support of `N₂` is the support of `N₁` together with
`V(𝔭)`. Uses the short exact sequence `0 → N₁ → N₂ → N₂/N₁ → 0`. -/
theorem support_eq_support_union_zeroLocus
    (A : Type*) [CommRing A] (M : Type*) [AddCommGroup M] [Module A M]
    [IsNoetherianRing A] [Module.Finite A M]
    (N₁ N₂ : Submodule A M) (hle : N₁ ≤ N₂)
    (q : PrimeSpectrum A)
    (e : (N₂ ⧸ N₁.submoduleOf N₂) ≃ₗ[A] A ⧸ q.asIdeal) :
    Module.support A N₂
      = Module.support A N₁ ∪ PrimeSpectrum.zeroLocus (q.asIdeal : Set A) := by
  -- Short exact sequence `0 → N₁.submoduleOf N₂ → N₂ → N₂ ⧸ N₁.submoduleOf N₂ → 0`,
  -- via `Stacks 00L3` (`Module.support_of_exact`).
  rw [Module.support_of_exact (LinearMap.exact_subtype_mkQ (N₁.submoduleOf N₂))
      (Submodule.subtype_injective _) (Submodule.mkQ_surjective _),
    support_eq_zeroLocus_of_equiv_quotient e]
  congr 1
  exact (Submodule.comapSubtypeEquivOfLe hle).support_eq

open Module PrimeSpectrum in
/-- Induction along the filtration: the support of the `m`-th submodule
`Mₘ = s.toFun m` is the union of `V(𝔭ᵢ)` over the steps `i` strictly below `m`. -/
theorem support_toFun_eq_iUnion_zeroLocus
    (A : Type*) [CommRing A] (M : Type*) [AddCommGroup M] [Module A M]
    [IsNoetherianRing A] [Module.Finite A M]
    (s : RelSeries {(N₁, N₂) : Submodule A M × Submodule A M |
          N₁.IsQuotientEquivQuotientPrime N₂})
    (hhead : s.head = ⊥)
    (p : Fin s.length → PrimeSpectrum A)
    (hp : ∀ i : Fin s.length,
      Nonempty (((s.toFun i.succ) ⧸ (s.toFun i.castSucc).submoduleOf (s.toFun i.succ))
        ≃ₗ[A] A ⧸ (p i).asIdeal)) :
    ∀ m : ℕ, (hm : m < s.length + 1) →
      Module.support A (s.toFun ⟨m, hm⟩) =
        ⋃ (i : Fin s.length) (_ : (i : ℕ) < m),
          PrimeSpectrum.zeroLocus ((p i).asIdeal : Set A) := by
  intro m
  induction m with
  | zero =>
    intro hm
    -- `M₀ = s.head = ⊥`, support is empty; RHS union is empty.
    rw [show s.toFun ⟨0, hm⟩ = ⊥ from hhead, Module.support_eq_empty_iff.mpr inferInstance]
    simp
  | succ k ih =>
    intro hm
    have hk : k < s.length := Nat.lt_of_succ_lt_succ hm
    have hkm : k < s.length + 1 := Nat.lt_succ_of_lt hk
    set i : Fin s.length := ⟨k, hk⟩
    -- Identify the two vertices with the endpoints of step `i`.
    have hcast : s.toFun ⟨k, hkm⟩ = s.toFun i.castSucc := by congr 1
    rw [show s.toFun ⟨k + 1, hm⟩ = s.toFun i.succ by congr 1,
      support_eq_support_union_zeroLocus A M _ _ (s.step i).left (p i) (hp i).some, ← hcast, ih hkm]
    ext x
    simp only [Set.mem_union, Set.mem_iUnion, exists_prop, Nat.lt_add_one_iff_lt_or_eq,
      or_and_right, exists_or]
    exact or_congr_right ⟨fun hx => ⟨i, rfl, hx⟩, fun ⟨j, hj, hx⟩ => (Fin.ext hj : j = i) ▸ hx⟩

open Module PrimeSpectrum in
/-- **Stacks 00L4, main statement.** With the filtration data of Stacks 00L0,
the support of `M` is the union of the closed sets `V(𝔭ᵢ)`. -/
@[stacks 00L4]
theorem support_eq_iUnion_zeroLocus
    (A : Type*) [CommRing A] (M : Type*) [AddCommGroup M] [Module A M]
    [IsNoetherianRing A] [Module.Finite A M]
    (s : RelSeries {(N₁, N₂) : Submodule A M × Submodule A M |
          N₁.IsQuotientEquivQuotientPrime N₂})
    (hhead : s.head = ⊥) (hlast : s.last = ⊤)
    (p : Fin s.length → PrimeSpectrum A)
    (hp : ∀ i : Fin s.length,
      Nonempty (((s.toFun i.succ) ⧸ (s.toFun i.castSucc).submoduleOf (s.toFun i.succ))
        ≃ₗ[A] A ⧸ (p i).asIdeal)) :
    Module.support A M
      = ⋃ i : Fin s.length, PrimeSpectrum.zeroLocus ((p i).asIdeal : Set A) := by
  -- `support M = support ↥⊤` and `⊤ = s.last = s.toFun s.length`.
  rw [← Submodule.topEquiv.support_eq, ← hlast]
  exact (support_toFun_eq_iUnion_zeroLocus A M s hhead p hp s.length (Nat.lt_succ_self _)).trans
    (Set.iUnion_congr fun i => by simp [i.isLt])

open Module PrimeSpectrum in
/-- **Stacks 00L4, "in particular".** Each prime `𝔭ᵢ` lies in the support of
`M`. -/
@[stacks 00L4]
theorem mem_support_of_isQuotientEquivQuotientPrime_series
    (A : Type*) [CommRing A] (M : Type*) [AddCommGroup M] [Module A M]
    [IsNoetherianRing A] [Module.Finite A M]
    (s : RelSeries {(N₁, N₂) : Submodule A M × Submodule A M |
          N₁.IsQuotientEquivQuotientPrime N₂})
    (hhead : s.head = ⊥) (hlast : s.last = ⊤)
    (p : Fin s.length → PrimeSpectrum A)
    (hp : ∀ i : Fin s.length,
      Nonempty (((s.toFun i.succ) ⧸ (s.toFun i.castSucc).submoduleOf (s.toFun i.succ))
        ≃ₗ[A] A ⧸ (p i).asIdeal)) :
    ∀ i : Fin s.length, p i ∈ Module.support A M := by
  -- Each `𝔭ᵢ ∈ V(𝔭ᵢ)`, and the union of the `V(𝔭ᵢ)` is `support M` by
  -- `support_eq_iUnion_zeroLocus`.
  intro i
  rw [support_eq_iUnion_zeroLocus A M s hhead hlast p hp]
  exact Set.mem_iUnion.mpr ⟨i, (PrimeSpectrum.mem_zeroLocus _ _).mpr (le_refl _)⟩

/-!
# Support of a finite module over a Noetherian local ring

Let `R` be a commutative Noetherian local ring with maximal ideal `𝔪`, and let
`M` be a nonzero finite `R`-module. The main result is

`Supp(M) = {𝔪}  ↔  M` has finite length over `R`.

Here the support of `M` is `Supp(M) = {𝔭 ∈ Spec(R) | M_𝔭 ≠ 0}`, and `M` has
finite length when it admits a finite chain of submodules
`0 = M₀ ⊊ M₁ ⊊ ⋯ ⊊ M_ℓ = M` with every quotient `Mᵢ ⧸ Mᵢ₋₁` simple
(equivalently, `M` is both Noetherian and Artinian).

In `{𝔪}` the maximal ideal is regarded as a point of `Spec(R)`, which is legitimate
because maximal ideals are prime. The hypothesis `M ≠ 0` is needed: for `M = 0` the
support is empty while the length is `0`, so the equivalence with the nonempty
singleton `{𝔪}` would fail.

The Mathlib notions modelling these are `Module.support R M : Set (PrimeSpectrum R)`,
`Module.Finite R M`, `IsFiniteLength R M`, and `IsLocalRing.closedPoint R` for `𝔪`
viewed as a point of `Spec(R)`. Nonvanishing of `M` is the typeclass `Nontrivial M`.
-/

@[expose] public section

open Module

/-- In a local ring, the Zariski-closed set `V(𝔪)` cut out by the maximal ideal is
exactly the singleton consisting of the closed point. This is the geometric form of
"`𝔪` is the unique maximal ideal": a prime `q` contains `𝔪` iff `q = 𝔪` (`𝔪` is
maximal, hence `𝔪 ≤ q` forces `q = 𝔪`; conversely `𝔪 ⊆ 𝔪`). -/
@[ega "I 1.1.7" "special case",
  ega "I 2.4.1" "partial",
  ega "I 2.4.5" "more general",
  ega "II 7.1.5" "a is closed"]
theorem zeroLocus_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R] :
    PrimeSpectrum.zeroLocus (IsLocalRing.maximalIdeal R : Set R) =
      {IsLocalRing.closedPoint R} := by
  apply le_antisymm
  · intro q hq
    simp only [PrimeSpectrum.mem_zeroLocus, Set.mem_singleton_iff] at *
    exact PrimeSpectrum.ext (le_antisymm (IsLocalRing.le_maximalIdeal q.isPrime.ne_top) hq)
  · rintro q rfl
    exact fun x hx => hx

/-- Over a local ring, the support of a simple module is the closed point. -/
theorem support_eq_closedPoint_of_isSimpleModule (R : Type*) [CommRing R] [IsLocalRing R]
    (S : Type*) [AddCommGroup S] [Module R S] [IsSimpleModule R S] :
    support R S = {IsLocalRing.closedPoint R} := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule R S›
  rw [support_eq_zeroLocus_of_equiv_quotient e, IsLocalRing.eq_maximalIdeal hI]
  exact zeroLocus_maximalIdeal

-- ===========================================================================
-- Direction (⇐): finite length ⇒ support = {𝔪}.
-- ===========================================================================

/-- A nonzero finite-length module `M` over a local ring `R` has support the single
closed point `{𝔪}`.

The proof inducts on `IsFiniteLength`, whose constructors are `of_subsingleton` and
`of_simple_quotient`. A subsingleton has empty support (`Module.support_eq_empty_iff`). A
simple module over a local ring is `R ⧸ 𝔪`, whose support is `V(𝔪) = {𝔪}`
(`support_eq_closedPoint_of_isSimpleModule`), and support is additive along
`0 → N → M → M ⧸ N → 0` (`Module.support_of_exact`); so `support R M ⊆ {𝔪}`. Since `M` is
nontrivial, its support is nonempty, hence equal to `{𝔪}`. -/
@[ega "0 16.1.10" "special case", ega "IV 4.7.7" "partial"]
theorem support_of_isFiniteLength {R : Type*} [CommRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (h : IsFiniteLength R M) :
    Module.support R M = {IsLocalRing.closedPoint R} := by
  have hsub : ∀ {N : Type _} [AddCommGroup N] [Module R N], IsFiniteLength R N →
      support R N ⊆ {IsLocalRing.closedPoint R} := by
    intro N _ _ hN
    induction hN with
    | of_subsingleton => simp [Module.support_eq_empty_iff.mpr ‹_›]
    | of_simple_quotient K ih =>
        rename_i P _ _ Q _
        rw [Module.support_of_exact (LinearMap.exact_subtype_mkQ Q) Q.subtype_injective
          Q.mkQ_surjective]
        exact Set.union_subset ih (support_eq_closedPoint_of_isSimpleModule R _).subset
  refine (Set.subset_singleton_iff_eq.mp (hsub h)).resolve_left fun hempty => ?_
  exact not_subsingleton M (Module.support_eq_empty_iff.mp hempty)

-- ===========================================================================
-- Direction (⇒): support = {𝔪} ⇒ finite length.
-- ===========================================================================

/-- If a module has support the closed point of a local ring, then any subquotient
isomorphic to `R ⧸ q` for a prime `q` is simple. -/
theorem isSimpleModule_of_equiv_quotientPrime {R : Type*} [CommRing R]
    [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (h : Module.support R M = {IsLocalRing.closedPoint R}) {N x : Submodule R M}
    {q : PrimeSpectrum R} (e : (↥x ⧸ N.submoduleOf x) ≃ₗ[R] R ⧸ q.asIdeal) :
    IsSimpleModule R (↥x ⧸ N.submoduleOf x) := by
  have hqmem : q ∈ support R (↥x ⧸ N.submoduleOf x) := by
    rw [support_eq_zeroLocus_of_equiv_quotient e]
    exact (PrimeSpectrum.mem_zeroLocus _ _).mpr le_rfl
  have hmem : q ∈ ({IsLocalRing.closedPoint R} : Set (PrimeSpectrum R)) :=
    h ▸ support_submodule_subset x
      (Module.support_subset_of_surjective _ (Submodule.mkQ_surjective _) hqmem)
  have hmax : q.asIdeal.IsMaximal :=
    (Set.mem_singleton_iff.mp hmem) ▸ IsLocalRing.maximalIdeal.isMaximal R
  have : IsSimpleModule R (R ⧸ q.asIdeal) :=
    isSimpleModule_iff_quot_maximal.mpr ⟨_, hmax, ⟨LinearEquiv.refl _ _⟩⟩
  exact IsSimpleModule.congr e

/-- If a finite module `M` over a Noetherian local ring `R` has support equal to the
single closed point `{𝔪}`, then `M` has finite length.

By `IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime` there is a filtration
`0 = M₀ ⊆ M₁ ⊆ ⋯ ⊆ M_ℓ = M` with `Mᵢ ⧸ Mᵢ₋₁ ≃ R ⧸ 𝔭ᵢ` for primes `𝔭ᵢ`. Each `𝔭ᵢ` lies in
the support of the subquotient `R ⧸ 𝔭ᵢ` of `M`, hence in `Supp(M) = {𝔪}`, so every factor is
the simple module `R ⧸ 𝔪` (`isSimpleModule_of_equiv_quotientPrime`). Induction along the
filtration with `IsFiniteLength.of_simple_quotient` then shows that `M` has finite length. -/
@[ega "0 16.1.10" "special case", ega "IV 4.7.7" "partial", sga "6 X 1.1.2" "special case"]
theorem isFiniteLength_of_support {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (h : Module.support R M = {IsLocalRing.closedPoint R}) :
    IsFiniteLength R M := by
  obtain ⟨s, hhead, hlast⟩ := IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime R M
  -- general claim by induction
  have key : ∀ (t : RelSeries {(N₁, N₂) : Submodule R M × Submodule R M |
      N₁.IsQuotientEquivQuotientPrime N₂}),
      t.head = ⊥ → IsFiniteLength R ↥(t.last) := by
    intro t
    induction t using RelSeries.inductionOn' with
    | singleton x =>
        intro hx
        rw [RelSeries.head_singleton] at hx
        rw [RelSeries.last_singleton, hx]
        exact IsFiniteLength.of_subsingleton
    | snoc p x hxr ih =>
        intro hhd
        rw [RelSeries.head_snoc] at hhd
        rw [RelSeries.last_snoc]
        obtain ⟨hle, q, ⟨e⟩⟩ := hxr
        have := isSimpleModule_of_equiv_quotientPrime h e
        exact IsFiniteLength.of_simple_quotient
          ((Submodule.submoduleOfEquivOfLe hle).symm.isFiniteLength (ih hhd))
  -- apply
  exact Submodule.topEquiv.isFiniteLength (hlast ▸ key s hhead)

/-- Stacks 00L5. Over a Noetherian local ring `R` with maximal ideal `m`, a nonzero
finite `R`-module `M` has support equal to the singleton `{m}` if and only if `M`
has finite length over `R`. -/
@[stacks 00L5,
  ega "0 16.1.10" "local ring case",
  ega "IV 4.7.7" "special case",
  sga "6 X 1.1.2" "special case"]
theorem support_point {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] :
    Module.support R M = {IsLocalRing.closedPoint R} ↔ IsFiniteLength R M :=
  -- The biconditional is exactly the two named directions above.
  ⟨isFiniteLength_of_support, support_of_isFiniteLength⟩

/-!
# Modules annihilated by a power of an ideal

Let `R` be a Noetherian ring, `I ⊆ R` an ideal and `M` a finite `R`-module.
The main result is that some power of `I` annihilates `M` if and only if the
support of `M` is contained in the zero locus of `I`.

Here `Module.support R M : Set (PrimeSpectrum R)` is the set of primes `p` at
which the localization of `M` is nonzero, `PrimeSpectrum.zeroLocus (I : Set R)`
is `V(I) = {p | I ⊆ p}`, and the submodule `Iⁿ M` of `M` is the pointwise
scalar action `(I ^ n) • (⊤ : Submodule R M)`, so that `Iⁿ M = 0` is written
`(I ^ n) • ⊤ = ⊥`.
-/

@[expose] public section

/-- For a finite module `M` over a Noetherian ring `R` and an ideal `I ⊆ R`,
some power of `I` annihilates `M` if and only if the support of `M` is contained
in the zero locus of `I`. -/
@[stacks 00L6, ega "I 9.3.4" "affine case"]
theorem main_theorem_00l6 {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M] (I : Ideal R) :
    (∃ n : ℕ, (I ^ n) • (⊤ : Submodule R M) = ⊥) ↔
      Module.support R M ⊆ PrimeSpectrum.zeroLocus (I : Set R) := by
  simp_rw [← Submodule.le_annihilator_iff, Submodule.annihilator_top]
  rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff]
  refine ⟨fun ⟨n, hn⟩ x hx ↦ ⟨n, hn (Ideal.pow_mem_pow hx n)⟩, fun h ↦ ?_⟩
  exact Ideal.exists_pow_le_of_le_radical_of_fg h (IsNoetherian.noetherian I)

/-- A finite module over a Noetherian local ring whose support is contained in the closed point
has finite length: either the support is empty, and the module vanishes, or it is the whole of
`{𝔪}` and `isFiniteLength_of_support` applies. -/
theorem isFiniteLength_of_support_subset {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (h : Module.support R M ⊆ {IsLocalRing.closedPoint R}) :
    IsFiniteLength R M := by
  rcases subsingleton_or_nontrivial M with _ | _
  · exact IsFiniteLength.of_subsingleton
  · exact isFiniteLength_of_support
      (h.antisymm (Set.singleton_subset_iff.mpr (IsLocalRing.closedPoint_mem_support R M)))

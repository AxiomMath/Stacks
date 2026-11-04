module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section


/-!
# Unique factorization domains

Associates and equal principal ideals, factorization into irreducibles under the ascending
chain condition for principal ideals, the definition of a unique factorization domain and its
characterization by existence and uniqueness of irreducible factorizations, the criterion
"irreducible implies prime", that a principal ideal domain is a UFD and a Dedekind domain,
that a UFD is integrally closed, that polynomial rings over a UFD are UFDs, and that a UFD
satisfies the ascending chain condition for principal ideals, are all Mathlib's.

What remains here is Stacks 0BUE: the polynomial ring over a domain satisfying ACCP again
satisfies ACCP, in both the monoid-theoretic (`WfDvdMonoid`) and the ideal-theoretic form.
-/

-- The former @[stacks 034Q] declaration is now the Mathlib theorem.
add_to_stacks 034Q "associates generate the same principal ideal"
  Ideal.span_singleton_eq_span_singleton

-- The former @[stacks 034R] declarations are now the Mathlib theorems: ACC on principal ideals
-- gives `WfDvdMonoid`, which gives a factorization into irreducibles.
add_to_stacks 034R "ACC on principal ideals implies `WfDvdMonoid`"
  WfDvdMonoid.of_setOfPred_isPrincipal_wellFoundedOn_gt
add_to_stacks 034R "a nonzero nonunit factors into irreducibles"
  WfDvdMonoid.not_isUnit_iff_exists_factors_eq

-- The former @[stacks_fixed 034S] structure is now the Mathlib class, whose characterization by
-- existence and uniqueness of irreducible factorizations is the source's definition.
add_to_stacks 034S "unique factorization domains" UniqueFactorizationMonoid
add_to_sga "2 XI 3.10" UniqueFactorizationMonoid
add_to_ega "IV 21.7.7" UniqueFactorizationMonoid
add_to_stacks 034S "existence and uniqueness of irreducible factorizations characterize a UFD"
  UniqueFactorizationMonoid.of_existsUnique_irreducible_factors
add_to_stacks 034S "uniqueness of irreducible factorizations, up to associates and permutation"
  UniqueFactorizationMonoid.factors_unique

-- The former @[stacks 034T] declarations are now the Mathlib theorems.
add_to_stacks 034T "in a UFD every irreducible element is prime"
  UniqueFactorizationMonoid.irreducible_iff_prime
add_to_stacks 034T "factorization into primes gives a UFD"
  UniqueFactorizationMonoid.of_exists_prime_factors

-- The former @[stacks 034V] declaration is now the Mathlib instance.
add_to_stacks 034V "a principal ideal domain is a UFD"
  PrincipalIdealRing.to_uniqueFactorizationMonoid

-- The former @[stacks 0AFV] declaration is now the Mathlib instance.
add_to_stacks 0AFV "a UFD is integrally closed" UniqueFactorizationMonoid.instIsIntegrallyClosed

-- The former @[stacks 0AUQ] declaration is now the Mathlib theorem.
add_to_stacks 0AUQ "a principal ideal domain is a Dedekind domain"
  IsPrincipalIdealRing.isDedekindDomain
add_to_ega "III 7.4.3" "special case" IsPrincipalIdealRing.isDedekindDomain

-- The former @[stacks 0BC1] declarations are now the Mathlib instances.
add_to_stacks 0BC1 "a polynomial ring over a UFD is a UFD" Polynomial.uniqueFactorizationMonoid
add_to_stacks 0BC1 "a multivariate polynomial ring over a UFD is a UFD"
  MvPolynomial.uniqueFactorizationMonoid

-- The former @[stacks 0BUD] declaration is now the Mathlib theorem, which states the ascending
-- chain condition as well-foundedness of `>` on the principal ideals.
add_to_stacks 0BUD "a UFD satisfies ACC on principal ideals"
  Ideal.setOfPred_isPrincipal_wellFoundedOn_gt


-- ===== merged from StacksDraft.Ch10.Sec120.Tag0BUE =====

/-!
# Factoring in a polynomial ring

Let `R` be a commutative domain satisfying the ascending chain condition for principal
ideals (ACCP). Then the polynomial ring `R[X]` also satisfies ACCP.
(Stacks Lemma 10.120.15, tag `0BUE`.)

In a commutative domain ACCP is equivalent to the monoid-theoretic predicate
`WfDvdMonoid R`, via the correspondence between principal-ideal inclusions and
divisibility (`Ideal.span_singleton_le_span_singleton` and
`Ideal.span_singleton_eq_span_singleton`).

The headline theorem is `polynomial_wfDvdMonoid`; the ideal-theoretic
re-statement `polynomial_accp_ideal` is provided for direct comparison with the
Stacks formulation.
-/

@[expose] public section

/-- Headline: if `R` is a commutative domain satisfying ACCP (`WfDvdMonoid R`),
then `R[X]` also satisfies ACCP. -/
@[stacks 0BUE]
theorem polynomial_wfDvdMonoid {R : Type*} [CommRing R] [IsDomain R] [WfDvdMonoid R] :
    WfDvdMonoid (Polynomial R) := Polynomial.wfDvdMonoid

/-- A partial order is `WellFoundedLT` iff every antitone sequence in it stabilizes. -/
private theorem wellFoundedLT_iff_antitone_stabilizes {α : Type*} [PartialOrder α] :
    WellFoundedLT α ↔ ∀ g : ℕ → α, Antitone g → ∃ n, ∀ m, n ≤ m → g m = g n :=
  (wellFoundedGT_iff_monotone_chain_condition (α := αᵒᵈ)).trans
    ⟨fun h g hg => (h ⟨OrderDual.toDual ∘ g, hg.dual_right⟩).imp fun _ hn m hm => (hn m hm).symm,
      fun h a => (h (OrderDual.ofDual ∘ a) a.monotone.dual_right).imp
        fun _ hn m hm => (hn m hm).symm⟩

/-- Principal ideals are ordered like the associated classes of their generators. -/
private theorem span_singleton_le_iff_mk_le {S : Type*} [CommRing S] [IsDomain S] (a b : S) :
    Ideal.span {a} ≤ Ideal.span {b} ↔ Associates.mk b ≤ Associates.mk a :=
  Ideal.span_singleton_le_span_singleton.trans Associates.mk_le_mk_iff_dvd.symm

/-- Principal ideals are equal iff the associated classes of their generators are. -/
private theorem span_singleton_eq_iff_mk_eq {S : Type*} [CommRing S] [IsDomain S] (a b : S) :
    Ideal.span {a} = Ideal.span {b} ↔ Associates.mk a = Associates.mk b :=
  Ideal.span_singleton_eq_span_singleton.trans Associates.mk_eq_mk_iff_associated.symm

/-- In a commutative domain that is a `WfDvdMonoid`, every ascending chain of
principal ideals stabilizes. -/
private theorem accp_of_wfDvdMonoid {S : Type*} [CommRing S] [IsDomain S] [WfDvdMonoid S]
    (f : ℕ → Ideal S) (hp : ∀ i, (f i).IsPrincipal) (hm : ∀ i, f i ≤ f (i + 1)) :
    ∃ n, ∀ m, n ≤ m → f m = f n := by
  set a : ℕ → S := fun i => (hp i).principal.choose
  have hfa : ∀ i, f i = Ideal.span {a i} := fun i => (hp i).principal.choose_spec
  have : WellFoundedLT (Associates S) := WfDvdMonoid.iff_wellFounded_associates.mp ‹_›
  obtain ⟨n, hn⟩ := wellFoundedLT_iff_antitone_stabilizes.mp this (fun i => Associates.mk (a i))
    (antitone_nat_of_succ_le fun i =>
      (span_singleton_le_iff_mk_le _ _).mp (hfa i ▸ hfa (i + 1) ▸ hm i))
  exact ⟨n, fun m hmn => by rw [hfa m, hfa n, span_singleton_eq_iff_mk_eq]; exact hn m hmn⟩

/-- Reverse direction (ideal-theoretic ACCP ⇒ `WfDvdMonoid`) for a commutative
domain. -/
private theorem wfDvdMonoid_of_accp {R : Type*} [CommRing R] [IsDomain R]
    (hR : ∀ f : ℕ → Ideal R, (∀ i, (f i).IsPrincipal) → (∀ i, f i ≤ f (i + 1)) →
      ∃ n, ∀ m, n ≤ m → f m = f n) :
    WfDvdMonoid R := by
  rw [WfDvdMonoid.iff_wellFounded_associates]
  refine wellFoundedLT_iff_antitone_stabilizes.mpr fun g hganti => ?_
  choose b hb using fun i => Associates.mk_surjective (g i)
  obtain ⟨n, hn⟩ := hR (fun i => Ideal.span {b i}) (fun i => ⟨⟨b i, rfl⟩⟩)
    fun i => (span_singleton_le_iff_mk_le _ _).mpr (hb i ▸ hb (i + 1) ▸ hganti (Nat.le_succ i))
  exact ⟨n, fun m hmn => by rw [← hb m, ← hb n, ← span_singleton_eq_iff_mk_eq]; exact hn m hmn⟩

/-- Equivalent ideal-theoretic phrasing: if every ascending chain of principal ideals
in `R` stabilizes, then the same holds in `R[X]`. -/
theorem polynomial_accp_ideal {R : Type*} [CommRing R] [IsDomain R]
    (hR : ∀ f : ℕ → Ideal R, (∀ i, (f i).IsPrincipal) → (∀ i, f i ≤ f (i + 1)) →
      ∃ n, ∀ m, n ≤ m → f m = f n) :
    ∀ f : ℕ → Ideal (Polynomial R), (∀ i, (f i).IsPrincipal) → (∀ i, f i ≤ f (i + 1)) →
      ∃ n, ∀ m, n ≤ m → f m = f n :=
  have := wfDvdMonoid_of_accp hR
  accp_of_wfDvdMonoid

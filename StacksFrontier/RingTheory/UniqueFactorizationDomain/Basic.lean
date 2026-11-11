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
that a UFD is integrally closed, and that polynomial rings over a UFD are UFDs, are all
Mathlib's.

What remains here is Stacks 0BUE: the polynomial ring over a domain satisfying ACCP again
satisfies ACCP, in both the monoid-theoretic (`WfDvdMonoid`) and the ideal-theoretic form; and
Stacks 0BUD: a UFD, in the sense of existence and uniqueness of irreducible factorizations,
satisfies ACCP.
-/

/-! ### Stacks 034P

The definitions of associates, irreducible elements and prime elements of a domain, each compared
with Mathlib's notion (`Associated`, `Irreducible`, `Prime`). -/

section Elements

variable {R : Type*} [CommRing R]

/-- **Stacks 034P (1).** In a domain `R`, elements `x, y` are associates in the Stacks sense, that
is `x = u y` for a unit `u ∈ R^*`, exactly when they are associated in Mathlib's sense
(`Associated x y`, a unit `u` with `x * u = y`). -/
@[stacks 034P "(1) associates: `x = u y` for a unit `u`"]
theorem associated_iff_exists_unit_eq_mul [IsDomain R] {x y : R} :
    Associated x y ↔ ∃ u : Rˣ, x = u * y := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u⁻¹, by rw [mul_comm x, ← mul_assoc, Units.inv_mul, one_mul]⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u⁻¹, by rw [mul_comm (u : R), mul_assoc, Units.mul_inv, mul_one]⟩

/-- **Stacks 034P (2).** In a domain `R`, an element `x` is irreducible in the Stacks sense, that
is nonzero, not a unit, and whenever `x = y z` the factor `y` is a unit or an associate `y = u x`
(`u ∈ R^*`) of `x`, exactly when it is irreducible in Mathlib's sense (`Irreducible x`). -/
@[stacks 034P "(2) irreducible elements"]
theorem irreducible_iff_ne_zero_and_isUnit_or_eq_unit_mul [IsDomain R] {x : R} :
    Irreducible x ↔ x ≠ 0 ∧ ¬IsUnit x ∧
      ∀ y z : R, x = y * z → IsUnit y ∨ ∃ u : Rˣ, y = u * x := by
  constructor
  · intro hx
    refine ⟨hx.ne_zero, hx.not_isUnit, fun y z h => ?_⟩
    rcases hx.isUnit_or_isUnit h with hy | hz
    · exact Or.inl hy
    · refine Or.inr ⟨hz.unit⁻¹, ?_⟩
      rw [h, mul_comm y, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
  · rintro ⟨hx0, hxu, hx⟩
    refine ⟨hxu, fun y z h => ?_⟩
    rcases hx y z h with hy | ⟨u, rfl⟩
    · exact Or.inl hy
    · refine Or.inr (IsUnit.of_mul_eq_one_right (u : R) ?_)
      refine (mul_left_cancel₀ hx0 ?_).symm
      calc x * 1 = x := mul_one x
        _ = u * x * z := h
        _ = x * (u * z) := by ring

/-- **Stacks 034P (3).** In a domain `R`, an element `x` is prime in the Stacks sense, that is the
ideal `(x)` is a prime ideal, exactly when `x = 0` or `x` is prime in Mathlib's sense
(`Prime x`, which excludes `0`). The case `x ≠ 0` is Mathlib's `Ideal.span_singleton_prime`; the
case `x = 0` is that `(0)` is a prime ideal of a domain (`Ideal.isPrime_bot`). -/
@[stacks 034P "(3) prime elements"]
theorem Ideal.isPrime_span_singleton_iff_eq_zero_or_prime [IsDomain R] {x : R} :
    (Ideal.span {x}).IsPrime ↔ x = 0 ∨ Prime x := by
  by_cases hx : x = 0
  · subst hx
    simp only [Set.singleton_zero, Ideal.span_zero, true_or, iff_true]
    exact Ideal.isPrime_bot
  · rw [Ideal.span_singleton_prime hx]
    simp [hx]

end Elements

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

-- Stacks 034T in the source's terms is `irreducible_factors_unique_iff_forall_irreducible_prime`
-- below; Mathlib's forward direction, from existence and uniqueness of irreducible factorizations:
add_to_stacks 034T "existence and uniqueness of irreducible factorizations make irreducibles prime"
  irreducible_iff_prime_of_existsUnique_irreducible_factors

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

-- Stacks 0BUD is `accp_of_existsUnique_irreducible_factors` below, stated for a domain that is a
-- UFD in the sense of 034S. Its proof, as in Stacks, writes each nonzero element as a product of
-- primes, which is Mathlib's `WfDvdMonoid.of_exists_prime_factors`. The Mathlib theorem
-- `Ideal.setOfPred_isPrincipal_wellFoundedOn_gt` restates ACCP in ideal form for a domain
-- already known to be a `WfDvdMonoid`; it is not registered for 0BUD.
add_to_stacks 0BUD "factorization into primes gives a well-founded divisibility relation"
  WfDvdMonoid.of_exists_prime_factors


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

/-- **Stacks 034T.** Let `R` be a domain in which every nonzero nonunit factors into
irreducibles. Then `R` is a UFD in the sense of Stacks 034S (every nonzero nonunit has a
factorization into irreducibles, and two factorizations of the same nonzero nonunit into
irreducibles agree up to permutation and associates) if and only if every irreducible element
of `R` is prime. -/
@[stacks 034T "a domain with irreducible factorizations is a UFD iff irreducibles are prime"]
theorem irreducible_factors_unique_iff_forall_irreducible_prime {R : Type*} [CommRing R]
    [IsDomain R]
    (hfac : ∀ x : R, x ≠ 0 → ¬IsUnit x → ∃ f : Multiset R, (∀ a ∈ f, Irreducible a) ∧ f.prod = x) :
    ((∀ x : R, x ≠ 0 → ¬IsUnit x → ∃ f : Multiset R, (∀ a ∈ f, Irreducible a) ∧ f.prod = x) ∧
      ∀ x : R, x ≠ 0 → ¬IsUnit x → ∀ f g : Multiset R, (∀ a ∈ f, Irreducible a) →
        (∀ b ∈ g, Irreducible b) → f.prod = x → g.prod = x → Multiset.Rel Associated f g) ↔
      ∀ p : R, Irreducible p → Prime p := by
  constructor
  · rintro ⟨-, huniq⟩ p hp
    refine (irreducible_iff_prime_of_existsUnique_irreducible_factors (fun a ha => ?_)
      (fun f g hf hg hfg => ?_) p).1 hp
    · by_cases hu : IsUnit a
      · exact ⟨0, by simp, by simpa using (associated_one_iff_isUnit.2 hu).symm⟩
      · obtain ⟨f, hf, rfl⟩ := hfac a ha hu
        exact ⟨f, hf, Associated.refl _⟩
    · obtain ⟨u, hu⟩ := hfg
      induction g using Multiset.induction_on with
      | empty =>
        have hfu : IsUnit (f.prod * ↑u) := by rw [hu, Multiset.prod_zero]; exact isUnit_one
        have : f = 0 := Multiset.eq_zero_of_forall_notMem fun a ha => (hf a ha).not_isUnit
          (isUnit_of_dvd_unit (Multiset.dvd_prod ha) (isUnit_of_mul_isUnit_left hfu))
        rw [this]
        exact Multiset.Rel.zero
      | cons b g _ =>
        have hbu : Irreducible (b * ↑u⁻¹) :=
          (irreducible_mul_isUnit u⁻¹.isUnit).2 (hg b (Multiset.mem_cons_self _ _))
        have hg' : ∀ c ∈ (b * ↑u⁻¹) ::ₘ g, Irreducible c := by
          intro c hc
          rcases Multiset.mem_cons.1 hc with rfl | hc
          exacts [hbu, hg c (Multiset.mem_cons_of_mem hc)]
        have hprod : ((b * ↑u⁻¹) ::ₘ g).prod = f.prod := by
          rw [Multiset.prod_cons, mul_right_comm, ← Multiset.prod_cons, ← hu,
            Units.mul_inv_cancel_right]
        have hne : f.prod ≠ 0 := Multiset.prod_ne_zero fun h0 => not_irreducible_zero (hf 0 h0)
        have hnu : ¬IsUnit f.prod := fun h => hbu.not_isUnit
          (isUnit_of_dvd_unit (hprod ▸ Multiset.dvd_prod (Multiset.mem_cons_self _ _)) h)
        obtain ⟨a, f', hab, hf', rfl⟩ := Multiset.rel_cons_right.1
          (huniq _ hne hnu f _ hf hg' rfl hprod)
        exact Multiset.Rel.cons (hab.trans (associated_mul_unit_left b _ u⁻¹.isUnit)) hf'
  · intro hprime
    refine ⟨hfac, fun x _ _ f g hf hg hfx hgx => prime_factors_unique
      (fun a ha => hprime a (hf a ha)) (fun b hb => hprime b (hg b hb))
      (hfx.trans hgx.symm ▸ .refl _)⟩

/-- A UFD satisfies the ascending chain condition for principal ideals: if `R` is a domain in
which every nonzero element is, up to a unit, a product of irreducibles, uniquely up to
associates and order (the definition of a UFD, Stacks 034S), then every ascending chain of
principal ideals of `R` stabilizes. As in Stacks, the proof factors elements into primes. -/
@[stacks 0BUD]
theorem accp_of_existsUnique_irreducible_factors {R : Type*} [CommRing R] [IsDomain R]
    (eif : ∀ a : R, a ≠ 0 → ∃ f : Multiset R, (∀ b ∈ f, Irreducible b) ∧ Associated f.prod a)
    (uif : ∀ f g : Multiset R, (∀ x ∈ f, Irreducible x) → (∀ x ∈ g, Irreducible x) →
      Associated f.prod g.prod → Multiset.Rel Associated f g)
    (f : ℕ → Ideal R) (hp : ∀ i, (f i).IsPrincipal) (hm : ∀ i, f i ≤ f (i + 1)) :
    ∃ n, ∀ m, n ≤ m → f m = f n :=
  have := UniqueFactorizationMonoid.of_existsUnique_irreducible_factors eif uif
  have : WfDvdMonoid R :=
    .of_exists_prime_factors fun _ ha ↦ UniqueFactorizationMonoid.exists_prime_factors _ ha
  accp_of_wfDvdMonoid f hp hm

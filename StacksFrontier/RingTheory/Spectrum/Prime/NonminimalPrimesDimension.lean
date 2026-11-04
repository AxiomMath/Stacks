module

public import Mathlib.Order.KrullDimension
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Topology.KrullDimension
public import StacksFrontier.RingTheory.Spectrum.Prime.NonminimalPrimes
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The dimension of a set of primes and the drop to its nonminimal primes

A subset `T` of the prime spectrum of a commutative ring carries two dimensions: the Krull
dimension of its order dual, that is the supremum of lengths of chains of primes of `T`, and
the topological Krull dimension of `T` as a subspace. Sending a prime to the closure of the
corresponding point of `T` is a strictly monotone map from the order dual of `T` to the
irreducible closed subsets of `T`, so the first dimension is at most the second. Passing from
`T` to its nonminimal primes strictly decreases the dimension, since every chain of nonminimal
primes extends by a prime of `T` strictly below its bottom.

## Main definitions

* `PrimeSpectrum.primePointClosure` — the irreducible closed subset of `T` cut out by a point.
* `PrimeSpectrum.nonminimalDim` — the dimension of `T` as a natural number.

## Main results

* `PrimeSpectrum.krullDim_orderDual_le_topologicalKrullDim` — the order dimension of `T` is at
  most its topological dimension.
* `PrimeSpectrum.krullDim_orderDual_nonminimalPrimes_lt` and
  `PrimeSpectrum.nonminimalDim_nonminimalPrimes_lt` — the dimension strictly drops when one
  passes to the nonminimal primes of a nonempty set.

## Implementation notes

Chains of primes of `T` grow upward for inclusion but downward for specialization, so the
order-theoretic statements are phrased for the order dual of `T`. The natural-number valued
`nonminimalDim` normalizes both the dimension of the empty set and an infinite dimension to
`0`; it is only compared with the topological dimension under hypotheses that rule out the
infinite case.
-/

@[expose] public noncomputable section

universe u

namespace PrimeSpectrum

/-- The irreducible closed subset of a subset `T` of the prime spectrum obtained as the closure
of a point of `T`. -/
def primePointClosure {A : Type u} [CommRing A] (T : Set (PrimeSpectrum A)) (p : ↥T) :
    TopologicalSpace.IrreducibleCloseds (↥T) :=
  ⟨closure {p}, isIrreducible_singleton.closure, isClosed_closure⟩

/-- Taking the closure of a point is strictly monotone from the order dual of `T` to the
irreducible closed subsets of `T`: a smaller prime has a larger closure. -/
theorem primePointClosure_strictMono {A : Type u} [CommRing A] (T : Set (PrimeSpectrum A)) :
    StrictMono (fun p : (↥T)ᵒᵈ => primePointClosure T (OrderDual.ofDual p)) := by
  have key : ∀ a b : ↥T, a ∈ closure {b} → b ≤ a := fun _ _ h =>
    (le_iff_specializes _ _).mpr
      ((subtype_specializes_iff _ _).mp (specializes_iff_mem_closure.mpr h))
  apply Monotone.strictMono_of_injective
  · intro x y hxy
    show closure {OrderDual.ofDual x} ⊆ closure {OrderDual.ofDual y}
    have hle : (OrderDual.ofDual y : ↥T) ≤ OrderDual.ofDual x := hxy
    have hx : (OrderDual.ofDual x : ↥T) ∈ closure {OrderDual.ofDual y} :=
      specializes_iff_mem_closure.mp
        ((subtype_specializes_iff _ _).mpr ((le_iff_specializes _ _).mp hle))
    exact closure_minimal (Set.singleton_subset_iff.mpr hx) isClosed_closure
  · intro x y hxy
    have hset : closure {OrderDual.ofDual x} = closure {OrderDual.ofDual y} :=
      congrArg TopologicalSpace.IrreducibleCloseds.carrier hxy
    apply Subtype.ext
    apply le_antisymm
    · exact key (OrderDual.ofDual y) (OrderDual.ofDual x) (by rw [hset]; exact subset_closure rfl)
    · exact key (OrderDual.ofDual x) (OrderDual.ofDual y) (by rw [← hset]; exact subset_closure rfl)

/-- The Krull dimension of the order dual of a subset `T` of the prime spectrum, that is the
supremum of lengths of chains of primes of `T`, is at most the topological Krull dimension of
`T` as a subspace. -/
@[ega "IV 5.1.1" "partial"]
theorem krullDim_orderDual_le_topologicalKrullDim {A : Type u} [CommRing A]
    (T : Set (PrimeSpectrum A)) :
    Order.krullDim (OrderDual (↥T)) ≤ topologicalKrullDim (↥T) := by
  show Order.krullDim (OrderDual (↥T)) ≤
    Order.krullDim (TopologicalSpace.IrreducibleCloseds (↥T))
  exact Order.krullDim_le_of_strictMono _ (primePointClosure_strictMono T)

/-- The topological Krull dimension of a subset of the prime spectrum is at most the Krull
dimension of the ring. -/
private theorem topologicalKrullDim_subtype_le_ringKrullDim {A : Type u} [CommRing A]
    (T : Set (PrimeSpectrum A)) : topologicalKrullDim (↥T) ≤ ringKrullDim A :=
  (topologicalKrullDim_subspace_le _ T).trans (topologicalKrullDim_eq_ringKrullDim A).le

/-- The Krull dimension of the order dual of a subset `T` of the prime spectrum is at most the
Krull dimension of the ring. -/
theorem krullDim_orderDual_le_ringKrullDim {A : Type u} [CommRing A]
    (T : Set (PrimeSpectrum A)) : Order.krullDim (OrderDual (↥T)) ≤ ringKrullDim A :=
  (krullDim_orderDual_le_topologicalKrullDim T).trans
    (topologicalKrullDim_subtype_le_ringKrullDim T)

/-- Over a ring of finite Krull dimension, the Krull dimension of the order dual of a nonempty
subset of the prime spectrum is a natural number. -/
theorem exists_coe_eq_krullDim_orderDual {A : Type u} [CommRing A]
    (T : Set (PrimeSpectrum A)) (hT : T.Nonempty) (hdim : ringKrullDim A < ⊤) :
    ∃ n : ℕ, ((n : ℕ∞) : WithBot ℕ∞) = Order.krullDim (OrderDual (↥T)) := by
  have hne : Order.krullDim (OrderDual (↥T)) ≠ ⊥ :=
    (Order.krullDim_ne_bot_iff).2 hT.to_subtype
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp hne
  have hetop : e ≠ ⊤ := by
    rintro rfl
    exact ((krullDim_orderDual_le_ringKrullDim T).trans_lt hdim).ne he.symm
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hetop
  exact ⟨n, he⟩

/-- Over a Noetherian ring of finite Krull dimension, the dimension of a nonempty subset of the
prime spectrum strictly exceeds the dimension of its nonminimal primes: any chain of
nonminimal primes can be extended downward by a prime of `T`. -/
theorem krullDim_orderDual_nonminimalPrimes_lt {A : Type u} [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : T.Nonempty) (hdim : ringKrullDim A < ⊤) :
    Order.krullDim (OrderDual (↥(nonminimalPrimes T))) < Order.krullDim (OrderDual (↥T)) := by
  let T' := nonminimalPrimes T
  obtain ⟨n, he⟩ := exists_coe_eq_krullDim_orderDual T hT hdim
  have hseries : ∀ p : LTSeries (OrderDual (↥T')), p.length < n := by
    intro p
    let incl : OrderDual (↥T') → OrderDual (↥T) := fun x =>
      OrderDual.toDual ⟨(OrderDual.ofDual x).1, (OrderDual.ofDual x).2.1⟩
    have hincl : StrictMono incl := fun _ _ h => h
    let pT := p.map incl hincl
    obtain ⟨_, q, hqT, hqp⟩ := (OrderDual.ofDual p.last).2
    let qT : OrderDual (↥T) := OrderDual.toDual ⟨q, hqT⟩
    have hlast : pT.last = incl p.last := by simp [pT]
    have hsnoc : pT.last < qT := by
      rw [hlast]
      show q < (OrderDual.ofDual p.last).1
      exact hqp
    have hD : ((p.length + 1 : ℕ) : WithBot ℕ∞) ≤ Order.krullDim (OrderDual (↥T)) := by
      simpa [pT] using Order.LTSeries.length_le_krullDim (pT.snoc qT hsnoc)
    have hnat : p.length + 1 ≤ n := by exact_mod_cast hD.trans_eq he.symm
    omega
  exact ((Order.krullDim_lt_coe_iff (α := OrderDual (↥T')) (n := n)).2 hseries).trans_eq he

/-- The dimension of a subset `T` of the prime spectrum as a natural number, namely the
supremum of lengths of chains of primes of `T`, with both the empty set and an infinite
dimension normalized to `0`. -/
def nonminimalDim {A : Type u} [CommRing A] (T : Set (PrimeSpectrum A)) : ℕ :=
  ((Order.krullDim (OrderDual (↥T))).unbotD 0).toNat

/-- If the dimension of `T` is the natural number `n`, then `nonminimalDim T = n`. -/
private theorem nonminimalDim_eq_of_coe_eq {A : Type u} [CommRing A] (T : Set (PrimeSpectrum A))
    (n : ℕ) (he : ((n : ℕ∞) : WithBot ℕ∞) = Order.krullDim (OrderDual (↥T))) :
    nonminimalDim T = n := by
  simp [nonminimalDim, ← he]

/-- Over a Noetherian ring of finite Krull dimension, the dimension of a nonempty subset of the
prime spectrum is at most its topological dimension, both read as natural numbers. -/
theorem nonminimalDim_le_topologicalDim {A : Type u} [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : T.Nonempty) (hdim : ringKrullDim A < ⊤) :
    nonminimalDim T ≤ ((topologicalKrullDim (↥T)).unbotD 0).toNat := by
  have hEneTop : topologicalKrullDim (↥T) ≠ ⊤ := ne_top_of_le_ne_top hdim.ne
    (topologicalKrullDim_subtype_le_ringKrullDim T)
  exact ENat.toNat_le_toNat (WithBot.unbotD_mono (a := (0 : ℕ∞))
    ((Order.krullDim_ne_bot_iff).2 hT.to_subtype)
    (krullDim_orderDual_le_topologicalKrullDim T))
    fun h => hEneTop ((WithBot.unbotD_eq_iff).mp h |>.resolve_right (by simp))

/-- Over a Noetherian ring of finite Krull dimension, passing from a nonempty subset of the
prime spectrum to its nonminimal primes strictly drops the dimension, provided the latter set
is itself nonempty. -/
theorem nonminimalDim_nonminimalPrimes_lt {A : Type u} [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : T.Nonempty) (hT' : (nonminimalPrimes T).Nonempty)
    (hdim : ringKrullDim A < ⊤) :
    nonminimalDim (nonminimalPrimes T) < nonminimalDim T := by
  obtain ⟨n, he⟩ := exists_coe_eq_krullDim_orderDual T hT hdim
  obtain ⟨n', he'⟩ := exists_coe_eq_krullDim_orderDual _ hT' hdim
  have hlt : (n' : WithBot ℕ∞) < (n : WithBot ℕ∞) := by
    simpa [← he', ← he] using krullDim_orderDual_nonminimalPrimes_lt T hT hdim
  rw [nonminimalDim_eq_of_coe_eq T n he, nonminimalDim_eq_of_coe_eq _ n' he']
  exact_mod_cast hlt

end PrimeSpectrum

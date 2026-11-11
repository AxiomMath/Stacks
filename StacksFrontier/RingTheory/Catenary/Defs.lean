module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.Topology.Dimension.Catenary
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Catenary rings: the order-theoretic core

A ring `R` is *catenary* if for every pair of prime ideals `𝔭 ⊆ 𝔮`, the lengths of the finite
chains of prime ideals from `𝔭` to `𝔮` are uniformly bounded, and all non-refinable such chains
have the same length.

## Main definitions

* `IsUniversallyCatenary`: every finite-type algebra over the ring has catenary prime spectrum
  (no Noetherian condition on the ring).
* `Catenary.IsCatenaryOrder`: catenarity of a partial order.
* `Catenary.IsCatenaryRing`: the poset of prime ideals of a ring is a catenary order.
* `PrimeChain`: a finite strictly increasing chain of prime ideals with given endpoints.

## Main results

* `Catenary.isCatenaryRing_iff_isCatenarySpace_primeSpectrum`: a ring is catenary if and only if
  the poset of irreducible closed subsets of its spectrum is a catenary order.
-/

@[expose] public section

universe u

/-- Every finite-type `R`-algebra `C`, in the universe of `R`, has catenary prime spectrum. This
is the second clause of Stacks Definition 00NL only, with no Noetherian condition on `R`; the
source's notion is `Ring.IsUniversallyCatenaryNoetherian`, and
`Ring.isUniversallyCatenaryNoetherian_iff_isNoetherianRing_and_isUniversallyCatenary` compares
the two. -/
def IsUniversallyCatenary (R : Type u) [CommRing R] : Prop :=
  ∀ (C : Type u) [CommRing C] [Algebra R C],
    Algebra.FiniteType R C → IrreducibleClosedsCodim.IsCatenarySpace (PrimeSpectrum C)

@[expose] public section

open TopologicalSpace

namespace Catenary

/-- A partial order `P` is *catenary* if for every comparable pair `x ≤ y` the lengths of the
strictly increasing chains (`LTSeries`) from `x` to `y` are bounded, and all maximal chains from
`x` to `y` (`RelSeries` for the covering relation `⋖`) have the same length. -/
def IsCatenaryOrder (P : Type*) [PartialOrder P] : Prop :=
  ∀ x y : P, x ≤ y →
    (∃ n : ℕ, ∀ p : LTSeries P, p.head = x → p.last = y → p.length ≤ n) ∧
    (∀ p q : RelSeries {(a, b) : P × P | a ⋖ b},
      p.head = x → p.last = y → q.head = x → q.last = y → p.length = q.length)

/-- A commutative ring `R` is *catenary* if its poset of prime ideals `PrimeSpectrum R`, ordered by
inclusion, is a catenary order. -/
@[ega "0 16.1.4"]
def IsCatenaryRing (R : Type*) [CommRing R] : Prop :=
  IsCatenaryOrder (PrimeSpectrum R)

set_option backward.isDefEq.respectTransparency false in
/-- The lengths of the chains of irreducible closed subsets from `T` to `T'` are bounded if and
only if their supremum in `ℕ∞`, the codimension of `T` in `T'`, is finite. -/
theorem codim_lt_top_iff_bddChains {X : Type*} [TopologicalSpace X]
    (T T' : IrreducibleCloseds X) :
    (∃ n : ℕ, ∀ p : LTSeries (IrreducibleCloseds X),
        p.head = T → p.last = T' → p.length ≤ n) ↔
      (⨆ (p : LTSeries (IrreducibleCloseds X)) (_ : p.head = T) (_ : p.last = T'),
          (p.length : ℕ∞)) < ⊤ := by
  constructor
  · rintro ⟨n, hn⟩
    refine lt_of_le_of_lt ?_ (WithTop.coe_lt_top (n : ℕ))
    simp only [iSup_le_iff]
    intro p hhead hlast
    exact Nat.cast_le.mpr (hn p hhead hlast)
  · intro hlt
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt hlt)
    refine ⟨m, fun p hhead hlast => ?_⟩
    have hle : (p.length : ℕ∞) ≤
        (⨆ (p : LTSeries (IrreducibleCloseds X)) (_ : p.head = T) (_ : p.last = T'),
          (p.length : ℕ∞)) :=
      le_iSup_of_le p (le_iSup_of_le hhead (le_iSup_of_le hlast le_rfl))
    rw [← hm] at hle
    exact Nat.cast_le.mp hle

/-! ### Transfer of catenarity along order isomorphisms and duality -/

set_option backward.isDefEq.respectTransparency false in
/-- `IsCatenaryOrder` transfers across an order isomorphism: if `P ≃o Q` and `P` is catenary,
then so is `Q`. -/
theorem isCatenaryOrder_of_orderIso {P Q : Type*} [PartialOrder P] [PartialOrder Q]
    (e : P ≃o Q) (hP : IsCatenaryOrder P) : IsCatenaryOrder Q := by
  intro x y hxy
  obtain ⟨hb, hm⟩ := hP (e.symm x) (e.symm y) (by simpa using hxy)
  refine ⟨?_, ?_⟩
  · obtain ⟨n, hn⟩ := hb
    refine ⟨n, fun q hqhead hqlast => ?_⟩
    have := hn (q.map e.symm (fun {a b} h => e.symm.lt_iff_lt.mpr h)) ?_ ?_
    · simpa using this
    · simp [LTSeries.head_map, hqhead]
    · simp [LTSeries.last_map, hqlast]
  · intro p q hphead hplast hqhead hqlast
    let f : SetRel.Hom {(a, b) : Q × Q | a ⋖ b} {(a, b) : P × P | a ⋖ b} :=
      { toFun := fun w => e.symm w
        map_rel' := fun {a b} h => (apply_covBy_apply_iff e.symm).mpr h }
    have hpm := hm (p.map f) (q.map f) ?_ ?_ ?_ ?_
    · simpa using hpm
    · rw [RelSeries.head_map, hphead]; rfl
    · rw [RelSeries.last_map, hplast]; rfl
    · rw [RelSeries.head_map, hqhead]; rfl
    · rw [RelSeries.last_map, hqlast]; rfl

/-- Catenarity passes to the order dual. -/
private theorem isCatenaryOrder_orderDual_of {P : Type*} [PartialOrder P]
    (hd : IsCatenaryOrder P) : IsCatenaryOrder Pᵒᵈ := by
  intro x y hxy
  obtain ⟨hb, hm⟩ := hd (OrderDual.ofDual y) (OrderDual.ofDual x) (by exact hxy)
  refine ⟨?_, ?_⟩
  · obtain ⟨n, hn⟩ := hb
    refine ⟨n, fun q hqhead hqlast => ?_⟩
    have hh := hn (q.reverse.map { toFun := fun w => OrderDual.ofDual w, map_rel' := fun {a b} h
        => h }) ?_ ?_
    · simpa using hh
    · rw [RelSeries.head_map, RelSeries.head_reverse, hqlast]; rfl
    · rw [RelSeries.last_map, RelSeries.last_reverse, hqhead]; rfl
  · intro p q hphead hplast hqhead hqlast
    have hpm := hm
      (p.reverse.map { toFun := fun w => OrderDual.ofDual w, map_rel' := fun {a b} h =>
          toDual_covBy_toDual_iff.mp h })
      (q.reverse.map { toFun := fun w => OrderDual.ofDual w, map_rel' := fun {a b} h =>
          toDual_covBy_toDual_iff.mp h }) ?_ ?_ ?_ ?_
    · simpa using hpm
    · rw [RelSeries.head_map, RelSeries.head_reverse, hplast]; rfl
    · rw [RelSeries.last_map, RelSeries.last_reverse, hphead]; rfl
    · rw [RelSeries.head_map, RelSeries.head_reverse, hqlast]; rfl
    · rw [RelSeries.last_map, RelSeries.last_reverse, hqhead]; rfl

/-- `IsCatenaryOrder` is self-dual: a partial order is catenary iff its order dual is. -/
theorem isCatenaryOrder_orderDual_iff {P : Type*} [PartialOrder P] :
    IsCatenaryOrder Pᵒᵈ ↔ IsCatenaryOrder P :=
  ⟨fun hd => isCatenaryOrder_orderDual_of (P := Pᵒᵈ) hd, isCatenaryOrder_orderDual_of⟩

/-- A commutative ring `R` is catenary if and only if the poset of irreducible closed subsets of
`PrimeSpectrum R` is a catenary order. -/
@[stacks 02IH, ega "0 16.1.4", ega "IV 5.1.1"]
theorem isCatenaryRing_iff_isCatenarySpace_primeSpectrum (R : Type*) [CommRing R] :
    IsCatenaryRing R ↔ IsCatenaryOrder (IrreducibleCloseds (PrimeSpectrum R)) :=
  let e := PrimeSpectrum.pointsEquivIrreducibleCloseds R
  ⟨fun h => isCatenaryOrder_orderDual_iff.mp (isCatenaryOrder_of_orderIso e h),
    fun h => isCatenaryOrder_of_orderIso e.symm (isCatenaryOrder_orderDual_iff.mpr h)⟩

end Catenary

@[expose] public section

/-- A `PrimeChain p q` is a finite strictly increasing chain of prime ideals
`p = p_0 ⊊ p_1 ⊊ ... ⊊ p_e = q`, encoded as an `LTSeries` on `PrimeSpectrum R`
whose head is `p` and whose last term is `q`. -/
structure PrimeChain (R : Type u) [CommRing R] (p q : PrimeSpectrum R) where
  /-- The underlying strictly increasing series of primes. -/
  series : LTSeries (PrimeSpectrum R)
  /-- The chain starts at `p`. -/
  head_eq : series.head = p
  /-- The chain ends at `q`. -/
  last_eq : series.last = q

namespace PrimeChain

variable {R : Type u} [CommRing R] {p q : PrimeSpectrum R}

/-- The length `e` of a chain `p_0 ⊊ ... ⊊ p_e`, i.e. the number of strict
inclusions (one less than the number of primes in the sequence). -/
def length (c : PrimeChain R p q) : ℕ := c.series.length

/-- A prime chain from `p` to `q` is *maximal* (saturated, with pinned endpoints)
if no prime can be inserted strictly between two consecutive terms; equivalently,
every consecutive pair is a covering pair (`CovBy`, written `⋖`). -/
@[ega "0 14.3.1" "special case"]
def IsMaximal (c : PrimeChain R p q) : Prop :=
  ∀ i : Fin c.series.length, c.series.toFun i.castSucc ⋖ c.series.toFun i.succ

end PrimeChain

namespace CatenaryTransport

open Topology

variable {X : Type*} [TopologicalSpace X] {Y : Set X}

end CatenaryTransport

@[expose] public section

open Order TopologicalSpace

@[expose] public section

open Ring


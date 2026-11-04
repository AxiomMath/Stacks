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
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Generic points, Kolmogorov spaces and sober spaces

A point `ξ` is a generic point of a subset `Z` when `ξ ∈ Z` and `Z = closure {ξ}`. A space is
Kolmogorov when any two distinct points are separated by a closed set, quasi-sober when every
irreducible closed subset has a generic point, and sober when that generic point is moreover
unique. This file identifies each of these conditions with its Mathlib counterpart
`IsGenericPoint`, `T0Space`, `QuasiSober`, and shows sober is exactly `T0Space` together with
`QuasiSober`.

## Main definitions

* `StacksSober`: every irreducible closed subset has a unique generic point.

## Main results

* `isGenericPoint_iff`: `ξ ∈ Z ∧ Z = closure {ξ}` is equivalent to `IsGenericPoint ξ Z`.
* `kolmogorov_iff`: separating distinct points by closed sets is equivalent to `T0Space`.
* `local_quasiSober_iff`: existence of generic points on irreducible closed subsets is equivalent
  to `QuasiSober`.
* `stacksSober_iff_t0_and_quasiSober`: `StacksSober X ↔ T0Space X ∧ QuasiSober X`.

## References

* [Stacks Project, Tag 004X](https://stacks.math.columbia.edu/tag/004X)
-/

@[expose] public section

variable {X : Type*} [TopologicalSpace X]

/-- A point `ξ` lies in `Z` with `Z = closure {ξ}` exactly when `ξ` is a generic point of `Z`. -/
@[stacks 004X "generic point"]
theorem isGenericPoint_iff (Z : Set X) (ξ : X) :
    (ξ ∈ Z ∧ Z = closure {ξ}) ↔ IsGenericPoint ξ Z :=
  ⟨fun ⟨_, hZ⟩ => hZ.symm, fun h => ⟨h ▸ subset_closure rfl, h.symm⟩⟩

/-- A space in which any two distinct points are separated by a closed set is exactly a
`T0Space`. -/
@[stacks 004X "Kolmogorov", ega "0 2.1.3"]
theorem kolmogorov_iff :
    (∀ x x' : X, x ≠ x' →
        ∃ C : Set X, IsClosed C ∧ ((x ∈ C) ↔ x' ∉ C)) ↔ T0Space X := by
  refine ⟨fun h => ⟨fun x y hxy => ?_⟩, fun _ x x' hxy => ?_⟩
  · by_contra hne
    obtain ⟨C, hC, hiff⟩ := h x y hne
    have hins : x ∈ Cᶜ ↔ y ∈ Cᶜ := hxy.mem_open_iff hC.isOpen_compl
    simp only [Set.mem_compl_iff] at hins
    tauto
  · obtain ⟨U, hU, hU'⟩ := not_inseparable_iff_exists_open.mp fun h ↦ hxy h.eq
    refine ⟨Uᶜ, hU.isClosed_compl, ?_⟩
    rcases hU' with ⟨hxU, hxU'⟩ | ⟨hxU, hxU'⟩ <;> simp [hxU, hxU']

/-- A space in which every irreducible closed subset `Z` admits some `ξ ∈ Z` with `Z = closure {ξ}`
is exactly a `QuasiSober` space. -/
@[stacks 004X "quasi-sober"]
theorem local_quasiSober_iff :
    (∀ Z : Set X, IsIrreducible Z → IsClosed Z →
        ∃ ξ ∈ Z, Z = closure {ξ}) ↔ QuasiSober X :=
  ⟨fun h => ⟨fun {S} hS hSc => (h S hS hSc).elim fun ξ ⟨_, hZ⟩ => ⟨ξ, hZ.symm⟩⟩,
    fun hQS _ hZi hZc => (hQS.sober hZi hZc).elim fun ξ hξ =>
      ⟨ξ, hξ ▸ subset_closure rfl, hξ.symm⟩⟩

/-- A space is sober when every irreducible closed subset has a *unique* generic point. -/
@[stacks 004X "sober", sga "4 IV 4.2.1" "sober definition", sga "4 VIII 7.9.3"]
def StacksSober (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ Z : Set X, IsIrreducible Z → IsClosed Z →
    ∃! ξ : X, ξ ∈ Z ∧ Z = closure {ξ}

/-- A space is sober if and only if it is both Kolmogorov and quasi-sober. -/
@[ega "0 2.1.3" "special case"]
theorem stacksSober_iff_t0_and_quasiSober :
    StacksSober X ↔ (T0Space X ∧ QuasiSober X) := by
  refine ⟨fun hS => ⟨?_, ⟨fun {S} hI hC =>
      (hS S hI hC).exists.imp fun _ ⟨_, h⟩ => h.symm⟩⟩,
    fun ⟨_, _⟩ Z hIrr hClosed => ?_⟩
  · rw [t0Space_iff_inseparable]
    intro x y hxy
    have hclo : closure {x} = closure {y} := inseparable_iff_closure_eq.mp hxy
    obtain ⟨_, _, huniq⟩ := hS (closure {x}) isIrreducible_singleton.closure isClosed_closure
    rw [huniq x ⟨subset_closure rfl, rfl⟩, huniq y ⟨hclo ▸ subset_closure rfl, hclo⟩]
  · obtain ⟨ξ, hξ⟩ := QuasiSober.sober hIrr hClosed
    refine ⟨ξ, ⟨hξ ▸ subset_closure rfl, hξ.symm⟩, ?_⟩
    rintro y ⟨_, hyZ⟩
    exact (inseparable_iff_closure_eq.mpr (by rw [← hyZ, hξ])).eq


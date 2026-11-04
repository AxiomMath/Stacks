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
public import StacksFrontier.Topology.Spectral.ConstructibleTopology
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The constructible topology on a spectral space is profinite

On a spectral space `X` the constructible topology is Hausdorff, totally disconnected and
quasi-compact. Two distinct points of a Kolmogorov prespectral space are separated by a
quasi-compact open `V`, and `V` together with `Vᶜ` is a constructible-open partition of `X`
separating them.

## Main results

* `totallySeparatedSpace_withConstructibleTopology`: `WithConstructibleTopology X` is totally
  separated.
* `totallyDisconnectedSpace_withConstructibleTopology`: `WithConstructibleTopology X` is totally
  disconnected.
* `withConstructibleTopology_t2_totallyDisconnected_compact`: on a spectral space the constructible
  topology is Hausdorff, totally
  disconnected and quasi-compact.
-/

@[expose] public section

open Topology TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

open WithConstructibleTopology in
/-- The total separation part: a quasi-compact open `V` separating the two underlying points of
`X` is clopen for the constructible topology, so `ofConstructible ⁻¹' V` and its complement
separate the two points of `WithConstructibleTopology X` in the strong sense. -/
@[ega "IV 1.9.15" "(ii), (iii)"]
instance totallySeparatedSpace_withConstructibleTopology
    [T0Space X] [PrespectralSpace X] :
    TotallySeparatedSpace (WithConstructibleTopology X) := by
  refine ⟨fun x _ y _ hxy ↦ ?_⟩
  obtain ⟨U, hU, hUxor⟩ := exists_isOpen_xor_mem (X := X)
    (show ofConstructible x ≠ ofConstructible y from fun h => hxy (ofConstructible.injective h))
  rcases hUxor with ⟨hxU, hyU⟩ | ⟨hyU, hxU⟩
  · obtain ⟨V, hV, hxV, hyV⟩ := exists_isClopen_constructibleTopology_of_mem_isOpen hU hxU hyU
    exact ⟨ofConstructible ⁻¹' V, ofConstructible ⁻¹' Vᶜ,
      isOpen_preimage_ofConstructible.mpr hV.2,
      isOpen_preimage_ofConstructible.mpr (@IsClopen.compl X (constructibleTopology X) V hV).2,
      hxV, hyV, fun z _ => (Classical.em (ofConstructible z ∈ V)).imp id id,
      disjoint_compl_right.preimage _⟩
  · obtain ⟨V, hV, hyV, hxV⟩ := exists_isClopen_constructibleTopology_of_mem_isOpen hU hyU hxU
    exact ⟨ofConstructible ⁻¹' Vᶜ, ofConstructible ⁻¹' V,
      isOpen_preimage_ofConstructible.mpr (@IsClopen.compl X (constructibleTopology X) V hV).2,
      isOpen_preimage_ofConstructible.mpr hV.2,
      hxV, hyV, fun z _ => (Classical.em (ofConstructible z ∈ V)).symm.imp id id,
      disjoint_compl_left.preimage _⟩

/-- Totally disconnected follows from totally separated. -/
instance totallyDisconnectedSpace_withConstructibleTopology
    [T0Space X] [PrespectralSpace X] :
    TotallyDisconnectedSpace (WithConstructibleTopology X) :=
  TotallySeparatedSpace.totallyDisconnectedSpace _

/-- **Stacks 0901**.
For a spectral space `X`, the constructible topology on `X` is Hausdorff, totally
disconnected and quasi-compact. -/
@[stacks 0901, ega "IV 1.9.15" "(ii)(iii) suff, spectral"]
theorem withConstructibleTopology_t2_totallyDisconnected_compact (X : Type*) [TopologicalSpace X]
  [SpectralSpace X] :
    T2Space (WithConstructibleTopology X) ∧
      TotallyDisconnectedSpace (WithConstructibleTopology X) ∧
        CompactSpace (WithConstructibleTopology X) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

add_to_ega "IV 1.9.15" "(iii) suff., spectral" compactSpace_withConstructibleTopology

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
public import Mathlib.Topology.Spectral.Prespectral
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Non-Jacobson spaces with a basis of quasi-compact opens

## Main results

* `main_theorem02I7`: a Kolmogorov space with a basis of quasi-compact open sets that fails to
  be Jacobson contains a point whose singleton is locally closed but not closed.
-/

@[expose] public section

open Set TopologicalSpace

/-- **Stacks 02I7**. If `X` is a Kolmogorov topological space with a basis of quasi-compact open
sets and `X` is not Jacobson, then there exists a point `x ∈ X` such that `{x}` is not closed
in `X` and `{x}` is locally closed in `X`. -/
@[stacks 02I7, ega "IV 10.4.5.1" "sufficiency"]
theorem main_theorem02I7
    (X : Type*) [TopologicalSpace X] [T0Space X]
    (hB : PrespectralSpace X) (hJ : ¬ JacobsonSpace X) :
    ∃ x : X, ¬ IsClosed ({x} : Set X) ∧ IsLocallyClosed ({x} : Set X) := by
  -- Extract a nonempty locally closed `E = U ∩ Z` with no closed points.
  rw [jacobsonSpace_iff_locallyClosed] at hJ
  push Not at hJ
  obtain ⟨E, hEne, ⟨U, Z, hU, hZ, rfl⟩, hEnoCP⟩ := hJ
  obtain ⟨e, heU, heZ⟩ := hEne
  -- Pick a quasi-compact open neighborhood `V ⊆ U` of `e` from the basis.
  obtain ⟨B, hBbasis, hBcpt⟩ :
      ∃ B : Set (Set X), TopologicalSpace.IsTopologicalBasis B ∧ ∀ S ∈ B, IsCompact S :=
    ⟨_, hB.isTopologicalBasis, fun _ hS => hS.2⟩
  obtain ⟨V, hV_in_B, heV, hVsub⟩ := hBbasis.exists_subset_of_mem_open heU hU
  have hVopen : IsOpen V := hBbasis.isOpen hV_in_B
  have : CompactSpace (↥V) := isCompact_iff_compactSpace.mp (hBcpt V hV_in_B)
  -- The preimage of `Z` in the compact `T0` subspace `↥V` is closed and nonempty,
  -- so it contains a closed singleton `{y₀}`.
  obtain ⟨y₀, hy₀Z, hy₀closed⟩ :=
    IsClosed.exists_closed_singleton (hZ.preimage_val (s := V)) ⟨⟨e, heV⟩, heZ⟩
  refine ⟨y₀.val, fun hCP ↦ ?_, ?_⟩
  · -- `{y₀.val}` is not closed, since `y₀.val ∈ U ∩ Z` and `U ∩ Z` avoids closed points.
    have : y₀.val ∈ (U ∩ Z) ∩ closedPoints X :=
      ⟨⟨hVsub y₀.property, hy₀Z⟩, hCP⟩
    simp [hEnoCP] at this
  · -- `{y₀.val}` is locally closed in `X`, since `{y₀}` is closed in `↥V`.
    rw [isClosed_induced_iff] at hy₀closed
    obtain ⟨Z', hZ'_closed, hZ'_pre⟩ := hy₀closed
    refine ⟨V, Z', hVopen, hZ'_closed, ?_⟩
    -- Show `{y₀.val} = V ∩ Z'`.
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_inter_iff]
    refine ⟨fun hy ↦ ?_, fun ⟨hyV, hyZ⟩ ↦ ?_⟩
    · subst hy
      exact ⟨y₀.property, show y₀ ∈ (Subtype.val : ↥V → X) ⁻¹' Z' by rw [hZ'_pre]; rfl⟩
    · have hmem : (⟨y, hyV⟩ : ↥V) ∈ ((Subtype.val : ↥V → X) ⁻¹' Z') := hyZ
      rw [hZ'_pre] at hmem
      simpa using congrArg Subtype.val hmem


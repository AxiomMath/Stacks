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
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restricting a constructible set to a retrocompact subspace

If quasi-compact opens form a basis for the topology of `X` and `T ⊆ X` is retrocompact,
then the intersection of a constructible subset of `X` with `T` is constructible in the
subspace `T`.

## Main results

* `isConstructible_subtype_preimage_of_isRetrocompact`: the preimage of a constructible set
  under the inclusion of a retrocompact subspace is constructible.
-/

@[expose] public section

/-- If `T ⊆ X` is retrocompact, quasi-compact opens form a basis for the topology on `X`,
and `A` is a retrocompact open subset of `X`, then `Subtype.val ⁻¹' A` is retrocompact in the
subspace `T`. -/
private lemma isRetrocompact_preimage_val_of_basis
    {X : Type*} [TopologicalSpace X]
    (T : Set X) (hT : IsRetrocompact T)
    (hbasis : TopologicalSpace.IsTopologicalBasis {U : Set X | IsOpen U ∧ IsCompact U})
    (A : Set X) (hAo : IsOpen A) (hAr : IsRetrocompact A) :
    IsRetrocompact (Subtype.val ⁻¹' A : Set T) := by
  intro W hWc hWo
  -- Subspace topology: `W = val ⁻¹' W'` for some open `W' ⊆ X`.
  rw [isOpen_induced_iff] at hWo
  obtain ⟨W', hW'o, rfl⟩ := hWo
  -- Basis cover: `W' = ⋃ K i` with each `K i` open and compact in `X`.
  obtain ⟨ι, K, rfl, hKbasis⟩ := hbasis.open_eq_iUnion hW'o
  rw [Set.preimage_iUnion] at hWc ⊢
  obtain ⟨s, hs⟩ := hWc.elim_finite_subcover _
    (fun i => ((hKbasis i).1).preimage continuous_subtype_val) Set.Subset.rfl
  have hWeq : (⋃ i, Subtype.val ⁻¹' K i : Set T) = ⋃ i ∈ s, Subtype.val ⁻¹' K i :=
    subset_antisymm hs (Set.iUnion₂_subset fun i _ => Set.subset_iUnion (Subtype.val ⁻¹' K ·) i)
  rw [hWeq, Set.inter_iUnion₂]
  simp_rw [← Set.preimage_inter]
  refine s.finite_toSet.isCompact_biUnion fun i _ => ?_
  rw [Subtype.isCompact_iff, Subtype.image_preimage_coe]
  exact hT (hAr (hKbasis i).2 (hKbasis i).1) (hAo.inter (hKbasis i).1)

/-- **Stacks 09YF**.
If `T ⊆ X` is retrocompact, quasi-compact opens form a basis for the topology on `X`, and
`E` is constructible in `X`, then `E ∩ T`, as a subset of the subspace `T`, is constructible
in `T`. -/
@[stacks 09YF,
  ega "0 9.1.8" "T retrocompact, qc basis",
  ega "0 9.1.9" "partial",
  ega "0 9.2.1" "partial", sga "3 VIB 4.2" "partial"]
theorem isConstructible_subtype_preimage_of_isRetrocompact
    {X : Type*} [TopologicalSpace X]
    (T : Set X) (E : Set X)
    (hT : IsRetrocompact T)
    (hbasis : TopologicalSpace.IsTopologicalBasis {U : Set X | IsOpen U ∧ IsCompact U})
    (hE : Topology.IsConstructible E) :
    Topology.IsConstructible (X := T) (Subtype.val ⁻¹' E) :=
  Topology.IsConstructible.preimage continuous_subtype_val
    (isRetrocompact_preimage_val_of_basis T hT hbasis) hE


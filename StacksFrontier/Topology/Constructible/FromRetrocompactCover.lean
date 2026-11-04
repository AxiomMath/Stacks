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
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Constructibility from a finite retrocompact open cover

For a finite cover `X = V 0 ∪ ⋯ ∪ V (m - 1)` of a topological space by retrocompact open
subsets, a subset `E ⊆ X` is constructible in `X` if and only if `E ∩ V j` is constructible
in the subspace `V j` for every `j`. Constructibility of `E` inside `V j` is expressed as
constructibility of the preimage of `E` under the inclusion `V j → X`.

## Main definitions

* `IsRetrocompactOpen`: retrocompactness of an open subset.
* `IsConstructibleIn`: constructibility of a subset of the ambient space.
* `IsConstructibleInSubspace`: constructibility of the preimage of `E` in the subspace `V`.

## Main results

* `main_theorem053W`: `E` is constructible in `X` iff it is constructible in each member of
  a finite retrocompact open cover.
-/

@[expose] public section

open Topology

/-- Retrocompactness of an open subset, as used for the members of a cover. -/
@[ega "0 9.1.1", ega "IV 1.2.7", sga "3 IV 6.4.3", sga "3 VIA 2.6.3", sga "3 VIB 3.7"]
abbrev IsRetrocompactOpen {X : Type*} [TopologicalSpace X] (U : Set X) : Prop :=
  IsRetrocompact U

/-- Constructibility of a subset `E` in the ambient space `X`. -/
@[ega "0 9.1.2", ega "IV 10.1.1", ega "IV 8.3.9", sga "3 VIB 3.7"]
abbrev IsConstructibleIn {X : Type*} [TopologicalSpace X] (E : Set X) : Prop :=
  Topology.IsConstructible E

/-- Constructibility of a subset `E` of `X` inside `V`: the preimage of `E` under the
inclusion `V → X` is constructible in the subspace topology on `V`. -/
@[sga "3 VIB 3.7"]
def IsConstructibleInSubspace {X : Type*} [TopologicalSpace X] (E V : Set X) : Prop :=
  Topology.IsConstructible ((Subtype.val : V → X) ⁻¹' E)

/-- **Stacks 053W**.
For a finite covering `V : Fin m → Set X` of `X` by retrocompact open subsets, a subset
`E ⊆ X` is constructible in `X` if and only if `E ∩ V j` is constructible in `V j` for
every `j`. -/
@[stacks 053W, ega "0 9.1.9", ega "0 9.1.8" "(i) for retrocompact U"]
theorem main_theorem053W
    {X : Type*} [TopologicalSpace X]
    {m : ℕ} (V : Fin m → Set X)
    (hVopen : ∀ j, IsOpen (V j))
    (hVretro : ∀ j, IsRetrocompact (V j))
    (hVcover : ⋃ j, V j = Set.univ)
    (E : Set X) :
    IsConstructibleIn E ↔ ∀ j, IsConstructibleInSubspace E (V j) := by
  refine ⟨fun hE j => IsConstructible.preimage continuous_subtype_val
    (fun _ _ hs => hs.preimage_of_isOpenEmbedding (hVopen j).isOpenEmbedding_subtypeVal) hE,
    fun h => ?_⟩
  -- Reverse: write `E = ⋃ j, E ∩ V j` and push each piece forward.
  rw [show E = ⋃ j, E ∩ V j by rw [← Set.inter_iUnion, hVcover, Set.inter_univ]]
  refine IsConstructible.iUnion fun j => ?_
  have hImg := (h j).image_of_isOpenEmbedding (hVopen j).isOpenEmbedding_subtypeVal
    (Subtype.range_coe ▸ hVretro j)
  rwa [Set.image_preimage_eq_inter_range, Subtype.range_coe] at hImg


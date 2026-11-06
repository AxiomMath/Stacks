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
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Jacobson spaces and open coverings

## Main results

* `jacobsonSpace_iff_of_isOpenCover`: a topological space is Jacobson if and only if every
  member of an open covering of it is Jacobson.
* `closedPoints_eq_iUnion_image_closedPoints_of_isOpenCover`: the closed points of a Jacobson
  space are the union of the images of the closed points of the members of an open covering.
-/

@[expose] public section

/-- For an open covering `U : ι → TopologicalSpace.Opens X` of a topological space `X`, the space
`X` is Jacobson if and only if each `U i`, with the subspace topology, is Jacobson. -/
@[stacks 005W, ega "IV 10.3.3", ega "IV 10.3.2" "special case"]
theorem jacobsonSpace_iff_of_isOpenCover
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} {U : ι → TopologicalSpace.Opens X}
    (hU : TopologicalSpace.IsOpenCover U) :
    JacobsonSpace X ↔ ∀ i, JacobsonSpace (U i) :=
  hU.jacobsonSpace_iff

/-- For an open covering `U : ι → TopologicalSpace.Opens X` of a Jacobson space `X`, the set of
closed points of `X` is the union over `i` of the images of the closed points of `U i` under the
inclusion `Subtype.val : ↥(U i) → X`. -/
@[stacks 005W, ega "IV 10.4.7" "open immersions", ega "IV 10.9.2" "special case"]
theorem closedPoints_eq_iUnion_image_closedPoints_of_isOpenCover
    {X : Type*} [TopologicalSpace X]
    {ι : Type*} {U : ι → TopologicalSpace.Opens X}
    (hU : TopologicalSpace.IsOpenCover U)
    [JacobsonSpace X] :
    closedPoints X = ⋃ i, (Subtype.val : ↥(U i) → X) '' closedPoints ↥(U i) := by
  have hpre (i) : (Subtype.val : ↥(U i) → X) ⁻¹' closedPoints X = closedPoints ↥(U i) :=
    (U i).isOpenEmbedding'.preimage_closedPoints
  ext x
  refine ⟨fun hx ↦ ?_, ?_⟩
  · obtain ⟨i, hxi⟩ := hU.exists_mem x
    exact Set.mem_iUnion.mpr ⟨i, ⟨x, hxi⟩, (hpre i).symm ▸ hx, rfl⟩
  · rintro ⟨_, ⟨i, rfl⟩, y, hy, rfl⟩
    rwa [← hpre i] at hy

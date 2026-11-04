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

/-!
# Irreducibility from a dense set of irreducible fibres

Let `f : X → Y` be a continuous open map, let `Y` be irreducible, and assume the set of points
`y ∈ Y` whose fibre `f ⁻¹' {y}` is *irreducible* is dense in `Y`. Then `X` is irreducible.

Mathlib's `IsPreirreducible.preimage_of_dense_isPreirreducible_fiber` is only the
preirreducible half of this, and it is genuinely weaker: the empty set is preirreducible
(`isPreirreducible_empty`), so its hypotheses are satisfied by a map all of whose fibres are
empty, in which case `X` is empty and hence *not* irreducible. The missing ingredient is
nonemptiness of `X`, and it comes from a single point of the dense set: its fibre is
irreducible, hence nonempty. (Mathlib's `IsIrreducible.preimage_of_isPreirreducible_fiber`
does reach an `IsIrreducible` conclusion, but it assumes *every* fibre is preirreducible, which
is the hypothesis of Stacks 037A rather than the dense hypothesis used here.)

## Main results

* `IsIrreducible.preimage_of_dense_isIrreducible_fiber`: the irreducible-valued form of
  Mathlib's lemma — if `V` is irreducible, `f` is open, and the points of `V` with irreducible
  fibre are dense in `V`, then `f ⁻¹' V` is irreducible.
* `irreducibleSpace_of_isOpenMap_of_dense_isIrreducible_fiber`: the same statement for
  `V = Set.univ`, with no continuity assumption on `f`.
* `irreducibleSpace_of_continuous_of_dense_isIrreducible_fiber`: **Stacks 004Z**, stated with
  the continuity hypothesis (a) of the source, which the proof does not need.
-/

@[expose] public section

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The irreducible-valued strengthening of
`IsPreirreducible.preimage_of_dense_isPreirreducible_fiber`: if `V ⊆ Y` is irreducible, `f` is
an open map, and the points of `V` whose fibre is *irreducible* are dense in `V`, then
`f ⁻¹' V` is irreducible.

Nonemptiness — which the preirreducible statement cannot supply, since the empty set is
preirreducible — comes from any point of `V` with irreducible, hence nonempty, fibre. -/
theorem IsIrreducible.preimage_of_dense_isIrreducible_fiber
    {V : Set Y} (hV : IsIrreducible V) (f : X → Y) (hfopen : IsOpenMap f)
    (hfib : V ⊆ closure (V ∩ {y | IsIrreducible (f ⁻¹' {y})})) :
    IsIrreducible (f ⁻¹' V) := by
  refine ⟨?_, hV.2.preimage_of_dense_isPreirreducible_fiber f hfopen
    (hfib.trans (closure_mono (Set.inter_subset_inter_right V fun _y hy ↦ hy.2)))⟩
  obtain ⟨y, hyV⟩ := hV.nonempty
  obtain ⟨y', hy'V, hy'irr⟩ := closure_nonempty_iff.mp ⟨y, hfib hyV⟩
  obtain ⟨x, hx⟩ := hy'irr.nonempty
  have hfx : f x = y' := hx
  exact ⟨x, by rw [Set.mem_preimage, hfx]; exact hy'V⟩

/-- If `Y` is irreducible, `f : X → Y` is an open map, and the set of points of `Y` whose fibre
is irreducible is dense, then `X` is irreducible. Continuity of `f` is not needed. -/
theorem irreducibleSpace_of_isOpenMap_of_dense_isIrreducible_fiber
    [IrreducibleSpace Y] {f : X → Y} (hfopen : IsOpenMap f)
    (hfib : Dense {y : Y | IsIrreducible (f ⁻¹' {y})}) :
    IrreducibleSpace X := by
  have h : IsIrreducible (Set.univ : Set X) := by
    have h' := (IrreducibleSpace.isIrreducible_univ Y).preimage_of_dense_isIrreducible_fiber
      f hfopen (by rw [Set.univ_inter]; exact fun y _ ↦ hfib y)
    rwa [Set.preimage_univ] at h'
  rw [irreducibleSpace_def, Set.top_eq_univ]
  exact h

/-- **Stacks 004Z**.
Let `f : X → Y` be a continuous map of topological spaces. Assume that (a) `Y` is irreducible,
(b) `f` is open, and (c) there exists a dense collection of points `y ∈ Y` such that `f ⁻¹' {y}`
is irreducible. Then `X` is irreducible.

The continuity hypothesis (a) is recorded here because the source states it; the proof does not
use it, see `irreducibleSpace_of_isOpenMap_of_dense_isIrreducible_fiber`. -/
@[stacks 004Z]
theorem irreducibleSpace_of_continuous_of_dense_isIrreducible_fiber
    [IrreducibleSpace Y] {f : X → Y} (_hfcont : Continuous f) (hfopen : IsOpenMap f)
    (hfib : Dense {y : Y | IsIrreducible (f ⁻¹' {y})}) :
    IrreducibleSpace X :=
  irreducibleSpace_of_isOpenMap_of_dense_isIrreducible_fiber hfopen hfib

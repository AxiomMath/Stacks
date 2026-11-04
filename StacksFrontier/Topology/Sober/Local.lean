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
public import StacksFrontier.Topology.Sober.Defs

/-!
# Locality of the Kolmogorov, quasi-sober and sober conditions

Let `U : I → Set X` be a covering of a topological space `X`. If every `U i` is locally closed
in `X`, then `X` is Kolmogorov exactly when every `U i` is. If every `U i` is open, then `X` is
quasi-sober exactly when every `U i` is, and the same holds for soberness.

## Main results

* `kolmogorov_iff_of_locallyClosed_cover`: `T0Space` is local for locally closed coverings.
* `quasiSober_iff_of_open_cover`: `QuasiSober` is local for open coverings.
* `sober_iff_of_open_cover`: soberness (`StacksSober`) is local for open coverings.
-/

@[expose] public section

open Set Topology

variable {X : Type*} [TopologicalSpace X]

/-- If a covering `U` of `X` consists of locally closed subsets, then `X` is Kolmogorov if and only
if each `U i` is. -/
@[stacks 06N9 "(1)"]
theorem kolmogorov_iff_of_locallyClosed_cover
    {I : Type*} (U : I → Set X)
    (hcov : ⋃ i, U i = Set.univ)
    (hlc : ∀ i, IsLocallyClosed (U i)) :
    T0Space X ↔ ∀ i, T0Space (U i) := by
  refine ⟨fun _ i => inferInstance, fun hT0 => ?_⟩
  refine ⟨fun x y hxy => ?_⟩
  have hxuniv : x ∈ (⋃ i, U i : Set X) := by rw [hcov]; trivial
  obtain ⟨i, hxi⟩ := mem_iUnion.mp hxuniv
  obtain ⟨V, Z, hV, hZ, hUi⟩ := hlc i
  obtain ⟨hxV, hxZ⟩ : x ∈ V ∩ Z := by rw [← hUi]; exact hxi
  have hyV : y ∈ V := (inseparable_iff_forall_isOpen.mp hxy V hV).mp hxV
  have hcxZ : closure ({x} : Set X) ⊆ Z :=
    hZ.closure_subset_iff.mpr (singleton_subset_iff.mpr hxZ)
  have hyclx : y ∈ closure ({x} : Set X) :=
    (inseparable_iff_closure_eq.mp hxy) ▸ subset_closure rfl
  have hyZ : y ∈ Z := hcxZ hyclx
  have hyi : y ∈ U i := by rw [hUi]; exact ⟨hyV, hyZ⟩
  have hins_sub : Inseparable (⟨x, hxi⟩ : U i) ⟨y, hyi⟩ :=
    (IsInducing.subtypeVal.inseparable_iff (x := (⟨x, hxi⟩ : U i))
      (y := ⟨y, hyi⟩)).mp hxy
  have := @Inseparable.eq _ _ (hT0 i) _ _ hins_sub
  exact Subtype.mk_eq_mk.mp this

/-- If a covering `U` of `X` consists of open subsets, then `X` is quasi-sober if and only if each
`U i` is. -/
@[stacks 06N9 "(2)"]
theorem quasiSober_iff_of_open_cover
    {I : Type*} (U : I → Set X)
    (hcov : ⋃ i, U i = Set.univ)
    (hopen : ∀ i, IsOpen (U i)) :
    QuasiSober X ↔ ∀ i, QuasiSober (U i) :=
  (TopologicalSpace.IsOpenCover.of_sets hopen hcov).quasiSober_iff_forall

/-- If a covering `U` of `X` consists of open subsets, then `X` is sober if and only if each `U i`
is. -/
@[stacks 06N9 "(3)"]
theorem sober_iff_of_open_cover
    {I : Type*} (U : I → Set X)
    (hcov : ⋃ i, U i = Set.univ)
    (hopen : ∀ i, IsOpen (U i)) :
    StacksSober X ↔ ∀ i, StacksSober (U i) := by
  have hlc : ∀ i, IsLocallyClosed (U i) := fun i => (hopen i).isLocallyClosed
  simp only [stacksSober_iff_t0_and_quasiSober]
  rw [kolmogorov_iff_of_locallyClosed_cover U hcov hlc,
      quasiSober_iff_of_open_cover U hcov hopen]
  exact ⟨fun ⟨hT, hQ⟩ i => ⟨hT i, hQ i⟩,
         fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩


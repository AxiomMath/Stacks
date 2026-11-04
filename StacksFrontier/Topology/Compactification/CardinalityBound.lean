module

public import Mathlib.Order.CompletePartialOrder
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

/-!
# A cardinality bound for spaces with a dense continuous image

## Main definitions

* `opensWithMemClosureImage`: for `f : X → Y`, the map sending `y : Y` to the collection of open
  `U ⊆ X` whose image has `y` in its closure.

## Main results

* `injective_closureImageOpens`: `opensWithMemClosureImage f` is injective when `f` is continuous
  with dense
  range and `Y` is Hausdorff.
* `mk_le_mk_set_set_of_denseRange` (Stacks 0909): under those hypotheses `#Y ≤ #P(P(X))`.
-/

@[expose] public section

universe u

open Set Topology

/-- The candidate injection `Φ : Y → P(P(X))`. For each `y ∈ Y`, `Φ(y)` is the
set of open subsets `U ⊆ X` such that `y` lies in the closure of `f '' U`. -/
def opensWithMemClosureImage {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (y : Y) : Set (Set X) :=
  {U | IsOpen U ∧ y ∈ closure (f '' U)}

section helper_lemmas

variable {X Y : Type u} [TopologicalSpace Y]

/-- If `f` has dense range and `V` is an open neighbourhood of `y`, then `y` lies
in the closure of `f '' (f ⁻¹' V)`. -/
lemma mem_closure_image_preimage_of_denseRange
    (f : X → Y) (hd : DenseRange f) {V : Set Y} (hV : IsOpen V) {y : Y}
    (hy : y ∈ V) : y ∈ closure (f '' (f ⁻¹' V)) := by
  rw [mem_closure_iff]
  intro U hU hyU
  obtain ⟨z, ⟨hzU, hzV⟩, x, hxz⟩ :=
    hd.inter_open_nonempty (U ∩ V) (hU.inter hV) ⟨y, hyU, hy⟩
  exact ⟨z, hzU, x, show f x ∈ V from hxz ▸ hzV, hxz⟩

/-- If `V₁`, `V₂ ⊆ Y` are disjoint with `V₂` open and `y₂ ∈ V₂`, then `y₂` is
not in the closure of `f '' (f ⁻¹' V₁)`, since `f '' (f ⁻¹' V₁) ⊆ V₁`. -/
lemma not_mem_closure_image_preimage_of_disjoint
    (f : X → Y) {V₁ V₂ : Set Y} (hV₂ : IsOpen V₂) (hdisj : Disjoint V₁ V₂)
    {y₂ : Y} (hy₂ : y₂ ∈ V₂) : y₂ ∉ closure (f '' (f ⁻¹' V₁)) := by
  intro hmem
  obtain ⟨z, hzV₂, hzImg⟩ := mem_closure_iff.mp hmem V₂ hV₂ hy₂
  exact Set.disjoint_left.mp hdisj (image_preimage_subset f V₁ hzImg) hzV₂

end helper_lemmas

/-- Under the hypotheses of Stacks 0909, the map `opensWithMemClosureImage f` is
injective: distinct points of `Y` give distinct sets in `P(P(X))`. -/
lemma injective_closureImageOpens
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    (f : X → Y) (hf : Continuous f) (hd : DenseRange f) :
    Function.Injective (opensWithMemClosureImage f) := by
  intro y₁ y₂ heq
  by_contra hne
  obtain ⟨V₁, V₂, hV₁, hV₂, hy₁, hy₂, hdisj⟩ := t2_separation hne
  have h₁ : f ⁻¹' V₁ ∈ opensWithMemClosureImage f y₂ := heq ▸
    ⟨hV₁.preimage hf, mem_closure_image_preimage_of_denseRange f hd hV₁ hy₁⟩
  exact not_mem_closure_image_preimage_of_disjoint f hV₂ hdisj hy₂ h₁.2

/-- **Stacks 0909.** If `f : X → Y` is a continuous map of topological spaces with dense image
and `Y` is Hausdorff, then `#Y ≤ #P(P(X))`. -/
@[stacks 0909]
theorem mk_le_mk_set_set_of_denseRange
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    (f : X → Y) (hf : Continuous f) (hd : DenseRange f) :
    Cardinal.mk Y ≤ Cardinal.mk (Set (Set X)) :=
  Cardinal.mk_le_of_injective (injective_closureImageOpens f hf hd)

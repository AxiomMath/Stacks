module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic

/-!
# Extending a rule on prime cycles over a cycle group

A cycle on a scheme `X` is a locally finite formal sum `∑ n_Z [Z]` of integral closed
subschemes, equivalently (Stacks 02QR) a locally finitely supported integer-valued function on
the points of `X`, the point `x` standing for the integral closed subscheme `closure {x}` with
its reduced structure. The constructions of chapter 42 which produce a cycle on a closed
subscheme `i : Y ⟶ X` — the Gysin map of the zero scheme of a section of an invertible sheaf
(Stacks 02T8), intersection with the first Chern class (Stacks 02SO), the sum of a locally
finite family of principal divisors (Stacks 02RW) — all have the same shape: a rule assigning
to each point `x` of `X` a cycle on `Y` supported over the closure of `x`, extended
coefficientwise over an arbitrary cycle.

This file provides that extension and its characterizing properties, at the level of
topological spaces and `Function.locallyFinsupp`, which is what
`AlgebraicGeometry.AlgebraicCycle` abbreviates. The two facts that make the extension well
defined are both proved here: opens of a topological space are stable under generalization, so
Mathlib's local finiteness of the *support* of a cycle is Stacks' local finiteness of the
*family of closed subschemes* it is supported on
(`Stacks.Chow.locallyFinite_closure_singleton_iff`); and the resulting pointwise sum is itself
locally finite (`Stacks.Chow.ComponentRule.locallyFiniteSupport_extendCoeff`).

## Main definitions

* `Stacks.Chow.ComponentRule` — a family of cycles on `Y`, one per point of `X`, the cycle at
  `x` supported over `closure {x}`.
* `Stacks.Chow.ComponentRule.extend` — the induced additive map on cycle groups.

## Main results

* `Stacks.Chow.locallyFinite_closure_singleton_iff` — a family of points is locally finite
  exactly when the family of their closures is.
* `Stacks.Chow.ComponentRule.extend_apply` — the coefficientwise formula for the extension.
* `Stacks.Chow.ComponentRule.extend_apply_single` — its value on a prime cycle.
* `Stacks.Chow.ComponentRule.extend_apply_of_presentation` — its value computed from an
  arbitrary locally finite presentation of the cycle by integral components.

## Implementation notes

A presentation of a cycle is taken in the shape the Stacks constructions use: an index type `J`,
generic points `σ : J → X`, coefficients `n : J → ℤ`, and the fundamental cycles `e : J → X → ℤ`
of the components, of which only `e j x ≠ 0 → x = σ j` and `e j (σ j) = 1` are used.
Repetitions in `σ` are allowed; local finiteness of the family of components forces every fibre
of `σ` to be finite, which is what makes the formal sums honest `finsum`s.

## References

* [Stacks Project, Tag 02QR](https://stacks.math.columbia.edu/tag/02QR)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
-/

@[expose] public noncomputable section

open Set Topology

namespace Stacks.Chow

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-! ### Local finiteness of a family of points and of their closures -/

/-- A family of points of a topological space is locally finite if and only if the family of
their closures is. -/
theorem locallyFinite_closure_singleton_iff {ι : Type*} (σ : ι → X) :
    LocallyFinite (fun j ↦ closure {σ j}) ↔ ∀ x : X, ∃ t ∈ 𝓝 x, {j | σ j ∈ t}.Finite := by
  constructor
  · intro h x
    obtain ⟨t, ht, hfin⟩ := h x
    exact ⟨t, ht, hfin.subset fun j hj ↦ ⟨σ j, subset_closure (mem_singleton _), hj⟩⟩
  · intro h x
    obtain ⟨t, ht, hfin⟩ := h x
    refine ⟨interior t, isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.2 ht),
      hfin.subset fun j hj ↦ ?_⟩
    obtain ⟨y, hy, hyt⟩ := hj
    have hσj : σ j ∈ t := interior_subset
      ((specializes_iff_mem_closure.2 hy).mem_open isOpen_interior hyt)
    exact hσj

/-- The integral closed subschemes a cycle is supported on form a locally finite family of
closed subsets. This is the local finiteness condition of Stacks 02QR. -/
theorem locallyFinite_closure_support {R : Type*} [Zero R] {c : X → R}
    (hc : LocallyFiniteSupport c) :
    LocallyFinite (fun x : Function.support c ↦ closure {(x : X)}) := by
  rw [locallyFinite_closure_singleton_iff]
  intro x
  obtain ⟨t, ht, hfin⟩ := hc x
  refine ⟨t, ht, ?_⟩
  have h : {j : Function.support c | (j : X) ∈ t} =
      Subtype.val ⁻¹' (t ∩ Function.support c) := by
    ext j
    exact ⟨fun hj ↦ ⟨hj, j.2⟩, fun hj ↦ hj.1⟩
  rw [h]
  exact Set.Finite.preimage Subtype.val_injective.injOn hfin

/-- A locally finite family of points has finite fibres: a formal sum over such a family has
only finitely many terms at each integral closed subscheme. -/
theorem finite_fiber_of_locallyFinite {ι : Type*} {σ : ι → X}
    (h : LocallyFinite fun j ↦ closure {σ j}) (x : X) : {j | σ j = x}.Finite := by
  obtain ⟨t, ht, hfin⟩ := (locallyFinite_closure_singleton_iff σ).1 h x
  refine hfin.subset fun j (hj : σ j = x) ↦ ?_
  have hσj : σ j ∈ t := by rw [hj]; exact mem_of_mem_nhds ht
  exact hσj

/-- Only finitely many members of a locally finite family of points have a given point in their
closure: only finitely many components of a cycle pass through a given point. -/
theorem finite_mem_closure_of_locallyFinite {ι : Type*} {σ : ι → X}
    (h : LocallyFinite fun j ↦ closure {σ j}) (x : X) :
    {j | x ∈ closure {σ j}}.Finite := by
  obtain ⟨t, ht, hfin⟩ := h x
  exact hfin.subset fun j hj ↦ ⟨x, hj, mem_of_mem_nhds ht⟩

/-! ### Component rules and their extensions -/

/-- A *component rule* along a map `i : Y → X` assigns to every point `x` of `X` — that is, to
every integral closed subscheme `closure {x}` of `X` — a cycle on `Y`, supported over the
closure of `x`. -/
structure ComponentRule (i : Y → X) where
  /-- The cycle on `Y` attached to a point of `X`. -/
  cycle : X → Function.locallyFinsupp Y ℤ
  /-- The cycle attached to `x` is supported over the closure of `x`. -/
  mem_closure_of_apply_ne_zero : ∀ (x : X) (y : Y), cycle x y ≠ 0 → i y ∈ closure {x}

namespace ComponentRule

variable {i : Y → X} (G : ComponentRule i)

/-- The coefficient at `y` of the extension of a component rule over a cycle with coefficient
function `α`: the formal sum of the component cycles weighted by `α`. -/
def extendCoeff (α : X → ℤ) (y : Y) : ℤ := ∑ᶠ x : X, α x * G.cycle x y

/-- At each point of `Y` only finitely many components of a cycle contribute to the extension. -/
theorem finite_support_extendTerm {α : X → ℤ} (hα : LocallyFiniteSupport α) (y : Y) :
    (Function.support fun x ↦ α x * G.cycle x y).Finite := by
  obtain ⟨t, ht, hfin⟩ := hα (i y)
  refine hfin.subset fun x (hx : α x * G.cycle x y ≠ 0) ↦ ⟨interior_subset ?_, ?_⟩
  · exact (specializes_iff_mem_closure.2
        (G.mem_closure_of_apply_ne_zero x y (right_ne_zero_of_mul hx))).mem_open
      isOpen_interior (mem_interior_iff_mem_nhds.2 ht)
  · exact left_ne_zero_of_mul hx

/-- The extension of a component rule is additive in the cycle. -/
theorem extendCoeff_add {α β : X → ℤ} (hα : LocallyFiniteSupport α)
    (hβ : LocallyFiniteSupport β) (y : Y) :
    G.extendCoeff (α + β) y = G.extendCoeff α y + G.extendCoeff β y := by
  simp only [extendCoeff, Pi.add_apply, add_mul]
  exact finsum_add_distrib (G.finite_support_extendTerm hα y)
    (G.finite_support_extendTerm hβ y)

/-- The extension of a component rule over a cycle is again a cycle: its support is locally
finite. -/
theorem locallyFiniteSupport_extendCoeff (hi : Continuous i) {α : X → ℤ}
    (hα : LocallyFiniteSupport α) : LocallyFiniteSupport (G.extendCoeff α) := by
  intro y₀
  obtain ⟨t, ht, hfin⟩ := hα (i y₀)
  choose V hV hVfin using fun x : X ↦ (G.cycle x).locallyFiniteSupport y₀
  refine ⟨i ⁻¹' interior t ∩ ⋂ x ∈ t ∩ Function.support α, V x, ?_, ?_⟩
  · exact Filter.inter_mem
      ((hi.isOpen_preimage _ isOpen_interior).mem_nhds (mem_interior_iff_mem_nhds.2 ht))
      ((Filter.biInter_mem hfin).2 fun x _ ↦ hV x)
  · refine Set.Finite.subset (hfin.biUnion fun x _ ↦ hVfin x) ?_
    rintro y ⟨⟨hyt, hyV⟩, hy⟩
    replace hy : G.extendCoeff α y ≠ 0 := hy
    obtain ⟨x, hx⟩ : ∃ x : X, α x * G.cycle x y ≠ 0 := by
      by_contra h
      push Not at h
      exact hy (finsum_eq_zero_of_forall_eq_zero h)
    have hxt : x ∈ t ∩ Function.support α := by
      refine ⟨interior_subset ?_, left_ne_zero_of_mul hx⟩
      exact (specializes_iff_mem_closure.2
          (G.mem_closure_of_apply_ne_zero x y (right_ne_zero_of_mul hx))).mem_open
        isOpen_interior hyt
    exact mem_biUnion hxt ⟨mem_iInter₂.1 hyV x hxt, right_ne_zero_of_mul hx⟩

/-- The cycle on `Y` obtained by extending a component rule over a cycle on `X`. -/
def extendCycle (hi : Continuous i) (α : Function.locallyFinsupp X ℤ) :
    Function.locallyFinsupp Y ℤ where
  toFun := G.extendCoeff α
  supportWithinDomain' _ _ := trivial
  supportLocallyFiniteWithinDomain' y _ :=
    G.locallyFiniteSupport_extendCoeff hi α.locallyFiniteSupport y

/-- The coefficient of `G.extendCycle hi α` at `y` is `G.extendCoeff α y`. -/
@[simp]
theorem extendCycle_apply (hi : Continuous i) (α : Function.locallyFinsupp X ℤ) (y : Y) :
    G.extendCycle hi α y = G.extendCoeff α y := rfl

/-- The extension of a component rule to an additive map on cycle groups. -/
def extend (hi : Continuous i) :
    Function.locallyFinsupp X ℤ →+ Function.locallyFinsupp Y ℤ where
  toFun := G.extendCycle hi
  map_zero' := by
    ext y
    simp only [extendCycle_apply, extendCoeff, Function.locallyFinsuppWithin.coe_zero,
      Pi.zero_apply, zero_mul, finsum_zero]
  map_add' α β := by
    ext y
    simp only [extendCycle_apply, Function.locallyFinsuppWithin.coe_add]
    exact G.extendCoeff_add α.locallyFiniteSupport β.locallyFiniteSupport y

/-- The coefficientwise formula for the extension of a component rule. -/
@[simp]
theorem extend_apply (hi : Continuous i) (α : Function.locallyFinsupp X ℤ) (y : Y) :
    G.extend hi α y = ∑ᶠ x : X, α x * G.cycle x y := rfl

/-- The extension of a component rule is supported where the component cycles are. -/
theorem support_extend_subset (hi : Continuous i) (α : Function.locallyFinsupp X ℤ) :
    Function.support (G.extend hi α) ⊆ ⋃ x : X, Function.support (G.cycle x) := by
  intro y hy
  replace hy : G.extendCoeff α y ≠ 0 := hy
  obtain ⟨x, hx⟩ : ∃ x : X, α x * G.cycle x y ≠ 0 := by
    by_contra h
    push Not at h
    exact hy (finsum_eq_zero_of_forall_eq_zero h)
  exact mem_iUnion.2 ⟨x, right_ne_zero_of_mul hx⟩

/-- On the prime cycle `n • [closure {x}]` the extension of a component rule is `n` times the
cycle the rule attaches to `x`. -/
theorem extend_apply_single (hi : Continuous i) [DecidableEq X] (x : X) (n : ℤ) (y : Y) :
    G.extend hi (Function.locallyFinsuppWithin.single x n) y = n * G.cycle x y := by
  rw [extend_apply, finsum_eq_single _ x fun x' hx' ↦ by simp [hx']]
  simp

/-- The extension of a component rule computed from an arbitrary locally finite presentation
`α = ∑ n j [σ j]` of a cycle by integral closed subschemes: this is the coefficientwise rule of
Stacks 02T8(2). The fundamental cycles of the components enter only through `he₀` and `he₁`, and
repetitions among the `σ j` are allowed. -/
theorem extend_apply_of_presentation (hi : Continuous i) {J : Type*} (σ : J → X) (n : J → ℤ)
    (e : J → X → ℤ) (he₀ : ∀ (j : J) (x : X), e j x ≠ 0 → x = σ j)
    (he₁ : ∀ j : J, e j (σ j) = 1)
    (hσ : LocallyFinite fun j ↦ closure {σ j}) (α : Function.locallyFinsupp X ℤ)
    (hα : ∀ x : X, α x = ∑ᶠ j : J, n j * e j x) (y : Y) :
    G.extend hi α y = ∑ᶠ j : J, n j * G.cycle (σ j) y := by
  classical
  have hsupp : (Function.support fun j ↦ n j * G.cycle (σ j) y).Finite :=
    (finite_mem_closure_of_locallyFinite hσ (i y)).subset
      fun j (hj : n j * G.cycle (σ j) y ≠ 0) ↦
        G.mem_closure_of_apply_ne_zero _ y (right_ne_zero_of_mul hj)
  have hssub : Function.support (fun j ↦ n j * G.cycle (σ j) y) ⊆
      (hsupp.toFinset : Set J) := by simp
  have key : ∀ x : X, α x * G.cycle x y =
      ∑ j ∈ hsupp.toFinset with σ j = x, n j * G.cycle (σ j) y := by
    intro x
    by_cases hxy : G.cycle x y = 0
    · rw [hxy, mul_zero]
      refine (Finset.sum_eq_zero fun j hj ↦ ?_).symm
      rw [(Finset.mem_filter.1 hj).2, hxy, mul_zero]
    · have hfsub : Function.support (fun j ↦ n j * e j x) ⊆
          ((hsupp.toFinset.filter fun j ↦ σ j = x : Finset J) : Set J) := by
        intro j (hj : n j * e j x ≠ 0)
        have hjx : σ j = x := (he₀ j x (right_ne_zero_of_mul hj)).symm
        refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hssub ?_, hjx⟩)
        have hne : n j * G.cycle (σ j) y ≠ 0 := by
          rw [hjx]
          exact mul_ne_zero (left_ne_zero_of_mul hj) hxy
        exact hne
      have hαx : α x = ∑ j ∈ hsupp.toFinset with σ j = x, n j := by
        rw [hα x, finsum_eq_sum_of_support_subset _ hfsub]
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        rw [← (Finset.mem_filter.1 hj).2, he₁, mul_one]
      rw [hαx, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j hj ↦ by rw [(Finset.mem_filter.1 hj).2]
  rw [extend_apply, finsum_congr key, finsum_sum_filter σ hsupp.toFinset _,
    ← finsum_eq_sum_of_support_subset _ hssub]

end ComponentRule

end Stacks.Chow

end

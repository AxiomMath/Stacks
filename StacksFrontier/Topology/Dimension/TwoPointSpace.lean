module

public import Mathlib.Order.KrullDimension
public import StacksFrontier.Topology.Dimension.Krull
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Two-point spaces of Krull dimension one

A topological space with exactly two points `x₀ ≠ x₁` in which `{x₁}` is open and `{x₀}` is not
is the Sierpiński space: its open sets are `∅`, `{x₁}` and the whole space. Its irreducible closed
subsets are `{x₀}` and the whole space, so `x₀` is a specialization of `x₁` and the Krull
dimension is one. This is the shape of the space of points of `[𝔸¹/𝔾ₘ]` in Stacks 0DRK.

## Main results

* `specializes_and_topologicalKrullDim_eq_one`: in such a space `x₁ ⤳ x₀` and
  `topologicalKrullDim X = 1`.
* `topologicalKrullDimAt_eq_zero_of_isOpen_singleton`: the dimension at an isolated point is
  `0`.
* `topologicalKrullDimAt_eq_topologicalKrullDim_of_forall_specializes`: the dimension at a point
  which is a specialization of every point is the dimension of the whole space; in particular the
  closed point of such a two-point space has dimension one.

## References

* [Stacks Project, Tag 0057](https://stacks.math.columbia.edu/tag/0057)
* [Stacks Project, Tag 0DRK](https://stacks.math.columbia.edu/tag/0DRK)
-/

@[expose] public section

open TopologicalSpace

/-- In a two-point space `{x₀, x₁}` in which `{x₀}` is not open, `x₁` specializes to `x₀`. -/
theorem specializes_of_not_isOpen_singleton {X : Type*} [TopologicalSpace X] {x₀ x₁ : X}
    (hne : x₀ ≠ x₁) (hall : ∀ y, y = x₀ ∨ y = x₁) (h₀ : ¬ IsOpen ({x₀} : Set X)) : x₁ ⤳ x₀ := by
  have hx₁ : x₁ ∈ closure ({x₁} : Set X) := subset_closure rfl
  rw [specializes_iff_mem_closure]
  by_contra h
  apply h₀
  convert (isClosed_closure (s := ({x₁} : Set X))).isOpen_compl
  ext y
  rcases hall y with rfl | rfl <;> simp [h, hx₁, hne.symm]

/-- A two-point space `{x₀, x₁}` in which `{x₁}` is open and `{x₀}` is not has Krull
dimension one. -/
theorem topologicalKrullDim_eq_one_of_isOpen_singleton {X : Type*} [TopologicalSpace X]
    {x₀ x₁ : X} (hne : x₀ ≠ x₁) (hall : ∀ y, y = x₀ ∨ y = x₁) (h₁ : IsOpen ({x₁} : Set X))
    (h₀ : ¬ IsOpen ({x₀} : Set X)) : topologicalKrullDim X = 1 := by
  have hspec := specializes_of_not_isOpen_singleton hne hall h₀
  have hcl : closure ({x₁} : Set X) = Set.univ := Set.eq_univ_of_forall fun y => by
    rcases hall y with rfl | rfl
    exacts [specializes_iff_mem_closure.1 hspec, subset_closure rfl]
  have hc₀ : ({x₀} : Set X) = {x₁}ᶜ := by
    ext y
    rcases hall y with rfl | rfl <;> simp [hne, hne.symm]
  let Z₀ : IrreducibleCloseds X := ⟨{x₀}, isIrreducible_singleton, hc₀ ▸ h₁.isClosed_compl⟩
  let Z₁ : IrreducibleCloseds X := ⟨Set.univ, hcl ▸ isIrreducible_singleton.closure, isClosed_univ⟩
  have hcases : ∀ Z : IrreducibleCloseds X, Z = Z₀ ∨ Z = Z₁ := by
    intro Z
    by_cases h1 : x₁ ∈ (Z : Set X)
    · refine Or.inr (SetLike.coe_injective (Set.eq_univ_of_univ_subset ?_))
      rw [← hcl]
      exact Z.isClosed.closure_subset_iff.2 (Set.singleton_subset_iff.2 h1)
    · exact Or.inl <| SetLike.coe_injective <| Z.isIrreducible.nonempty.subset_singleton_iff.1
        fun y hy => (hall y).resolve_right fun h => h1 (h ▸ hy)
  have hlt : Z₀ < Z₁ := by
    refine lt_of_le_of_ne (fun y _ => trivial) fun h => hne ?_
    have : x₁ ∈ (Z₀ : Set X) := by rw [h]; trivial
    exact this.symm
  apply le_antisymm
  · rw [topologicalKrullDim, Order.krullDim_le_one_iff]
    intro Z
    rcases hcases Z with rfl | rfl
    · refine Or.inl fun W hW => ?_
      rcases hcases W with rfl | rfl
      · exact le_rfl
      · exact absurd hW (not_le_of_gt hlt)
    · refine Or.inr fun W _ => ?_
      rcases hcases W with rfl | rfl
      · exact hlt.le
      · exact le_rfl
  · rw [topologicalKrullDim]
    exact Order.le_krullDim_iff.2 ⟨⟨1, fun i => if i = 0 then Z₀ else Z₁, fun i => by
      fin_cases i; simpa using hlt⟩, rfl⟩

/-- **A two-point space with exactly one open point is Sierpiński space**: the closed point is
a specialization of the open one, and the Krull dimension is one. -/
@[ega "0 14.1.12" "dim(Y) = 1"]
theorem specializes_and_topologicalKrullDim_eq_one {X : Type*} [TopologicalSpace X] {x₀ x₁ : X}
    (hne : x₀ ≠ x₁) (hall : ∀ y, y = x₀ ∨ y = x₁) (h₁ : IsOpen ({x₁} : Set X))
    (h₀ : ¬ IsOpen ({x₀} : Set X)) : x₁ ⤳ x₀ ∧ topologicalKrullDim X = 1 :=
  ⟨specializes_of_not_isOpen_singleton hne hall h₀,
    topologicalKrullDim_eq_one_of_isOpen_singleton hne hall h₁ h₀⟩

/-- The Krull dimension of a space at an isolated point is `0`: the point is an open
neighbourhood of itself, and a one-point space has dimension `0`. -/
theorem topologicalKrullDimAt_eq_zero_of_isOpen_singleton {X : Type*} [TopologicalSpace X]
    {x : X} (h : IsOpen ({x} : Set X)) : topologicalKrullDimAt X x = 0 := by
  refine le_antisymm (iInf_le_of_le ⟨{x}, rfl, h⟩ ?_) (topologicalKrullDimAt_nonneg x)
  have : DiscreteTopology ({x} : Set X) := Subsingleton.discreteTopology
  exact topologicalKrullDim_zero_of_discreteTopology _

/-- The Krull dimension of a space at a point `x` which is a specialization of every point is the
Krull dimension of the whole space: an open neighbourhood of `x` contains every generization of
`x`, so the only one is the whole space. -/
theorem topologicalKrullDimAt_eq_topologicalKrullDim_of_forall_specializes {X : Type*}
    [TopologicalSpace X] {x : X} (h : ∀ y, y ⤳ x) :
    topologicalKrullDimAt X x = topologicalKrullDim X := by
  refine le_antisymm (topologicalKrullDimAt_le_topologicalKrullDim x) ?_
  obtain ⟨⟨U, hxU, hU, hd⟩, -⟩ := topologicalKrullDimAt_isLeast X x
  obtain rfl : U = Set.univ := Set.eq_univ_of_forall fun y => (h y).mem_open hU hxU
  rw [hd]
  exact (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph).ge

end

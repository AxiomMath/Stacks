module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.Etale
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.EtaleNeighbourhood.SmoothBranches
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalGermAtPoint

/-!
# Local irreducibility of an algebraic stack

Fix `n`. Having exactly `n` geometric branches is a property of a local ring, so having exactly
`n` geometric branches at the distinguished point is a property `𝒫 n` of germs of schemes, and
`𝒫 n` is smooth local (**Stacks 04N1**) because a smooth morphism of schemes preserves the
number of geometric branches at a point (**Stacks 0DQ2**). The four conditions of **Stacks
04YI** comparing `𝒫 n` against the smooth charts of an algebraic stack `𝒳` through a point `x`
are therefore equivalent, and at most one `n` satisfies them. That `n` is the number of
geometric branches of `𝒳` at `x`, and `𝒳` is geometrically unibranch at `x` when it is `1`.

## Main definitions

* `AlgebraicGeometry.GermOfScheme.GeometricBranchCountEq`: the property `𝒫 n` of germs of
  schemes, that the number of geometric branches at the distinguished point is `n`.
* `AlgebraicGeometry.Stack.numberOfGeometricBranches`: **Stacks 0DQH, part (1)**, the number of
  geometric branches of an algebraic stack at a point, with value in `ℕ∞`.
* `AlgebraicGeometry.Stack.IsGeometricallyUnibranchAt`: **Stacks 0DQH, part (2)**, geometric
  unibranchness of an algebraic stack at a point.

## Main results

* `AlgebraicGeometry.GermOfScheme.isSmoothLocal_geometricBranchCountEq`: `𝒫 n` is smooth local.
* `AlgebraicGeometry.Stack.numberOfGeometricBranches_eq_nat_iff`: a finite value of the count is
  exactly the value for which the conditions of Tag 04YI hold.
* `AlgebraicGeometry.Stack.numberOfGeometricBranches_eq_top_iff`: the count is infinite exactly
  when those conditions hold for no natural number.

## Implementation notes

The count is the infimum in `ℕ∞` of the natural numbers `n` for which `𝒫 n` holds on some smooth
scheme chart through the point, so that the empty infimum records the infinite case of the
source. Smooth locality of `𝒫 n` makes the chart condition determine `n`, which is what the two
characterizations below rest on; clients use them rather than unfolding the infimum.

The chart condition used is condition (2) of Tag 04YI, the existential one over charts by a
scheme. Independence of the chart is not assumed here: it is Tag 04YI itself, available as
`AlgebraicGeometry.Stack.tfae_germProperty_at_point`, which also converts the condition into any
of the other three — every scheme chart, every algebraic space chart, some algebraic space
chart.

The number of geometric branches of a *scheme* at a point is
`AlgebraicGeometry.numberOfGeometricBranches` and of an *algebraic space* at a point is
`AlgebraicGeometry.Space.numberOfGeometricBranches` (**Stacks 0DQ4**); only the étale locality of
`𝒫 n` was available, as
`AlgebraicGeometry.GermOfScheme.isEtaleLocal_numberOfGeometricBranches_eq`.

## References

* [Stacks Project, Tag 04N1](https://stacks.math.columbia.edu/tag/04N1)
* [Stacks Project, Tag 04YI](https://stacks.math.columbia.edu/tag/04YI)
* [Stacks Project, Tag 0DQ2](https://stacks.math.columbia.edu/tag/0DQ2)
* [Stacks Project, Tag 0DQH](https://stacks.math.columbia.edu/tag/0DQH)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u w

/-- The property of a germ of schemes that the number of geometric branches at its
distinguished point is `n`, equivalently that its local ring there has `n` geometric
branches. -/
abbrev GermOfScheme.GeometricBranchCountEq (n : ℕ∞) (g : GermOfScheme.{u}) : Prop :=
  numberOfGeometricBranches g.scheme g.point = n

/-- Having a prescribed number of geometric branches is a smooth-local property of germs of
schemes: a smooth morphism of schemes preserves the number of geometric branches at a point,
which is Tag 0DQ2. -/
theorem GermOfScheme.isSmoothLocal_geometricBranchCountEq (n : ℕ∞) :
    GermOfScheme.IsSmoothLocal (GermOfScheme.GeometricBranchCountEq.{u} n) := by
  intro X Y f hf
  obtain ⟨g, -, hg⟩ := hf
  have : Smooth g.hom := hg
  have : Smooth (Scheme.Opens.ι g.source) := inferInstance
  have h := (numberOfGeometricBranches_eq_of_smooth (Scheme.Opens.ι g.source)
      ⟨X.point, g.mem_source⟩).symm.trans
    (numberOfGeometricBranches_eq_of_smooth g.hom ⟨X.point, g.mem_source⟩)
  rw [show Scheme.Opens.ι g.source ⟨X.point, g.mem_source⟩ = X.point from rfl, g.map_point] at h
  show (numberOfGeometricBranches Y.scheme Y.point = n) ↔
    (numberOfGeometricBranches X.scheme X.point = n)
  rw [h]

namespace Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS) (x : points B S hS 𝒳.val.val 𝒳.val.property)

/-- At most one natural number is the number of geometric branches on a smooth scheme chart
through a point of an algebraic stack: smooth locality of the germ property turns one chart
condition into the universal condition of Tag 04YI, which is then read on the other chart. -/
private theorem geometricBranchCountChart_unique {m n : ℕ}
    (hm : GermPropertyAtSomeSchemeChart B S hS 𝒳 x
      (GermOfScheme.GeometricBranchCountEq (m : ℕ∞)))
    (hn : GermPropertyAtSomeSchemeChart B S hS 𝒳 x
      (GermOfScheme.GeometricBranchCountEq (n : ℕ∞))) : m = n := by
  have hall := ((tfae_germProperty_at_point.{u, w} B S hS 𝒳 x _
    (GermOfScheme.isSmoothLocal_geometricBranchCountEq (m : ℕ∞))).out 2 1).mp hm
  obtain ⟨U, a, p, ha, hax, hPp⟩ := hn
  exact_mod_cast (hall U a ha p hax).symm.trans hPp

/-- **Stacks 0DQH, part (1).** The number of geometric branches of an algebraic stack at a
point: the natural number for which the equivalent conditions of Tag 04YI hold for the germ
property of having that many geometric branches, and `⊤` otherwise. -/
@[stacks 0DQH "part (1)"]
def numberOfGeometricBranches : ℕ∞ :=
  sInf {v : ℕ∞ | ∃ n : ℕ, GermPropertyAtSomeSchemeChart B S hS 𝒳 x
    (GermOfScheme.GeometricBranchCountEq (n : ℕ∞)) ∧ v = (n : ℕ∞)}

/-- A smooth scheme chart through the point with `n` geometric branches computes the count: it
puts `n` in the set the infimum is taken over, and uniqueness makes `n` a lower bound. -/
private theorem numberOfGeometricBranches_eq_of_someSchemeChart (n : ℕ)
    (hn : GermPropertyAtSomeSchemeChart B S hS 𝒳 x
      (GermOfScheme.GeometricBranchCountEq (n : ℕ∞))) :
    numberOfGeometricBranches.{u, w} B S hS 𝒳 x = (n : ℕ∞) :=
  le_antisymm (sInf_le ⟨n, hn, rfl⟩)
    (le_sInf fun _ ⟨k, hk, hvk⟩ ↦ by
      rw [hvk, geometricBranchCountChart_unique.{u, w} B S hS 𝒳 x hn hk])

/-- The count is infinite when no smooth scheme chart through the point has a finite number of
geometric branches. -/
private theorem numberOfGeometricBranches_eq_top_of_forall_not
    (h : ∀ n : ℕ, ¬ GermPropertyAtSomeSchemeChart B S hS 𝒳 x
      (GermOfScheme.GeometricBranchCountEq (n : ℕ∞))) :
    numberOfGeometricBranches.{u, w} B S hS 𝒳 x = ⊤ :=
  sInf_eq_top.2 fun _ ⟨n, hn, _⟩ ↦ (h n hn).elim

/-- **Stacks 0DQH, part (1).** A finite value of the number of geometric branches of an
algebraic stack at a point is exactly the value for which the equivalent conditions of Tag 04YI
hold. -/
@[stacks 0DQH "part (1), finite value"]
theorem numberOfGeometricBranches_eq_nat_iff (n : ℕ) :
    numberOfGeometricBranches.{u, w} B S hS 𝒳 x = (n : ℕ∞) ↔
      GermPropertyAtSomeSchemeChart B S hS 𝒳 x
        (GermOfScheme.GeometricBranchCountEq (n : ℕ∞)) := by
  refine ⟨fun h ↦ ?_, numberOfGeometricBranches_eq_of_someSchemeChart.{u, w} B S hS 𝒳 x n⟩
  by_cases hex : ∃ k : ℕ, GermPropertyAtSomeSchemeChart B S hS 𝒳 x
      (GermOfScheme.GeometricBranchCountEq (k : ℕ∞))
  · obtain ⟨k, hk⟩ := hex
    have hkn : k = n := by
      exact_mod_cast
        (numberOfGeometricBranches_eq_of_someSchemeChart.{u, w} B S hS 𝒳 x k hk).symm.trans h
    exact hkn ▸ hk
  · have := numberOfGeometricBranches_eq_top_of_forall_not.{u, w} B S hS 𝒳 x (not_exists.mp hex)
    exact absurd (this.symm.trans h) (ENat.natCast_ne_top n).symm

/-- **Stacks 0DQH, part (1).** The number of geometric branches of an algebraic stack at a point
is infinite exactly when the equivalent conditions of Tag 04YI hold for no natural number. -/
@[stacks 0DQH "part (1), infinite value"]
theorem numberOfGeometricBranches_eq_top_iff :
    numberOfGeometricBranches.{u, w} B S hS 𝒳 x = ⊤ ↔
      ∀ n : ℕ, ¬ GermPropertyAtSomeSchemeChart B S hS 𝒳 x
        (GermOfScheme.GeometricBranchCountEq (n : ℕ∞)) := by
  refine ⟨fun h n hn ↦ ?_, fun h ↦ ?_⟩
  · rw [numberOfGeometricBranches_eq_of_someSchemeChart.{u, w} B S hS 𝒳 x n hn] at h
    exact absurd h (ENat.natCast_ne_top n)
  · exact numberOfGeometricBranches_eq_top_of_forall_not.{u, w} B S hS 𝒳 x h

/-- **Stacks 0DQH, part (2).** An algebraic stack is geometrically unibranch at a point when its
number of geometric branches there is `1`. -/
@[stacks 0DQH "part (2)"]
abbrev IsGeometricallyUnibranchAt : Prop :=
  numberOfGeometricBranches.{u, w} B S hS 𝒳 x = 1

end Stack

end AlgebraicGeometry

end

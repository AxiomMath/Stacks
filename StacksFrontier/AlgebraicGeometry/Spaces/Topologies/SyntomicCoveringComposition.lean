module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Syntomic

/-!
# Composition of syntomic coverings of algebraic spaces (Stacks 041B, composition)

Let `S` be a scheme contained in a big fppf site `B`. Covering every member of a syntomic
covering of an algebraic space over `S` by a syntomic covering of that member gives a syntomic
covering of the original space, indexed by the dependent sum of the two index types. This is
part (2) of **Stacks 041B**; part (1) is
`AlgebraicGeometry.Space.isSyntomicCovering_of_isIso` in
`StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SyntomicCoverings`, and part (3) is
`AlgebraicGeometry.Space.isSyntomicCovering_pullback` in
`StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SyntomicCoveringBaseChange`.

## Main results

* `AlgebraicGeometry.Space.isSyntomicCovering_comp`: **Stacks 041B**, the composition clause.

## Implementation notes

Each member of the composed family is syntomic by **Stacks 03Z8**, and the family is jointly
surjective because a point of the target lifts through the outer covering and that lift again
through the inner one; `AlgebraicGeometry.Space.pointsMap_class` identifies the point obtained
from the two lifts with the one started from.

The two coverings are indexed by types in two unrelated universes `v` and `w`, and the composed
family by the dependent sum, matching the composition clauses of the other covering notions for
algebraic spaces such as `AlgebraicGeometry.Space.isSmoothCovering_comp` and
`AlgebraicGeometry.Space.isPHCovering_comp`.

## References

* [Stacks Project, Tag 03Z8](https://stacks.math.columbia.edu/tag/03Z8)
* [Stacks Project, Tag 041B](https://stacks.math.columbia.edu/tag/041B)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 041B**, the composition clause. A syntomic covering of each member of a syntomic
covering composes to a syntomic covering of the original algebraic space. -/
@[stacks 041B "part (2), composition"]
theorem isSyntomicCovering_comp {I : Type v} (J : I → Type w)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (Xᵢ : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : ∀ i, Xᵢ i ⟶ X)
    (Xᵢⱼ : ∀ i, J i → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (g : ∀ i j, Xᵢⱼ i j ⟶ Xᵢ i)
    (hf : IsSyntomicCovering B S hS Xᵢ f)
    (hg : ∀ i, IsSyntomicCovering B S hS (Xᵢⱼ i) (g i)) :
    IsSyntomicCovering B S hS
      (fun ij : (i : I) × J i => Xᵢⱼ ij.1 ij.2)
      (fun ij => g ij.1 ij.2 ≫ f ij.1) := by
  refine ⟨hf.target_isAlgebraicSpace, fun ij => (hg ij.1).source_isAlgebraicSpace ij.2,
    fun ij => isSyntomic_comp B S hS ((hg ij.1).source_isAlgebraicSpace ij.2)
      (hf.source_isAlgebraicSpace ij.1) hf.target_isAlgebraicSpace _ _
      ((hg ij.1).syntomic ij.2) (hf.syntomic ij.1), ?_⟩
  refine Set.eq_univ_iff_forall.mpr fun p => ?_
  obtain ⟨i, q, rfl⟩ := Set.mem_iUnion.mp (hf.jointly_surjective ▸ Set.mem_univ p)
  obtain ⟨j, r, rfl⟩ := Set.mem_iUnion.mp ((hg i).jointly_surjective ▸ Set.mem_univ q)
  refine Set.mem_iUnion.mpr ⟨⟨i, j⟩, Set.mem_range.mpr ⟨r, ?_⟩⟩
  refine Quot.inductionOn r fun t => ?_
  simp only [pointsMap_class]
  rfl

end AlgebraicGeometry.Space

end

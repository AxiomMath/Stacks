module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypePointsLocallyClosed
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedInducedSubstackLocallyClosed

/-!
# Reduced induced substacks give the hypothesis of Stacks 06G2

`StacksFrontier/AlgebraicGeometry/Stacks/FiniteTypePointsLocallyClosed.lean` follows the source's
proof of **Stacks 06G2** relative to the predicate
`AlgebraicGeometry.Stack.HasReducedInducedSubstacks`. This file derives that predicate from the
two inputs `hOpen` and `hReduced` of `AlgebraicGeometry.Stack.exists_reducedInducedSubstack`
(**Stacks 06FK**), together with **Stacks 06FV**. Stacks 06G2 itself is proved without the
predicate, as `AlgebraicGeometry.Stack.nonempty_inter_and_closure_inter_finiteTypePoints`.

## Main results

* `AlgebraicGeometry.Stack.hasReducedInducedSubstacks_of_openSubstacks_of_reducedStructures`:
  the two inputs of **Stacks 06FK** give the predicate used by the source's proof of
  **Stacks 06G2**.

## References

* [Stacks Project, Tag 06FK](https://stacks.math.columbia.edu/tag/06FK)
* [Stacks Project, Tag 06FV](https://stacks.math.columbia.edu/tag/06FV)
* [Stacks Project, Tag 06G2](https://stacks.math.columbia.edu/tag/06G2)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {𝒳 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 06FK supplies the predicate used by the source's proof of Stacks 06G2.**

`AlgebraicGeometry.Stack.HasReducedInducedSubstacks` asks, for every locally closed `T ⊆ |𝒳|`,
for a 1-morphism onto `T` which is locally of finite type; the immersion that
`AlgebraicGeometry.Stack.exists_reducedInducedSubstack` produces is one, by **Stacks 06FV**.

So `AlgebraicGeometry.Stack.nonempty_inter_finiteTypePoints` and
`AlgebraicGeometry.Stack.subset_closure_inter_finiteTypePoints` do not rest on a gap of their own:
their hypothesis is exactly the two inputs of Stacks 06FK, `_hOpen` and `_hReduced`, and it is
discharged the moment those are. The two reducedness clauses of Stacks 06FK are dropped here,
Stacks 06G2 using only the local finite type of the 1-morphism and its image on points. -/
theorem hasReducedInducedSubstacks_of_openSubstacks_of_reducedStructures
    [(Space.immersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    (_hOpen : ∀ V : Set (AlgebraicStacks.points B S hS 𝒳),
      @IsOpen _ (pointTopology B S hS 𝒳.val) V →
        ∃ 𝒰 : OpenSubstack 𝒳, 𝒰.pointSet B S hS = V)
    (_hReduced : ∀ (𝒴 : Stack.AlgebraicStacks.{u, w} B S hS)
        (Z : Set (AlgebraicStacks.points B S hS 𝒴)),
        @IsClosed _ (pointTopology B S hS 𝒴.val) Z →
      ∃ P : ObjectProperty 𝒴.val.val.obj, IsReducedInducedStackStructure B S hS Z P) :
    HasReducedInducedSubstacks.{u, w} B S hS 𝒳 := by
  intro T hT
  obtain ⟨_, _, _, -, -, himm, -, hrange⟩ := exists_reducedInducedSubstack B S hS T hT
  exact ⟨_, _, AlgebraicStacks.isLocallyOfFiniteType_of_isImmersion B S hS _ himm, hrange⟩

end AlgebraicGeometry.Stack

end

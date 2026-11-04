module

public import StacksFrontier.AlgebraicGeometry.StalkwiseGeneration.Pullback

/-!
# Pullback of a generating family indexed by a type of any universe

`AlgebraicGeometry.generatesStalks_pullbackGlobalSections` says that a generating family of global
sections of an invertible module pulls back to a generating family.  It is stated for an index
type in the universe `u` of the schemes, and that is the only obstacle to using it where the
family is indexed by `Fin (n + 1)`:  a concrete `Type 0`, which lies in `Type u` only when `u`
happens to be `0`.  The morphism to projective space of [Stacks, Tag 01ND] takes exactly such a
family, so the statement is needed with the index universe free.

This file records that form.  Nothing about the mathematics changes;  the index type is carried
through `ULift` at the one step whose input is universe-bound, namely
`Stacks.FinGenFromCover.span_eq_top_of_mem_nonvanishingLocus`, and `ULift.down` being surjective
the set of germs whose span is taken is unchanged.

## Main results

* `AlgebraicGeometry.generatesStalks_pullbackGlobalSections'`: the pullback of a generating family
  generates the stalks, for an index type in an arbitrary universe.

## References

* [Stacks Project, Tag 01AN](https://stacks.math.columbia.edu/tag/01AN)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open Stacks.Ample Stacks.ProjectiveFromSections
open scoped Stacks.ModuleStalk Stacks.FinGenFromCover

universe v u

namespace AlgebraicGeometry

/-- **A generating family of global sections of an invertible module pulls back to a generating
family, for an index type in any universe.**  This is
`AlgebraicGeometry.generatesStalks_pullbackGlobalSections` with the index universe free, which is
what a family indexed by `Fin (n + 1)` needs.

The proof is the same one:  at a point `x` of `X` some member `sᵢ` of the family does not vanish
at `f x`, so its pullback does not vanish at `x`, and a global section of an invertible module
that does not vanish at a point already spans the stalk there.  Only the last step is stated for
an index type in the universe of the schemes, so it is applied to the family reindexed by
`ULift ι`;  `ULift.down` is surjective, so the family of germs whose span is taken is the same
set, and the spans agree. -/
theorem generatesStalks_pullbackGlobalSections' {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
    [IsInvertibleModule Y L] {ι : Type v} (s : ι → Γ(L, ⊤)) (hs : GeneratesStalks s) :
    GeneratesStalks (fun i => pullbackGlobalSections f L (s i)) := by
  refine Stacks.StalkwiseGeneration.generatesStalks_of_span_eq_top
    (M := (Scheme.Modules.pullback f).obj L) _ fun x => ?_
  obtain ⟨i, hi⟩ := exists_mem_nvCover_of_generatesStalks s hs (f.base x)
  have hspan := Stacks.FinGenFromCover.span_eq_top_of_mem_nonvanishingLocus
    ((Scheme.Modules.pullback f).obj L)
    (fun _ : PUnit.{u + 1} => pullbackGlobalSections f L (s i)) (i := PUnit.unit)
    (Stacks.TwistPullbackPinned.mem_nonvanishingLocus_pullbackGlobalSections f L (s i) hi)
  refine eq_top_iff.mpr fun w _ => ?_
  exact Submodule.span_mono (fun _ hz => by obtain ⟨_, rfl⟩ := hz; exact ⟨i, rfl⟩)
    (hspan.ge Submodule.mem_top)

end AlgebraicGeometry

end

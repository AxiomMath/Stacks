module

public import StacksFrontier.AlgebraicGeometry.TwistPullbackRatio.Comparison
public import StacksFrontier.AlgebraicGeometry.Variety.SeparatingPointsTangentVectors.DegreeTwoGeneration

/-!
# Stalkwise generation is preserved by pulling back

Let `L` be an invertible `𝒪_Y`-module and let `s : ι → Γ(Y, L)` be a family of global sections
generating `L` stalkwise. Then for any morphism of schemes `f : X ⟶ Y` the pulled-back family
`i ↦ f^* sᵢ` generates `f^* L` stalkwise.

For an invertible module, generation at a point is nonvanishing of one member of the family
there ([Stacks, Tag 01CY] and Nakayama at a rank-one stalk), and the pullback of a section does
not vanish where the section does not vanish ([Stacks, Tag 0H78]). So the statement needs no
hypothesis on `f` whatsoever: the point `x` of `X` is handed the member that does not vanish at
`f(x)`.

## Main results

* `AlgebraicGeometry.generatesStalks_pullbackGlobalSections`: a generating family of global
  sections of an invertible module pulls back to a generating family.

## Implementation notes

This is hypothesis (2) of [Stacks, Tag 0FD6] — the image of `ψ` generates `ℒ` — in the form in
which it transports to a base change `X_K` of `X` along a field extension `K/k`: the sections of
the base-changed linear system are the pullbacks `f^* ψ(v)` of the sections of the original one,
so they generate the pulled-back module.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public section

open CategoryTheory
open Stacks.Ample Stacks.ProjectiveFromSections

universe u

namespace AlgebraicGeometry

/-- **A generating family of global sections of an invertible module pulls back to a generating
family.** At a point `x` of `X` some member `sᵢ` of the family does not vanish at `f(x)`, so its
pullback does not vanish at `x`, and a global section of an invertible module that does not
vanish at a point already generates the stalk there. -/
theorem generatesStalks_pullbackGlobalSections {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
    [IsInvertibleModule Y L] {ι : Type u} (s : ι → Γ(L, ⊤)) (hs : GeneratesStalks s) :
    GeneratesStalks (fun i => pullbackGlobalSections f L (s i)) := by
  refine Stacks.StalkwiseGeneration.generatesStalks_of_span_eq_top _ fun x => ?_
  obtain ⟨i, hi⟩ := exists_mem_nvCover_of_generatesStalks s hs (f.base x)
  exact Stacks.FinGenFromCover.span_eq_top_of_mem_nonvanishingLocus _ _
    (Stacks.TwistPullbackPinned.mem_nonvanishingLocus_pullbackGlobalSections f L (s i) hi)

end AlgebraicGeometry

end

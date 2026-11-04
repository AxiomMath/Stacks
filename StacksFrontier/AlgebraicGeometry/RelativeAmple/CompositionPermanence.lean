module

public import StacksFrontier.AlgebraicGeometry.RelativeAmple.LocalOnBase

/-!
# Stacks Tag 0C4L: relative ampleness passes to the first factor of a composition

Let `f : X ⟶ Y` and `g : Y ⟶ S` be morphisms of schemes and let `L` be an invertible
`𝒪_X`-module. Stacks Tag 0C4L says that if `L` is ample relative to the composite `g ∘ f` and `f`
is quasi-compact, then `L` is ample relative to `f`.

Relative ampleness is `Stacks.RelativeAmple.IsRelativelyAmple`, [Stacks, Tag 01VH]: the morphism
is quasi-compact and the restriction of the module to the preimage of **every** affine open of the
base is ample.

## Main results

* `Stacks.RelativeAmpleCompositionPermanence.isRelativelyAmple_of_comp`: **Stacks Tag 0C4L**, with
  no premise.

## The route

Both halves of the argument are already in the repository and this file joins them.

`Stacks.RelativeAmpleComposition.isAmple_preimage_of_le_preimage` is the source's local step — for
an affine open `V ⊆ Y` lying inside `g⁻¹U` with `U ⊆ S` affine, the open `f⁻¹V` sits inside
`(g ∘ f)⁻¹U`, where `L` is ample by hypothesis, and ampleness restricts to the quasi-compact open
`f⁻¹V` by [Stacks, Tag 0B3E]. That step reaches only the affine opens `V` lying inside some
`g⁻¹U`, which form a *basis* of `Y` rather than all of its affine opens, and bridging the two is
base-locality: [Stacks, Tag 01VJ], clause (3) implies clause (1).

Base-locality is a theorem here —
`Stacks.RelativeAmpleLocalOnBase.relativeAmpleLocalOnBase` — so the tag is unconditional.

## Implementation notes

The statement is given in the binder order of the source — `f`, `g`, `L`, then the two
hypotheses — with no extra premise.

## References

* [Stacks Project, Tag 0C4L](https://stacks.math.columbia.edu/tag/0C4L)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 01VJ](https://stacks.math.columbia.edu/tag/01VJ)
* [Stacks Project, Tag 0B3E](https://stacks.math.columbia.edu/tag/0B3E)
* [EGA II, Proposition 4.6.13 (ii)]
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.Ample

universe u

namespace Stacks.RelativeAmpleCompositionPermanence

/-- **Stacks Tag 0C4L.** Let `f : X ⟶ Y` and `g : Y ⟶ S` be morphisms of schemes and let `L` be
an invertible `𝒪_X`-module. If `L` is ample relative to `g ∘ f` and `f` is quasi-compact, then
`L` is ample relative to `f`.

Through a point `y : Y` choose an affine open `U ⊆ S` containing `g(y)` and then, since the affine
opens of `Y` are a basis, an affine open `V` with `y ∈ V ≤ g⁻¹U`. On that `V` the restriction of
`L` is ample by `Stacks.RelativeAmpleComposition.isAmple_preimage_of_le_preimage`. These `V` cover
`Y`, and `Stacks.RelativeAmpleLocalOnBase.relativeAmpleLocalOnBase` — [Stacks, Tag 01VJ], clause
(3) implies clause (1) — upgrades them to every affine open of `Y`. -/
@[stacks 0C4L]
theorem isRelativelyAmple_of_comp {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] (hL : Stacks.RelativeAmple.IsRelativelyAmple (f ≫ g) L)
    (hf : QuasiCompact f) :
    Stacks.RelativeAmple.IsRelativelyAmple f L := by
  refine Stacks.RelativeAmpleLocalOnBase.relativeAmpleLocalOnBase X Y f L inferInstance hf
    fun y => ?_
  obtain ⟨-, ⟨U, hU, rfl⟩, hgyU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g.base y)) isOpen_univ
  obtain ⟨-, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (a := y) hgyU (g ⁻¹ᵁ U).isOpen
  have := hf
  exact ⟨V, hV, hyV, Stacks.RelativeAmpleComposition.isAmple_preimage_of_le_preimage f g L
    (U := U) hVU hV.isCompact (hL.2 U hU)⟩

end Stacks.RelativeAmpleCompositionPermanence

end

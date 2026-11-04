module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationResolutionAugmentationTranspose

/-!
# The comparison with the resolution, followed by its augmentation, is the counit

Let `S` be a simplicial-site situation and `F` an abelian sheaf on its total site. The canonical
map `g_{0!}(F_0) ⟶ bar_0(F)` of `componentLowerShriekMap'` is the transpose, along
`g_{0!} ⊣ g_0^{-1}`, of the inclusion of `F_0` as the summand of `bar_0(F)|_0` labelled by the
identity simplex map, and `componentSheafInclusion_comp_barAugmentation` says that that summand
inclusion followed by the restriction of the augmentation of the resolution is the identity. So
the comparison followed by the augmentation is the transpose of the identity, which is the counit
of the adjunction.

This is the resolution-side half of the degree-zero reading of Stacks 0D9K: the source's `X₀ ⟶ K`
is, through Stacks 0D9E, the counit `g_{0!}K_0 ⟶ K`, and the transpose of the counit is the
identity, which is what identifies the degree-zero restriction of the morphism the source
constructs with the given one.

## Main results

* `CategoryTheory.SimplicialSiteSituation.componentLowerShriekMap_comp_barAugmentation`: **the
  canonical map `g_{0!}(F_0) ⟶ bar_0(F)` followed by the augmentation of the resolution is the
  counit of `g_{0!} ⊣ g_0^{-1}`.**

## References

* [Stacks Project, Tag 0D78](https://stacks.math.columbia.edu/tag/0D78)
* [Stacks Project, Tag 0D9K](https://stacks.math.columbia.edu/tag/0D9K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (F : Sheaf S.totalTopology Ab.{u})

/-- **The canonical map `g_{0!}(F_0) ⟶ bar_0(F)` followed by the augmentation of the resolution
of Stacks 0D78 is the counit of `g_{0!} ⊣ g_0^{-1}`.** Both sides have the identity of `F_0` as
their transpose: for the left-hand side because the comparison is the transpose of the
identity-labelled summand inclusion and that inclusion followed by the restricted augmentation is
the identity (`componentSheafInclusion_comp_barAugmentation`), and for the counit because that is
the triangle identity of the adjunction. -/
theorem componentLowerShriekMap_comp_barAugmentation :
    (componentLowerShriekMap' S ⦋0⦌).app F ≫ barAugmentation' S F =
      (S.componentLowerShriekAbAdjunction' ⦋0⦌).counit.app F := by
  refine ((S.componentLowerShriekAbAdjunction' ⦋0⦌).homEquiv _ _).injective ?_
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    show (S.componentLowerShriekAbAdjunction' ⦋0⦌).unit.app ((S.restrictAb ⦋0⦌).obj F) ≫
        (S.restrictAb ⦋0⦌).map ((componentLowerShriekMap' S ⦋0⦌).app F) =
      (componentSheafInclusion' S ⦋0⦌).app F from
      ((S.componentLowerShriekAbAdjunction' ⦋0⦌).homEquiv_unit _ _ _).symm.trans
        (((S.componentLowerShriekAbAdjunction' ⦋0⦌).homEquiv _ _).apply_symm_apply _),
    componentSheafInclusion_comp_barAugmentation,
    (S.componentLowerShriekAbAdjunction' ⦋0⦌).right_triangle_components]

end CategoryTheory.SimplicialSiteSituation

end

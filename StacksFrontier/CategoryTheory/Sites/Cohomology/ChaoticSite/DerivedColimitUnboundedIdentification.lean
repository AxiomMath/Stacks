module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitUnboundedFunctoriality

/-!
# Restricting the unit of `colim ⊣ const` along a functor

For a functor `f : C' ⥤ C` of small categories and a diagram `G : Cᵒᵖ ⥤ D`, restricting the unit
of `colim_{Cᵒᵖ} ⊣ const_{Cᵒᵖ}` at `G` along `f.op` gives the unit of `colim_{C'ᵒᵖ} ⊣ const_{C'ᵒᵖ}`
at `f.op ⋙ G` followed by the constant diagram of `colimit.pre G f.op`.

## Main results

* `Stacks.ChaoticSite.restrict_colimConstAdj_unit`: for a diagram `G : Cᵒᵖ ⥤ D`, the
  restriction of `η_G` along `f.op` is `η'_{f.op ⋙ G} ≫ const_{C'ᵒᵖ}(colimit.pre G f.op)`.

## References

* [Stacks Project, Tag 08QA](https://stacks.math.columbia.edu/tag/08QA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.CategoryHomology

namespace Stacks.ChaoticSite

universe uD vD u

variable {C C' : Type u} [SmallCategory C] [SmallCategory C'] (f : C' ⥤ C)
  (D : Type uD) [Category.{vD} D] [HasColimitsOfShape Cᵒᵖ D] [HasColimitsOfShape C'ᵒᵖ D]

/-- Restriction along `f.op` carries the unit of `colim ⊣ const` at `G` to the unit of
`colim ⊣ const` at `f.op ⋙ G` followed by the constant diagram of the comparison
`colimit.pre G f.op` (`Stacks.CategoryHomology.diagramColimitRestrictionPre`). -/
theorem restrict_colimConstAdj_unit (G : Cᵒᵖ ⥤ D) :
    ((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).map
        ((colimConstAdj : (colim : (Cᵒᵖ ⥤ D) ⥤ D) ⊣ Functor.const Cᵒᵖ).unit.app G) =
      (colimConstAdj : (colim : (C'ᵒᵖ ⥤ D) ⥤ D) ⊣ Functor.const C'ᵒᵖ).unit.app
          (((Functor.whiskeringLeft C'ᵒᵖ Cᵒᵖ D).obj f.op).obj G) ≫
        (Functor.const C'ᵒᵖ : D ⥤ (C'ᵒᵖ ⥤ D)).map
          ((diagramColimitRestrictionPre f D).app G) := by
  ext V
  exact (colimit.ι_pre G f.op V).symm

end Stacks.ChaoticSite

end

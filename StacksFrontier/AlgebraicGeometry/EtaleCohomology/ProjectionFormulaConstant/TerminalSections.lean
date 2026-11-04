module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules

/-!
# Global sections of a sheaf of modules on a site with a terminal object

On a site with a terminal object `T`, the compatible families of sections of a sheaf of modules
are its sections over `T`. This is recorded as an isomorphism of functors to abelian groups,
`Stacks.EtaleCohomology.ProjectionFormulaConstant.globalSectionsForgetIsoOfIsTerminal`, between
`Stacks.Cohomology.SiteModules.globalSectionsFunctor` and sections over `T`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v w r

namespace Stacks.EtaleCohomology.ProjectionFormulaConstant

open Stacks.Cohomology.SiteModules

variable {C : Type w} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r})

/-- On a site with a terminal object `T`, a global section of a sheaf of modules is its value
at `T`. -/
def sectionsAddEquivOfIsTerminal {T : C} (hT : IsTerminal T) (M : SheafOfModules.{w} R) :
    M.sections ≃+ M.val.obj (op T) where
  toFun s := s.eval (op T)
  invFun x := M.val.sectionsMk (fun U => M.val.map (hT.from U.unop).op x) (fun U V g => by
    have h : (hT.from U.unop).op ≫ g = (hT.from V.unop).op := Quiver.Hom.unop_inj (hT.hom_ext _ _)
    rw [← PresheafOfModules.map_comp_apply, h])
  left_inv s := PresheafOfModules.sections_ext _ _ fun _ => PresheafOfModules.sections_property s _
  right_inv x := by
    change (M.val.map (hT.from T).op) x = x
    rw [hT.hom_ext (hT.from T) (𝟙 T), op_id, PresheafOfModules.map_id]
    rfl
  map_add' _ _ := rfl

/-- **Global sections of sheaves of modules on a site with a terminal object `T` are the
sections at `T`**, as abelian groups, naturally. -/
def globalSectionsForgetIsoOfIsTerminal {T : C} (hT : IsTerminal T) :
    globalSectionsFunctor R ⋙ forget₂ _ AddCommGrpCat.{w} ≅
      SheafOfModules.toSheaf R ⋙ (sheafSections J AddCommGrpCat.{w}).obj (op T) :=
  NatIso.ofComponents (fun M => (sectionsAddEquivOfIsTerminal R hT M).toAddCommGrpIso)
    (fun _ => rfl)

end Stacks.EtaleCohomology.ProjectionFormulaConstant

module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsInitial

/-!
# Global sections at an initial object, at independent universes

If `X` is an initial object of `Cᵒᵖ` (a terminal object of the site), the global sections of a
sheaf of modules are its sections at `X`.
`Stacks.Cohomology.SiteModules.globalSectionsEquivInitial` states this when the site, the
structure rings and the modules live in one universe.  This file states it with all four universes
independent, and records the resulting comparison of the global-sections functor with evaluation
at `X` on underlying abelian groups, the sections at `X` being lifted to the universe of the
global sections.  That is the form needed on the small étale site of an algebraic space, whose
objects live one universe above its modules.

## Main results

* `Stacks.Cohomology.SiteModules.globalSectionsEquivOfIsInitial`;
* `Stacks.Cohomology.SiteModules.globalSectionsFunctorForgetIsoEvaluation`.

These statements extend
`StacksFrontier/CategoryTheory/Sites/Cohomology/Modules/GlobalSectionsInitial.lean`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v r w

namespace Stacks.Cohomology.SiteModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Sheaf J RingCat.{r}) [∀ X : Cᵒᵖ, IsMulCommutative (O.obj.obj X)]

/-- Evaluation at an initial object `X` of `Cᵒᵖ` is a bijection from the compatible families of
sections of an `O`-module to its sections at `X`, with the universes of the objects and morphisms
of the site, of the structure rings and of the module all independent.
`Stacks.Cohomology.SiteModules.globalSectionsEquivInitial` is the case of a single universe. -/
def globalSectionsEquivOfIsInitial (M : SheafOfModules.{w} O) (X : Cᵒᵖ) (hX : IsInitial X) :
    GlobalSections O M ≃ M.val.obj X := by
  refine Equiv.ofBijective (fun s => s.eval X) ?_
  constructor
  · intro s t hst
    refine Subtype.ext (funext fun Y => ?_)
    have hs := s.2 (hX.to Y)
    have ht := t.2 (hX.to Y)
    exact hs.symm.trans ((congrArg (M.val.map (hX.to Y)) hst).trans ht)
  · intro a
    refine ⟨⟨fun Y => M.val.map (hX.to Y) a, ?_⟩, ?_⟩
    · intro Y Z f
      change M.val.map f (M.val.map (hX.to Y) a) = _
      rw [← PresheafOfModules.map_comp_apply, hX.hom_ext (hX.to Y ≫ f) (hX.to Z)]
    · change M.val.map (hX.to X) a = a
      rw [hX.hom_ext (hX.to X) (𝟙 X)]
      simp only [PresheafOfModules.map_id]
      rfl

/-- Evaluation at an initial object `X` of `Cᵒᵖ`, naturally in the module, on underlying abelian
groups and at an arbitrary module universe: the global sections of an `O`-module, which live in
the universe `max u w`, are its sections at `X`, lifted to that universe. -/
def globalSectionsFunctorForgetIsoEvaluation (X : Cᵒᵖ) (hX : IsInitial X) :
    globalSectionsFunctor.{u, v, r, w} O ⋙
        forget₂ (ModuleCat.{max u w} ↥(GlobalSectionRing O)) AddCommGrpCat.{max u w} ≅
      SheafOfModules.evaluation.{w} O X ⋙ forget₂ (ModuleCat.{w} (O.obj.obj X)) AddCommGrpCat.{w} ⋙
        AddCommGrpCat.uliftFunctor.{max u w, w} :=
  NatIso.ofComponents
    (fun M => AddEquiv.toAddCommGrpIso
      { (globalSectionsEquivOfIsInitial O M X hX).trans Equiv.ulift.symm with
        map_add' := fun _ _ => rfl })
    (fun _ => rfl)

end Stacks.Cohomology.SiteModules

end

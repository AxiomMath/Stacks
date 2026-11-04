module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules

/-!
# Global sections of a sheaf of modules over a site with a terminal object

On a site with a terminal object `V`, a compatible family of sections of a sheaf of modules is
determined by, and may be prescribed arbitrarily as, its value at `V`: every object of the site
has exactly one morphism to `V`, so the value at an object is forced to be the restriction of the
value at `V`, and those restrictions are automatically compatible.

Accordingly the global-sections functor `Stacks.Cohomology.SiteModules.globalSectionsFunctor` is
evaluation at `V`, read over the ring of global sections through
`Stacks.Cohomology.SiteModules.globalSectionEval` and lifted to the universe in which the
compatible families live.  Restriction of scalars and the universe lift are exact, so the same
holds of the right derived functors; in particular the vanishing of the derived sections over `V`
gives the vanishing of the derived global sections.

## Main definitions

* `Stacks.Cohomology.SiteModules.globalSectionsEvalLinear`: evaluation of a compatible family at
  an object, as a map of modules over the ring of global sections.
* `Stacks.Cohomology.SiteModules.globalSectionsIsoEvaluation`: **the global-sections functor is
  evaluation at a terminal object**, as a natural isomorphism.

## Main results

* `Stacks.Cohomology.SiteModules.bijective_globalSectionsEval`: evaluation at a terminal object is
  bijective on compatible families.

## Implementation notes

The ring of global sections lies in the universe `max u r` of the objects of the site and of the
sections of the structure sheaf, while the sections of the structure sheaf over a single object
lie in `Type r`.  The two are identified by `globalSectionEval` at a terminal object, which is a
bijection by the same argument as for modules — but that is not needed here: restriction of
scalars along the ring *map* suffices, so no ring isomorphism has to be formed.

The module universes differ in the same way, compatible families lying in `Type (max u w)` and
the sections over one object in `Type w`, so `CategoryTheory.ModuleCat.uliftFunctor` is inserted.
Both it and `CategoryTheory.ModuleCat.restrictScalars` are additive and exact, which is what
carries the isomorphism through `CategoryTheory.Functor.rightDerived` and what makes them
preserve zero objects.

## References

* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology.SiteModules

universe u v r w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (O : Sheaf J RingCat.{r})

/-- Evaluation of a compatible family of sections at an object of the site, as a map of modules
over the ring of global sections of the structure sheaf: the scalars of the target are restricted
along `Stacks.Cohomology.SiteModules.globalSectionEval`, and the universe lift puts the target in
the universe the compatible families live in. -/
def globalSectionsEvalLinear (V : C) (M : SheafOfModules.{w} O) :
    (globalSectionsFunctor.{u, v, r, w} O).obj M ⟶
      (ModuleCat.uliftFunctor.{max u w}
          (RingCat.sectionsSubring O.obj)).obj
        ((ModuleCat.restrictScalars (globalSectionEval O (op V))).obj
          ((SheafOfModules.evaluation O (op V)).obj M)) :=
  ModuleCat.ofHom
    { toFun := fun s ↦ ULift.up (s.eval (op V))
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

/-- The map `globalSectionsEvalLinear O V M` sends a compatible family `s` to its value at `V`. -/
@[simp]
theorem globalSectionsEvalLinear_apply (V : C) (M : SheafOfModules.{w} O) (s : M.sections) :
    (globalSectionsEvalLinear O V M).hom s = ULift.up (s.eval (op V)) :=
  rfl

variable {V : C}

/-- **Evaluation at a terminal object is bijective on compatible families.** -/
theorem bijective_globalSectionsEval (hV : IsTerminal V) (M : SheafOfModules.{w} O) :
    Function.Bijective (globalSectionsEvalLinear O V M).hom := by
  have key : ∀ (s : M.sections) (X : Cᵒᵖ),
      (M.val.presheaf ⋙ forget _).map (hV.from X.unop).op (s.1 (op V)) = s.1 X :=
    fun s X ↦ s.2 (hV.from X.unop).op
  refine ⟨fun s t hst ↦ Subtype.ext (funext fun X ↦ ?_), fun x ↦ ?_⟩
  · rw [← key s X, ← key t X]
    exact congrArg _ (congrArg ULift.down hst)
  · refine ⟨⟨fun X ↦ (M.val.presheaf ⋙ forget _).map (hV.from X.unop).op
      (show (M.val.presheaf ⋙ forget _).obj (op V) from x.down), ?_⟩, ?_⟩
    · intro X Y f
      show (M.val.presheaf ⋙ forget _).map f
        ((M.val.presheaf ⋙ forget _).map (hV.from X.unop).op _) = _
      rw [← FunctorToTypes.map_comp_apply,
        show (hV.from X.unop).op ≫ f = (hV.from Y.unop).op from
          Quiver.Hom.unop_inj (hV.hom_ext _ _)]
    · refine ULift.ext _ _ ?_
      show (M.val.presheaf ⋙ forget _).map (hV.from V).op
        (show (M.val.presheaf ⋙ forget _).obj (op V) from x.down) = x.down
      rw [show (hV.from V).op = 𝟙 (op V) from Quiver.Hom.unop_inj (hV.hom_ext _ _),
        FunctorToTypes.map_id_apply]

/-- **The global-sections functor is evaluation at a terminal object of the site**, read over the
ring of global sections and lifted to the universe of the compatible families. -/
def globalSectionsIsoEvaluation (hV : IsTerminal V) :
    globalSectionsFunctor.{u, v, r, w} O ≅
      SheafOfModules.evaluation O (op V) ⋙
        ModuleCat.restrictScalars (globalSectionEval O (op V)) ⋙
        ModuleCat.uliftFunctor.{max u w} (RingCat.sectionsSubring O.obj) :=
  NatIso.ofComponents
    (fun M ↦ (LinearEquiv.ofBijective (globalSectionsEvalLinear O V M).hom
      (bijective_globalSectionsEval O hV M)).toModuleIso)
    (fun _ ↦ rfl)

end Stacks.Cohomology.SiteModules

end

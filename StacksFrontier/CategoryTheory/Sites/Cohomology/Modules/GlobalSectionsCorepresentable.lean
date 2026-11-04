module

public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Global sections of modules on a site are corepresented by the structure sheaf

For a sheaf of rings `O` on a site `(C, J)`, the functor
`Stacks.Cohomology.SiteModules.globalSectionsFunctor` of global sections of `O`-modules is
corepresented by `CategoryTheory.SheafOfModules.unit O`, the structure sheaf read as a module
over itself: a map `O ⟶ M` is the same thing as a global section of `M`.  Consequently global
sections are left exact.

The point of this file is the *universes*.  `globalSectionsFunctor.{u, v, r, w}` takes
`O`-modules with sections in a universe `w` to modules over `Γ(C, O)` in the universe
`max u w`, where `u` is the universe of the objects of the site; its left exactness is already
in the library twice, but both times with the module universe constrained:

* `Stacks.Cohomology.SiteModules.globalSectionsFunctor_preservesFiniteLimits` of
  `StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.FirstCohomologyAndExtensions` forces
  all four universes equal, `u = v = r = w`;
* `Stacks.Cohomology.SiteModules.preservesFiniteLimits_globalSectionsFunctor` of
  `StacksFrontier.AlgebraicGeometry.Spaces.CohomologyDegreeZero` leaves the site free but forces
  the module universe to contain the universe of the objects of the site, `w = max u w'`.

Neither is available on the small étale site of an algebraic space over a `Scheme.{u}`, whose
objects lie in `Type (u + 1)` while its structure sheaf and its modules lie at `u`: the first
needs `u + 1 = u`, and the second needs `max (u + 1) w' = w'`.  What *is* available there is
the case `w = r` of a module universe equal to the universe of the structure rings — which is
exactly the case in which the structure sheaf is itself a module, so the corepresentability
argument applies.  That case, with the two universes of the site free, is proved here.

## Main definitions

* `Stacks.Cohomology.SiteModules.unitSectionsAddEquiv`: maps out of the structure sheaf are its
  global sections, as an additive equivalence.
* `Stacks.Cohomology.SiteModules.coyonedaUnitGlobalSectionsIso`: the corepresentability
  isomorphism `Hom(O, -) ≅ Γ(C, -)` of functors to abelian groups.

## Main results

* `Stacks.Cohomology.SiteModules.preservesFiniteLimits_globalSectionsFunctor_ringUniverse`:
  **global sections of `O`-modules whose sections lie in the universe of the structure rings
  preserve finite limits**, on an arbitrary site.

## Implementation notes

No universe lift appears, and none is possible: the hom types of `SheafOfModules.{r} O` on a
site with objects in `Type u` lie in `Type (max u r)`, which is precisely the universe of
`globalSectionsFunctor.{u, v, r, r}`'s values, so `CategoryTheory.preadditiveCoyoneda` applied
to the structure sheaf and the forgetful functor from those values land in one and the same
`AddCommGrpCat.{max u r}`.  This is the reason the statement is free of the site's universes
whereas the comparison with `CategoryTheory.Sheaf.Γ` is not: the latter compares values in
`AddCommGrpCat.{max u w}` with a functor valued in `AddCommGrpCat.{w}`.

`Stacks.Cohomology.SiteModules.unitSectionsAddEquiv` is
`CategoryTheory.SheafOfModules.unitHomEquiv` promoted to an additive equivalence.  It is re-proved
rather than taken from `Stacks.Cohomology.SiteModules.unitHomAddEquiv` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.FirstCohomologyAndExtensions`, which is the
same statement on a `CategoryTheory.SmallCategory` site with all universes equal; the proof is four
lines and the generalisation cannot be obtained from the special case.  For the same reason
`Stacks.Cohomology.SiteModules.coyonedaUnitGlobalSectionsIso` is not
`Stacks.Cohomology.SiteModules.unitCoyonedaSectionsIso` of that module: that isomorphism is stated
with both sides pushed one universe up by `CategoryTheory.AddCommGrpCat.uliftFunctor`, because it
is compared there with `Ext` groups, and the lift is what makes it useless as a source of left
exactness at a site whose objects outrun its morphisms.

No `@[stacks]` attribute is carried: left exactness of global sections is not an enumerated
part of [Stacks, Tag 071H], which is registered in
`StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules` on the construction of
cohomology itself.

## References

* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v r

namespace Stacks.Cohomology.SiteModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Maps out of the structure sheaf are its global sections, as an additive equivalence: this is
`CategoryTheory.SheafOfModules.unitHomEquiv`, whose additivity is checked section by section. -/
def unitSectionsAddEquiv (R : Sheaf J RingCat.{r}) (M : SheafOfModules.{r} R) :
    (SheafOfModules.unit R ⟶ M) ≃+ M.sections := by
  let f : (SheafOfModules.unit R ⟶ M) →+ M.sections :=
    { toFun := M.unitHomEquiv
      map_zero' := by
        apply Subtype.ext
        funext Y
        rw [SheafOfModules.unitHomEquiv_apply_coe]
        rfl
      map_add' := by
        intro g h
        apply Subtype.ext
        funext Y
        rw [SheafOfModules.unitHomEquiv_apply_coe]
        rfl }
  exact AddEquiv.ofBijective f M.unitHomEquiv.bijective

/-- **`Hom(O, -) = Γ(C, -)`.**  Global sections of `O`-modules whose sections lie in the universe
of the structure rings, read in abelian groups, are corepresented by the structure sheaf.

The components are `Stacks.Cohomology.SiteModules.unitSectionsAddEquiv` and naturality is
`CategoryTheory.SheafOfModules.unitHomEquiv_comp_apply`. -/
def coyonedaUnitGlobalSectionsIso (R : Sheaf J RingCat.{r}) :
    preadditiveCoyoneda.obj (op (SheafOfModules.unit R)) ≅
      globalSectionsFunctor.{u, v, r, r} R ⋙
        forget₂ (ModuleCat.{max u r} (RingCat.sectionsSubring R.obj))
          AddCommGrpCat.{max u r} :=
  NatIso.ofComponents (fun M => (unitSectionsAddEquiv R M).toAddCommGrpIso) (by
    intro M N f
    ext g
    change N.unitHomEquiv (g ≫ f) = SheafOfModules.sectionsMap f (M.unitHomEquiv g)
    exact SheafOfModules.unitHomEquiv_comp_apply g f)

/-- **Global sections of sheaves of modules on a site are left exact**, with no constraint on
the universes of the site, provided the module sections lie in the universe of the structure
rings.

The functor is corepresented by the structure sheaf
(`Stacks.Cohomology.SiteModules.coyonedaUnitGlobalSectionsIso`), and a corepresentable functor
to abelian groups preserves all limits; the forgetful functor from modules over the ring of
global sections reflects them. -/
@[sga "4½ Arcata 1.6.5" "more general"]
theorem preservesFiniteLimits_globalSectionsFunctor_ringUniverse (R : Sheaf J RingCat.{r}) :
    PreservesFiniteLimits (globalSectionsFunctor.{u, v, r, r} R) := by
  have h : PreservesFiniteLimits (globalSectionsFunctor.{u, v, r, r} R ⋙
      forget₂ (ModuleCat.{max u r} (RingCat.sectionsSubring R.obj))
        AddCommGrpCat.{max u r}) :=
    preservesFiniteLimits_of_natIso (coyonedaUnitGlobalSectionsIso R)
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (forget₂ (ModuleCat.{max u r} (RingCat.sectionsSubring R.obj)) AddCommGrpCat.{max u r})

end Stacks.Cohomology.SiteModules

end

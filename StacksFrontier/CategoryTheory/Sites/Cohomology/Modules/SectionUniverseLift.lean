module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UliftForPresentationPreservesInjectives
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftDerived

/-!
# Cohomology of sheaves of modules does not depend on the universe of the sections

Let `R` be a sheaf of rings on a site `C` and `M` a sheaf of `R`-modules. The cohomology
`Hⁱ(C, M)` of Stacks 071H is the right derived functor of the global sections functor
`Stacks.Cohomology.SiteModules.globalSectionsFunctor`, computed in the category of sheaves of
modules whose sections lie in some universe. Raising that universe, by
`SheafOfModules.uliftForPresentation`, does not change the cohomology: the cohomology of the
lifted module is the universe lift of the cohomology of `M`, over the ring `Γ(C, R)` of global
sections of the structure sheaf.

Global sections commute with the lift on the nose, sectionwise. The lift of sheaves of modules
is exact and carries injective objects to injective objects
(`SheafOfModules.uliftForPresentationFunctor_preservesInjectiveObjects`), so it carries an
injective resolution of `M` to one of its lift, and the universe lift of modules is exact, so it
commutes with taking cohomology of the complex of global sections.

## Main definitions

* `Stacks.Cohomology.SiteModules.globalSectionsUliftIso`: global sections commute with the
  universe lift of the sections, naturally in the sheaf of modules.
* `Stacks.Cohomology.SiteModules.rightDerivedGlobalSectionsUliftIso`: **the cohomology of the
  universe lift of a sheaf of modules is the universe lift of its cohomology**, naturally in the
  sheaf of modules and in every degree.

## Implementation notes

The comparison is stated from the universe `max v r` of the hom-sets and the rings to a
universe `max u v r t` containing the site as well, the generality in which
`SheafOfModules.uliftForPresentationFunctor_preservesInjectiveObjects` holds. The abelian
structures on both categories of sheaves of modules are Mathlib's `SheafOfModules.instAbelian`,
whose instance arguments are propositions, so the derived functors do not depend on how those
arguments are supplied.

## References

* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t u v r m

namespace Stacks.Cohomology.SiteModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r})

/-- The global sections of the universe lift of a sheaf of modules are, linearly over the ring
of global sections of the structure sheaf, the universe lift of its global sections. -/
def globalSectionsUliftLinearEquiv (M : SheafOfModules.{m} R) :
    ULift.{t} M.sections ≃ₗ[RingCat.sectionsSubring R.obj]
      (SheafOfModules.uliftForPresentation.{u, v, r, m, t} M).sections where
  toFun x := (SheafOfModules.uliftForPresentation.{u, v, r, m, t} M).val.sectionsMk
    (fun X ↦ ULift.up (x.down.eval X))
    (fun _ _ f ↦ congrArg ULift.up (M.val.sections_property x.down f))
  invFun s := ULift.up (M.val.sectionsMk (fun X ↦ (s.eval X).down)
    (fun _ _ f ↦ congrArg ULift.down
      ((SheafOfModules.uliftForPresentation.{u, v, r, m, t} M).val.sections_property s f)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Global sections commute with the universe lift of the sections**, naturally in the sheaf
of modules: a compatible family of lifted sections is the lift of a compatible family of
sections. -/
def globalSectionsUliftIso :
    globalSectionsFunctor.{u, v, r, m} R ⋙ ModuleCat.uliftFunctor.{t} _ ≅
      SheafOfModules.uliftForPresentationFunctor.{u, v, r, m, t} ⋙
        globalSectionsFunctor.{u, v, r, max t m} R :=
  NatIso.ofComponents (fun M ↦ (globalSectionsUliftLinearEquiv.{t} R M).toModuleIso)
    (fun _ ↦ rfl)

section Derived

attribute [local instance 5000] SheafOfModules.instAbelian

variable [HasSheafify J AddCommGrpCat.{max v r}] [J.WEqualsLocallyBijective AddCommGrpCat.{max v r}]
  [HasSeparator (SheafOfModules.{max v r} R)] [HasInjectiveResolutions (SheafOfModules.{max v r} R)]
  [HasSheafify J AddCommGrpCat.{max u v r t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r t}]
  [HasInjectiveResolutions (SheafOfModules.{max u v r t} R)]

/-- **Cohomology of sheaves of modules commutes with the universe lift of the sections.**  For
a sheaf of `R`-modules `M` with sections in the universe `max v r` of the hom-sets and the
rings, and every degree `q`, the cohomology `H^q(C, M)` lifted to the universe `max u v r t` is
`H^q` of the universe lift of `M`, naturally in `M`, as modules over the global sections of `R`.

The lift of sheaves of modules is exact and preserves injective objects, the universe lift of
modules is exact, and global sections commute with both
(`Stacks.Cohomology.SiteModules.globalSectionsUliftIso`); this is
`CategoryTheory.Functor.rightDerivedIsoOfSquare` applied to that square. -/
def rightDerivedGlobalSectionsUliftIso (q : ℕ) :
    (globalSectionsFunctor.{u, v, r, max v r} R).rightDerived q ⋙
        ModuleCat.uliftFunctor.{max u v r t} _ ≅
      SheafOfModules.uliftForPresentationFunctor.{u, v, r, max v r, max u v r t} ⋙
        (globalSectionsFunctor.{u, v, r, max u v r t} R).rightDerived q := by
  let U := SheafOfModules.uliftForPresentationFunctor.{u, v, r, max v r, max u v r t} (R := R)
  have : U.PreservesInjectiveObjects :=
    SheafOfModules.uliftForPresentationFunctor_preservesInjectiveObjects.{u, v, r, t} R
  have : PreservesFiniteColimits U :=
    SheafOfModules.preservesFiniteColimits_uliftForPresentationFunctor.{u, v, r, max v r,
      max u v r t}
  have : U.Additive := ⟨fun {_ _ _ _} ↦ by ext; rfl⟩
  have : (ModuleCat.uliftFunctor.{max u v r t} (RingCat.sectionsSubring R.obj)).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  exact Functor.rightDerivedIsoOfSquare U _ _ _ (globalSectionsUliftIso.{max u v r t} R) q

end Derived

end Stacks.Cohomology.SiteModules

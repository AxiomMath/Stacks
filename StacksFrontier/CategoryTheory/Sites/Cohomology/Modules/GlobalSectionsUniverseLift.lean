module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UliftForPresentationPreservesInjectives
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentClosure
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.SectionUniverseLift
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftDerived

/-!
# The cohomology of a sheaf of modules does not depend on the universe of its sections

Let `R` be a sheaf of rings on a site `C` and `M` a sheaf of `R`-modules. The cohomology
`Hⁱ(C, M)` of Stacks 071H is the right derived functor of the global sections functor
`Stacks.Cohomology.SiteModules.globalSectionsFunctor`, computed among sheaves of modules whose
sections lie in a fixed universe. Raising that universe by `SheafOfModules.uliftForPresentation`
does not change it: the cohomology of the lifted module is the universe lift of the cohomology of
`M`, linearly over the ring `Γ(C, R)` of global sections of the structure sheaf.

## Main definitions

The constructions of this file are those of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Modules/SectionUniverseLift.lean`; the names below
are kept as aliases of them.

* `Stacks.Cohomology.SiteModules.globalSectionsUliftForPresentationIso`: global sections commute
  with the universe lift of the sections, naturally in the sheaf of modules; an alias of
  `Stacks.Cohomology.SiteModules.globalSectionsUliftIso`.
* `Stacks.Cohomology.SiteModules.rightDerivedGlobalSectionsUliftForPresentationIso`: **the
  cohomology of the universe lift of a sheaf of modules is the universe lift of its cohomology**,
  naturally, in every degree; an alias of
  `Stacks.Cohomology.SiteModules.rightDerivedGlobalSectionsUliftIso`.

## Implementation notes

Global sections commute with the lift on the nose, sectionwise. The lift is exact and preserves
injective objects (`SheafOfModules.uliftForPresentationFunctor_preservesInjectiveObjects`), and
the universe lift of modules is exact, so `CategoryTheory.Functor.rightDerivedIsoOfSquare`
applies. The comparison runs from the universe `max v r` of the morphisms of the site and of the
rings to a universe `max u v r t` containing the site.

## References

* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t u v r m

namespace Stacks.Cohomology.SiteModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r})

/-- The global sections of the universe lift of a sheaf of modules are, linearly over the global
sections of the structure sheaf, the universe lift of its global sections. -/
alias globalSectionsUliftForPresentationLinearEquiv :=
  Stacks.Cohomology.SiteModules.globalSectionsUliftLinearEquiv

/-- **Global sections commute with the universe lift of the sections**, naturally in the sheaf
of modules. -/
alias globalSectionsUliftForPresentationIso := Stacks.Cohomology.SiteModules.globalSectionsUliftIso

attribute [local instance 5000] SheafOfModules.instAbelian

variable [HasSheafify J AddCommGrpCat.{max v r}] [J.WEqualsLocallyBijective AddCommGrpCat.{max v r}]
  [HasSeparator (SheafOfModules.{max v r} R)] [HasInjectiveResolutions (SheafOfModules.{max v r} R)]
  [HasSheafify J AddCommGrpCat.{max u v r t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r t}]
  [HasInjectiveResolutions (SheafOfModules.{max u v r t} R)]

/-- **The cohomology of the universe lift of a sheaf of modules is the universe lift of its
cohomology.** For a sheaf of `R`-modules `M` with sections in the universe `max v r` and every
degree `q`, `H^q(C, M)` lifted to the universe `max u v r t` is `H^q` of the universe lift of `M`,
naturally in `M`, as modules over the global sections of `R`. -/
alias rightDerivedGlobalSectionsUliftForPresentationIso :=
  Stacks.Cohomology.SiteModules.rightDerivedGlobalSectionsUliftIso

end Stacks.Cohomology.SiteModules

end

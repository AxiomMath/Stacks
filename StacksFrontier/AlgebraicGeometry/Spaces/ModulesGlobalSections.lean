module

public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjects
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsCorepresentable

/-!
# Global sections and injectives on the small étale site of an algebraic space

Let `F` be an algebraic space over a scheme `S` of a big fppf site `B`. The small étale site of
`F` has its objects in `Type (u + 1)` and its morphisms, structure sheaf and modules at `u`. This
file shows that, at the universe `u` of the structure rings, sheaves of abelian groups on it have
a global-sections functor, its `𝒪_F`-modules have enough injectives, and global sections of
`𝒪_F`-modules preserve finite limits.

## Main results

* `AlgebraicGeometry.Space.hasLimitsOfShape_op_smallEtale`: `AddCommGrpCat.{u}` has limits
  indexed by the opposite of the small étale site.
* `AlgebraicGeometry.Space.hasGlobalSectionsFunctor_smallEtale`: the small étale site admits a
  global-sections functor for sheaves of abelian groups at the universe of the structure rings.
* `AlgebraicGeometry.Space.enoughInjectives_modules`: the `𝒪_F`-modules at the universe of the
  structure rings have enough injectives.
* `AlgebraicGeometry.Space.preservesFiniteLimits_globalSectionsFunctor_structureRingSheaf`:
  global sections of those modules preserve finite limits.

## References

* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- Abelian groups at the universe of the structure rings have limits indexed by the opposite of
the small étale site of a presheaf on the big fppf site. -/
theorem hasLimitsOfShape_op_smallEtale :
    HasLimitsOfShape (SmallEtale B S hS F)ᵒᵖ AddCommGrpCat.{u} :=
  hasLimitsOfShape_of_essentiallySmall.{u} _ _

/-- The small étale site admits a global-sections functor `CategoryTheory.Sheaf.Γ` for sheaves of
abelian groups at the universe of the structure rings. -/
instance hasGlobalSectionsFunctor_smallEtale :
    HasGlobalSectionsFunctor (SmallEtale.topology B S hS F) AddCommGrpCat.{u} := by
  have := hasLimitsOfShape_op_smallEtale B S hS F
  infer_instance

/-- The `𝒪_F`-modules on the small étale ringed site of an algebraic space have enough
injectives, at the universe of the structure rings. -/
theorem enoughInjectives_modules (hF : IsAlgebraicSpace B S hS F) :
    EnoughInjectives (Modules.{u, u} B S hS F hF) := by
  have hes : EssentiallySmall.{u} (smallEtaleRingedSite B S hS F hF).C := by
    show EssentiallySmall.{u} (SmallEtale B S hS F)
    infer_instance
  have : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS F hF) :=
    SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _
  infer_instance

/-- Global sections of `𝒪_F`-modules on the small étale ringed site of an algebraic space
preserve finite limits, at the universe of the structure rings. -/
theorem preservesFiniteLimits_globalSectionsFunctor_structureRingSheaf
    (hF : IsAlgebraicSpace B S hS F) :
    PreservesFiniteLimits (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))) :=
  Stacks.Cohomology.SiteModules.preservesFiniteLimits_globalSectionsFunctor_ringUniverse _

end AlgebraicGeometry.Space

end

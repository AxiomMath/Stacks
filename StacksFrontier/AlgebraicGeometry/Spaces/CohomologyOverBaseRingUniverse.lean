module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleHigherPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomology

/-!
# Cohomology over the base ring at the module universe of the structure rings

`AlgebraicGeometry.Space.cohomologyOverBase` is cohomology of `𝒪_X`-modules on the small étale
ringed site of an algebraic space over `Spec A`, read as `A`-modules along
`AlgebraicGeometry.Space.baseRingHom`.  It is built from
`Stacks.Cohomology.SiteModules.globalModuleCohomology`, whose module universe is
`max (u + 1) w`: the objects of the small étale site of a `Scheme.{u}` lie in `Type (u + 1)`,
and that is the module universe at which
`Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives` supplies the enough injectives a
right derived functor needs.

The module universe `u` of the structure rings is where
`AlgebraicGeometry.Space.modulePushforward` lives, so no direct image is ever an argument of
`AlgebraicGeometry.Space.cohomologyOverBase`: `max (u + 1) w = u` is impossible.  This file
gives the same `A`-module at that universe instead, from the derived functors of
`Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}`, which are available
there — the small étale site is essentially small at `u`, which is what
`AlgebraicGeometry.Space.enoughInjectives_modules` and
`AlgebraicGeometry.Space.hasInjectiveResolutions_modules` exploit.

## Main definitions

* `AlgebraicGeometry.Space.cohomologyOverBaseRingUniverse` is the cohomology over `A` of an
  `𝒪_X`-module whose sections lie in the universe of the structure rings.

## Main results

* `AlgebraicGeometry.Space.isZero_cohomologyOverBaseRingUniverse_iff`: it vanishes exactly when
  the derived global sections do, restriction of scalars along
  `AlgebraicGeometry.Space.baseRingHom` changing no underlying group.

## Implementation notes

The two inputs are carried as `have`s inside the statements, as everywhere else in this
development that works at this module universe
(`StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyCollapse`): both are theorems
taking the site as an argument, so neither can be a global instance, and instance search
reaches for `Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives` and gets stuck on
`u =?= max (u + 1) ?w` when the module universe is left open.

The target module category is `ModuleCat.{max (u + 1) u} A`.  Global sections on a site are
compatible families of sections indexed by the objects of the site, so they lie one universe
above the sections themselves whatever the module universe is; only the *source* of the derived
functor is at `u` here.

This file does **not** relate either form of the cohomology to abelian sheaf cohomology, but the
obstruction to doing so is no longer the seating of Stacks 03FD.
`ModuleSheafCohomology.Univ.globalSectionsComparisonIso` is now stated for a site whose objects lie
in `Type u` and whose morphisms lie in `Type v` with `v` unconstrained, over a sheaf of rings
with sections in `Type r`, at coefficients `Ab.{max u r m}`; the small étale site of a scheme,
whose objects lie in `Type (u + 1)` and whose morphisms in `Type u`, is covered, with the ring
sheaf at `u` and the coefficients at `max (u + 1) m`.  What is still seated at a
`CategoryTheory.SmallCategory` is the sections-over-an-object half,
`ModuleSheafCohomology.sectionsComparisonIso` and hence
`Stacks.Cohomology.ModuleComparison.rightDerivedSectionsIsoCohomologyPresheaf`, because the
object corepresenting sections over `U` is built from the hom-types of the site and therefore
pins the coefficient universe to the morphism universe.

## References

* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

noncomputable section

universe u

namespace AlgebraicGeometry.Space

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u})
    (hA : B.Contains (Spec (.of A)))
    (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)

/-- Cohomology of an `𝒪_X`-module on the small étale ringed site of an algebraic space over
`Spec A` whose sections lie in the universe of the structure rings, regarded as an `A`-module
along `AlgebraicGeometry.Space.baseRingHom`.

This is `AlgebraicGeometry.Space.cohomologyOverBase` at the module universe where
`AlgebraicGeometry.Space.modulePushforward` lives; see the implementation notes of this file
for why the two cannot be the same declaration. -/
def cohomologyOverBaseRingUniverse (M : Modules.{u, u} B (Spec (.of A)) hA X hX) (i : ℕ) :
    have := hasInjectiveResolutions_modules B (Spec (.of A)) hA X hX
    ModuleCat.{max (u + 1) u} A :=
  have := hasInjectiveResolutions_modules B (Spec (.of A)) hA X hX
  (ModuleCat.restrictScalars (baseRingHom A B hA X hX)).obj
    (((globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)).rightDerived i).obj M)

/-- **The cohomology over `A` vanishes exactly when the derived global sections do.**
Restriction of scalars along `AlgebraicGeometry.Space.baseRingHom` leaves the underlying group
alone, so it neither creates nor destroys a zero object. -/
theorem isZero_cohomologyOverBaseRingUniverse_iff
    (M : Modules.{u, u} B (Spec (.of A)) hA X hX) (i : ℕ) :
    have := hasInjectiveResolutions_modules B (Spec (.of A)) hA X hX
    IsZero (cohomologyOverBaseRingUniverse A B hA X hX M i) ↔
      IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)).rightDerived
          i).obj M) := by
  have := hasInjectiveResolutions_modules B (Spec (.of A)) hA X hX
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [ModuleCat.isZero_iff_subsingleton]
    exact ModuleCat.subsingleton_of_isZero
      (M := cohomologyOverBaseRingUniverse A B hA X hX M i) h
  · exact (ModuleCat.restrictScalars (baseRingHom A B hA X hX)).map_isZero h

end AlgebraicGeometry.Space

end

end

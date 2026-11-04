module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedSectionsOverObject
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleModuleHigherDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleEnoughObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.AcyclicObject

/-!
# Hypercohomology over an affine object of the small étale site

Let `S` be a scheme contained in a big étale site `B`.  For an object `K` of the unbounded
derived category of `𝒪`-modules on the small étale site of [Stacks, Tag 021B] whose cohomology
sheaves are all quasi-coherent on the site, and for an *affine* object `U` of that site, the
hypercohomology edge morphism

`H^q(U, K) ⟶ Γ(U, H^q(K))`

is invertible, in every degree `q` and with no boundedness hypothesis on `K`.

This is [Stacks, Tag 0BKZ] read at the class of affine objects of the small étale site.  Both
hypotheses of that tag are available there:

* the affine objects cover every object of the site, which is
  `AlgebraicGeometry.SmallEtale.hasEnoughObjects_isAffine`;
* a quasi-coherent `𝒪`-module has no higher cohomology over an affine object, which is proved
  first below.

## Main results

* `AlgebraicGeometry.SmallEtale.isZero_rightDerived_evaluation_of_isQuasicoherentOnSite`:
  `R^pΓ(U, 𝒢) = 0` for `p > 0`, an affine object `U` of the small étale site and an `𝒪`-module
  `𝒢` quasi-coherent on the site.
* `AlgebraicGeometry.SmallEtale.isIso_hypercohomologyEdge_app_of_isAffine`: the hypercohomology
  edge morphism over an affine object is invertible at an object with quasi-coherent cohomology.

## The vanishing, and how it relates to the associated-module one

`AlgebraicGeometry.SmallEtale.isZero_rightDerived_evaluation_associatedModule` is the same
vanishing for a module of the shape `𝓕ᵃ` with `𝓕` a quasi-coherent `𝒪_S`-module.  An `𝒪`-module
on `S_étale` which is quasi-coherent *on the site* is of that shape: the counit of
`AlgebraicGeometry.SmallEtale.associatedModuleAdjunction` at it is invertible, by
`AlgebraicGeometry.SmallEtale.isIso_counit'`, and its direct image along
`ε` is quasi-coherent by `AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule`.  So the
first result below is that vanishing transported along that counit, exactly as
`AlgebraicGeometry.SmallEtale.isZero_rightDerived_restrictModuleOfSheaf` transports the
cohomology-of-a-cover criterion.

## Implementation notes

**Two global instances are switched off.**  `Stacks.Cohomology.SiteModules.moduleSheavesAbelian`
and `Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives` state the abelian structure and
the injectives of `SheafOfModules.{max u v r w} O` at a module universe which is a `max` of the
site universes.  The small étale site has its objects in `Type (u + 1)` and the modules here have
their sections in `Type u`, so instance search against those two leaves a stuck universe
constraint `u =?= max (u + 1) ?w` — and then even the binder
`[HasDerivedCategory.{u + 1} (SheafOfModules.{u} (structureSheaf B S hS))]` fails to elaborate.
The erasure is section-scoped and the instances actually used are the ones available at the
pinned universes; this is the same treatment
`StacksFrontier/AlgebraicGeometry/Spaces/CoherentSubmoduleColimitNoetherian.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/MayerVietorisSections.lean` give them.  The
erasure is also the reason this is a module of its own rather than a section of the module
carrying `AlgebraicGeometry.SmallEtale.isZero_rightDerived_evaluation_associatedModule`.

**The derived category is the standard one.**  `Stacks.Cohomology.HypercohomologyEdge` is stated
at `CategoryTheory.HasDerivedCategory.standard`, so the statements below are too.  That universe
is `u + 1`: the objects of `SheafOfModules.{u} (structureSheaf B S hS)` lie in `Type (u + 1)`,
being sheaves valued in `ModuleCat.{u}`, and so do the morphisms of the site.  The instance is
named explicitly rather than activated with `attribute [local instance]`, because at a goal whose
universe is already fixed to `u + 1` its synthesis would have to solve
`max ?u_obj ?u_hom =?= u + 1` with both sides metavariables, which Lean does not do.  The named
instance is not declared again here: it is
`AlgebraicGeometry.SmallEtale.hasDerivedCategoryStandard_structureSheaf` of
`SmallEtaleDerivedSectionsOverObject.lean`, a `local` instance of that module, activated here
with `attribute [local instance]`.  It stays `local`, so importing this module registers nothing
in global instance search.

**No `@[stacks]` attribute is attached.**  Both statements are the instance at the small étale
site of a tag proved in general — [Stacks, Tag 0BKZ] is
`Stacks.Cohomology.HypercohomologyEdge.isIso_hypercohomologyEdge_app_of_acyclic_cover` and
[Stacks, Tag 03DW] at the affine objects is
`AlgebraicGeometry.SmallEtale.isZero_rightDerived_evaluation_associatedModule` — and a tag is not
restated at an instance.

## References

* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.SmallEtale

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A quasi-coherent `𝒪`-module on the small étale site has no higher cohomology over an
affine object**, in the module-valued spelling: `R^pΓ(U, 𝒢) = 0` for `p > 0`, where `R^pΓ(U, -)`
is the `p`-th right derived functor of `CategoryTheory.SheafOfModules.evaluation` at `U`.

This is `AlgebraicGeometry.SmallEtale.isZero_rightDerived_evaluation_associatedModule`
transported along the counit of the associated-module adjunction, which is invertible at `𝒢`
because `𝒢` is quasi-coherent on the site; the direct image `ε_*𝒢` is then a quasi-coherent
`𝒪_S`-module and `𝒢` is its associated module. -/
theorem isZero_rightDerived_evaluation_of_isQuasicoherentOnSite
    (G : SheafOfModules.{u} (structureSheaf B S hS)) (hG : G.IsQuasicoherentOnSite)
    (V : SmallEtale B S hS) (hV : SmallEtale.IsAffine B S hS V) (p : ℕ) (hp : 0 < p) :
    IsZero (((SheafOfModules.evaluation (structureSheaf B S hS) (op V)).rightDerived p).obj G) := by
  have : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((restrictModule B S hS).obj G) := isQuasicoherent_restrictModule B S hS G hG
  have : IsIso ((associatedModuleAdjunction B S hS).counit.app G) :=
    isIso_counit' B S hS G hG
  refine IsZero.of_iso ?_
    (((SheafOfModules.evaluation (structureSheaf B S hS) (op V)).rightDerived p).mapIso
      (asIso ((associatedModuleAdjunction B S hS).counit.app G)).symm)
  exact isZero_rightDerived_evaluation_associatedModule B S hS _ V hV p hp

attribute [local instance] hasDerivedCategoryStandard_structureSheaf

/-- **The hypercohomology edge morphism over an affine object of the small étale site is
invertible**, at an object of `D(S_étale, 𝒪)` whose cohomology sheaves are all quasi-coherent on
the site, in every degree and with no boundedness hypothesis.

This is [Stacks, Tag 0BKZ] at the class of affine objects of the small étale site: the class has
enough objects by `AlgebraicGeometry.SmallEtale.hasEnoughObjects_isAffine`, and the cohomology
sheaves are acyclic over every member of it by
`AlgebraicGeometry.SmallEtale.isZero_rightDerived_evaluation_of_isQuasicoherentOnSite`. -/
theorem isIso_hypercohomologyEdge_app_of_isAffine
    (U : SmallEtale B S hS) (hU : SmallEtale.IsAffine B S hS U)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheaf B S hS)))
    (hK : ∀ m : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheaf B S hS)) m).obj K).IsQuasicoherentOnSite)
    (q : ℤ) :
    IsIso ((Stacks.Cohomology.HypercohomologyEdge.hypercohomologyEdge
      (structureSheaf B S hS) U q).app K) :=
  Stacks.Cohomology.HypercohomologyEdge.isIso_hypercohomologyEdge_app_of_acyclic_cover
    (structureSheaf B S hS) U K (SmallEtale.IsAffine B S hS)
    (SmallEtale.hasEnoughObjects_isAffine B S hS)
    (fun V hV p hp m =>
      isZero_rightDerived_evaluation_of_isQuasicoherentOnSite B S hS _ (hK m) V hV p hp)
    hU q

end AlgebraicGeometry.SmallEtale

end

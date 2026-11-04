module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedReflectsZero
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFiniteType
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFiniteTypeDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedFiniteTypeOnCharts

/-!
# Finite type of the cohomology descends along `ε`, at the derived level

Let `S` be a scheme contained in a big étale site and let
`ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` be the morphism of ringed sites of Stacks 08H7. Let `E` be an
object of `D(𝒪_S)` and `n` an integer. If the `n`-th cohomology of `ε^*E` is of finite type on the
small étale site, then `Hⁿ(E)` is of finite type on the small Zariski site. No quasi-coherence
hypothesis is needed.

This is the derived-level form of the converse of Stacks 08HD, as used in Stacks 08HE
(2) ⇒ (1). The cohomology objects `Hⁿ(ε^*E)` and `ε^*(Hⁿ(E))` are identified by
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso` at `ε^*`, which reduces the statement to
the module-level descent
`AlgebraicGeometry.SmallEtale.isFiniteTypeOnSite_of_isFiniteTypeOnSite_associatedModule`.

## Main results

* `isFiniteTypeOnSite_homology_of_isFiniteTypeOnSite_homology_associatedModule`: the descent, in
  the categorical finite-type condition of Stacks 03DL (5).

## Implementation notes

Finite type is transported along `CategoryTheory.Functor.mapDerivedCategoryHomologyIso` by
`Stacks.SheafOfModules.FiniteTypeTransport.isFiniteTypeOnSite_of_iso`, the iso-invariance of
clause (5) of Stacks 03DL on an arbitrary site.

`SheafOfModules` is written `_root_.SheafOfModules` throughout: inside
`namespace AlgebraicGeometry.SmallEtale` the short name resolves to a namespace of this development
and not to Mathlib's structure, and the resulting instance search leaves a universe unpinned.

The global instance `Stacks.Cohomology.SiteModules.moduleSheavesAbelian` is switched off for
this file. It states the abelian structure of `SheafOfModules.{max u v r w} O` at a module
universe which is a `max` of the site universes; the small étale site has its objects in
`Type (u + 1)` while the modules here have sections in `Type u`, so instance search against it
leaves the stuck universe constraint `u =?= max (u + 1) ?w` and the `HasDerivedCategory` binders
fail to elaborate. The abelian structure used is Mathlib's, at the pinned universes.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 08FX](https://stacks.math.columbia.edu/tag/08FX)
* [Stacks Project, Tag 08HD](https://stacks.math.columbia.edu/tag/08HD)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u d d'

namespace AlgebraicGeometry.SmallEtale

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  [HasDerivedCategory.{d} (_root_.SheafOfModules.{u} S.ringCatSheaf)]
  [HasDerivedCategory.{d'} (_root_.SheafOfModules.{u} (structureSheaf B S hS))]

/-- **Finite type of the `n`-th cohomology descends along `ε`**: for an arbitrary object `E` of
`D(𝒪_S)`, if `Hⁿ(ε^*E)` is of finite type on the small étale site of `S`, then `Hⁿ(E)` is of
finite type on the small Zariski site. -/
public theorem isFiniteTypeOnSite_homology_of_isFiniteTypeOnSite_homology_associatedModule
    (E : DerivedCategory (_root_.SheafOfModules.{u} S.ringCatSheaf)) (n : ℤ)
    (hft : _root_.SheafOfModules.IsFiniteTypeOnSite
      ((DerivedCategory.homologyFunctor (_root_.SheafOfModules.{u} (structureSheaf B S hS)) n).obj
        ((associatedModuleOfSheaf B S hS).mapDerivedCategory.obj E))) :
    _root_.SheafOfModules.IsFiniteTypeOnSite
      ((DerivedCategory.homologyFunctor (_root_.SheafOfModules.{u} S.ringCatSheaf) n).obj E) := by
  have hpull : _root_.SheafOfModules.IsFiniteTypeOnSite
      ((associatedModule B S hS).obj
        ((DerivedCategory.homologyFunctor (_root_.SheafOfModules.{u} S.ringCatSheaf) n).obj E)) :=
    Stacks.SheafOfModules.FiniteTypeTransport.isFiniteTypeOnSite_of_iso
      (((associatedModuleOfSheaf B S hS).mapDerivedCategoryHomologyIso n).app E) hft
  exact isFiniteTypeOnSite_of_associatedModule B S hS _ hpull

end AlgebraicGeometry.SmallEtale

end

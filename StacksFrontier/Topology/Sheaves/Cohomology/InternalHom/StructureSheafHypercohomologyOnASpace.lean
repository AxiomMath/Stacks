module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.StructureSheafHypercohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.GlobalDerivedHomOnASpace

/-!
# Hypercohomology of a ringed space in every degree is morphisms out of the structure sheaf

`AlgebraicGeometry.RingedSite.derivedStructureSheafGlobalSectionsDegreeEquiv` identifies the
degree-`n` hypercohomology of an object of `D(O)` on a ringed site with the group of morphisms
`O[0] ⟶ Z[n]`. This file reads that at the site of opens of a topological space, which is the
form a ringed space — and so a scheme, through `AlgebraicGeometry.Scheme.toRingedSpace` — uses.

`Stacks.SheafOfModules.ringedSite` is an abbreviation, so the ringed site of `Rc` has
`structureSheaf Rc` as its structure sheaf and `StructureSheafModules Rc` as its category of
modules; nothing here is more than reading the site statement at that site.

## Main definitions

* `Stacks.SheafOfModules.derivedStructureSheafGlobalSectionsDegreeEquiv`:
  `H^n(X, Z) ≃+ Hom_{D(O_X)}(O_X[0], Z[n])`.

## Main results

* `Stacks.SheafOfModules.not_isZero_homology_derivedModuleGlobalSections_of_ne_zero`: a nonzero
  morphism `O_X[0] ⟶ Z[n]` forces `H^n(X, Z)` to be nonzero.

## References

* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 0B6A](https://stacks.math.columbia.edu/tag/0B6A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections
open Stacks.Cohomology.SiteModules

namespace Stacks.SheafOfModules

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Hypercohomology of a ringed space in every degree is morphisms out of the structure
sheaf.** For an object `Z` of `D(O_X)` the hypercohomology group `H^n(X, Z)`, the degree-`n`
homology of unbounded derived global sections, is `Hom_{D(O_X)}(O_X[0], Z[n])`.

This is `AlgebraicGeometry.RingedSite.derivedStructureSheafGlobalSectionsDegreeEquiv` read at the
site of opens of `X`. -/
@[stacks 08JA "hypercohomology of a ringed space out of the structure sheaf in every degree"]
def derivedStructureSheafGlobalSectionsDegreeEquiv
    (Z : DerivedCategory (StructureSheafModules Rc)) (n : ℤ) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        ((derivedModuleGlobalSections (ringedSite Rc)).obj Z) : Type u) ≃+
      (RingedSite.derivedStructureSheaf (ringedSite Rc) ⟶ Z⟦n⟧) :=
  RingedSite.derivedStructureSheafGlobalSectionsDegreeEquiv (ringedSite Rc) Z n

/-- **A nonzero morphism out of the structure sheaf makes the hypercohomology of a ringed space
nonzero.** If there is a nonzero morphism `O_X[0] ⟶ Z[n]` in `D(O_X)` then `H^n(X, Z) ≠ 0`.

This is the direction of
`Stacks.SheafOfModules.derivedStructureSheafGlobalSectionsDegreeEquiv` that [Stacks, Tag 0BQR]
consumes: the argument there produces a chain map out of the structure sheaf which is nonzero
already on the `n`-th cohomology sheaf, and what the tag asserts is that a hypercohomology group
does not vanish. -/
theorem not_isZero_homology_derivedModuleGlobalSections_of_ne_zero
    (Z : DerivedCategory (StructureSheafModules Rc)) (n : ℤ)
    (φ : RingedSite.derivedStructureSheaf (ringedSite Rc) ⟶ Z⟦n⟧) (hφ : φ ≠ 0) :
    ¬ IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
      ((derivedModuleGlobalSections (ringedSite Rc)).obj Z)) :=
  RingedSite.not_isZero_homology_derivedModuleGlobalSections_of_ne_zero
    (ringedSite Rc) Z n φ hφ

end Stacks.SheafOfModules

end

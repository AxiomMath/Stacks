module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomShift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.FromTheStructureSheaf
import StacksCore.Tactic.StacksAttribute

/-!
# Hypercohomology in every degree is morphisms out of the structure sheaf

Let `(C, O)` be a ringed site and let `Z` be an object of `D(O)`. This file identifies the
hypercohomology group `H^n(C, Z)` — the degree-`n` homology of unbounded derived global sections
`RΓ(C, Z)` — with the group of morphisms `O[0] ⟶ Z[n]` of `D(O)`.

In degree zero this is `AlgebraicGeometry.RingedSite.derivedStructureSheafGlobalSectionsEquiv`
of `StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualityPairing`. The general degree is
the same two-step composite, with the degree-`n` cohomology of the global derived hom
(`AlgebraicGeometry.RingedSite.globalDerivedHomDegreeEquiv`, Tag 0B6E) in place of the
degree-zero one:

`H^n(RΓ(C, Z)) ≅ H^n(RΓ(C, RSheafHom(O[0], Z))) = H^n(RHom_O(O[0], Z)) ≅ Hom(O[0], Z[n])`,

the first step being derived global sections of the identification `RSheafHom(O[0], Z) ≅ Z` of
`AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso` and the second Tag 0B6E.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedStructureSheafGlobalSectionsDegreeEquiv`:
  `H^n(C, Z) ≃+ Hom_{D(O)}(O[0], Z[n])`.

## Main results

* `AlgebraicGeometry.RingedSite.not_isZero_homology_derivedModuleGlobalSections_of_ne_zero`:
  **a nonzero morphism `O[0] ⟶ Z[n]` forces `H^n(C, Z)` to be nonzero.** This is the direction
  in which the identification is used to detect nonvanishing hypercohomology: a cocycle
  witnessing a nonzero map in the derived category witnesses a nonzero hypercohomology group.

## References

* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 0B6E](https://stacks.math.columbia.edu/tag/0B6E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections
open Stacks.Cohomology.SiteModules
open Stacks.SheafOfModules.Tensor (ringSheaf)

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Hypercohomology in every degree is morphisms out of the structure sheaf.** For an object
`Z` of `D(O)` the hypercohomology group `H^n(C, Z)`, the degree-`n` homology of unbounded derived
global sections, is the group `Hom_{D(O)}(O[0], Z[n])`.

This is Tag 08JA at source the structure sheaf in every degree: derived global sections of the
identification `RSheafHom(O[0], Z) ≅ Z` of
`AlgebraicGeometry.RingedSite.derivedStructureSheafHomIso` turn `H^n(C, Z)` into the degree-`n`
cohomology of the global derived hom `RHom_O(O[0], Z)`, which is `Hom(O[0], Z[n])` by Tag 0B6E
(`AlgebraicGeometry.RingedSite.globalDerivedHomDegreeEquiv`). In degree zero it is
`AlgebraicGeometry.RingedSite.derivedStructureSheafGlobalSectionsEquiv`. -/
@[stacks 08JA "hypercohomology out of the structure sheaf in every degree",
  stacks 0B6E "the case K = O[0], where RHom_O(O[0], Z) is RGamma(C, Z)"]
def derivedStructureSheafGlobalSectionsDegreeEquiv
    (Z : DerivedCategory (SheafOfModules.{u} (ringSheaf X.O))) (n : ℤ) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        ((derivedModuleGlobalSections X).obj Z) : Type u) ≃+
      (derivedStructureSheaf X ⟶ Z⟦n⟧) :=
  (((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).mapIso
        ((derivedModuleGlobalSections X).mapIso
          (derivedStructureSheafHomIso X Z).symm)).addCommGroupIsoToAddEquiv).trans
    (globalDerivedHomDegreeEquiv X (derivedStructureSheaf X) Z n)

/-- **A nonzero morphism out of the structure sheaf makes hypercohomology nonzero.** If there is
a nonzero morphism `O[0] ⟶ Z[n]` in `D(O)` then `H^n(C, Z) ≠ 0`.

This is the direction of
`AlgebraicGeometry.RingedSite.derivedStructureSheafGlobalSectionsDegreeEquiv` that detects
nonvanishing hypercohomology from a morphism of the derived category, which is how a global
cocycle is turned into a nonzero hypercohomology class. -/
theorem not_isZero_homology_derivedModuleGlobalSections_of_ne_zero
    (Z : DerivedCategory (SheafOfModules.{u} (ringSheaf X.O))) (n : ℤ)
    (φ : derivedStructureSheaf X ⟶ Z⟦n⟧) (hφ : φ ≠ 0) :
    ¬ IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
      ((derivedModuleGlobalSections X).obj Z)) := by
  intro hz
  have hs := AddCommGrpCat.isZero_iff_subsingleton.mp hz
  exact hφ ((derivedStructureSheafGlobalSectionsDegreeEquiv X Z n).symm.injective
    (hs.elim _ _))

end AlgebraicGeometry.RingedSite

end

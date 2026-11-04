module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedModuleReflectsZero
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtalePseudoCoherentObligation
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology

/-!
# `ε^*` reflects the vanishing of cohomology

Let `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` be the morphism of ringed sites of Stacks 08H7.  The
associated-module functor `ε^* = (𝓕 ↦ 𝓕^a)` of Stacks 03DU (4) is exact — the exactness
assertion of Stacks 08H8 — so it commutes with the cohomology of the derived category, and it
detects the zero module by
`AlgebraicGeometry.SmallEtale.isZero_of_isZero_associatedModule_zariskiModules`.  Together these
say that `Hⁿ(ε^*E)` vanishes exactly when `Hⁿ(E)` does, for every object `E` of `D(𝒪_S)` and
every `n`.

## Main definitions

* the identification `Hⁿ(ε^*E) ≅ ε^*(Hⁿ(E))` is not restated here; it is Mathlib's
  `CategoryTheory.Functor.mapDerivedCategoryHomologyIso` at `ε^*`, natural
  in `E`.

## Main results

* `AlgebraicGeometry.SmallEtale.isZero_homology_associatedModule_iff`: `Hⁿ(ε^*E)` is a zero
  object if and only if `Hⁿ(E)` is.

## Implementation notes

`AlgebraicGeometry.SmallEtale.associatedModuleDerivedHomologyIso` of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleDerivedConservativity.lean`
states the same isomorphism, with the same body: both read
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso` at `ε^*`, so what is duplicated is the
name, not a proof.  Neither file imports the other; importing that one here would add 194
modules to this file's import closure, against 49 the other way, so the two names are kept.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 08H7](https://stacks.math.columbia.edu/tag/08H7)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u d d'

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  [HasDerivedCategory.{d} (SheafOfModules.{u} S.ringCatSheaf)]
  [HasDerivedCategory.{d'} (SheafOfModules.{u} (structureSheaf B S hS))]

/-- **`ε^*` reflects the vanishing of cohomology.**  For an object `E` of `D(𝒪_S)` and an integer
`n`, the `n`-th cohomology of `ε^*E` on the small étale site of `S` is a zero object if and only
if the `n`-th cohomology of `E` is.

The "if" half is exactness of `ε^*`; the "only if" half is the zero-detection assertion of
Stacks 08H8, `AlgebraicGeometry.SmallEtale.isZero_of_isZero_associatedModule_zariskiModules`,
applied to `Hⁿ(E)` through `CategoryTheory.Functor.mapDerivedCategoryHomologyIso` at `ε^*`. -/
public theorem isZero_homology_associatedModule_iff
    (E : DerivedCategory (SheafOfModules.{u} S.ringCatSheaf)) (n : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheaf B S hS)) n).obj
      ((associatedModuleOfSheaf B S hS).mapDerivedCategory.obj E)) ↔
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} S.ringCatSheaf) n).obj E) := by
  refine (((associatedModuleOfSheaf B S hS).mapDerivedCategoryHomologyIso n).app E).isZero_iff.trans
    ⟨isZero_of_isZero_associatedModule_zariskiModules B S hS _,
      (associatedModuleOfSheaf B S hS).map_isZero⟩

end AlgebraicGeometry.SmallEtale

end

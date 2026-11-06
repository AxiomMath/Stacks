module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechAndResolutions.FunctorialDerivedGlobalSections

/-!
# Deriving global sections before or after restricting scalars

Let `f : X ⟶ Y` be a morphism of ringed spaces. Global sections on `X` can be derived either
as a functor to `Γ(X, 𝒪_X)`-modules and then composed with the derived restriction of scalars
along `Γ(Y, 𝒪_Y) → Γ(X, 𝒪_X)`, or directly as a functor to `Γ(Y, 𝒪_Y)`-modules. Restriction of
scalars is exact, so every object is right acyclic for it and the canonical comparison of
[Stacks, Tag 015M] is an isomorphism. This file records that isomorphism, and the unit
comparing the image in the derived category of a bounded-below complex with scalars restricted
termwise to the value there of the derived restriction of scalars.

Both are inputs to the compatibility of Čech refinement with derived global sections,
[Stacks, Tag 01FD].

## Main definitions

* `Stacks.Cohomology.derivedSectionsScalarComparison`: the isomorphism
  `RΓ(X, -) ⋙ R(restriction of scalars) ≅ RΓ(X, -)` with values in `Γ(Y, 𝒪_Y)`-modules.
* `Stacks.Cohomology.scalarRestrictionUnit`: for a bounded-below complex `K` of
  `Γ(X, 𝒪_X)`-modules, the comparison of the image of `K` with scalars restricted termwise with
  the value at `K` of the derived restriction of scalars.

## Implementation notes

`derivedSectionsScalarComparison` is the first factor of
`Stacks.Cohomology.derivedModuleGlobalSectionsAlongIso`, inverted; it is named separately
because the compatibility square of [Stacks, Tag 01FD] uses that factor on its own.

`scalarRestrictionUnit` is assembled from `DerivedCategory.Plus.quotientCompQhIso`, which
identifies the localization functor on bounded-below cochain complexes with its factorization
through the bounded-below homotopy category, and the unit of the right derived functor. No
transport is needed: the two readings of the termwise image of `K` in the bounded-below
homotopy category agree definitionally.

## References

* [Stacks Project, Tag 01FD](https://stacks.math.columbia.edu/tag/01FD)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Cohomology

noncomputable section

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **Deriving global sections commutes with restriction of scalars.** Restriction of scalars
along `Γ(Y, 𝒪_Y) → Γ(X, 𝒪_X)` is exact, so [Stacks, Tag 015M] applies to the composite
`Γ(X, -) ⋙ (restriction of scalars)`: deriving the composite is deriving the two factors
separately. This is the first factor of
`Stacks.Cohomology.derivedModuleGlobalSectionsAlongIso`, read in the opposite direction. -/
def derivedSectionsScalarComparison
    [HasSheafify (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat]
    [(Opens.grothendieckTopology (X : TopCat)).WEqualsLocallyBijective AddCommGrpCat]
    [EnoughInjectives (Modules X)] :
    derivedModuleGlobalSections X ⋙
        (restrictGlobalScalars f).rightDerivedFunctorPlus ≅
      derivedModuleGlobalSectionsAlong f :=
  (DerivedPushforwardSections.compIso (moduleGlobalSections X) (restrictGlobalScalars f)
    (fun _ _ => DerivedPushforwardSections.rightAcyclic_restrictScalars _ _)).symm

/-- **The unit for derived restriction of scalars on a bounded-below complex.** For a
bounded-below complex `K` of `Γ(X, 𝒪_X)`-modules, this compares the image in the derived
category of `K` with scalars restricted termwise to `Γ(Y, 𝒪_Y)` with the value at `K` of the
right derived functor of restriction of scalars. -/
def scalarRestrictionUnit
    (K : CochainComplex.Plus (ModuleCat ((ringCatSheaf X).obj.obj (op ⊤)))) :
    DerivedCategory.Plus.Q.obj
        ((restrictGlobalScalars f).mapCochainComplexPlus.obj K) ⟶
      (restrictGlobalScalars f).rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Q.obj K) :=
  (DerivedCategory.Plus.quotientCompQhIso
        (ModuleCat ((ringCatSheaf Y).obj.obj (op ⊤)))).inv.app
      ((restrictGlobalScalars f).mapCochainComplexPlus.obj K) ≫
    (restrictGlobalScalars f).rightDerivedFunctorPlusUnith.app
      ((HomotopyCategory.Plus.quotient
        (ModuleCat ((ringCatSheaf X).obj.obj (op ⊤)))).obj K) ≫
    (restrictGlobalScalars f).rightDerivedFunctorPlus.map
      ((DerivedCategory.Plus.quotientCompQhIso
        (ModuleCat ((ringCatSheaf X).obj.obj (op ⊤)))).hom.app K)

end

end Stacks.Cohomology

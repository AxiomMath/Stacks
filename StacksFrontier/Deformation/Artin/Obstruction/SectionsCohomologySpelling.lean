module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsObstructionOverBase
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.CohomologyPullback

/-!
# The two spellings of the cohomology of a sheaf of modules on a scheme

The pullback map on cohomology, `Stacks.Cohomology.moduleCohomologyPullbackMap`, is stated with
cohomology in the bounded-below spelling `Stacks.Cohomology.spaceModuleCohomology`, built from
`DerivedCategory.Plus`; the obstruction theory of Stacks 07YH uses the `Functor.rightDerived`
spelling, through `Deformation.Artin.SectionsSheaf.cohomologyDeltaFunctor`. This file identifies
the two, so that the pullback map on cohomology can be read as a map of obstruction modules.

Both spellings are `Functor.rightDerivedPlus` resp. `Functor.rightDerived` of the same global
sections functor, so the identification is
`Stacks.DerivedIndexing.rightDerivedIso`, the comparison of the two indexings, with no new
homological algebra.

## Main results

* `Deformation.Artin.SectionsSheaf.spaceModuleCohomology_eq` and
  `moduleCohomologyAlong_eq` — the two bounded-below cohomology functors are
  `Functor.rightDerivedPlus` of global sections, on the nose.
* `Deformation.Artin.SectionsSheaf.moduleGlobalSections_eq` — the scheme-level and
  ringed-space-level global-sections functors agree, on the nose.
* `Deformation.Artin.SectionsSheaf.spaceModuleCohomologyIso` and
  `moduleCohomologyAlongIso` — each bounded-below cohomology functor is the corresponding
  `Functor.rightDerived`.
* `Deformation.Artin.SectionsSheaf.cohomologyPlusDeltaIso` — **the bridge**: the bounded-below
  cohomology of `X`, with scalars restricted to the base ring, is the degree-`n` part of
  `cohomologyDeltaFunctor`.

## Implementation notes

The three `rfl`-lemmas are what make the bridge cheap: each unfolds one abbreviation
(`spaceModuleCohomology`, `moduleCohomologyAlong`, `moduleGlobalSections`) and nothing else, so
`Stacks.DerivedIndexing.rightDerivedIso` applies directly at the global sections functor rather
than through a chain of transports.

The instance `HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso` is given raised
priority, as in the other files that mention `Functor.rightDerivedFunctorPlus`: the
cheap instance derived from `EnoughInjectives` is wanted, not the one that would set out to
prove termwise injectivity of an unknown complex.

## References

* [Stacks Project, Tag 07YH](https://stacks.math.columbia.edu/tag/07YH)
* [Stacks Project, Tag 015A](https://stacks.math.columbia.edu/tag/015A)
* [Stacks Project, Tag 01FA](https://stacks.math.columbia.edu/tag/01FA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Deformation.Artin.SectionsSheaf

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- The bounded-below cohomology of a ringed space is `Functor.rightDerivedPlus` of its
global-sections functor. -/
theorem spaceModuleCohomology_eq (Z : RingedSpace.{u, u}) (i : ℤ) :
    Stacks.Cohomology.spaceModuleCohomology Z i =
      (Stacks.Cohomology.moduleGlobalSections Z).rightDerivedPlus i :=
  rfl

/-- The bounded-below cohomology read over the target of a morphism is
`Functor.rightDerivedPlus` of global sections followed by restriction of scalars. -/
theorem moduleCohomologyAlong_eq {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (i : ℤ) :
    Stacks.Cohomology.moduleCohomologyAlong f i =
      (Stacks.Cohomology.moduleGlobalSections X ⋙
        Stacks.Cohomology.restrictGlobalScalars f).rightDerivedPlus i :=
  rfl

/-- The scheme-level global-sections functor is the ringed-space one. -/
theorem moduleGlobalSections_eq (X : Scheme.{u}) :
    Stacks.Cohomology.AffineBase.moduleGlobalSections X =
      Stacks.Cohomology.moduleGlobalSections X.toRingedSpace :=
  rfl

/-- **The bounded-below cohomology of a scheme is its `Functor.rightDerived` cohomology.** -/
def spaceModuleCohomologyIso (X : Scheme.{u}) (n : ℕ) :
    Stacks.Cohomology.spaceModuleCohomology X.toRingedSpace (n : ℤ) ≅
      (Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived n :=
  (Stacks.DerivedIndexing.rightDerivedIso
    (Stacks.Cohomology.AffineBase.moduleGlobalSections X) n).symm

/-- **The bounded-below cohomology read over the target of a morphism is the corresponding
`Functor.rightDerived`.** This is the target of `Stacks.Cohomology.moduleCohomologyPullbackMap`. -/
def moduleCohomologyAlongIso {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    Stacks.Cohomology.moduleCohomologyAlong f.toLRSHom.toShHom (n : ℤ) ≅
      (Stacks.Cohomology.moduleGlobalSections X.toRingedSpace ⋙
        Stacks.Cohomology.restrictGlobalScalars f.toLRSHom.toShHom).rightDerived n :=
  (Stacks.DerivedIndexing.rightDerivedIso
    (Stacks.Cohomology.moduleGlobalSections X.toRingedSpace ⋙
      Stacks.Cohomology.restrictGlobalScalars f.toLRSHom.toShHom) n).symm

/-- **The bridge**: the bounded-below cohomology of `X` in degree `n`, with scalars restricted
along `R → Γ(X, 𝒪_X)`, is the degree-`n` part of `cohomologyDeltaFunctor`, which is the spelling
the obstruction modules of Stacks 07YH are built in.

**No `@[stacks 07YH]` attribute**: this is an identification of two spellings of cohomology used
inside the development, not a clause of that tag. -/
def cohomologyPlusDeltaIso {R : CommRingCat.{u}} {X : Scheme.{u}} (π : X ⟶ Spec R) (n : ℕ) :
    Stacks.Cohomology.spaceModuleCohomology X.toRingedSpace (n : ℤ) ⋙
        ModuleCat.restrictScalars (baseHom π) ≅
      (cohomologyDeltaFunctor π).functor n :=
  Functor.isoWhiskerRight (spaceModuleCohomologyIso X n)
      (ModuleCat.restrictScalars (baseHom π)) ≪≫
    cohomologyRestrictIso π n

end Deformation.Artin.SectionsSheaf

end

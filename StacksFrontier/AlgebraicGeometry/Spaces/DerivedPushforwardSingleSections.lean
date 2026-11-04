module

public import StacksFrontier.AlgebraicGeometry.Spaces.HigherDirectImageSectionsOverChart
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyIso
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentSubobjectDirectedSupremum
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.SingleObject
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjectiveLocalization

/-!
# Cohomology sheaves of the derived direct image of a module

Let `f : X ⟶ Y` be a morphism of algebraic spaces and `𝓜` an `𝒪_X`-module.  The derived direct
image `Rf_*(𝓜[0])` of `𝓜` placed in degree `0` has cohomology sheaves the higher direct images,
`H^n(Rf_*(𝓜[0])) = R^n f_*𝓜`.  When these are acyclic for global sections on `Y`, the Leray
spectral sequence of `f` degenerates and

`Γ(Y, H^n(Rf_*(𝓜[0]))) = R^n(Γ(Y, f_* −))(𝓜)`,

the right hand side being the cohomology of `𝓜` on `X` read through the direct image (Stacks
0733, part (2)).  This is the comparison by which the derived fibre of `Rf_*(𝓜[0])` over the
spectrum of a field is read as the cohomology of `𝓜` on the fibre.

## Main results

* `AlgebraicGeometry.Space.homologyDerivedModulePushforwardSingleZeroIso`:
  `H^n(Rf_*(𝓜[0])) ≅ R^n f_*𝓜`.
* `AlgebraicGeometry.Space.globalSectionsHomologyDerivedModulePushforwardSingleIso`:
  `Γ(Y, H^n(Rf_*(𝓜[0]))) ≅ R^n(Γ(Y, f_* −))(𝓜)`, given that the higher direct images are acyclic
  for global sections on `Y`.

## Implementation notes

The derived direct image is `Stacks.DerivedFunctor.totalRightDerived` of
`AlgebraicGeometry.Space.modulePushforward`, the convention of
`AlgebraicGeometry.Space.NumericalSituation.numericalDirectImage`; the higher direct images are
Mathlib's `CategoryTheory.Functor.rightDerived`.  The acyclicity of the direct image of an
injective module needed for the degeneration is
`AlgebraicGeometry.Space.acyclicPushforwardOfInjective`; the acyclicity of the higher direct
images is the hypothesis `AlgebraicGeometry.Space.AcyclicHigherDirectImages` of
`AlgebraicGeometry.Space.globalSectionsRightDerivedIso`.

## References

* [Stacks Project, Tag 0733](https://stacks.math.columbia.edu/tag/0733)
* [Stacks Project, Tag 015A](https://stacks.math.columbia.edu/tag/015A)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives
attribute [local instance] isGrothendieckAbelian_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}

/-- **The cohomology sheaves of `Rf_*(𝓜[0])` are the higher direct images**:
`H^n(Rf_*(𝓜[0])) ≅ R^n f_*𝓜` for a morphism `f` of algebraic spaces and an `𝒪_X`-module `𝓜`. -/
def homologyDerivedModulePushforwardSingleZeroIso (f : X ⟶ Y)
    (M : Modules.{u, u} B S hS X.1 X.2) (n : ℕ) :
    (DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) n).obj
      ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj
        ((DerivedCategory.singleFunctor _ 0).obj M)) ≅
      ((modulePushforward B S hS f).rightDerived n).obj M :=
  Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso (modulePushforward B S hS f) _
    ((Stacks.DerivedFunctor.homotopyMap (modulePushforward B S hS f)).totalRightDerivedUnit
      DerivedCategory.Qh _)
    Stacks.Cohomology.Localization.enoughKInjectives M n

/-- **Global sections of the cohomology sheaves of `Rf_*(𝓜[0])`**:
`Γ(Y, H^n(Rf_*(𝓜[0]))) ≅ R^n(Γ(Y, f_* −))(𝓜)` when the higher direct images of `𝓜` are
acyclic for global sections on `Y`. -/
def globalSectionsHomologyDerivedModulePushforwardSingleIso (f : X ⟶ Y)
    (M : Modules.{u, u} B S hS X.1 X.2) (hcoh : AcyclicHigherDirectImages B S hS f M) (n : ℕ) :
    (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).obj
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) n).obj
        ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj
          ((DerivedCategory.singleFunctor _ 0).obj M))) ≅
      ((modulePushforward B S hS f ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS Y.1 Y.2).O))).rightDerived n).obj M :=
  (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).mapIso
    (homologyDerivedModulePushforwardSingleZeroIso B S hS f M n) ≪≫
  (globalSectionsRightDerivedIso B S hS f M (acyclicPushforwardOfInjective B S hS f) hcoh n).symm

end AlgebraicGeometry.Space

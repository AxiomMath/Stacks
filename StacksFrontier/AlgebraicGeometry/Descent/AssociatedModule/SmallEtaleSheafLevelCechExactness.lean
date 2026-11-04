module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleEssSurjReduction
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSheafLevelCechAugmentation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.SheafLevelComplexDegreeZero
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.SheafLevelComplexSections

/-!
# Exactness of the sheaf-level Čech complex at the small étale site

Let `S` be a scheme of a big étale site and let `{U_i → S/S}` be a family of morphisms of its
small étale site covering the final object. For an `𝒪`-module `ℱ` the sheaf-level Čech complex
`AlgebraicGeometry.SmallEtale.sheafLevelCechComplex` is exact in every positive degree, its
augmentation is a monomorphism, and the augmentation is a quasi-isomorphism: the complex is a
resolution of `ℱ`.

## Main results

* `AlgebraicGeometry.SmallEtale.exactAt_sheafLevelCechComplex`: the sheaf-level Čech complex of a
  covering of the final object is exact in every positive degree.
* `AlgebraicGeometry.SmallEtale.mono_sheafLevelCechAugmentation`: its augmentation is a
  monomorphism.
* `AlgebraicGeometry.SmallEtale.quasiIso_sheafLevelCechAugmentation`: its augmentation is a
  quasi-isomorphism.

## Implementation notes

The family is required to lie over the final object `SmallEtale.final B S hS`, which is terminal
(`AlgebraicGeometry.SmallEtale.finalIsTerminal`): the sheaf-level complex of a family over a
non-final object is not a resolution in general.

## References

* [Stacks Project, Tag 03AT](https://stacks.math.columbia.edu/tag/03AT)
* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance 5000] SheafOfModules.instAbelian

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The sheaf-level Čech complex of a covering of the final object of the small étale site is
exact in every positive degree.** -/
theorem exactAt_sheafLevelCechComplex (E : PreZeroHypercover.{u} (SmallEtale.final B S hS))
    (hE : (SmallEtale.topology B S hS).CoversTop E.X)
    (F : SheafOfModules.{u} (structureSheaf B S hS)) (n : ℕ) (hn : 0 < n) :
    ((sheafLevelCechComplex B S hS E).obj F).ExactAt n :=
  Stacks.CechSite.SheafLevel.exactAt_complexFunctor_of_coversTop _ E
    (SmallEtale.finalIsTerminal B S hS) hE F n hn

/-- **The augmentation of the sheaf-level Čech complex of a covering of the final object of the
small étale site is a monomorphism.** -/
theorem mono_sheafLevelCechAugmentation (E : PreZeroHypercover.{u} (SmallEtale.final B S hS))
    (hE : (SmallEtale.topology B S hS).CoversTop E.X)
    (F : SheafOfModules.{u} (structureSheaf B S hS)) :
    Mono (Stacks.CechSite.SheafLevel.augmentation (structureSheaf B S hS) E F) :=
  Stacks.CechSite.SheafLevel.mono_augmentation_of_coversTop _ E
    (SmallEtale.finalIsTerminal B S hS) hE F

/-- **The sheaf-level Čech complex of a covering of the final object of the small étale site is a
resolution of `ℱ`**: the augmentation
`AlgebraicGeometry.SmallEtale.sheafLevelCechAugmentation` is a quasi-isomorphism. This is
[Stacks, Tag 03AT] with sheaves of modules on the small étale site as coefficients. -/
theorem quasiIso_sheafLevelCechAugmentation
    (E : PreZeroHypercover.{u} (SmallEtale.final B S hS))
    (hE : (SmallEtale.topology B S hS).CoversTop E.X)
    (F : SheafOfModules.{u} (structureSheaf B S hS)) :
    QuasiIso (sheafLevelCechAugmentation B S hS E F) :=
  Stacks.CechSite.SheafLevel.quasiIso_augmentationHom_of_coversTop _ E
    (SmallEtale.finalIsTerminal B S hS) hE F

end AlgebraicGeometry.SmallEtale

end

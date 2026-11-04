module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFreeFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts

/-!
# A finite locally free module on an algebraic space is of finite presentation

Let `X` be an algebraic space and `E` a finite locally free `𝒪_X`-module on the small étale site.
Then `E` is of finite presentation, in Mathlib's sense and on the site, and hence quasi-coherent.
These are the hypotheses on the module in Stacks 0CTM (2) and 0E6A as formalized in this
library, consumed by Stacks 0D23.

## Main results

* `AlgebraicGeometry.Space.isFinitePresentation_modules_of_isFiniteLocallyFree`: `E` is of
  finite presentation.
* `AlgebraicGeometry.Space.isFinitePresentationOnSite_of_isFiniteLocallyFree`: `E` is of finite
  presentation on the site.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isFiniteLocallyFree`: `E` is quasi-coherent.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 0CTM](https://stacks.math.columbia.edu/tag/0CTM)
* [Stacks Project, Tag 0D23](https://stacks.math.columbia.edu/tag/0D23)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A finite locally free module on an algebraic space is of finite presentation.** -/
theorem isFinitePresentation_modules_of_isFiniteLocallyFree {X : AlgebraicSpaces B S hS}
    (E : Modules.{u, u} B S hS X.1 X.2) (hE : SheafOfModules.IsFiniteLocallyFree E) :
    E.IsFinitePresentation :=
  Stacks.SheafOfModules.isFinitePresentation_of_isFiniteLocallyFree E (h := hE)

/-- **A finite locally free module on an algebraic space is of finite presentation on the
site.** -/
theorem isFinitePresentationOnSite_of_isFiniteLocallyFree {X : AlgebraicSpaces B S hS}
    (E : Modules.{u, u} B S hS X.1 X.2) (hE : SheafOfModules.IsFiniteLocallyFree E) :
    E.IsFinitePresentationOnSite :=
  SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite
    (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_isFiniteLocallyFree E hE)

/-- **A finite locally free module on an algebraic space is quasi-coherent.** -/
theorem isQuasicoherentOnSite_of_isFiniteLocallyFree {X : AlgebraicSpaces B S hS}
    (E : Modules.{u, u} B S hS X.1 X.2) (hE : SheafOfModules.IsFiniteLocallyFree E) :
    E.IsQuasicoherentOnSite :=
  @SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite _ _ _ _ E
    (isFinitePresentationOnSite_of_isFiniteLocallyFree E hE)

end AlgebraicGeometry.Space

end

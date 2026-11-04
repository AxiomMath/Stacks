module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedModulePushforward
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness

/-!
# The derived direct image along a morphism of algebraic spaces is left t-exact

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`.  The unbounded derived direct image `Rf_*` exists with no hypothesis on `f`
(`AlgebraicGeometry.Space.hasRightDerivedFunctor_modulePushforward`), and this file proves that
it carries `D^{≥ n}(𝒪_X)` into `D^{≥ n}(𝒪_Y)`: an object of `D(𝒪_X)` with no cohomology below
degree `n` has derived direct image with no cohomology below degree `n`.

This is the clause "boundedness from below is trivial" of the conclusion of Stacks 08GK, that
`Rf_*E` lies in `D^b_{Coh}(𝒪_Y)`.  Only additivity of the degreewise direct image is used, so
the statements below assume nothing of `f`, of `Y` or of the cohomology sheaves of `E`.

## Main results

* `AlgebraicGeometry.Space.isGE_derivedModulePushforward_obj`: `Rf_*` is left t-exact.
* `AlgebraicGeometry.Space.isZero_homology_derivedModulePushforward_obj`: the same, read as
  vanishing of the cohomology sheaves of `Rf_*E` below a bound of `E`.
* `AlgebraicGeometry.Space.isZero_homology_derivedModulePushforward_single`: the case of a
  module placed in degree zero, where the vanishing is in all negative degrees.

## Implementation notes

The derived functor is `Stacks.DerivedFunctor.totalRightDerived` of
`AlgebraicGeometry.Space.modulePushforward`, which is the functor written out in
`AlgebraicGeometry.Space.hasRightDerivedFunctor_modulePushforward`; left t-exactness is
`Stacks.DerivedFunctor.isGE_totalRightDerived_obj`, whose hypotheses on the source category are
that it be Grothendieck abelian with enough injectives.  Both are supplied for the
`𝒪_X`-modules at the module universe `u` of the structure rings by
`AlgebraicGeometry.Space.isGrothendieckAbelian_modules` and
`CategoryTheory.IsGrothendieckAbelian.enoughInjectives`, introduced here as file-scoped local
instances; no global instance is added.

The other two clauses of Stacks 08GK's conclusion are not proved here and are not reachable
from unconditional content of this library.  Coherence of the cohomology sheaves of `Rf_*E` is
Stacks 08GC, whose library form
`AlgebraicGeometry.Space.isCoherent_rightDerived_modulePushforward_of_hasProperSupport`
carries Stacks 08AR, itself proved only with Stacks 0720, Stacks 08AN and Chow's lemma for
algebraic spaces carried.  Boundedness from above is Stacks 073G or Stacks 08FA; Stacks 073G
is `AlgebraicGeometry.Space.exists_forall_isZero_rightDerived_modulePushforward`, which bounds
the higher direct images of a quasi-coherent module, and Stacks 08FA has no presence.

## References

* [Stacks Project, Lemma 75.8.1 (Tag 08GK)](https://stacks.math.columbia.edu/tag/08GK)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 013K](https://stacks.math.columbia.edu/tag/013K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] isGrothendieckAbelian_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Y : AlgebraicSpaces B S hS}

/-- **Left t-exactness of the derived direct image.**  If an object `E` of `D(𝒪_X)` has no
cohomology below degree `n`, then `Rf_*E` has no cohomology below degree `n`, for every morphism
`f : X ⟶ Y` of algebraic spaces and with no further hypothesis. -/
theorem isGE_derivedModulePushforward_obj (f : X ⟶ Y)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (n : ℤ) (hE : E.IsGE n) :
    ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj E).IsGE n :=
  have := hE
  Stacks.DerivedFunctor.isGE_totalRightDerived_obj (modulePushforward B S hS f) E n

/-- The cohomology sheaves of `Rf_*E` vanish in every degree below a degree below which the
cohomology sheaves of `E` vanish. -/
theorem isZero_homology_derivedModulePushforward_obj (f : X ⟶ Y)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (n : ℤ) (hE : E.IsGE n)
    (q : ℤ) (hq : q < n) :
    IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) q).obj
      ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj E)) :=
  have := hE
  Stacks.DerivedFunctor.isZero_homology_totalRightDerived_obj
    (modulePushforward B S hS f) E n q hq

/-- The cohomology sheaves of the derived direct image of an `𝒪_X`-module placed in degree zero
vanish in every negative degree. -/
theorem isZero_homology_derivedModulePushforward_single (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (q : ℤ) (hq : q < 0) :
    IsZero ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) q).obj
      ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj
        ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj F))) :=
  isZero_homology_derivedModulePushforward_obj B S hS f _ 0 inferInstance q hq

end AlgebraicGeometry.Space

end

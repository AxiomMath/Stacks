module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFreeDualOnSite
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallSiteMonoidalClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFree
import StacksCore.Tactic.StacksAttribute

/-!
# The dual of a finite locally free module on an algebraic space is finite locally free

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let `M` be
a finite locally free `𝒪_F`-module on its small étale site, in the sense of Stacks 03DL(2).
Then the dual `M^∨ = 𝓗om_{𝒪_F}(M, 𝒪_F)` is finite locally free.

The dual is `AlgebraicGeometry.Space.smallEtaleInternalHomSmall` into the monoidal unit, the
internal Hom of Stacks 03EM brought down to the module universe of the schemes by the essential
smallness of the small étale site; the monoidal unit of
`AlgebraicGeometry.Space.modulesMonoidalCategory` is the structure sheaf itself, on the nose.

## Main results

* `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_smallEtaleDual`: **the dual of a finite
  locally free `𝒪_F`-module on an algebraic space is finite locally free.**
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_dual_pushforwardStructureModule`: the case
  the dual twist of Stacks 0GUV needs — for `f : X ⟶ Y` finite locally free in the sense of
  Stacks 03ZV, the dual `(f_*𝒪_X)^∨` is finite locally free on the small étale site of `Y`.

## Implementation notes

Nothing is proved here: both statements are
`AlgebraicGeometry.RingedSite.isFiniteLocallyFreeOnSite_internalHomSheafSmall_unit`, Stacks 0FA7
on an essentially small ringed site, read on the small étale ringed site of `F`.  That site is
`AlgebraicGeometry.RingedSite.{u + 1, u, u}` and is essentially `u`-small
(`AlgebraicGeometry.Space.instEssentiallySmallSmallEtaleRingedSite`), which is what puts the
dual at the module universe `u` of the schemes; the site-level statement leaves the object and
morphism universes of the site free, so no universe lift of the site is needed, exactly as for
the tensor product in `StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeModuleTensor`.

**This is one of the two inputs of the dual twist of Stacks 0GUV, not the obstruction.**  The
twist needs `(f_*𝒪_X)^∨` finite locally free, which is the second statement below, *and* the
coevaluation `𝒪_Y ⟶ f_*𝒪_X ⊗ (f_*𝒪_X)^∨` of Stacks 0FNY, which the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyFiniteLocallyFreeDualTwist`
record as unavailable at this module universe.  Supplying the finite local freeness does not
supply the coevaluation.

**No `@[stacks 0FA7]` attribute is carried.**  That tag is about a module on a scheme, where it
is proved as `Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFree_dualSheaf`; what is
new here is the statement for the small étale site of an algebraic space, which the tag does not
say.  The same convention is followed by
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeModuleTensor` for Stacks 0FDK.

## References

* [Stacks Project, Tag 0FA7](https://stacks.math.columbia.edu/tag/0FA7)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03ZV](https://stacks.math.columbia.edu/tag/03ZV)
* [Stacks Project, Tag 0GUV](https://stacks.math.columbia.edu/tag/0GUV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The dual of a finite locally free module on an algebraic space is finite locally free.**
The dual is `AlgebraicGeometry.Space.smallEtaleInternalHomSmall` into the monoidal unit of
`AlgebraicGeometry.Space.modulesMonoidalCategory`, which is the structure sheaf of `F`.

This is `AlgebraicGeometry.RingedSite.isFiniteLocallyFreeOnSite_internalHomSheafSmall_unit`,
Stacks 0FA7 on an essentially small ringed site, read on the small étale ringed site of `F`. -/
theorem isFiniteLocallyFreeOnSite_smallEtaleDual
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (M : Modules.{u, u} B S hS F hF)
    (hM : SheafOfModules.IsFiniteLocallyFreeOnSite M) :
    SheafOfModules.IsFiniteLocallyFreeOnSite
      (smallEtaleInternalHomSmall B S hS F hF M (𝟙_ (Modules.{u, u} B S hS F hF))) :=
  RingedSite.isFiniteLocallyFreeOnSite_internalHomSheafSmall_unit
    (smallEtaleRingedSite B S hS F hF) M hM

variable {X Y : AlgebraicSpaces B S hS}

/-- **The dual of the direct image of the structure sheaf along a finite locally free morphism
of algebraic spaces is finite locally free.**

For `f : X ⟶ Y` finite locally free in the sense of Stacks 03ZV the module `f_*𝒪_X` is finite
locally free on the small étale site of `Y` by definition, so
`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_smallEtaleDual` applies to it.  This is the
finite local freeness of `(f_*𝒪_X)^∨` that the dual twist in the proof of Stacks 0GUV needs in
order to make `(f_*𝒪_X)^∨ ⊗ f_*ℰ` finite locally free. -/
theorem isFiniteLocallyFreeOnSite_dual_pushforwardStructureModule (f : X ⟶ Y)
    (hf : IsFiniteLocallyFree B S hS f) :
    SheafOfModules.IsFiniteLocallyFreeOnSite
      (smallEtaleInternalHomSmall B S hS Y.1 Y.2 (pushforwardStructureModule B S hS f)
        (𝟙_ (Modules.{u, u} B S hS Y.1 Y.2))) :=
  isFiniteLocallyFreeOnSite_smallEtaleDual B S hS Y.1 Y.2 _ hf.2

end AlgebraicGeometry.Space

end

module

public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.DerivedPullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOnARingedSite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.KFlatResolvingDatum
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.OnARingedSpace

/-!
# `Lf^*` of a flat module in a single degree

Let `f : X ⟶ Y` be a morphism of schemes and `M` a flat `𝒪_Y`-module. The complex with `M` in
degree `q` and `0` elsewhere is K-flat, so the derived pullback `Lf^*` is computed on it by the
degreewise pullback:

`Lf^*(M[-q]) ≅ (f^*M)[-q]`.

## Main definitions

* `Stacks.Duality.derivedPullbackSingleIsoOfFlat` — the displayed isomorphism, at the locally
  small model of the two derived categories that `Stacks.Duality.derivedPullback` is stated at.

## Implementation notes

The three steps are `CategoryTheory.DerivedCategory.singleFunctorIsoCompQ` at either end —
which replaces the single object of the derived category by the class of the single complex —
`Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat` in the middle, and
`CategoryTheory.Functor.mapCochainComplexSingleFunctor` for the degreewise pullback of a single
complex. K-flatness of the single complex is the base case of [Stacks, Tag 06YQ],
`Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat`.

The flatness predicate is `AlgebraicGeometry.SheafOfModules.IsFlat` at `O := Y.sheaf`, which is
the one the K-flatness development consumes; it is produced for an invertible module by
`Stacks.AmpleNonvanishing.isFlat_of_isInvertibleModule`.

## References

* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Duality

/-- **`Lf^*` of a flat module placed in a single degree is its pullback in that degree.** For
`f : X ⟶ Y` a morphism of schemes and `M` a flat `𝒪_Y`-module, the complex `M[-q]` is K-flat, so
`Lf^*` is computed on it by the degreewise pullback. -/
def derivedPullbackSingleIsoOfFlat {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) M) (q : ℤ) :
    (Stacks.Duality.derivedPullback f).obj ((DerivedCategory.singleFunctor Y.Modules q).obj M) ≅
      (DerivedCategory.singleFunctor X.Modules q).obj ((Scheme.Modules.pullback f).obj M) :=
  have hK : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y.toRingedSpace
      ((CochainComplex.singleFunctor Y.Modules q).obj M) :=
    Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat _ _ hM q
  (Stacks.Duality.derivedPullback f).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ Y.Modules q).app M) ≪≫
    Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat f.toLRSHom.toShHom _ hK ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapCochainComplexSingleFunctor (modulePullback f.toLRSHom.toShHom) q).app M) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ X.Modules q).app
      ((Scheme.Modules.pullback f).obj M)).symm

end Stacks.Duality

end

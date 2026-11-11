module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackExistence
import StacksCore.Tactic.StacksAttribute

/-!
# The ordinary and the derived pullback–pushforward counit of a morphism of ringed topoi

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be a morphism of ringed topoi and let `K` be a complex
of `𝒪_C`-modules.  Three canonical maps are available: the comparison `Lf^* ⟶ f^*` of the
derived pullback with degreewise pullback, the comparison `f_* ⟶ Rf_*` of degreewise
pushforward with the derived pushforward, and the counit `Lf^* ∘ Rf_* ⟶ id` of the derived
adjunction.  Together with the ordinary counit `f^* f_* K ⟶ K` they form a square

```
Lf^* f_* K ⟶ f^* f_* K
    ↓              ↓
Lf^* Rf_* K ⟶      K
```

in `D(𝒪_C)`, and this file proves that it commutes.

## Main results

* `Stacks.Cohomology.DerivedPullbackOnRingedTopoi.derivedAdjunction_counit_fac`: Stacks 0FPI,
  the commutativity of the square above.

## Implementation notes

The commutativity of the square is proved, relative to the exactness of degreewise pullback on
K-flat complexes with flat terms, by `derivedPullbackPushforwardAdjunctionOfKFlat` (in the
namespace `Stacks.Cohomology.DerivedPullbackPushforwardAdjunction`) and its `_counit_fac`.  That
exactness is `pullbackInvertsQuasiIso_isKFlat`, which holds along every morphism of ringed topoi,
so the square specializes with no hypothesis beyond `hmos`.  The counit is that of
`derivedAdjunction`, Tag 07A6 at the same discharge, which
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPullback/DerivedPullbackExistence.lean`
states.

*What `hmos` is.*  `AlgebraicGeometry.RingedToposSiteHom` records only that the underlying
functor `f.u` is *continuous* — that is its sole `Prop` field, `isContinuous` — so `f` on its
own is a morphism of ringed *sites*.  Exactness of `f^{-1} = u_s`, the other half of the
source's Definition 00X1, is not a field of it, and
`CategoryTheory.Functor.IsMorphismOfSites` is this library's encoding of that definition
(`StacksFrontier/CategoryTheory/Sites/MorphismOfSites.lean`) for Grothendieck topologies:
continuity plus left and right exactness of `u_s`.  So `hmos` supplies the half of *morphism of
ringed topoi* that the structure omits rather than restricting the source's hypothesis — by
Stacks 00XC it is exactly what makes the geometric datum of `f` a morphism of topoi
(`CategoryTheory.Functor.IsMorphismOfSites.morphismOfTopoi`).  What is narrower than the source
here is not `hmos` but the *presentation*: `f` carries a functor between the underlying sites
rather than an arbitrary adjoint pair, as the docstring of `RingedToposSiteHom` (a site-level
variant of the morphisms of ringed topoi of Stacks 01D3) records and as the `@[stacks 07A6]` note on
`derivedAdjunction` repeats.

The square is stated for an object of the unbounded homotopy category rather than for a
cochain complex, which is the form the comparison maps of the two derived functors take and is
more general: a complex gives such an object through `HomotopyCategory.quotient`.

The instance argument `(pullbackOnHomotopy f).HasLeftDerivedFunctor` is not a residual
hypothesis either: it is a `Prop` class, it is discharged for every morphism of ringed topoi
by `hasLeftDerivedFunctor_pullbackOnHomotopy`, and by proof irrelevance `derivedPullback f`
does not depend on the witness.  It is carried as a binder only because `Lf^*` cannot be
written down without it.

## References

* [Stacks Project, Tag 0FPI](https://stacks.math.columbia.edu/tag/0FPI)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

namespace Stacks.Cohomology.DerivedPullbackOnRingedTopoi

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposSiteHom X Y) (hmos : f.u.IsMorphismOfSites Y.J X.J)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]

include hmos in
/-- **Stacks 0FPI.**  For a complex `K` of `𝒪_C`-modules the square

```
Lf^* f_* K ⟶ f^* f_* K
    ↓              ↓
Lf^* Rf_* K ⟶      K
```

commutes in `D(𝒪_C)`: its upper edge is the comparison `Lf^* ⟶ f^*`, its left edge is `Lf^*`
applied to the comparison `f_* ⟶ Rf_*`, its lower edge is the counit of the derived adjunction
`Lf^* ⊣ Rf_*`, and its right edge is the ordinary counit `f^* f_* ⟶ id`.

The derived counit is the one induced by the ordinary counit, which is exactly this
commutativity, so the proof is `derivedPullbackPushforwardAdjunctionOfKFlat_counit_fac`.

The source's hypothesis is just that `f` be a morphism of ringed topoi, and `hmos` is how that is
spelled here, not an extra condition: `AlgebraicGeometry.RingedToposSiteHom` records only the
continuity of `f.u`, while `CategoryTheory.Functor.IsMorphismOfSites` is the library's encoding
of Stacks 00X1 — continuity together with exactness of `f^{-1}` — and by Stacks 00XC
(`CategoryTheory.Functor.IsMorphismOfSites.morphismOfTopoi`) it is exactly `hmos` that makes the
geometric datum of `f` a morphism of topoi.  See the implementation notes above for the
presentation restriction, which is the repository's convention for ringed topoi and is separate
from `hmos`. -/
@[stacks 0FPI]
theorem derivedAdjunction_counit_fac
    (K : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)) :
    (derivedPullback f).map ((derivedPushforwardUnit f).app K) ≫
        (derivedAdjunction f hmos).counit.app (DerivedCategory.Qh.obj K) =
      (derivedPullbackComparison f).app
          ((f.pushforwardTopos.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((homotopyPullbackPushforwardAdjunction f).counit.app K) :=
  derivedPullbackPushforwardAdjunctionOfKFlat_counit_fac f hmos
    (fun h ↦ pullbackInvertsQuasiIso_isKFlat f h) K

end Stacks.Cohomology.DerivedPullbackOnRingedTopoi

end

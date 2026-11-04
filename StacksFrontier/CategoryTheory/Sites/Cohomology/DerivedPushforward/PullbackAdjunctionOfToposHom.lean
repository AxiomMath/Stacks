module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PullbackAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.PullbackInvertsQuasiIsoOfToposHom
import StacksCore.Tactic.StacksAttribute

/-!
# The derived adjunction `Lf^* ⊣ Rf_*` for a morphism of ringed topoi, unconditionally

Let `f : (Sh(C), 𝒪) ⟶ (Sh(D), 𝒪')` be a morphism of ringed topoi, given as the two-field
`AlgebraicGeometry.RingedToposHom` of Stacks 01D3, part (2). [Stacks, Tag 07A6] says that the
derived pullback `Lf^* : D(𝒪') ⥤ D(𝒪)` is left adjoint to the derived direct image
`Rf_* : D(𝒪) ⥤ D(𝒪')`.

This file constructs that adjunction for every morphism of ringed topoi whose two sites are
small in the universe of the sections of their structure sheaves.

## Main definitions

* `Stacks.Cohomology.DerivedPushforward.leftDerivedPullbackOfKFlat`: the resolving datum of
  K-flat complexes with flat terms.
* `Stacks.Cohomology.DerivedPushforward.derivedPullbackPushforwardAdjunctionOfToposHom`:
  `Lf^* ⊣ Rf_*`, with `Lf^*` the functor
  `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback`.

## References

* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (IsKFlat hasResolutions_isKFlat)

universe u

namespace Stacks.Cohomology.DerivedPushforward

attribute [local instance 10000] HasDerivedCategory.standard

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposHom X Y)

/-- The resolving datum `Stacks.Cohomology.DerivedPushforward.LeftDerivedPullback` of a
morphism of ringed topoi given by the K-flat complexes with flat terms. -/
def leftDerivedPullbackOfKFlat : LeftDerivedPullback f :=
  LeftDerivedPullback.ofResolving f (IsKFlat (Y := Y))
    (hasResolutions_isKFlat (Y := Y)) (DerivedPullbackOfToposHom.pullbackInvertsQuasiIso_isKFlat f)

/-- Degreewise pullback along a morphism of ringed topoi has a total left derived functor. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_ofToposHom :
    (DerivedPullbackOfToposHom.pullbackOnHomotopy f).HasLeftDerivedFunctor
      (DerivedPullbackOfToposHom.quasiIsoTarget (Y := Y)) :=
  DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy f

/-- The functor of `leftDerivedPullbackOfKFlat` is the derived pullback `Lf^*`. -/
theorem leftDerivedPullbackOfKFlat_functor :
    (leftDerivedPullbackOfKFlat f).functor = DerivedPullbackOfToposHom.derivedPullback f :=
  rfl

/-- For a morphism of ringed topoi `f`, the derived pullback `Lf^*` is left adjoint to the
derived direct image `Rf_*` on the unbounded derived categories,
`Hom_{D(𝒪)}(Lf^*G, F) = Hom_{D(𝒪')}(G, Rf_*F)`. -/
@[stacks 07A6 "for a morphism of ringed topoi whose two sites are small in the universe of the
  sections of their structure sheaves"]
def derivedPullbackPushforwardAdjunctionOfToposHom :
    DerivedPullbackOfToposHom.derivedPullback f ⊣ derivedPushforward (X := X) (Y := Y) f :=
  derivedPullbackPushforwardAdjunction f (leftDerivedPullbackOfKFlat f)

end Stacks.Cohomology.DerivedPushforward

end

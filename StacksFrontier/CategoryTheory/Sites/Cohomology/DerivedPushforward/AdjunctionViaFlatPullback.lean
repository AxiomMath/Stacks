module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.AcyclicityOfDegreewisePullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.InverseImageExactness

/-!
# The derived pullback–pushforward adjunction from flatness of pullback

Let `f : (Sh(C), 𝒪) ⟶ (Sh(D), 𝒪')` be a morphism of ringed topoi whose underlying functor is a
morphism of sites, and suppose that pullback along every morphism of ringed topoi preserves
flatness of modules (`Stacks.Sheaves.InverseImageExactness.PullbackPreservesIsFlatUniv`). Then
degreewise pullback carries a quasi-isomorphism between K-flat complexes with flat terms to an
isomorphism of `D(𝒪)`, the unbounded derived pullback `Lf^*` exists, and `Lf^*` is left adjoint
to the unbounded derived pushforward `Rf_*`.

## Main results

* `pullbackInvertsQuasiIso_isKFlat_of_flatPullback`: degreewise pullback carries a
  quasi-isomorphism between K-flat complexes with flat terms to an isomorphism of `D(𝒪)`.
* `pullbackOnHomotopy_hasLeftDerivedFunctor_of_flatPullback`: the derived pullback `Lf^*` exists.
* `derivedPullbackPushforwardAdjunctionOfFlatPullback`, together with
  `derivedPullbackPushforwardAdjunctionOfFlatPullback_unit_fac` and
  `derivedPullbackPushforwardAdjunctionOfFlatPullback_counit_fac`: `Lf^*` is left adjoint to
  `Rf_*`, with unit and counit compatible with those of the pullback–pushforward adjunction.

## References

* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 0G6R](https://stacks.math.columbia.edu/tag/0G6R)
* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
-/

open Stacks.Sheaves.RingedToposDerivedPullback

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposSiteHom X Y)

/-- For a morphism of ringed topoi, degreewise pullback carries a quasi-isomorphism between
K-flat complexes with flat terms to an isomorphism of `D(𝒪)`, provided pullback along every
morphism of ringed topoi preserves flatness of a module and `f.u` is a morphism of sites. -/
theorem pullbackInvertsQuasiIso_isKFlat_of_flatPullback
    (hpf : Stacks.Sheaves.InverseImageExactness.PullbackPreservesIsFlatUniv.{u}) :
    f.u.IsMorphismOfSites Y.J X.J →
      PullbackInvertsQuasiIso f (IsKFlat (Y := Y)) :=
  pullbackInvertsQuasiIso_isKFlat_of_pullbackPreservesShortExact f
    (Stacks.Sheaves.InverseImageExactness.pullbackPreservesShortExact f hpf)

/-- For a morphism of ringed topoi, degreewise pullback has a left derived functor on the whole
unbounded derived category, i.e. `Lf^*` exists, provided pullback along every morphism of ringed
topoi preserves flatness of a module. -/
theorem pullbackOnHomotopy_hasLeftDerivedFunctor_of_flatPullback
    (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (hpf : Stacks.Sheaves.InverseImageExactness.PullbackPreservesIsFlatUniv.{u}) :
    (pullbackOnHomotopy f).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (.up ℤ)) :=
  pullbackOnHomotopy_hasLeftDerivedFunctor_of_kFlat f hmos
    (pullbackInvertsQuasiIso_isKFlat_of_flatPullback f hpf)

section Adjunction

variable [(pullbackOnHomotopy f).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (.up ℤ))]

/-- For a morphism of ringed topoi, the unbounded derived pullback `Lf^*` is left adjoint to the
unbounded derived pushforward `Rf_*`, provided pullback along every morphism of ringed topoi
preserves flatness of a module. -/
def derivedPullbackPushforwardAdjunctionOfFlatPullback
    (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (hpf : Stacks.Sheaves.InverseImageExactness.PullbackPreservesIsFlatUniv.{u}) :
    derivedPullback f ⊣ derivedPushforward f :=
  derivedPullbackPushforwardAdjunctionOfKFlat f hmos
    (pullbackInvertsQuasiIso_isKFlat_of_flatPullback f hpf)

/-- The unit of `derivedPullbackPushforwardAdjunctionOfFlatPullback` agrees with the ordinary
pullback--pushforward unit of Stacks 03D7 after applying the canonical comparison maps of
`Lf^*` and `Rf_*`. -/
theorem derivedPullbackPushforwardAdjunctionOfFlatPullback_unit_fac
    (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (hpf : Stacks.Sheaves.InverseImageExactness.PullbackPreservesIsFlatUniv.{u})
    (M : HomotopyCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (.up ℤ)) :
    (derivedPullbackPushforwardAdjunctionOfFlatPullback f hmos hpf).unit.app
          (DerivedCategory.Qh.obj M) ≫
        (derivedPushforward f).map ((derivedPullbackComparison f).app M) =
      DerivedCategory.Qh.map ((homotopyPullbackPushforwardAdjunction f).unit.app M) ≫
        (derivedPushforwardUnit f).app
          ((f.pullbackTopos.mapHomotopyCategory (.up ℤ)).obj M) :=
  derivedPullbackPushforwardAdjunctionOfKFlat_unit_fac f hmos
    (pullbackInvertsQuasiIso_isKFlat_of_flatPullback f hpf) M

/-- The counit of `derivedPullbackPushforwardAdjunctionOfFlatPullback` agrees with the ordinary
pullback--pushforward counit of Stacks 03D7 after applying the canonical comparison maps of
`Rf_*` and `Lf^*`. -/
theorem derivedPullbackPushforwardAdjunctionOfFlatPullback_counit_fac
    (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (hpf : Stacks.Sheaves.InverseImageExactness.PullbackPreservesIsFlatUniv.{u})
    (K : HomotopyCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (.up ℤ)) :
    (derivedPullback f).map ((derivedPushforwardUnit f).app K) ≫
        (derivedPullbackPushforwardAdjunctionOfFlatPullback f hmos hpf).counit.app
          (DerivedCategory.Qh.obj K) =
      (derivedPullbackComparison f).app
          ((f.pushforwardTopos.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((homotopyPullbackPushforwardAdjunction f).counit.app K) :=
  derivedPullbackPushforwardAdjunctionOfKFlat_counit_fac f hmos
    (pullbackInvertsQuasiIso_isKFlat_of_flatPullback f hpf) K

end Adjunction

end Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

end

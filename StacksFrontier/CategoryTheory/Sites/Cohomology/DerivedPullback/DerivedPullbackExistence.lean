module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.AcyclicityOfDegreewisePullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOfRingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.PullbackPreservesFlatness
public import StacksCore.Tactic.StacksAttribute

/-!
# The derived pullback along a morphism of ringed topoi exists and is exact

Let `f : (Sh(C), O) ⟶ (Sh(C'), O')` be a morphism of ringed topoi.  Tag 06YY asserts that there
is an exact functor of triangulated categories

`Lf^* : D(O') ⟶ D(O)`

with `Lf^* K^• = f^* K^•` for every K-flat complex `K^•` of `O'`-modules with flat terms, and in
particular for every bounded above complex of flat `O'`-modules.

`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPullback/DerivedPullbackOfRingedTopoi.lean`
proves all of this *relative to* the hypothesis
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.PullbackInvertsQuasiIso f IsKFlat` —
that degreewise pullback carries a quasi-isomorphism between K-flat complexes with flat terms to
an isomorphism of `D(O)`.  **This file discharges that hypothesis**, so Tag 06YY holds with no
input beyond `f` being a morphism of ringed topoi.

## How the hypothesis is discharged

The source gets it from the factorization `f^* = (f^{-1}-) ⊗_{f^{-1}O'} O` together with
Tags 0G7E and 06YT.  The route that closes in this tree is the other one the source offers,
through the splicing of the cycles sequences: the hypothesis reduces, by
`Stacks.Sheaves.RingedToposDerivedPullback`'s
`pullbackInvertsQuasiIso_isKFlat_of_pullbackPreservesShortExact`, to Tag 0G6R — that pullback
keeps a short exact sequence with flat third term short exact — and Tag 0G6R reduces in turn to
Tag 05VD for the abstract module pullback, which is
`AlgebraicGeometry.RingedToposSiteHom.pullbackPreservesShortExact` of
`StacksFrontier/CategoryTheory/Sites/Modules/FlatMorphisms/PullbackPreservesFlatness.lean`.  The
flatness of the cycles that Tag 0G6R consumes there is Tag 0G7C, which is unconditional.

## Main results

* `pullbackInvertsQuasiIso_isKFlat`: **the hypothesis carried by every ringed-topos derived
  pullback result in this tree, discharged.**
* `hasLeftDerivedFunctor_pullbackOnHomotopy`: degreewise pullback followed by localization has
  an everywhere-defined left derived functor, so `Lf^*` exists.  This is the witness for the
  instance argument that the clauses of Tag 06YY stated on
  `Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback` carry.
* `derivedAdjunction`: **the adjunction `Lf^* ⊣ Rf_*` of Tag 07A6**, which the conditional
  statements of that tag carry the same discharged hypothesis for, with no hypothesis beyond
  `hmos`.
* `isTriangulated_derivedPullback`: **the exactness assertion of Tag 06YY**, with no hypothesis
  beyond `hmos`.
* `isIso_derivedPullbackComparison_app_kFlat` and
  `isIso_derivedPullbackComparison_app_boundedAbove`: **the two computation assertions of
  Tag 06YY**, likewise.

## Implementation notes

*What `hmos` is, and why it is not an added hypothesis.*
`AlgebraicGeometry.RingedToposSiteHom` asks only that the underlying functor `f.u` be
*continuous*; left exactness of `f^{-1}` is not a field of it.  A morphism of ringed topoi in the
source's sense has that exactness, and `f.u.IsMorphismOfSites Y.J X.J` is exactly what supplies
it — it is what makes `f` a morphism of ringed *topoi* at all, as
`AlgebraicGeometry.RingedToposSiteHom.toToposHom` records.  The same hypothesis is carried by the
Tag 05VD, Tag 0G6R and Tag 04JC statements of this chain for the same reason.

*The instance argument.*  The clauses below that mention `Lf^*` by name are stated in the binder
context of `Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback`, which takes
`HasLeftDerivedFunctor` as an instance argument — the functor cannot be written down without it.
That argument is **not** a residual hypothesis: it is a `Prop` class, it is discharged for every
morphism of ringed topoi by `hasLeftDerivedFunctor_pullbackOnHomotopy` below, and by proof
irrelevance `derivedPullback f` is the same functor whichever witness is supplied.

*Why this is a separate module and not an extension of the Tag 06YY file.*  The reduction to
Tag 0G6R lives in
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPullback/AcyclicityOfDegreewisePullback.lean`,
which imports
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/AdjunctionAcyclicityInput.lean`,
which imports the Tag 06YY file for `isKFlat_mappingCone`.  Adding the discharge to the Tag 06YY
file itself would therefore close an import cycle.  Nothing is restated: each clause below is one
application of the corresponding conditional result, with the discharged hypothesis supplied.

## References

* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 0G6R](https://stacks.math.columbia.edu/tag/0G6R)
* [Stacks Project, Tag 0G7C](https://stacks.math.columbia.edu/tag/0G7C)
* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Sheaves.RingedToposDerivedPullback

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

include hmos in
/-- **Degreewise pullback inverts the quasi-isomorphisms between K-flat complexes with flat
terms.**  This is the hypothesis that the ringed-topos derived pullback and the derived
adjunction of Tag 07A6 were carrying as a parameter, and it holds along every morphism of ringed
topoi.

It reduces to Tag 0G6R by the splicing argument of
`Stacks.Sheaves.RingedToposDerivedPullback.acyclic_pullbackComplex_of_kFlat_of_acyclic`, and
Tag 0G6R is now unconditional. -/
theorem pullbackInvertsQuasiIso_isKFlat : PullbackInvertsQuasiIso f (IsKFlat (Y := Y)) :=
  pullbackInvertsQuasiIso_isKFlat_of_pullbackPreservesShortExact f
    (RingedToposSiteHom.pullbackPreservesShortExact f) hmos

include hmos in
/-- **The derived pullback exists.**  Degreewise pullback followed by localization has an
everywhere-defined left derived functor, so `Lf^*` is defined on the whole of `D(O')`.

The resolving half of the datum is Tag 06YS (`hasResolutions_isKFlat`) and the exactness half is
`pullbackInvertsQuasiIso_isKFlat`.  This is the witness for the instance argument of
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback`. -/
theorem hasLeftDerivedFunctor_pullbackOnHomotopy :
    (pullbackOnHomotopy f).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ)) :=
  pullbackOnHomotopy_hasLeftDerivedFunctor f _ hasResolutions_isKFlat
    (pullbackInvertsQuasiIso_isKFlat f hmos)

variable [(pullbackOnHomotopy f).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]

/-- **Stacks 07A6 along an arbitrary morphism of ringed topoi.**  The unbounded derived
pullback `Lf^*` is left adjoint to the unbounded derived pushforward `Rf_*`.

This is `derivedPullbackPushforwardAdjunctionOfKFlat` with its one deferred input supplied by
`pullbackInvertsQuasiIso_isKFlat`.  An `Adjunction` is exactly the bifunctorial bijection
`Hom_{D(𝒪_C)}(Lf^*G, F) = Hom_{D(𝒪_D)}(G, Rf_*F)` that the source states: its `homEquiv` is
the bijection and `Adjunction.homEquiv_naturality_left`, `homEquiv_naturality_right` are its
naturality in the two arguments.

The only input is `hmos`, and it is not an assumption beyond the source's.  `RingedToposSiteHom`
records continuity of `f.u` and nothing else, so `f` alone is a morphism of ringed *sites*;
`hmos : f.u.IsMorphismOfSites Y.J X.J` adds the exactness of `f^{-1}` that Stacks 00X1 demands,
which is what makes `f` a morphism of ringed *topoi* (Stacks 00XC,
`CategoryTheory.Functor.IsMorphismOfSites.morphismOfTopoi`).  Everything else the construction
needed has been discharged: the deferred exactness input is `pullbackInvertsQuasiIso_isKFlat`,
which holds along every morphism of ringed topoi, and the `HasLeftDerivedFunctor` binder is a
`Prop` class discharged by `hasLeftDerivedFunctor_pullbackOnHomotopy`. -/
@[stacks 07A6 "for a morphism of ringed topoi presented by a morphism of the underlying sites,
at RingedTopos.{u, u, u}"]
noncomputable def derivedAdjunction : derivedPullback f ⊣ derivedPushforward f :=
  derivedPullbackPushforwardAdjunctionOfKFlat f hmos
    (fun h ↦ pullbackInvertsQuasiIso_isKFlat f h)

include hmos in
/-- **Tag 06YY, exactness.**  The derived pullback along a morphism of ringed topoi is an exact
functor of triangulated categories. -/
@[stacks 06YY "exactness"]
theorem isTriangulated_derivedPullback : (derivedPullback f).IsTriangulated :=
  derivedPullback_isTriangulated f (pullbackInvertsQuasiIso_isKFlat f hmos)

include hmos in
/-- **Tag 06YY, the computation.**  The canonical comparison `Lf^* K^• ⟶ f^* K^•` is invertible
at a K-flat complex of `O'`-modules with flat terms: the derived pullback of such a complex is
computed by degreewise pullback. -/
@[stacks 06YY "computation on K-flat complexes with flat terms"]
theorem isIso_derivedPullbackComparison_app_kFlat
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK :
      letI := Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u} Y.O
      @CochainComplex.KFlatBifunctor.KFlat
        (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)
        (Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u, u, u, u, u} Y.O)
        (Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u} Y.O)
        inferInstance K)
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i)) :
    IsIso ((derivedPullbackComparison f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) :=
  isIso_derivedPullbackComparison_app_of_kFlat_of_flat f
    (pullbackInvertsQuasiIso_isKFlat f hmos) K hK hflat

include hmos in
/-- **Tag 06YY, the computation on bounded above complexes of flat modules.**  A bounded above
complex of flat `O'`-modules is K-flat by Tag 06YQ, so its derived pullback is computed by
degreewise pullback. -/
@[stacks 06YY "computation on bounded above flat complexes"]
theorem isIso_derivedPullbackComparison_app_boundedAbove
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hbound : ∃ n : ℤ, K.IsStrictlyLE n)
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i)) :
    IsIso ((derivedPullbackComparison f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) :=
  isIso_derivedPullbackComparison_app_of_boundedAbove_of_flat f
    (pullbackInvertsQuasiIso_isKFlat f hmos) K hbound hflat

end Stacks.Cohomology.DerivedPullbackOnRingedTopoi

end

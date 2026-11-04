module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorBraidingDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorBraidingKFlat
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposTensorBraiding
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposTensorTotalBraiding

/-!
# `Lf^*` is a braided functor for the derived tensor product, on a ringed topos

Let `f : (Sh(C), 𝒪) ⟶ (Sh(D), 𝒪')` be a morphism of ringed topoi presented by a morphism of
sites.  This file assembles, with nothing assumed, the statement that the comparison of
[Stacks, Tag 07A4],

`Lf^*(M ⊗^𝐋_{𝒪'} N) ≅ Lf^*M ⊗^𝐋_𝒪 Lf^*N`,

carries the commutativity constraint of the symmetric monoidal derived category of
[Stacks, Tag 0FPT] on `D(𝒪')` to the one on `D(𝒪)` — that is, that `Lf^*` is a *braided* and not
merely a monoidal functor for the derived tensor product of [Stacks, Tag 06YU].

Each of the three layers it joins is proved elsewhere; this file is the wiring, and every
declaration below is one application.

1. **Modules.** `Stacks.Sheaves.DerivedPullback.pullbackToposTensorMapDeg_braiding` — the
   comparison of [Stacks, Tag 03EL] for the site-presented pullback commutes with the symmetry
   of the tensor product sheaf, at the modules of a fixed bidegree.  It rests on
   `Stacks.SheafOfModules.RingedToposPullback.braiding`, the braided clause of Tag 03EL, which
   is the fourth coherence alongside the associativity and the two unitalities of
   `Stacks.SheafOfModules.RingedToposPullback.PullbackCoherence`.
2. **Complexes.** `Stacks.Sheaves.DerivedPullback.pullbackToposTensorTotalIso_braiding_of_module`
   — the comparison of total tensor complexes is braided for the Koszul symmetry
   `Stacks.SheafOfModules.Tensor.tensorComplexFlipIso` of [Stacks, Tag 06YM], summand by summand
   with the sign `(-1)^{pq}`, granted layer 1.
3. **The derived category.**
   `Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_braiding_app_of_kFlat` at a pair of
   K-flat complexes with flat terms, and
   `Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_braiding_of_models` for the descent
   to all of `D(𝒪') × D(𝒪')` by [Stacks, Tag 06YS].

## Main results

* `Stacks.Sheaves.DerivedPullback.pullbackToposTensorTotalIso_braiding` — layer 2 with its
  hypothesis discharged.
* `Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_braiding` — **the braidedness of the
  comparison of [Stacks, Tag 07A4] for arbitrary `M, N` in `D(𝒪')`**, with no finiteness,
  boundedness, flatness or quasi-coherence hypothesis.

## Implementation notes

*No tag is registered here.*  [Stacks, Tag 07A4] is registered on the comparison itself,
`Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso`, and the braidedness is not a separate
tag of the source: the source states the comparison and leaves its coherences to Tag 0FPT's
section.  What consumes the result is [Stacks, Tag 0FPM], in
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/RelativeCupProductBraiding.lean`.

*The constraint is the one the source prescribes.*  It is
`Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingHom`, the braiding of
`canonicalDerivedSymmetric`, whose monoidal product is
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor` of [Stacks, Tag 06YU] on the nose.
Nothing below supplies a symmetry as data, and no second braiding or associator is defined.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Sheaves.DerivedPullback.KFlatPullback
open Stacks.SheafOfModules.DerivedMonoidal (canonicalBraidingHom DerivedModules)
open scoped CategoryTheory.Prod

namespace Stacks.Sheaves.DerivedPullback

universe u

attribute [local instance] HasDerivedCategory.standard

section Assembly

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]
  (hmos : f.u.IsMorphismOfSites Y.J X.J)

omit [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))] in
/-- **The comparison of total tensor complexes of [Stacks, Tag 03EL] is braided for the Koszul
symmetry of [Stacks, Tag 06YM]**, with nothing assumed: this is
`pullbackToposTensorTotalIso_braiding_of_module` with its module-level hypothesis discharged by
`pullbackToposTensorMapDeg_braiding`, the braided clause of Tag 03EL read at the modules of a
bidegree. -/
theorem pullbackToposTensorTotalIso_braiding
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    (pullbackComplex f).map (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso Y.O K L).hom ≫
        (pullbackToposTensorTotalIso f hmos L K).hom =
      (pullbackToposTensorTotalIso f hmos K L).hom ≫
        (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso X.O
          ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)).hom :=
  pullbackToposTensorTotalIso_braiding_of_module f hmos K L
    (fun p q => pullbackToposTensorMapDeg_braiding f hmos K L p q)

/-- **The comparison of [Stacks, Tag 07A4] carries the commutativity constraint of
[Stacks, Tag 0FPT] on `D(𝒪')` to the one on `D(𝒪)`**, for arbitrary `M, N` in `D(𝒪')` and with no
finiteness, boundedness, flatness or quasi-coherence hypothesis.

Equivalently: for a morphism of ringed topoi presented by a morphism of sites, `Lf^*` is a
*braided* functor for the derived tensor product of [Stacks, Tag 06YU], and not merely a functor
carrying a comparison.

This is the ringed-topos counterpart of
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_braiding`, and it is the whole
remaining content of [Stacks, Tag 0FPM] in this development. -/
theorem derivedPullbackTensorIso_braiding (M N : DerivedModules Y.O) :
    (derivedPullback f).map (canonicalBraidingHom Y.O M N) ≫
        (derivedPullbackTensorIso f hmos).hom.app (N, M) =
      (derivedPullbackTensorIso f hmos).hom.app (M, N) ≫
        canonicalBraidingHom X.O ((derivedPullback f).obj M) ((derivedPullback f).obj N) :=
  derivedPullbackTensorIso_braiding_of_models f hmos
    (fun P Q hP hQ hflatP hflatQ =>
      derivedPullbackTensorIso_braiding_app_of_kFlat f hmos P Q hP hQ hflatP hflatQ
        (fun A B => pullbackToposTensorTotalIso_braiding f hmos A B))
    M N

end Assembly

end Stacks.Sheaves.DerivedPullback

end

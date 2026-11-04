module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.FlatKFlatDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorBraidingNatTrans

/-!
# From K-flat representatives to all of `D(𝒪') × D(𝒪')`, for the braidedness of Tag 07A4

Let `f : (Sh(C), 𝒪) ⟶ (Sh(D), 𝒪')` be a morphism of ringed topoi presented by a morphism of
sites.  The comparison of [Stacks, Tag 07A4],

`Lf^*(M ⊗^𝐋_{𝒪'} N) ≅ Lf^*M ⊗^𝐋_𝒪 Lf^*N`,

is *braided* when it carries the commutativity constraint of the symmetric monoidal derived
category of [Stacks, Tag 0FPT] on `D(𝒪')` to the one on `D(𝒪)`.  This file expresses the two
sides as natural transformations on `D(𝒪') × D(𝒪')` and shows that the braidedness for
*arbitrary* `M, N` follows from the braidedness at every pair of K-flat complexes with flat
terms; by [Stacks, Tag 06YS] such complexes localize to the whole derived category.

## Main definitions

* `Stacks.Sheaves.DerivedPullback.braidingThenComparison` — the transformation
  `(M, N) ↦ Lf^*(M ⊗^𝐋 N) ⟶ Lf^*N ⊗^𝐋 Lf^*M` given by the derived pullback of the commutativity
  constraint followed by the comparison of Tag 07A4 at the swapped pair.
* `Stacks.Sheaves.DerivedPullback.comparisonThenBraiding` — the transformation given by the
  comparison of Tag 07A4 followed by the commutativity constraint of the derived pullbacks.

## Main results

* `Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_braiding_of_models` — the braidedness
  of the comparison of Tag 07A4 for **all** `M, N` in `D(𝒪')`, from its braidedness at every pair
  of K-flat complexes with flat terms.
* `Stacks.Sheaves.DerivedPullback.braidingThenComparison_app` and
  `Stacks.Sheaves.DerivedPullback.comparisonThenBraiding_app` — the components of the two
  transformations.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Sheaves.DerivedPullback.KFlatPullback
open Stacks.SheafOfModules.DerivedMonoidal (canonicalBraidingHom canonicalBraidingNatTrans
  DerivedModules)
open scoped CategoryTheory.Prod

namespace Stacks.Sheaves.DerivedPullback

universe u

attribute [local instance] HasDerivedCategory.standard

section Descent

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

/-- **The left-hand side of the braidedness of Tag 07A4, as a natural transformation** on
`D(𝒪') × D(𝒪')`: the derived pullback of the commutativity constraint of [Stacks, Tag 0FPT],
followed by the comparison of [Stacks, Tag 07A4] at the swapped pair. -/
def braidingThenComparison :
    Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O) ⋙
        derivedPullback f ⟶
      CategoryTheory.Prod.swap _ _ ⋙
        ((derivedPullback f).prod (derivedPullback f) ⋙
          Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)) :=
  Functor.whiskerRight (canonicalBraidingNatTrans Y.O) (derivedPullback f) ≫
    Functor.whiskerLeft (CategoryTheory.Prod.swap _ _) (derivedPullbackTensorIso f hmos).hom

/-- **The right-hand side of the braidedness of Tag 07A4, as a natural transformation**: the
comparison of [Stacks, Tag 07A4], followed by the commutativity constraint of
[Stacks, Tag 0FPT] at the pair of derived pullbacks. -/
def comparisonThenBraiding :
    Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O) ⋙
        derivedPullback f ⟶
      CategoryTheory.Prod.swap _ _ ⋙
        ((derivedPullback f).prod (derivedPullback f) ⋙
          Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)) :=
  (derivedPullbackTensorIso f hmos).hom ≫
    Functor.whiskerLeft ((derivedPullback f).prod (derivedPullback f))
      (canonicalBraidingNatTrans X.O)

/-- The components of `braidingThenComparison`. -/
theorem braidingThenComparison_app (M N : DerivedModules Y.O) :
    (braidingThenComparison f hmos).app (M, N) =
      (derivedPullback f).map (canonicalBraidingHom Y.O M N) ≫
        (derivedPullbackTensorIso f hmos).hom.app (N, M) :=
  rfl

/-- The components of `comparisonThenBraiding`. -/
theorem comparisonThenBraiding_app (M N : DerivedModules Y.O) :
    (comparisonThenBraiding f hmos).app (M, N) =
      (derivedPullbackTensorIso f hmos).hom.app (M, N) ≫
        canonicalBraidingHom X.O ((derivedPullback f).obj M) ((derivedPullback f).obj N) :=
  rfl

/-- **The comparison of [Stacks, Tag 07A4] carries the commutativity constraint of
[Stacks, Tag 0FPT] on `D(𝒪')` to the one on `D(𝒪)` for arbitrary `M, N`, as soon as it does so at
every pair of K-flat complexes with flat terms.** -/
theorem derivedPullbackTensorIso_braiding_of_models
    (hmodel : ∀ P N : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ,
      CochainComplex.KFlatBifunctor.KFlat
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) P →
      CochainComplex.KFlatBifunctor.KFlat
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) N →
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (P.X i)) →
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (N.X i)) →
      (derivedPullback f).map
            (canonicalBraidingHom Y.O (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N)) ≫
          (derivedPullbackTensorIso f hmos).hom.app
            (DerivedCategory.Q.obj N, DerivedCategory.Q.obj P) =
        (derivedPullbackTensorIso f hmos).hom.app
            (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N) ≫
          canonicalBraidingHom X.O
            ((derivedPullback f).obj (DerivedCategory.Q.obj P))
            ((derivedPullback f).obj (DerivedCategory.Q.obj N)))
    (M N : DerivedModules Y.O) :
    (derivedPullback f).map (canonicalBraidingHom Y.O M N) ≫
        (derivedPullbackTensorIso f hmos).hom.app (N, M) =
      (derivedPullbackTensorIso f hmos).hom.app (M, N) ≫
        canonicalBraidingHom X.O ((derivedPullback f).obj M) ((derivedPullback f).obj N) :=
  NatTrans.congr_app (natTrans_ext_of_flatKFlat Y (braidingThenComparison f hmos)
    (comparisonThenBraiding f hmos) hmodel) (M, N)

end Descent

end Stacks.Sheaves.DerivedPullback

end

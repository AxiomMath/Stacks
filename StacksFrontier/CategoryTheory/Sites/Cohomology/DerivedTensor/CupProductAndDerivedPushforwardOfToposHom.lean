module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorTotalSquareOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.DerivedAdjunctionOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.CupProductAndDerivedPushforward
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RelativeCupProductBraidingOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.NaiveCupProductOfToposHom

/-! # The naive cup product and the relative cup product, for a morphism of ringed topoi

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi in the sense of Stacks 01D3,
part (2) — a morphism of the underlying topoi together with the structure map, with no functor
between the underlying sites — and let `K`, `M` be unbounded cochain complexes of
`O_C`-modules.  **Stacks 0FPK** asserts that the diagram

```
f_*K ⊗^L_{O_D} f_*M ───────────→ Rf_*K ⊗^L_{O_D} Rf_*M
        │                                 │
        ↓                                 ↓
Tot(f_*K ⊗_{O_D} f_*M)            Rf_*(K ⊗^L_{O_C} M)
        │                                 │
        ↓                                 ↓
f_*Tot(K ⊗_{O_C} M) ───────────→ Rf_*Tot(K ⊗_{O_C} M)
```

commutes in `D(O_D)`.  The two horizontal maps and the top right vertical one are the comparison
`f_* ⟶ Rf_*`; the right-hand column is the relative cup product of **Stacks 0B6C** followed by
`Rf_*` of the canonical map from the derived tensor product to the ordinary total tensor complex
(**Stacks 06YU**); the left-hand column is that same canonical map followed by the naive cup
product of Stacks 0FPJ.

## Main definitions

* `Stacks.Cohomology.CupProductAndDerivedPushforwardOfToposHom.pushforwardComparisonQ`: the
  comparison `Q(f_*K) ⟶ Rf_*(QK)` of the derived direct image with degreewise direct image, read
  between the images of the localization functor `Q`.

## Main results

All in the namespace `Stacks.Cohomology.CupProductAndDerivedPushforwardOfToposHom`.

* `derivedCounit_pushforwardComparisonQ`: **Stacks 0FPI** read at `Q`.
* `naiveCupProduct_relativeCupProduct`: **Stacks 0FPK**, with no hypothesis and no class
  argument.
* `naiveCupProduct_relativeCupProduct_of_instances`: the same hexagon with the class arguments of
  the cup product kept as binders.

## Implementation notes

The proof is the source's, and is the one of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/CupProductAndDerivedPushforward.lean`
with each input replaced by its counterpart for a morphism of ringed topoi: the adjunction
`Lf^* ⊣ Rf_*` of Stacks 07A6 and its counit factorization Stacks 0FPI
(`Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction`,
`derivedAdjunction_counit_fac`), the comparison of Stacks 07A4
(`Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso`), Stacks 0FPH
(`Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullback_toTensor_square`), the relative cup
product `Stacks.Cohomology.RelativeCupProductOfToposHom.relativeCupProduct` and the naive cup
product `Stacks.Cohomology.NaiveCupProductOfToposHom.naiveCupProduct`.  None of them asks for a
functor between the underlying sites.  Both composites are maps into `Rf_*Tot(K ⊗_{O_C} M)`, so
they are compared through their adjoints along `Lf^*`; the bookkeeping is the abstract
`Stacks.Cohomology.CupProductAndDerivedPushforward.hexagon_of_transposes`.

No boundedness hypothesis is imposed on `K` or `M`: the source imposes none.

## References

* [Stacks Project, Tag 0FPK](https://stacks.math.columbia.edu/tag/0FPK)
* [Stacks Project, Tag 0FPH](https://stacks.math.columbia.edu/tag/0FPH)
* [Stacks Project, Tag 0FPI](https://stacks.math.columbia.edu/tag/0FPI)
* [Stacks Project, Tag 0B6C](https://stacks.math.columbia.edu/tag/0B6C)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.NaiveCupProductOfToposHom
open Stacks.Cohomology.RelativeCupProductOfToposHom
open Stacks.DerivedTensor.RingedSite
open Stacks.Sheaves.DerivedPullback (bifunctorMap)
open Stacks.Sheaves.DerivedPullback.OfToposHom (pullbackComparisonQ pullbackComparisonQ_naturality
  derivedPullbackTensorIso pullbackTensorComplexIso derivedPullback_toTensor_square_of_instances)
open Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom (pullbackComplex)

namespace Stacks.Cohomology.CupProductAndDerivedPushforwardOfToposHom

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  (f : RingedToposHom X Y)

/-! ## The comparison `f_* ⟶ Rf_*` at the localization functor -/

/-- **The comparison `Q(f_*K) ⟶ Rf_*(QK)`** of degreewise direct image with the derived direct
image, from the image in `D(O_D)` of the degreewise direct image of a complex of `O_C`-modules to
the derived direct image of its image in `D(O_C)`.  It is the canonical comparison of the derived
functor with the two identifications between `Q` and `Qh ∘ quotient` inserted at either end. -/
def pushforwardComparisonQ
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    DerivedCategory.Q.obj ((pushforwardComplex f).obj K) ⟶
      (derivedPushforward f).obj (DerivedCategory.Q.obj K) :=
  (DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).inv.app
        ((pushforwardComplex f).obj K) ≫
    (((pushforwardOnHomotopy (X := X) (Y := Y) f).totalRightDerivedUnit DerivedCategory.Qh
          (sourceQuasiIso X)).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
      (derivedPushforward f).map ((DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.app K))

/-! ## Stacks 0FPI at the localization functor -/

/-- **Stacks 0FPI read at the localization functor `Q`, for a morphism of ringed topoi.**  For a
complex `N` of `O_C`-modules the square whose upper edge is `Lf^*` of the comparison
`f_* ⟶ Rf_*`, whose lower edge is the counit of `Lf^* ⊣ Rf_*`, whose left edge is the comparison
`Lf^* ⟶ f^*` and whose right edge is the ordinary counit `f^*f_* ⟶ id` commutes in `D(O_C)`. -/
theorem derivedCounit_pushforwardComparisonQ
    (N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (derivedPullback f).map (pushforwardComparisonQ f N) ≫
        (derivedAdjunction f).counit.app (DerivedCategory.Q.obj N) =
      pullbackComparisonQ f ((pushforwardComplex f).obj N) ≫
        DerivedCategory.Q.map ((complexAdjunction f).counit.app N) :=
  Stacks.Cohomology.CupProductAndDerivedPushforward.counit_comp_of_counit_fac
    (derivedAdjunction f)
    ((DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).inv.app
      ((pushforwardComplex f).obj N))
    (((pushforwardOnHomotopy (X := X) (Y := Y) f).totalRightDerivedUnit DerivedCategory.Qh
        (sourceQuasiIso X)).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N))
    ((DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.app N)
    ((derivedPullbackComparison f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj ((pushforwardComplex f).obj N)))
    (DerivedCategory.Qh.map ((pullbackAdjPushforwardMapHomotopy f).counit.app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N)))
    ((DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.app
      ((pullbackComplex f).obj ((pushforwardComplex f).obj N)))
    (DerivedCategory.Q.map ((complexAdjunction f).counit.app N))
    (derivedAdjunction_counit_fac f _)
    (DerivedCategory.quotientCompQhIso_hom_naturality ((complexAdjunction f).counit.app N))

/-! ## Stacks 0FPK -/

section Square

variable
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

/-- **Stacks 0FPK, at the variable block of the cup product.**  This is
`naiveCupProduct_relativeCupProduct` with the `Prop`-valued class arguments under which the
total tensor complexes, the derived tensor products and the relative cup product are formed kept
as binders. -/
theorem naiveCupProduct_relativeCupProduct_of_instances
    (K M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (canonicalDerivedTensorProduct Y.O).toTensor ((pushforwardComplex f).obj K)
          ((pushforwardComplex f).obj M) ≫
        DerivedCategory.Q.map (naiveCupProduct f K M) ≫
        pushforwardComparisonQ f (HomologicalComplex.mapBifunctor K M
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)) =
      bifunctorMap (derivedTensorProductFunctor Y.O) (pushforwardComparisonQ f K)
            (pushforwardComparisonQ f M) ≫
        relativeCupProduct f (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj M) ≫
        (derivedPushforward f).map ((canonicalDerivedTensorProduct X.O).toTensor K M) := by
  have hcomparison := (derivedPullbackTensorIso f).hom.naturality
    ((pushforwardComparisonQ f K, pushforwardComparisonQ f M) :
      ((DerivedCategory.Q.obj ((pushforwardComplex f).obj K),
        DerivedCategory.Q.obj ((pushforwardComplex f).obj M)) : _ × _) ⟶
      ((derivedPushforward f).obj (DerivedCategory.Q.obj K),
        (derivedPushforward f).obj (DerivedCategory.Q.obj M)))
  exact Stacks.Cohomology.CupProductAndDerivedPushforward.hexagon_of_transposes
    (derivedAdjunction f)
    (derivedTensorProductFunctor Y.O) (derivedTensorProductFunctor X.O)
    (pushforwardComparisonQ f K) (pushforwardComparisonQ f M)
    ((canonicalDerivedTensorProduct Y.O).toTensor ((pushforwardComplex f).obj K)
      ((pushforwardComplex f).obj M))
    (DerivedCategory.Q.map (naiveCupProduct f K M))
    (pushforwardComparisonQ f (HomologicalComplex.mapBifunctor K M
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)))
    (relativeCupProduct f (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj M))
    ((canonicalDerivedTensorProduct X.O).toTensor K M)
    ((derivedPullbackTensorIso f).hom.app
      (DerivedCategory.Q.obj ((pushforwardComplex f).obj K),
        DerivedCategory.Q.obj ((pushforwardComplex f).obj M)))
    ((derivedPullbackTensorIso f).hom.app
      ((derivedPushforward f).obj (DerivedCategory.Q.obj K),
        (derivedPushforward f).obj (DerivedCategory.Q.obj M)))
    (pullbackComparisonQ f ((pushforwardComplex f).obj K))
    (DerivedCategory.Q.map ((complexAdjunction f).counit.app K))
    (pullbackComparisonQ f ((pushforwardComplex f).obj M))
    (DerivedCategory.Q.map ((complexAdjunction f).counit.app M))
    (pullbackComparisonQ f (HomologicalComplex.mapBifunctor ((pushforwardComplex f).obj K)
      ((pushforwardComplex f).obj M)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)))
    (pullbackComparisonQ f ((pushforwardComplex f).obj (HomologicalComplex.mapBifunctor K M
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ))))
    (DerivedCategory.Q.map ((complexAdjunction f).counit.app (HomologicalComplex.mapBifunctor K M
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ))))
    (DerivedCategory.Q.map ((pullbackComplex f).map (naiveCupProduct f K M)))
    (DerivedCategory.Q.map (pullbackTensorComplexIso f ((pushforwardComplex f).obj K)
      ((pushforwardComplex f).obj M)).hom)
    (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
      ((complexAdjunction f).counit.app K) ((complexAdjunction f).counit.app M)
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)))
    ((canonicalDerivedTensorProduct X.O).toTensor
      ((pullbackComplex f).obj ((pushforwardComplex f).obj K))
      ((pullbackComplex f).obj ((pushforwardComplex f).obj M)))
    (Equiv.symm_apply_apply _ _) hcomparison
    (derivedCounit_pushforwardComparisonQ f K)
    (derivedCounit_pushforwardComparisonQ f M)
    (derivedCounit_pushforwardComparisonQ f (HomologicalComplex.mapBifunctor K M
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)))
    (pullbackComparisonQ_naturality f (naiveCupProduct f K M))
    ((DerivedCategory.Q.map_comp _ _).symm.trans
      ((congrArg DerivedCategory.Q.map (pullbackComplex_naiveCupProduct_counit f K M)).trans
        (DerivedCategory.Q.map_comp _ _)))
    (derivedPullback_toTensor_square_of_instances f ((pushforwardComplex f).obj K)
      ((pushforwardComplex f).obj M))
    (((canonicalDerivedTensorProduct X.O).toTensor_naturality _ _).symm.trans
      (Category.assoc _ _ _).symm)

end Square

section Unconditional

attribute [local instance high]
  Stacks.Cohomology.RelativeCupProductOfToposHom.hasMapBifunctor_sheafTensor_ringedTopos

/-- **Stacks 0FPK.**  For a morphism of ringed topoi `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` — a
morphism of the underlying topoi together with the structure map, with no functor between the
underlying sites — and unbounded cochain complexes `K`, `M` of `O_C`-modules, the hexagon

```
f_*K ⊗^L_{O_D} f_*M ───────────→ Rf_*K ⊗^L_{O_D} Rf_*M
        │                                 │
        ↓                                 ↓
Tot(f_*K ⊗_{O_D} f_*M)            Rf_*(K ⊗^L_{O_C} M)
        │                                 │
        ↓                                 ↓
f_*Tot(K ⊗_{O_C} M) ───────────→ Rf_*Tot(K ⊗_{O_C} M)
```

commutes in `D(O_D)`.  Its horizontal edges and its top right edge are the comparison
`f_* ⟶ Rf_*`; the top left and bottom right edges are the canonical map from the derived tensor
product to the ordinary total tensor complex of Stacks 06YU; the middle left edge is the naive
cup product and the middle right edge is the relative cup product of Stacks 0B6C.

The statement has no hypothesis and no class argument of its own: instance search supplies
every class argument of `naiveCupProduct_relativeCupProduct_of_instances`. -/
@[stacks 0FPK "the whole tag, for an arbitrary morphism of ringed topoi in the two-field sense \
  of Tag 01D3, part (2) (a morphism of the underlying topoi with its structure map, no functor \
  between the underlying sites and no morphism-of-sites hypothesis), at RingedTopos.{u, u, u}, \
  for all unbounded complexes K, M; the statement carries no hypothesis or class argument"]
theorem naiveCupProduct_relativeCupProduct {X Y : RingedTopos.{u, u, u}} (f : RingedToposHom X Y)
    (K M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (canonicalDerivedTensorProduct Y.O).toTensor ((pushforwardComplex f).obj K)
          ((pushforwardComplex f).obj M) ≫
        DerivedCategory.Q.map (naiveCupProduct f K M) ≫
        pushforwardComparisonQ f (HomologicalComplex.mapBifunctor K M
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)) =
      bifunctorMap (derivedTensorProductFunctor Y.O) (pushforwardComparisonQ f K)
            (pushforwardComparisonQ f M) ≫
        relativeCupProduct f (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj M) ≫
        (derivedPushforward f).map ((canonicalDerivedTensorProduct X.O).toTensor K M) :=
  naiveCupProduct_relativeCupProduct_of_instances f K M

end Unconditional

end Stacks.Cohomology.CupProductAndDerivedPushforwardOfToposHom

end

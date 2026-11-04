module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExistenceOnARingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RightTExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.CanonicalDerivedTensorComparison
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport
public import StacksFrontier.Homology.KFlat.BifunctorModelComparison

/-!
# The derived tensor product of a ringed site at the standard and the locally small model

The derived tensor product of a ringed site,
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`, is a functor on `D(Mod(O))` at
whatever model of that derived category is in force. At the standard model and at the locally
small model of Tag 079Q the two functors agree up to the comparison equivalence
`Stacks.Injectives.grothendieckModelEquiv`, applied to both arguments and to the output.

## Main definitions

* `Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso` — the comparison
  `T_ls(G K, G L) ≅ G(T_std(K, L))`, natural in `K` and `L`, for `G` the comparison equivalence.
* `Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorIsoSheafOfModules` — the two
  canonical derived tensor products of a ringed site, that of
  `Stacks.DerivedTensor.RingedSite` and that of `Stacks.SheafOfModules`, agree at every model.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.DerivedTensor.RingedSite

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj M).Additive]
  [∀ (K L : CochainComplex (Modules R) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]
  [IsGrothendieckAbelian.{u} (Modules R)]

section

variable [h : HasDerivedCategory (Modules R)]

/-- The derived tensor product at a model of `D(Mod(O))` is the derived bifunctor of the total
tensor complex at that model. -/
def derivedTensorProductFunctorIsoDerivedBifunctor :
    derivedTensorProductFunctor R ≅
      CochainComplex.KFlatBifunctor.derivedBifunctor (Stacks.SheafOfModules.Tensor.sheafTensor R) :=
  eqToIso (congrArg DerivedTensorProduct.tensor (canonicalDerivedTensorProduct_eq R))

end

/-- **The derived tensor product at the two models.** For the comparison equivalence `G` between
the standard model of `D(Mod(O))` and the locally small one of Tag 079Q,
`T_ls(G K, G L) ≅ G(T_std(K, L))` naturally in `K` and `L`. -/
def derivedTensorProductFunctorModelIso :
    (Stacks.Injectives.grothendieckModelEquiv.{u} (Modules R)).functor ⋙
        @derivedTensorProductFunctor _ _ _ R _ _
          (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules R)) _ _ _ ⋙
        (Functor.whiskeringLeft _ _ _).obj
          (Stacks.Injectives.grothendieckModelEquiv.{u} (Modules R)).functor ≅
      @derivedTensorProductFunctor _ _ _ R _ _ (HasDerivedCategory.standard (Modules R)) _ _ _ ⋙
        (Functor.whiskeringRight _ _ _).obj
          (Stacks.Injectives.grothendieckModelEquiv.{u} (Modules R)).functor :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      (derivedTensorProductFunctorIsoDerivedBifunctor R
      (h := Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} (Modules R))) _) ≪≫
    CochainComplex.KFlatBifunctor.derivedBifunctorModelIso
      (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (HasDerivedCategory.standard _)
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
      (HasDerivedCategory.standard _)
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
      (HasDerivedCategory.standard _)
      (Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{u} _)
      (exists_kFlatLeft_quasiIso R) (exists_kFlat_quasiIso R)
      _ _ _
      (StacksDraft.DerivedModel.shrinkComparisonQhIso (Modules R)).symm
      (StacksDraft.DerivedModel.shrinkComparisonQhIso (Modules R)).symm
      (StacksDraft.DerivedModel.shrinkComparisonQhIso (Modules R)).symm ≪≫
    Functor.isoWhiskerRight (derivedTensorProductFunctorIsoDerivedBifunctor R
      (h := HasDerivedCategory.standard _)).symm _

end Stacks.DerivedTensor.RingedSite

namespace Stacks.DerivedTensor.RingedSite

variable (X : AlgebraicGeometry.RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory (Modules X.O)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **The two canonical derived tensor products of a ringed site agree.** The derived tensor
product `Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor` of the structure sheaf and
`Stacks.SheafOfModules.derivedTensorProductFunctor` of the site are both descents of the total
tensor product of K-flat complexes
(`Stacks.SheafOfModules.DerivedMonoidal.derivedBifunctorTensorIso`). -/
def derivedTensorProductFunctorIsoSheafOfModules :
    derivedTensorProductFunctor X.O ≅ Stacks.SheafOfModules.derivedTensorProductFunctor X :=
  (Stacks.SheafOfModules.DerivedMonoidal.canonicalTensorIso X.O).symm ≪≫
    Stacks.SheafOfModules.DerivedMonoidal.derivedBifunctorTensorIso X.O
      (Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct X))

end Stacks.DerivedTensor.RingedSite

end

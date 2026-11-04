module
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.MonoidalClosed
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.CategoryTheory.Adjunction.ProjectionFormulaMap
public import StacksFrontier.Homology.KFlat.BifunctorLocalization

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.DerivedAdjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnbounded
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModuleTensor.InverseImageKFlat
public import StacksFrontier.AlgebraicGeometry.Perfect.Coherator.DerivedAdjunctionOfExactLeftAdjoint
public import StacksFrontier.Homology.KFlat.BifunctorTransportSquare
public import StacksFrontier.Homology.KFlat.ProjectionFormulaRepresentatives

/-!
# The projection formula map for étale sheaves of `Λ`-modules

Let `Λ` be a commutative ring and `f : X ⟶ Y` a morphism of schemes. For `E ∈ D(X_étale, Λ)` and
`K ∈ D(Y_étale, Λ)` there is a canonical map

`Rf_*E ⊗^L_Λ K ⟶ Rf_*(E ⊗^L_Λ f⁻¹K)`

of Cohomology on Sites, Section 21.50 ([Stacks, Tag 0943]): the map adjoint, for the adjunction
`f⁻¹ ⊣ Rf_*`, to `f⁻¹(Rf_*E ⊗^L_Λ K) ≅ f⁻¹Rf_*E ⊗^L_Λ f⁻¹K ⟶ E ⊗^L_Λ f⁻¹K`, whose first arrow is
the compatibility of the inverse image with the derived tensor product ([Stacks, Tag 07A4]) and
whose second is the counit in the first factor.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleDerivedAdjunction`: **`f⁻¹ ⊣ Rf_*`** on the unbounded
  derived categories `D(-_étale, Λ)`, for the unbounded derived direct image
  `Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnbounded`.
* `Stacks.EtaleCohomology.etaleModuleDerivedInverseImageTensorIso`: **`f⁻¹(K ⊗^L_Λ L) ≅
  f⁻¹K ⊗^L_Λ f⁻¹L`**, naturally in both variables.
* `Stacks.EtaleCohomology.etaleModuleProjectionFormulaMap`: **the projection formula map**.

## Implementation notes

The unbounded derived direct image of sheaves of `Λ`-modules is a right derived functor along the
localization of cochain complexes. It is read along the localization of the homotopy category by
`Stacks.DerivedAdjunction.homotopyUnitOfComplex`, and the adjunction is then
`Stacks.DerivedFunctor.derivedAdjunction`, exactly as for abelian étale sheaves
(`Stacks.EtaleCohomology.etaleAbelianDerivedAdjunction`): the inverse image is exact, and
K-injective resolutions make the right derived functor absolute. The compatibility with the
derived tensor product is `CochainComplex.KFlatBifunctor.derivedTransportProdIso` applied to the
monoidality of `f⁻¹` (`Stacks.EtaleCohomology.etaleModuleInverseImageTensorIso`), and the map is
the abstract `CategoryTheory.adjunctionTensorMap`. Nothing about `f` is assumed.

## References

* [Stacks Project, Tag 0943](https://stacks.math.columbia.edu/tag/0943)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModuleMonoidalCategory isMonoidal_W_smallEtale_module
  HasDerivedCategory.standard etaleModuleInverseImageMonoidal

variable (Λ : Type r) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Inverse image of étale sheaves of `Λ`-modules preserves colimits indexed by categories in
`Type`, being a left adjoint; the total complexes of the transported tensor product need it. -/
instance etaleModuleInverseImage_preservesColimitsOfSize_zero :
    PreservesColimitsOfSize.{0, 0} (etaleModuleInverseImage.{u, r} Λ f) :=
  (etaleModuleInverseImageAdj.{u, r} Λ f).leftAdjoint_preservesColimits

/-- **The derived inverse image of étale sheaves of `Λ`-modules is left adjoint to the unbounded
derived direct image** (Stacks 09T5): `f⁻¹ ⊣ Rf_*` on `D(-_étale, Λ)`. -/
noncomputable def etaleModuleDerivedAdjunction :
    (etaleModuleInverseImage.{u, r} Λ f).mapDerivedCategory ⊣
      etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f :=
  haveI := Stacks.DerivedAdjunction.homotopyUnitOfComplex_isRightDerivedFunctor
    (etaleModuleDirectImage.{u, r} Λ f) (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f)
    (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f)
  Stacks.DerivedFunctor.derivedAdjunction (etaleModuleInverseImageAdj.{u, r} Λ f)
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f)
    (Stacks.DerivedAdjunction.homotopyUnitOfComplex (etaleModuleDirectImage.{u, r} Λ f)
      (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f)
      (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f))
    Stacks.DerivedFunctor.exists_quasiIso_isKInjective

/-- **The inverse image commutes with the derived tensor product**: `f⁻¹(K ⊗^L_Λ L) ≅
f⁻¹K ⊗^L_Λ f⁻¹L` on the unbounded derived categories of étale sheaves of `Λ`-modules, naturally in
the pair `(K, L)` ([Stacks, Tag 07A4]). -/
noncomputable abbrev etaleModuleDerivedInverseImageTensorIso :
    Functor.uncurry.obj (etaleModuleDerivedTensor.{u, r} Λ Y) ⋙
        (etaleModuleInverseImage.{u, r} Λ f).mapDerivedCategory ≅
      (etaleModuleInverseImage.{u, r} Λ f).mapDerivedCategory.prod
          (etaleModuleInverseImage.{u, r} Λ f).mapDerivedCategory ⋙
        Functor.uncurry.obj (etaleModuleDerivedTensor.{u, r} Λ X) :=
  CochainComplex.KFlatBifunctor.derivedTransportProdIso (etaleModuleTensor.{u, r} Λ Y)
    (etaleModuleTensor.{u, r} Λ X) (etaleModuleInverseImage.{u, r} Λ f)
    (fun a b ↦ etaleModuleInverseImageTensorIso.{u, r} Λ f a b)
    (fun φ N ↦ etaleModuleInverseImageTensorIso_hom_natural_left.{u, r} Λ f φ N)
    (fun M _ _ ψ ↦ etaleModuleInverseImageTensorIso_hom_natural_right.{u, r} Λ f M ψ)
    (fun K hK ↦ kFlatLeft_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ f K hK)
    (fun L hL ↦ kFlat_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ f L hL)

/-- **The projection formula map** `Rf_*E ⊗^L_Λ K ⟶ Rf_*(E ⊗^L_Λ f⁻¹K)` for étale sheaves of
`Λ`-modules ([Stacks, Tag 0943]): the adjoint transpose, for `f⁻¹ ⊣ Rf_*`, of the compatibility
`f⁻¹(Rf_*E ⊗^L_Λ K) ≅ f⁻¹Rf_*E ⊗^L_Λ f⁻¹K` followed by the counit `f⁻¹Rf_*E ⟶ E` in the first
factor.

The comparison is written out as the transport `derivedTransportProdIso` rather than through its
abbreviation `etaleModuleDerivedInverseImageTensorIso`, and the tensor products as
`derivedBifunctor`, so that the map is literally the one the generic base change hexagon
`Stacks.AffineProjectionFormula.adjunctionTensorMap_baseChange_square` produces, and its type,
`(Rf_*E ⊗^L_Λ K) ⟶ Rf_*(E ⊗^L_Λ f⁻¹K)` for the uncurried tensor products, is left to be inferred
from `CategoryTheory.adjunctionTensorMap`: the kernel does not identify another spelling of it in
its budget. -/
noncomputable def etaleModuleProjectionFormulaMap
    (E : DerivedCategory (EtaleModules.{u, r} Λ X))
    (K : DerivedCategory (EtaleModules.{u, r} Λ Y)) :=
  adjunctionTensorMap (etaleModuleDerivedAdjunction.{u, r} Λ f)
    (Functor.uncurry.obj (CochainComplex.KFlatBifunctor.derivedBifunctor
      (etaleModuleTensor.{u, r} Λ Y)))
    (Functor.uncurry.obj (CochainComplex.KFlatBifunctor.derivedBifunctor
      (etaleModuleTensor.{u, r} Λ X)))
    (CochainComplex.KFlatBifunctor.derivedTransportProdIso (etaleModuleTensor.{u, r} Λ Y)
      (etaleModuleTensor.{u, r} Λ X) (etaleModuleInverseImage.{u, r} Λ f)
      (fun a b ↦ etaleModuleInverseImageTensorIso.{u, r} Λ f a b)
      (fun φ N ↦ etaleModuleInverseImageTensorIso_hom_natural_left.{u, r} Λ f φ N)
      (fun M _ _ ψ ↦ etaleModuleInverseImageTensorIso_hom_natural_right.{u, r} Λ f M ψ)
      (fun K hK ↦ kFlatLeft_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ f K hK)
      (fun L hL ↦ kFlat_etaleModuleInverseImage_mapHomologicalComplex.{u, r} Λ f L hL)).hom E K

end Stacks.EtaleCohomology

end

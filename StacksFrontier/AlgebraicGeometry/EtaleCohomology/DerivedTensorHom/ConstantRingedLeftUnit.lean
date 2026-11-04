module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.ConstantRingedUnit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapCohomologyExt
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.LeftUnitorNaturality

/-!
# Tensoring with `f⁻¹Λ` is the identity of `D(X_étale, Λ)`

Let `f : X ⟶ S` be a morphism of schemes and `Λ` a commutative ring. On `D(X_étale, Λ)` the
derived tensor product `- ⊗^L_Λ -` (`Stacks.EtaleCohomology.etaleDerivedTensor`) is that of the
constant ringed site `etaleRingedSite Λ X`, read through `etaleDerivedEquivalence`. This file
shows:

* `Λ_X[0]` corresponds to the unit object `𝒪[0]` of the ringed site
  (`Stacks.EtaleCohomology.etaleDerivedEquivalenceSingleConstantIso`), from the abelian statement
  `Stacks.EtaleCohomology.etaleModulesEquivalenceConstantIso`;
* `f⁻¹(Λ_S[0]) ≅ Λ_X[0]` (`Stacks.EtaleCohomology.etaleDerivedInverseImageSingleConstantIso`);
* for every `E` corresponding to `𝒪[0]`, the functor `E ⊗^L_Λ -` is isomorphic to the identity
  (`Stacks.EtaleCohomology.etaleDerivedTensorLeftUnitIso`), by the natural left unit constraint
  `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitNatIso` of the ringed site.

The derived categories are those of the standard model `HasDerivedCategory.standard`, in which
the étale derived tensor product is defined.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type r) [CommRing Λ]

/-- **`Λ_X[0]` read on the constant ringed site is the unit object `𝒪[0]`.** -/
def etaleDerivedEquivalenceSingleConstantIso (X : Scheme.{u}) :
    (etaleDerivedEquivalence.{u, r} Λ X).functor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Stacks.Cohomology.GlobalSections.constantModuleSheaf.{r} Λ X.smallEtaleTopology)) ≅
      Stacks.DerivedTensor.RingedSite.unitObject (etaleRingedSite.{u, r} Λ X) :=
  ((etaleModulesEquivalence.{u, r} Λ X).functor.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (etaleModulesEquivalenceConstantIso.{u, r} Λ X)

/-- **`f⁻¹(Λ_S[0]) ≅ Λ_X[0]`** for the derived inverse image. -/
def etaleDerivedInverseImageSingleConstantIso {X S : Scheme.{u}} (f : X ⟶ S) :
    (etaleModuleDerivedInverseImage.{u, r} Λ f).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Stacks.Cohomology.GlobalSections.constantModuleSheaf.{r} Λ S.smallEtaleTopology)) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf.{r} Λ X.smallEtaleTopology) :=
  ((etaleModuleInverseImage.{u, r} Λ f).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      ((etaleModuleInverseImageConstantIso.{u, r} Λ f).app
        (ModuleCat.of Λ (ULift.{u + 1} Λ)))

/-- **`f⁻¹(Λ_S[0])` read on the constant ringed site of `X` is the unit object `𝒪[0]`.** -/
def etaleDerivedEquivalenceInverseImageSingleConstantIso {X S : Scheme.{u}} (f : X ⟶ S) :
    (etaleDerivedEquivalence.{u, r} Λ X).functor.obj
        ((etaleModuleDerivedInverseImage.{u, r} Λ f).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (Stacks.Cohomology.GlobalSections.constantModuleSheaf.{r} Λ S.smallEtaleTopology))) ≅
      Stacks.DerivedTensor.RingedSite.unitObject (etaleRingedSite.{u, r} Λ X) :=
  (etaleDerivedEquivalence.{u, r} Λ X).functor.mapIso
      (etaleDerivedInverseImageSingleConstantIso.{u, r} Λ f) ≪≫
    etaleDerivedEquivalenceSingleConstantIso.{u, r} Λ X

/-- **Tensoring with an object corresponding to `𝒪[0]` is the identity of `D(X_étale, Λ)`**:
`E ⊗^L_Λ Z ≅ Z`, naturally in `Z`, from the natural left unit constraint of the ringed site. -/
def etaleDerivedTensorLeftUnitIso (X : Scheme.{u})
    {E : DerivedCategory (EtaleModules.{u, r} Λ X)}
    (i : (etaleDerivedEquivalence.{u, r} Λ X).functor.obj E ≅
      Stacks.DerivedTensor.RingedSite.unitObject (etaleRingedSite.{u, r} Λ X)) :
    (etaleDerivedTensor.{u, r} Λ X).obj E ≅ 𝟭 _ :=
  Functor.isoWhiskerLeft (etaleDerivedEquivalence.{u, r} Λ X).functor
      (Functor.isoWhiskerRight
        ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
            (etaleRingedSite.{u, r} Λ X).O).mapIso i ≪≫
          Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitNatIso
            (etaleRingedSite.{u, r} Λ X)
            (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
              (etaleRingedSite.{u, r} Λ X).O))
        (etaleDerivedEquivalence.{u, r} Λ X).inverse) ≪≫
    (etaleDerivedEquivalence.{u, r} Λ X).unitIso.symm

end Stacks.EtaleCohomology

end

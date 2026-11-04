module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.ConstantRingedLeftUnit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.ProjectionFormula
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormulaOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BraidingNatIso

/-!
# Tensoring with a shift of `Λ` on `D(X_étale, Λ)`

Let `X` be a scheme and `Λ` a commutative ring. This file records three facts about the derived
tensor product `- ⊗^L_Λ -` of `D(X_étale, Λ)` (`Stacks.EtaleCohomology.etaleDerivedTensor`):

* tensoring on the right by an object `H` corresponding to a shift `𝒪[0]⟦m⟧` of the unit object
  of the constant ringed site is an equivalence
  (`Stacks.EtaleCohomology.isEquivalence_etaleTensorRightOf`); this applies to `Λ_X[0]⟦m⟧`
  (`Stacks.EtaleCohomology.etaleDerivedEquivalenceShiftSingleConstantIso`) and to
  `f⁻¹(Λ_S[0]⟦m⟧)` (`Stacks.EtaleCohomology.etaleDerivedEquivalenceInverseImageShiftIso`);
* the symmetry `Stacks.EtaleCohomology.etaleDerivedTensorBraidingIso` is natural
  (`Stacks.EtaleCohomology.etaleDerivedTensorBraidingIso_naturality`).

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

section TensorRight

variable (X : Scheme.{u})

/-- Tensoring on the right by `H` on `D(X_étale, Λ)` is tensoring on the right by the
corresponding object on the constant ringed site, conjugated by the equivalence. -/
def etaleTensorRightOfIso (H : DerivedCategory (EtaleModules.{u, r} Λ X)) :
    Stacks.ProjectionFormula.tensorRightOf
        (Functor.uncurry.obj (etaleDerivedTensor.{u, r} Λ X)) H ≅
      (etaleDerivedEquivalence.{u, r} Λ X).functor ⋙
        Stacks.ProjectionFormula.tensorRightOf
          (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
            (etaleRingedSite.{u, r} Λ X).O))
          ((etaleDerivedEquivalence.{u, r} Λ X).functor.obj H) ⋙
        (etaleDerivedEquivalence.{u, r} Λ X).inverse :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun g => by
    simp [Stacks.ProjectionFormula.tensorRightOf_map])

/-- **Tensoring on the right by an object corresponding to `𝒪[0]⟦m⟧` is an equivalence** of
`D(X_étale, Λ)`: on the constant ringed site it is the shift by `m`. -/
theorem isEquivalence_etaleTensorRightOf (H : DerivedCategory (EtaleModules.{u, r} Λ X)) (m : ℤ)
    (i : (etaleDerivedEquivalence.{u, r} Λ X).functor.obj H ≅
      (Stacks.DerivedTensor.RingedSite.unitObject (etaleRingedSite.{u, r} Λ X))⟦m⟧) :
    (Stacks.ProjectionFormula.tensorRightOf
      (Functor.uncurry.obj (etaleDerivedTensor.{u, r} Λ X)) H).IsEquivalence := by
  have : (Stacks.ProjectionFormula.tensorRightOf
      (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        (etaleRingedSite.{u, r} Λ X).O))
      ((etaleDerivedEquivalence.{u, r} Λ X).functor.obj H)).IsEquivalence :=
    Functor.isEquivalence_tensorRightOf_of_iso _ i
      (Functor.isEquivalence_tensorRightOf_shiftedUnit _ _
        (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitorNatIso
          (etaleRingedSite.{u, r} Λ X)
          (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
            (etaleRingedSite.{u, r} Λ X).O)) m)
  exact Functor.isEquivalence_of_iso (etaleTensorRightOfIso.{u, r} Λ X H).symm

/-- `Λ_X[0]⟦m⟧` read on the constant ringed site is `𝒪[0]⟦m⟧`. -/
def etaleDerivedEquivalenceShiftSingleConstantIso (m : ℤ) :
    (etaleDerivedEquivalence.{u, r} Λ X).functor.obj
        (((DerivedCategory.singleFunctor _ 0).obj
          (Stacks.Cohomology.GlobalSections.constantModuleSheaf.{r} Λ X.smallEtaleTopology))⟦m⟧) ≅
      (Stacks.DerivedTensor.RingedSite.unitObject (etaleRingedSite.{u, r} Λ X))⟦m⟧ :=
  ((etaleModulesEquivalence.{u, r} Λ X).functor.mapDerivedCategory.commShiftIso m).app _ ≪≫
    (shiftFunctor _ m).mapIso (etaleDerivedEquivalenceSingleConstantIso.{u, r} Λ X)

/-- `f⁻¹(Λ_S[0]⟦m⟧)` read on the constant ringed site of `X` is `𝒪[0]⟦m⟧`. -/
def etaleDerivedEquivalenceInverseImageShiftIso {S : Scheme.{u}} (f : X ⟶ S) (m : ℤ) :
    (etaleDerivedEquivalence.{u, r} Λ X).functor.obj
        ((etaleModuleDerivedInverseImage.{u, r} Λ f).obj
          (((DerivedCategory.singleFunctor _ 0).obj
            (Stacks.Cohomology.GlobalSections.constantModuleSheaf.{r} Λ
              S.smallEtaleTopology))⟦m⟧)) ≅
      (Stacks.DerivedTensor.RingedSite.unitObject (etaleRingedSite.{u, r} Λ X))⟦m⟧ :=
  (etaleDerivedEquivalence.{u, r} Λ X).functor.mapIso
      (((etaleModuleDerivedInverseImage.{u, r} Λ f).commShiftIso m).app _) ≪≫
    ((etaleModulesEquivalence.{u, r} Λ X).functor.mapDerivedCategory.commShiftIso m).app _ ≪≫
    (shiftFunctor _ m).mapIso (etaleDerivedEquivalenceInverseImageSingleConstantIso.{u, r} Λ f)

end TensorRight

section Braiding

variable (X : Scheme.{u})

/-- **The symmetry of `- ⊗^L_Λ -` on `D(X_étale, Λ)` is natural** in the second object, in the
form consumed by `Stacks.CupDuality.bijective_comp_map_iff`. -/
theorem etaleDerivedTensorBraidingIso_naturality (A : DerivedCategory (EtaleModules.{u, r} Λ X))
    {B B' : DerivedCategory (EtaleModules.{u, r} Λ X)} (g : B ⟶ B') :
    ((etaleDerivedTensor.{u, r} Λ X).obj A).map g ≫
        (etaleDerivedTensorBraidingIso.{u, r} Λ X A B').hom =
      (etaleDerivedTensorBraidingIso.{u, r} Λ X A B).hom ≫
        ((etaleDerivedTensor.{u, r} Λ X).map g).app A := by
  open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi in
  simp only [etaleDerivedTensorBraidingIso, Functor.mapIso_hom, Iso.app_hom,
    TensorHomAdjunction.transportTensor_map_app, TensorHomAdjunction.transportTensor_obj_map,
    ← Functor.map_comp]
  congr 1
  exact ((Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingNatIso
    (etaleRingedSite.{u, r} Λ X)
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
      (etaleRingedSite.{u, r} Λ X).O)).hom.app _).naturality _

end Braiding

end Stacks.EtaleCohomology

end

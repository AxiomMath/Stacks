module

public import StacksFrontier.Homology.Tor.BaseChangeTensorIso
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.RingHom.Flat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes
public import StacksFrontier.CategoryTheory.Localization.LeftDerivedByResolutions
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.KFlat.ScalarBaseChange
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.Homology.Tor.DerivedTensor

/-!
# Further results on `BaseChangeTensorIso`

Results about the objects of `StacksFrontier.Homology.Tor.BaseChangeTensorIso` that need
imports beyond those of that module.
-/

@[expose] public noncomputable section


open CategoryTheory CategoryTheory.Limits
open CategoryTheory.LeftDerivedByResolutions

namespace CochainComplex.DerivedTensor

attribute [local instance] HasDerivedCategory.standard

section Construction

universe uR uA v

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A]


universe v₁ v₂ u₁ u₂
end Construction

section Consequences

universe u uR uA v wR wA

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A]

/-- Flat extension of scalars commutes with homology, naturally in the derived object.
This is obtained from the comparison of `totalDerivedExtensionScalars`: flatness makes
termwise extension exact, so its total left derived comparison is an isomorphism. In
particular, this construction does not use the tagged tensor comparison of Equation 068I. -/
public noncomputable def derivedExtensionScalarsHomologyIsoAtModel
    (f : R →+* A) (hf : f.Flat) (i : ℤ)
    [HasDerivedCategory.{wR} (ModuleCat.{max uR uA v} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max uR uA v} A)] :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{uR, uA, v} f).functor ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{max uR uA v} A) i ≅
      DerivedCategory.homologyFunctor (ModuleCat.{max uR uA v} R) i ⋙
        ModuleCat.extendScalars f := by
  let F := extensionScalars.{uR, uA, v} f
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{uR, uA, v} f
  have : F.PreservesHomology := extensionScalars_preservesHomology f hf
  have : PreservesFiniteLimits F := F.preservesFiniteLimits_of_preservesHomology
  have : IsIso D.comparison := Functor.isIso_of_isLeftDerivedFunctor_of_inverts
    D.functor D.comparison (W := HomologicalComplex.quasiIso
      (ModuleCat.{max uR uA v} R) (ComplexShape.up ℤ)) (by
      intro X Y g hg
      have : QuasiIso g := hg
      change IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex _).map g))
      infer_instance)
  let e : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{max uR uA v} A) (ComplexShape.up ℤ) i ≅
      HomologicalComplex.homologyFunctor (ModuleCat.{max uR uA v} R) (ComplexShape.up ℤ) i ⋙ F :=
    NatIso.ofComponents (fun K ↦ (K.sc i).mapHomologyIso F) (fun φ ↦
      ShortComplex.mapHomologyIso_hom_naturality
        ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℤ) i).map φ) F)
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{max uR uA v} R) (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ (D.functor ⋙ DerivedCategory.homologyFunctor _ i))
    (DerivedCategory.Q ⋙ (DerivedCategory.homologyFunctor _ i ⋙ F)) _ _
    (Functor.isoWhiskerRight (asIso D.comparison) (DerivedCategory.homologyFunctor _ i) ≪≫
      Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
        (DerivedCategory.homologyFunctorFactors _ i) ≪≫ e ≪≫
      Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors _ i).symm F)

/-- For any localization of a commutative ring, homology after total derived extension of
scalars is the localization of homology, naturally in the derived object. Restriction of
scalars expresses both sides as modules over the original ring. -/
public noncomputable def derivedExtensionScalarsLocalizationHomologyIsoAtModel
    (S : Submonoid R) [Algebra R A] [IsLocalization S A] (i : ℤ)
    [HasDerivedCategory.{wR} (ModuleCat.{max uR uA v} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max uR uA v} A)] :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{uR, uA, v}
        (algebraMap R A)).functor ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{max uR uA v} A) i ⋙
        ModuleCat.restrictScalars (algebraMap R A) ≅
      DerivedCategory.homologyFunctor (ModuleCat.{max uR uA v} R) i ⋙
        localizedModuleFunctor.{uR, max uA v} S :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (derivedExtensionScalarsHomologyIsoAtModel.{uR, uA, v} (algebraMap R A)
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat A S)) i) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (extensionScalarsLocalizedModuleNatIso.{uR, uA, v} (A := A) S)

end Consequences

end CochainComplex.DerivedTensor

end

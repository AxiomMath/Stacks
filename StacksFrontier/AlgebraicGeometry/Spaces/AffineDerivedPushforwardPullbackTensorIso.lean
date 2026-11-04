module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDerivedPushforwardPullbackTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.CompactGeneration.AffineGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedFunctorAmplitudeUnbounded
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedPushforwardDirectSums
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.SheafTensorColimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.CartesianObjectsTriangulatedSubcategory
public import StacksFrontier.Homology.Devissage.CompactGeneratedNatTransAllShifts

public import StacksFrontier.Homology.Devissage.CompactGeneratedNatTransLocallySmall
/-!
# `Rf_*Lf^*E = E ⊗^L f_*𝒪_X` for an affine morphism to an affine algebraic space

Let `f : X ⟶ Y` be an affine morphism of algebraic spaces with `Y` affine. For `E` in
`D_QCoh(𝒪_Y)` the canonical map `E ⊗^L Rf_*𝒪_X ⟶ Rf_*Lf^*E` is an isomorphism. Both sides are
exact functors of `E` commuting with direct sums, `𝒪_Y[0]` is a compact generator of
`D_QCoh(𝒪_Y)`, and the map is invertible at every shift of `𝒪_Y[0]`.

## Main results

* `AlgebraicGeometry.Space.isIso_derivedPushforwardStructureTensorMap_of_isAffineSpace`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward (derivedPushforward)

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] isGrothendieckAbelian_modules_ringUniverse
  Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- `𝒪_Y[0]⟦n⟧` is the structure sheaf placed in degree `-n`. -/
def structureDerivedShiftIso (Y : AlgebraicSpaces B S hS) (n : ℤ) :
    (structureDerived Y)⟦n⟧ ≅ DerivedCategory.Q.obj
      (Stacks.SheafOfModules.singleUnitComplex (smallEtaleRingedTopos B S hS Y).O (-n)) :=
  ((DerivedCategory.singleFunctors _).shiftIso n (-n) 0 (by omega)).app _ ≪≫
    (DerivedCategory.singleFunctorIsoCompQ _ (-n)).app _

/-- An affine morphism of algebraic spaces is quasi-compact. -/
theorem isQuasiCompact_of_isAffineHom_hom (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom) :
    IsQuasiCompact B S hS f.hom :=
  isQuasiCompact_of_isAffineHom' B S hS f.hom X.2 Y.2 hf

/-- An affine morphism of algebraic spaces is quasi-separated. -/
theorem isQuasiSeparated_of_isAffineHom_hom (f : X ⟶ Y) (hf : IsAffineHom B S hS f.hom) :
    IsQuasiSeparated B S hS f.hom :=
  isQuasiSeparated_of_isSeparated B S hS (isSeparated_of_isAffineHom B S hS f.hom X.2 Y.2 hf)

/-- **Stacks 08IJ over an affine target.** For an affine morphism `f : X ⟶ Y` of algebraic
spaces with `Y` affine and `E` in `D_QCoh(𝒪_Y)`, the canonical map
`E ⊗^L Rf_*𝒪_X ⟶ Rf_*Lf^*E` is an isomorphism. -/
theorem isIso_derivedPushforwardStructureTensorMap_of_isAffineSpace (f : X ⟶ Y)
    (hf : IsAffineHom B S hS f.hom) (hY : IsAffineSpace B S hS Y.1)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hE : QcohDerived B S hS Y E) :
    IsIso (derivedPushforwardStructureTensorMap f E) := by
  let P := QcohDerived B S hS Y
  let DY := DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
  let DX := DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
  let ι : P.FullSubcategory ⥤ DY := P.ι
  let : ι.CommShift ℤ := (inferInstance : P.ι.CommShift ℤ)
  let : ι.IsTriangulated := (inferInstance : P.ι.IsTriangulated)
  let L : DY ⥤ DX := smallEtaleDerivedModulePullback B S hS f
  let R : DX ⥤ DY := derivedModulePushforward B S hS f
  let : R.CommShift ℤ := derivedModulePushforward_commShift B S hS f
  let : R.IsTriangulated := derivedModulePushforward_isTriangulated B S hS f
  have hfqc := isQuasiCompact_of_isAffineHom_hom f hf
  have hfqs := isQuasiSeparated_of_isAffineHom_hom f hf
  have hcl : ∀ I : Type u, P.IsClosedUnderColimitsOfShape (Discrete I) :=
    isClosedUnderColimitsOfShape_qcohDerived B S hS Y
  have : HasCoproducts.{u} P.FullSubcategory := fun I => by
    have := hcl I
    infer_instance
  have : LocallySmall.{u} P.FullSubcategory := inferInstance
  let TY := smallEtaleDerivedTensorProduct B S hS Y
  let M : DY := R.obj (structureDerived X)
  let T₁ : DY ⥤ DY := TY.tensor.flip.obj M
  let : T₁.CommShift ℤ := TY.commShift_left M
  let : T₁.IsTriangulated := TY.exact_left M
  let τ : ι ⋙ T₁ ⟶ ι ⋙ L ⋙ R :=
    Functor.whiskerLeft P.ι (derivedPushforwardStructureTensorNatTrans f)
  have : ∀ I : Type u, PreservesColimitsOfShape (Discrete I) (ι ⋙ T₁) :=
    fun I => by
      have := hcl I
      have : PreservesColimitsOfShape (Discrete I) T₁ :=
        Stacks.SheafOfModules.DerivedTensorProduct.preservesColimitsOfShape_tensor_flip_obj TY M I
      have : PreservesColimitsOfShape (Discrete I) ι :=
        (inferInstance : PreservesColimitsOfShape (Discrete I) P.ι)
      infer_instance
  have : ∀ I : Type u, PreservesColimitsOfShape (Discrete I) (ι ⋙ L ⋙ R) := fun I => by
    have := hcl I
    have := isClosedUnderColimitsOfShape_qcohDerived B S hS X I
    have := preservesCoproducts_quasicoherentDerivedPushforward B S hS f hfqc hfqs I
    have : PreservesColimitsOfSize.{u, u} (quasicoherentDerivedModulePullback (B := B) (S := S)
        (hS := hS) f) :=
      (quasicoherentDerivedModuleAdjunction B S hS f hfqc hfqs).leftAdjoint_preservesColimits
    let e : quasicoherentDerivedModulePullback f ⋙
        quasicoherentDerivedPushforward B S hS f hfqc hfqs ⋙ P.ι ≅ ι ⋙ L ⋙ R :=
      Functor.isoWhiskerLeft _ (quasicoherentDerivedPushforwardCompιIso B S hS f hfqc hfqs) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (quasicoherentDerivedModulePullbackCompιIso f) R ≪≫
        Functor.associator _ _ _
    have h1 : PreservesColimitsOfShape (Discrete I) (quasicoherentDerivedModulePullback (B := B)
        (S := S) (hS := hS) f) := inferInstance
    have h3 : PreservesColimitsOfShape (Discrete I)
        (quasicoherentDerivedPushforward B S hS f hfqc hfqs ⋙ P.ι) := inferInstance
    have h4 : PreservesColimitsOfShape (Discrete I) (quasicoherentDerivedModulePullback f ⋙
        quasicoherentDerivedPushforward B S hS f hfqc hfqs ⋙ P.ι) := inferInstance
    exact @preservesColimitsOfShape_of_natIso _ _ _ _ (Discrete I) _ _ _ e h4
  obtain ⟨hc, hg⟩ :=
    isCompactObject_and_isWeakTriangulatedGenerator_unitQuasicoherent (X := Y.1) (hX := Y.2) hY
  exact
    StacksDraft.CompactDevissage.isIso_app_of_isCompactlyGenerated_of_forall_shift_of_locallySmall
      τ (fun _ : PUnit.{u + 1} => unitQuasicoherent Y.2) (fun _ => hc)
      (fun Z hZ => hg Z (by
        have : ObjectProperty.ofObj (fun _ : PUnit.{u + 1} => unitQuasicoherent Y.2) =
            ObjectProperty.singleton (unitQuasicoherent Y.2) := by
          ext Z
          rw [ObjectProperty.ofObj_iff, ObjectProperty.singleton_iff]
          exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨PUnit.unit, h⟩⟩
        rwa [← this]))
      (fun _ n => by
        change IsIso (derivedPushforwardStructureTensorMap f (P.ι.obj ((unitQuasicoherent Y.2)⟦n⟧)))
        exact isIso_derivedPushforwardStructureTensorMap_of_iso f (-n)
          ((P.ι.commShiftIso n).app _ ≪≫ structureDerivedShiftIso Y n))
      ⟨E, hE⟩

end AlgebraicGeometry.Space

end

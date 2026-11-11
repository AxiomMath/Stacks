module

public import StacksFrontier.AlgebraicGeometry.Duality.InternalHom.LocallySmall
public import StacksFrontier.AlgebraicGeometry.Duality.SheafyTraceProperIso
import StacksCore.Tactic.StacksAttribute

/-!
# When the sheafy trace of a morphism of qcqs schemes is an isomorphism

Let `f : X ⟶ Y` be a morphism of quasi-compact quasi-separated schemes, `a` the right adjoint of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` ([Stacks, Tag 0A9E]), `DQ_X`, `DQ_Y` the coherators
([Stacks, Tag 0CR0]), `L ∈ D_QCoh(𝒪_X)` and `K ∈ D_QCoh(𝒪_Y)`. [Stacks, Tag 0GEV]:

* `DQ_Y(Rf_*R𝓗om(L, a(K))) = Rf_*DQ_X(R𝓗om(L, a(K)))` ([Stacks, Tag 0CR1]);
* the sheafy trace `Rf_*R𝓗om(L, a(K)) ⟶ R𝓗om(Rf_*L, K)` of [Stacks, Tag 0B6H] is an
  isomorphism if (1) `L` and `Rf_*L` are perfect, or (2) `K` is bounded below and `L` and
  `Rf_*L` are pseudo-coherent.

The proof is the source's: [Stacks, Tag 0A9Q] (`isIso_coherator_map_sheafyTrace_of_qcqs`) makes
the trace an isomorphism after `DQ_Y`, both sides lie in `D_QCoh` by [Stacks, Tag 0A6H]
(`InternalHom.derivedCategoryB_derivedSheafHom_of_isPerfect` for (1),
`derivedCategoryB_derivedSheafHom_of_isPseudoCoherent` and [Stacks, Tag 0A9I] for (2)), and the
criterion `isIso_sheafyTrace_of_derivedCategoryB` erases `DQ_Y`. Everything is at the standard
model, where the trace is defined.

## Main results

* `Stacks.Duality.coheratorDerivedPushforwardIsoStd` — [Stacks, Tag 0CR1] at the standard model.
* `Stacks.Duality.sheafyTrace_quasiCoherent_criteria` — **[Stacks, Tag 0GEV]**.

## References

* [Stacks Project, Tag 0GEV](https://stacks.math.columbia.edu/tag/0GEV)
* [Stacks Project, Tag 0CR1](https://stacks.math.columbia.edu/tag/0CR1)
* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
* [Stacks Project, Tag 0A9Q](https://stacks.math.columbia.edu/tag/0A9Q)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces renaming derivedPullback → derivedPullbackRS,
  derivedAdjunction → derivedAdjunctionRS

namespace Stacks.Duality

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.AssociatedSheaf.hasModuleSheafify
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y]

/-- `Lf^* : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)` at the standard model ([Stacks, Tag 08DW]). -/
def quasiCoherentDerivedPullbackStd :
    quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ derivedPullbackRS f.toLRSHom.toShHom)
    (fun M i => isQuasicoherent_homology_derivedPullback_anyModel f M.obj M.property i)

/-- `Lf^* ⊣ Rf_*` restricted to the quasi-coherent derived categories of the standard model. -/
def quasiCoherentDerivedAdjunctionStd :
    quasiCoherentDerivedPullbackStd f ⊣ quasiCoherentDerivedPushforward f
      (StandardModel.isQuasicoherent_homology_derivedPushforward f) :=
  (derivedAdjunctionRS f.toLRSHom.toShHom).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _) (Iso.refl _) (Iso.refl _)

/-- **[Stacks, Tag 0CR1] at the standard model**: `Rf_* ∘ DQ_X ≅ DQ_Y ∘ Rf_*` for the coherators
`DQ_X`, `DQ_Y` of [Stacks, Tag 0CR0]. Both are right adjoint to
`Lf^* : D_QCoh(𝒪_Y) ⥤ D(𝒪_X)`. -/
def coheratorDerivedPushforwardIsoStd :
    (DerivedCategoryB.derivedCategoryB (A := X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι.rightAdjoint ⋙
      quasiCoherentDerivedPushforward f
        (StandardModel.isQuasicoherent_homology_derivedPushforward f) ≅
    derivedPushforward f ⋙ (DerivedCategoryB.derivedCategoryB (A := Y.Modules)
        (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).ι.rightAdjoint :=
  Adjunction.rightAdjointUniq
    ((quasiCoherentDerivedAdjunctionStd f).comp (Adjunction.ofIsLeftAdjoint
      (DerivedCategoryB.derivedCategoryB (A := X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι))
    ((Adjunction.ofIsLeftAdjoint (DerivedCategoryB.derivedCategoryB (A := Y.Modules)
        (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).ι).comp
      (derivedAdjunctionRS f.toLRSHom.toShHom))

/-- **Stacks Project, Tag 0GEV.** Let `f : X ⟶ Y` be a morphism of quasi-compact quasi-separated
schemes, `a` the right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`, `DQ_X`, `DQ_Y` the
coherators, `L ∈ D_QCoh(𝒪_X)` and `K ∈ D_QCoh(𝒪_Y)`. Then
`DQ_Y(Rf_*R𝓗om(L, a(K))) ≅ Rf_*DQ_X(R𝓗om(L, a(K)))` ([Stacks, Tag 0CR1]), and the map
`Rf_*R𝓗om_{𝒪_X}(L, a(K)) ⟶ R𝓗om_{𝒪_Y}(Rf_*L, K)` of [Stacks, Tag 0B6H] is an isomorphism if
(1) `L` and `Rf_*L` are perfect, or (2) `K` is bounded below and `L` and `Rf_*L` are
pseudo-coherent.

The coherator is the one constructed for qcqs schemes ([Stacks, Tag 0CR0]); [Stacks, Tag 0A9Q],
[Stacks, Tag 0A6H] and [Stacks, Tag 0A9I] enter through their proofs in this development. The
erasure statements of the remark are in
`StacksFrontier/AlgebraicGeometry/Duality/SheafyTraceCoheratorErasure.lean`. -/
@[stacks 0GEV "the 0CR1 identity for DQ_Y and Rf_*, and the trace of 0B6H is an isomorphism \
in cases (1) L and Rf_*L perfect, (2) K bounded below and L and Rf_*L pseudo-coherent"]
theorem sheafyTrace_quasiCoherent_criteria (L : quasiCoherentDerivedCategory X)
    (K : quasiCoherentDerivedCategory Y) :
    Nonempty ((DerivedCategoryB.derivedCategoryB (A := Y.Modules)
        (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).ι.rightAdjoint.obj
          ((derivedPushforward f).obj (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj
            (op L.obj)).obj ((twistedInverseImage f
              (StandardModel.isQuasicoherent_homology_derivedPushforward f)).obj K).obj)) ≅
        (quasiCoherentDerivedPushforward f
          (StandardModel.isQuasicoherent_homology_derivedPushforward f)).obj
          ((DerivedCategoryB.derivedCategoryB (A := X.Modules)
            (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι.rightAdjoint.obj
              (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L.obj)).obj
                ((twistedInverseImage f
                  (StandardModel.isQuasicoherent_homology_derivedPushforward f)).obj K).obj))) ∧
    (RingedSpace.IsPerfect (X := X.toRingedSpace) L.obj →
      RingedSpace.IsPerfect (X := Y.toRingedSpace)
        ((quasiCoherentDerivedPushforward f
          (StandardModel.isQuasicoherent_homology_derivedPushforward f)).obj L).obj →
      IsIso (sheafyTrace f
        (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite X.sheaf))
        (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite Y.sheaf))
        (StandardModel.isQuasicoherent_homology_derivedPushforward f)
        (twistedInverseImageAdjunction f
          (StandardModel.isQuasicoherent_homology_derivedPushforward f)) L K)) ∧
    (DerivedCategoryB.IsBoundedBelow K.obj →
      RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) L.obj →
      RingedSpace.IsPseudoCoherent (X := Y.toRingedSpace)
        ((quasiCoherentDerivedPushforward f
          (StandardModel.isQuasicoherent_homology_derivedPushforward f)).obj L).obj →
      IsIso (sheafyTrace f
        (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite X.sheaf))
        (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite Y.sheaf))
        (StandardModel.isQuasicoherent_homology_derivedPushforward f)
        (twistedInverseImageAdjunction f
          (StandardModel.isQuasicoherent_homology_derivedPushforward f)) L K)) :=
  ⟨⟨((coheratorDerivedPushforwardIsoStd f).app _).symm⟩,
    isIso_sheafyTrace_of_isPerfect f _ _ _ _ (Adjunction.ofIsLeftAdjoint _) L K
      (fun M N hM hN => InternalHom.derivedCategoryB_derivedSheafHom_of_isPerfect X M N hM hN)
      (fun M N hM hN => InternalHom.derivedCategoryB_derivedSheafHom_of_isPerfect Y M N hM hN)
      (isIso_coherator_map_sheafyTrace_of_qcqs f L K),
    isIso_sheafyTrace_of_isPseudoCoherent f _ _ _ _ (Adjunction.ofIsLeftAdjoint _) L K
      (isBoundedBelow_twistedInverseImage_obj_standard f K)
      (isIso_coherator_map_sheafyTrace_of_qcqs f L K)⟩

end Stacks.Duality

end

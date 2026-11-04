module

public import StacksFrontier.AlgebraicGeometry.Duality.SheafyTraceQuasiCoherentCriterionUnconditional

/-!
# Erasing the coherator from the sheafy trace of a morphism of qcqs schemes

Let `f : X ⟶ Y` be a morphism of quasi-compact quasi-separated schemes, `a` the right adjoint of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`, `DQ_Y` the coherator, `L ∈ D_QCoh(𝒪_X)` and
`K ∈ D_QCoh(𝒪_Y)`. By [Stacks, Tag 0A9Q] the map
`DQ_Y(Rf_*R𝓗om(L, a(K))) ⟶ DQ_Y(R𝓗om(Rf_*L, K))` induced by the trace of [Stacks, Tag 0B6H] is
an isomorphism. [Stacks, Tag 0GEV]: if `R𝓗om(L, a(K)) ∈ D_QCoh(𝒪_X)` the `DQ_Y` on the left can
be erased, if `R𝓗om(Rf_*L, K) ∈ D_QCoh(𝒪_Y)` the one on the right can, and if both hold the
trace `Rf_*R𝓗om(L, a(K)) ⟶ R𝓗om(Rf_*L, K)` is an isomorphism.

## Main results

* `Stacks.Duality.isIso_coherator_homEquiv_sheafyTrace_of_qcqs`: erasing `DQ_Y` on the left.
* `Stacks.Duality.isIso_coherator_counit_comp_sheafyTrace_of_qcqs`: erasing `DQ_Y` on the right.
* `Stacks.Duality.isIso_sheafyTrace_of_derivedCategoryB_of_qcqs`: both.

## References

* [Stacks Project, Tag 0GEV](https://stacks.math.columbia.edu/tag/0GEV)
* [Stacks Project, Tag 0A9Q](https://stacks.math.columbia.edu/tag/0A9Q)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi

namespace Stacks.Duality

universe u

attribute [local instance] Stacks.AssociatedSheaf.hasModuleSheafify
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y]

/-- For a fully faithful `ι` with right adjoint `R`, the transpose `A ⟶ R B` of `g : ι A ⟶ B`
is an isomorphism once `R g` is. -/
private theorem isIso_homEquiv_of_isIso_map {C D : Type*} [Category C] [Category D] {ι : C ⥤ D}
    [ι.Full] [ι.Faithful] {R : D ⥤ C} (adj : ι ⊣ R) {A : C} {B : D} (g : ι.obj A ⟶ B)
    (hg : IsIso (R.map g)) : IsIso (adj.homEquiv A B g) := by
  have := adj.unit_isIso_of_L_fully_faithful
  rw [Adjunction.homEquiv_unit]
  infer_instance

/-- For an adjunction `ι ⊣ R` and `g : A ⟶ B`, the composite `ι(R A) ⟶ A ⟶ B` of the counit and
`g` is an isomorphism once `R g` and the counit at `B` are. -/
private theorem isIso_counit_comp_of_isIso_map {C D : Type*} [Category C] [Category D]
    {ι : C ⥤ D} {R : D ⥤ C} (adj : ι ⊣ R) {A B : D} (g : A ⟶ B)
    (hB : IsIso (adj.counit.app B)) (hg : IsIso (R.map g)) : IsIso (adj.counit.app A ≫ g) := by
  have h : adj.counit.app A ≫ g = ι.map (R.map g) ≫ adj.counit.app B :=
    (adj.counit.naturality g).symm
  rw [h]
  infer_instance

/-- **[Stacks, Tag 0GEV], erasing `DQ_Y` on the left.** Let `f : X ⟶ Y` be a morphism of
quasi-compact quasi-separated schemes, `L ∈ D_QCoh(𝒪_X)` and `K ∈ D_QCoh(𝒪_Y)`. If
`R𝓗om_{𝒪_X}(L, a(K))` lies in `D_QCoh(𝒪_X)`, the map
`Rf_*R𝓗om_{𝒪_X}(L, a(K)) ⟶ DQ_Y(R𝓗om_{𝒪_Y}(Rf_*L, K))` in `D_QCoh(𝒪_Y)` adjoint to the trace of
[Stacks, Tag 0B6H] is an isomorphism. All derived categories are at the standard model. -/
@[stacks 0GEV "if RHom(L, a(K)) is in D_QCoh, erase DQ_Y on the left hand side of the arrow"]
theorem isIso_coherator_homEquiv_sheafyTrace_of_qcqs :
    letI := HasDerivedCategory.standard X.Modules
    letI := HasDerivedCategory.standard Y.Modules
    ∀ (L : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y)
      (hsrc : DerivedCategoryB.derivedCategoryB (A := X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)
        (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L.obj)).obj
          ((twistedInverseImage f
            (StandardModel.isQuasicoherent_homology_derivedPushforward f)).obj K).obj)),
      IsIso ((Adjunction.ofIsLeftAdjoint (DerivedCategoryB.derivedCategoryB (A := Y.Modules)
        (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).ι).homEquiv
        ⟨_, StandardModel.isQuasicoherent_homology_derivedPushforward f ⟨_, hsrc⟩⟩ _
        (sheafyTrace f
          (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite X.sheaf))
          (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite Y.sheaf))
          (StandardModel.isQuasicoherent_homology_derivedPushforward f)
          (twistedInverseImageAdjunction f
            (StandardModel.isQuasicoherent_homology_derivedPushforward f)) L K)) := by
  intro L K _
  exact isIso_homEquiv_of_isIso_map _ _ (isIso_coherator_map_sheafyTrace_of_qcqs f L K)

/-- **[Stacks, Tag 0GEV], erasing `DQ_Y` on the right.** Let `f : X ⟶ Y` be a morphism of
quasi-compact quasi-separated schemes, `L ∈ D_QCoh(𝒪_X)` and `K ∈ D_QCoh(𝒪_Y)`. If
`R𝓗om_{𝒪_Y}(Rf_*L, K)` lies in `D_QCoh(𝒪_Y)`, the map
`DQ_Y(Rf_*R𝓗om_{𝒪_X}(L, a(K))) ⟶ R𝓗om_{𝒪_Y}(Rf_*L, K)`, the counit of the coherator followed by
the trace of [Stacks, Tag 0B6H], is an isomorphism. All derived categories are at the standard
model. -/
@[stacks 0GEV "if RHom(Rf_*L, K) is in D_QCoh, erase DQ_Y on the right hand side of the arrow"]
theorem isIso_coherator_counit_comp_sheafyTrace_of_qcqs :
    letI := HasDerivedCategory.standard X.Modules
    letI := HasDerivedCategory.standard Y.Modules
    ∀ (L : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y)
      (_htgt : DerivedCategoryB.derivedCategoryB (A := Y.Modules)
        (SheafOfModules.isQuasicoherent Y.ringCatSheaf)
        (((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).obj
          (op ((derivedPushforward f).obj L.obj))).obj K.obj)),
      IsIso ((Adjunction.ofIsLeftAdjoint (DerivedCategoryB.derivedCategoryB (A := Y.Modules)
        (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).ι).counit.app _ ≫
        sheafyTrace f
          (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite X.sheaf))
          (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite Y.sheaf))
          (StandardModel.isQuasicoherent_homology_derivedPushforward f)
          (twistedInverseImageAdjunction f
            (StandardModel.isQuasicoherent_homology_derivedPushforward f)) L K) := by
  intro L K htgt
  exact isIso_counit_comp_of_isIso_map _ _
    (isIso_counit_app_of_prop (Adjunction.ofIsLeftAdjoint _) htgt)
    (isIso_coherator_map_sheafyTrace_of_qcqs f L K)

/-- **[Stacks, Tag 0GEV], both sides in `D_QCoh`.** Let `f : X ⟶ Y` be a morphism of
quasi-compact quasi-separated schemes, `L ∈ D_QCoh(𝒪_X)` and `K ∈ D_QCoh(𝒪_Y)`. If
`R𝓗om_{𝒪_X}(L, a(K))` lies in `D_QCoh(𝒪_X)` and `R𝓗om_{𝒪_Y}(Rf_*L, K)` lies in `D_QCoh(𝒪_Y)`, the
trace `Rf_*R𝓗om_{𝒪_X}(L, a(K)) ⟶ R𝓗om_{𝒪_Y}(Rf_*L, K)` of [Stacks, Tag 0B6H] is an isomorphism.
All derived categories are at the standard model. -/
@[stacks 0GEV "if both RHom's are in D_QCoh, then the map of Tag 0B6H is an isomorphism"]
theorem isIso_sheafyTrace_of_derivedCategoryB_of_qcqs :
    letI := HasDerivedCategory.standard X.Modules
    letI := HasDerivedCategory.standard Y.Modules
    ∀ (L : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y)
      (_hsrc : DerivedCategoryB.derivedCategoryB (A := X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)
        (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L.obj)).obj
          ((twistedInverseImage f
            (StandardModel.isQuasicoherent_homology_derivedPushforward f)).obj K).obj))
      (_htgt : DerivedCategoryB.derivedCategoryB (A := Y.Modules)
        (SheafOfModules.isQuasicoherent Y.ringCatSheaf)
        (((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).obj
          (op ((derivedPushforward f).obj L.obj))).obj K.obj)),
      IsIso (sheafyTrace f
          (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite X.sheaf))
          (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite Y.sheaf))
          (StandardModel.isQuasicoherent_homology_derivedPushforward f)
          (twistedInverseImageAdjunction f
            (StandardModel.isQuasicoherent_homology_derivedPushforward f)) L K) := by
  intro L K hsrc htgt
  exact isIso_sheafyTrace_of_derivedCategoryB f _ _ _ _ (Adjunction.ofIsLeftAdjoint _) L K hsrc htgt
    (isIso_coherator_map_sheafyTrace_of_qcqs f L K)

end Stacks.Duality

end

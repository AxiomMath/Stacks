module

public import StacksFrontier.Homology.RelativelyPerfect.Colimit.DerivedExtensionPseudofunctor
import all StacksFrontier.Homology.RelativelyPerfect.Colimit.ExtensionScalars
import all StacksFrontier.Homology.RelativelyPerfect.Colimit.RingColimit
import all StacksFrontier.Homology.RelativelyPerfect.Colimit.ComplexDescent
import all StacksFrontier.Homology.RelativelyPerfect.Colimit.HomComplexColimit
import all StacksFrontier.Homology.RelativelyPerfect.Colimit.DerivedExtensionPseudofunctor

/-!
# The diagram of relatively perfect categories

The diagram of categories of relatively perfect objects, descent of relatively perfect objects
and of morphisms to a stage of the filtered system, and the strictification of a pseudofunctor
out of a locally discrete category.

This is part 8 of 10 of `StacksFrontier.Homology.RelativelyPerfect.Colimit`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ZeroObject
open CochainComplex.DerivedExtensionScalars
open StacksDraft.TorAmplitude
open scoped TensorProduct

open Stacks.HomologyColimit

namespace PseudoCoherence

open StacksDraft.RelativelyPerfect (finite_homCochain_support homCochainBaseChange
    homCochainBaseChange_bijective homCochainBaseChange_tmul homCochainExtendScalars
    homCochainRestrict homComplexBaseChange linearMap_isBaseChange_of_finiteFree)

universe uI uJ uR uA uM

attribute [local instance] HasDerivedCategory.standard
attribute [-instance] CochainComplex.DerivedTensor.instAdditiveModuleCatExtensionScalars
  CochainComplex.DerivedTensor.instIsLeftAdjointModuleCatExtensionScalars

section RelativePerfectDiagram

open scoped CategoryTheory.Bicategory

variable
    (comp : ∀ {A B C : Type (max uR uA)} [CommRing A] [CommRing B] [CommRing C]
      (f : A →+* B) (g : B →+* C),
      (totalDerivedExtensionScalars.{max uR uA, max uR uA, uM} f).functor ⋙
        (totalDerivedExtensionScalars.{max uR uA, max uR uA, uM} g).functor ≅
        (totalDerivedExtensionScalars.{max uR uA, max uR uA, uM} (g.comp f)).functor)
    (hcomp : ∀ {A B C : Type (max uR uA)} [CommRing A] [CommRing B] [CommRing C]
      (f : A →+* B) (g : B →+* C)
      (P : CochainComplex (ModuleCat.{max uR uA uM} A) ℤ),
      (comp f g).hom.app (DerivedCategory.Q.obj P) ≫
        (totalDerivedExtensionScalars.{max uR uA, max uR uA, uM} (g.comp f)).comparison.app P =
        (totalDerivedExtensionScalars.{max uR uA, max uR uA, uM} g).functor.map
          ((totalDerivedExtensionScalars.{max uR uA, max uR uA, uM} f).comparison.app P) ≫
          (totalDerivedExtensionScalars.{max uR uA, max uR uA, uM} g).comparison.app
            (((ModuleCat.extendScalars.{max uR uA, max uR uA, max uR uA uM}
              f).mapHomologicalComplex (.up ℤ)).obj P) ≫
          (extensionOfScalarsComplexComp.{max uR uA, uM} f g).inv.app P)

set_option backward.isDefEq.respectTransparency false in
include hcomp in
private def relativelyPerfectPseudofunctor
    {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I]
    (F : I ⥤ CommAlgCat.{uR} R₀) (A₀ : Type uA)
    [CommRing A₀] [Algebra R₀ A₀]
    [Module.Flat R₀ A₀] [Algebra.FinitePresentation R₀ A₀]
    (D : ∀ i : I, DerivedTensoringDatum.{uR, max uR uA uM} (F.obj i)) :
    LocallyDiscrete I ⥤ᵖ Cat.{max uR uA uM + 1, max uR uA uM + 1} := by
  let J := stageUnderFunctor F A₀ ⋙ Under.forget (CommRingCat.of (ULift.{uR} A₀))
  let E := J.toPseudofunctor.comp (derivedExtensionScalarsPseudofunctor comp hcomp)
  let P : E.ObjectProperty := ⟨fun i ↦
    (fun K : DerivedCategory (ModuleCat.{max uR uA uM} (stageAlgebra F A₀ i.as)) ↦
      IsRelativelyPerfect.{uR, max uR uA, uM}
        (R := F.obj i.as) (A := stageAlgebra F A₀ i.as)
        (D i.as).tensor (D i.as).comparison (D i.as).isLeftDerived K)⟩
  letI : P.IsClosedUnderMapObj :=
    { map_obj := by
        intro X Y K hK f
        exact isRelativelyPerfect_tensorProduct_map.{uR, uA, uM} (F.map f.as).hom A₀
          (D X.as) (D Y.as) K hK }
  exact P.fullsubcategory

include hcomp in
private def relativelyPerfectDiagram
    {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I]
    (F : I ⥤ CommAlgCat.{uR} R₀) (A₀ : Type uA)
    [CommRing A₀] [Algebra R₀ A₀]
    [Module.Flat R₀ A₀] [Algebra.FinitePresentation R₀ A₀]
    (D : ∀ i : I, DerivedTensoringDatum.{uR, max uR uA uM} (F.obj i)) :
    I ⥤ Cat.{max uI uJ (max uR uA uM + 1), max uI uJ (max uR uA uM + 1)} :=
  splitPseudofunctor (relativelyPerfectPseudofunctor comp hcomp F A₀ D) ⋙
    Cat.asSmallFunctor.{max uI uJ}

set_option maxHeartbeats 1200000 in
-- identifying the strictified fibre with the full subcategory unfolds the pseudofunctor
set_option backward.isDefEq.respectTransparency false in
include hcomp in
private def relativelyPerfectDiagramEquivalence
    {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I]
    (F : I ⥤ CommAlgCat.{uR} R₀) (A₀ : Type uA)
    [CommRing A₀] [Algebra R₀ A₀]
    [Module.Flat R₀ A₀] [Algebra.FinitePresentation R₀ A₀]
    (D : ∀ i : I, DerivedTensoringDatum.{uR, max uR uA uM} (F.obj i)) (i : I) :
    (relativelyPerfectDiagram comp hcomp F A₀ D).obj i ≌
      ObjectProperty.FullSubcategory
        (fun K : DerivedCategory (ModuleCat.{max uR uA uM} (stageAlgebra F A₀ i)) ↦
          IsRelativelyPerfect.{uR, max uR uA, uM}
            (R := F.obj i) (A := stageAlgebra F A₀ i)
            (D i).tensor (D i).comparison (D i).isLeftDerived K) :=
  AsSmall.equiv.symm.trans
    (splitPseudofunctorEquivalence (relativelyPerfectPseudofunctor comp hcomp F A₀ D) i)


set_option backward.isDefEq.respectTransparency false in
include hcomp in
private def relativelyPerfectDiagramTransition
    {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I]
    (F : I ⥤ CommAlgCat.{uR} R₀) (A₀ : Type uA)
    [CommRing A₀] [Algebra R₀ A₀]
    [Module.Flat R₀ A₀] [Algebra.FinitePresentation R₀ A₀]
    (D : ∀ i : I, DerivedTensoringDatum.{uR, max uR uA uM} (F.obj i)) {i j : I} (f : i ⟶ j) :
    (relativelyPerfectDiagramEquivalence.{uI, uJ, uR, uA, uM} comp hcomp F A₀ D i).inverse ⋙
      ((relativelyPerfectDiagram.{uI, uJ, uR, uA, uM} comp hcomp F A₀ D).map f).toFunctor ⋙
      (relativelyPerfectDiagramEquivalence.{uI, uJ, uR, uA, uM} comp hcomp F A₀ D j).functor ≅
    ((relativelyPerfectPseudofunctor.{uI, uJ, uR, uA, uM} comp hcomp F A₀ D).map f.toLoc).toFunctor
      := by
  let E := relativelyPerfectPseudofunctor.{uI, uJ, uR, uA, uM} comp hcomp F A₀ D
  let ei := relativelyPerfectDiagramEquivalence.{uI, uJ, uR, uA, uM} comp hcomp F A₀ D i
  let ej := relativelyPerfectDiagramEquivalence.{uI, uJ, uR, uA, uM} comp hcomp F A₀ D j
  let G := relativelyPerfectDiagram.{uI, uJ, uR, uA, uM} comp hcomp F A₀ D
  let h : ei.functor ⋙ (E.map f.toLoc).toFunctor ≅ (G.map f).toFunctor ⋙ ej.functor :=
    smallSplitPseudofunctorMapIso.{uI, uJ, max uR uA uM + 1, max uR uA uM + 1, max uI uJ} E f
  exact h.symm.inverseCompIso (G := ei)

set_option backward.isDefEq.respectTransparency false in
include hcomp in
private def relativelyPerfectLimitPseudofunctor
    {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I]
    (F : I ⥤ CommAlgCat.{uR} R₀) (c : Cocone F) (A₀ : Type uA)
    [CommRing A₀] [Algebra R₀ A₀]
    [Module.Flat R₀ A₀] [Algebra.FinitePresentation R₀ A₀]
    (D : ∀ stage : I, DerivedTensoringDatum.{uR, max uR uA uM} (F.obj stage))
    (Dlim : DerivedTensoringDatum.{uR, max uR uA uM} c.pt) :
    LocallyDiscrete (WithTerminal I) ⥤ᵖ
      Cat.{max uR uA uM + 1, max uR uA uM + 1} := by
  let extended := WithTerminal.lift F (fun stage ↦ c.ι.app stage)
    (fun _ _ arrow ↦ c.w arrow)
  let tensors : ∀ stage : WithTerminal I,
      DerivedTensoringDatum.{uR, max uR uA uM} (extended.obj stage) := fun stage ↦
    match stage with
    | .of stage => D stage
    | .star => Dlim
  exact relativelyPerfectPseudofunctor comp hcomp extended A₀ tensors

end RelativePerfectDiagram

private theorem exists_relativelyPerfect_stage
    {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I]
    (F : I ⥤ CommAlgCat.{uR} R₀) (c : Cocone F)
    (hc : IsColimit ((CommAlgCat.uliftFunctor.{max uI uJ, uR, uR} R₀).mapCocone c))
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀]
    [Module.Flat R₀ A₀] [Algebra.FinitePresentation R₀ A₀]
    (D : ∀ i : I, DerivedTensoringDatum.{uR, max uR uA uM} (F.obj i))
    (Dlim : DerivedTensoringDatum.{uR, max uR uA uM} c.pt)
    (K : DerivedCategory (ModuleCat.{max uR uA uM} (c.pt ⊗[R₀] A₀)))
    (hK : IsRelativelyPerfect.{uR, max uR uA, uM} Dlim.tensor Dlim.comparison Dlim.isLeftDerived K)
      :
    ∃ (i : I) (Ki : DerivedCategory (ModuleCat.{max uR uA uM} (stageAlgebra F A₀ i))),
      IsRelativelyPerfect.{uR, max uR uA, uM} (D i).tensor (D i).comparison (D i).isLeftDerived Ki ∧
      Nonempty ((totalDerivedExtensionScalars.{max uR uA, max uR uA, uM}
        (stageToLimitMap c A₀ i)).functor.obj Ki ≅ K) := by
  let DL := toKFlatDerivedTensorProduct.{uR, max uR uA uM} Dlim
  obtain ⟨P, ⟨a, ha⟩, ⟨b, hb⟩, hP, ⟨eP⟩⟩ :=
    (isRelativelyPerfect_iff_exists_bounded_flat_finitePresentation_bundled.{uR, max uR uA, uM}
      DL K).mp hK
  let := ha
  let := hb
  obtain ⟨i, Q, hQa, hQb, hQ, ⟨eQ⟩⟩ :=
    exists_stage_bounded_flat_finitePresentation_complex.{uI, uJ, uR, uA, uM} hc A₀ P a b hP
  let := hQa
  let := hQb
  let := fun n ↦ (hQ n).1
  let Di := toKFlatDerivedTensorProduct.{uR, max uR uA uM} (D i)
  have hQi : IsRelativelyPerfect.{uR, max uR uA, uM} (D i).tensor (D i).comparison (D
    i).isLeftDerived
      (DerivedCategory.Q.obj Q) :=
    (isRelativelyPerfect_iff_exists_bounded_flat_finitePresentation_bundled.{uR, max uR uA, uM}
      Di (DerivedCategory.Q.obj Q)).mpr ⟨Q, ⟨a, hQa⟩, ⟨b, hQb⟩, hQ, ⟨Iso.refl _⟩⟩
  let S := totalDerivedExtensionScalars.{max uR uA, max uR uA, uM} (stageToLimitMap c A₀ i)
  let : IsIso (S.comparison.app Q) := isIso_stage_comparison_app_of_flat c A₀ i Q b
  exact ⟨i, DerivedCategory.Q.obj Q, hQi,
    ⟨asIso (S.comparison.app Q) ≪≫ DerivedCategory.Q.mapIso eQ ≪≫ eP⟩⟩

section StageTailHomColimit

set_option backward.isDefEq.respectTransparency false

private def stageTailUnderFunctor
    {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I]
    (F : I ⥤ CommAlgCat.{uR} R₀) (A₀ : Type uA)
    [CommRing A₀] [Algebra R₀ A₀] (stage : I) :
    Under stage ⥤ Under (CommRingCat.of (stageAlgebra F A₀ stage)) :=
  Under.post (stageUnderFunctor F A₀ ⋙
    Under.forget (CommRingCat.of (ULift.{uR} A₀)))

private def stageTailUnderCocone
    {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I]
    {F : I ⥤ CommAlgCat.{uR} R₀} (c : Cocone F) (A₀ : Type uA)
    [CommRing A₀] [Algebra R₀ A₀] (stage : I) :
    Cocone (stageTailUnderFunctor F A₀ stage) where
  pt := Under.mk (CommRingCat.ofHom (stageToLimitMap c A₀ stage))
  ι.app item := Under.homMk (CommRingCat.ofHom (stageToLimitMap c A₀ item.right)) (by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro element
    exact stageToLimitMap_comp_stageMap c A₀ item.hom element)
  ι.naturality first second arrow := by
    apply Under.UnderMorphism.ext
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro element
    exact stageToLimitMap_comp_stageMap c A₀ arrow.right element

private def isColimit_stageTailUnderCocone_forget
    {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I]
    {F : I ⥤ CommAlgCat.{uR} R₀} {c : Cocone F}
    (hc : IsColimit ((CommAlgCat.uliftFunctor.{max uI uJ, uR, uR} R₀).mapCocone c))
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀] [Module.Flat R₀ A₀]
    (stage : I) :
    IsColimit (((commAlgCatEquivUnder (CommRingCat.of (stageAlgebra F A₀ stage))).inverse ⋙
      forget (CommAlgCat.{max uR uA} (stageAlgebra F A₀ stage))).mapCocone
        (stageTailUnderCocone c A₀ stage)) :=
  (Functor.Final.isColimitWhiskerEquiv (Under.forget stage) _).symm
    (isColimit_stageUnderCocone_forget hc A₀)

private lemma isIso_stageMap_comparison_app_of_flat
    {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] {F : I ⥤ CommAlgCat.{uR} R₀}
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀] [Module.Flat R₀ A₀]
    {source target : I} (arrow : source ⟶ target)
    (complex : CochainComplex (ModuleCat.{max uR uA uM} (stageAlgebra F A₀ source)) ℤ)
    (bound : ℤ) [complex.IsStrictlyLE bound]
    [∀ degree, Module.Flat (F.obj source) ((ModuleCat.restrictScalars
      (algebraMap (F.obj source) (stageAlgebra F A₀ source))).obj (complex.X degree))] :
    IsIso ((totalDerivedExtensionScalars.{max uR uA, max uR uA, uM}
      (stageMap F A₀ arrow)).comparison.app complex) := by
  let diagram : Discrete PUnit.{1} ⥤ CommAlgCat.{uR} R₀ :=
    (Functor.const _).obj (F.obj source)
  let cone : Cocone diagram :=
    { pt := F.obj target
      ι := { app := fun _ ↦ F.map arrow
             naturality := fun _ _ _ ↦ by simp [diagram] } }
  let (degree : ℤ) : Module.Flat (diagram.obj ⟨PUnit.unit⟩)
      ((ModuleCat.restrictScalars
        (algebraMap (diagram.obj ⟨PUnit.unit⟩) (stageAlgebra diagram A₀ ⟨PUnit.unit⟩))).obj
          (complex.X degree)) := by
    change Module.Flat (F.obj source) ((ModuleCat.restrictScalars
      (algebraMap (F.obj source) (stageAlgebra F A₀ source))).obj (complex.X degree))
    infer_instance
  exact isIso_stage_comparison_app_of_flat cone A₀ ⟨PUnit.unit⟩ complex bound

variable
    (comp : ∀ {A B C : Type (max uR uA)} [CommRing A] [CommRing B] [CommRing C]
      (f : A →+* B) (g : B →+* C),
      (totalDerivedExtensionScalars.{max uR uA, max uR uA, uM} f).functor ⋙
        (totalDerivedExtensionScalars.{max uR uA, max uR uA, uM} g).functor ≅
        (totalDerivedExtensionScalars.{max uR uA, max uR uA, uM} (g.comp f)).functor)
    (hcomp : ∀ {A B C : Type (max uR uA)} [CommRing A] [CommRing B] [CommRing C]
      (f : A →+* B) (g : B →+* C)
      (complex : CochainComplex (ModuleCat.{max uR uA uM} A) ℤ),
      (comp f g).hom.app (DerivedCategory.Q.obj complex) ≫
        (totalDerivedExtensionScalars.{max uR uA, max uR uA, uM} (g.comp f)).comparison.app complex
          =
      (totalDerivedExtensionScalars.{max uR uA, max uR uA, uM} g).functor.map
          ((totalDerivedExtensionScalars.{max uR uA, max uR uA, uM} f).comparison.app complex) ≫
        (totalDerivedExtensionScalars.{max uR uA, max uR uA, uM} g).comparison.app
          (((ModuleCat.extendScalars.{max uR uA, max uR uA, max uR uA uM} f).mapHomologicalComplex
            (.up ℤ)).obj complex) ≫
        (extensionOfScalarsComplexComp.{max uR uA, uM} f g).inv.app complex)

include hcomp in
private def isColimit_stageTail_derivedHomFunctor
    {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I]
    (F : I ⥤ CommAlgCat.{uR} R₀) (c : Cocone F)
    (hc : IsColimit ((CommAlgCat.uliftFunctor.{max uI uJ, uR, uR} R₀).mapCocone c))
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀] [Module.Flat R₀ A₀]
    (stage : I) (tensor : DerivedTensoringDatum.{uR, max uR uA uM} (F.obj stage))
    (source target : DerivedCategory (ModuleCat.{max uR uA uM} (stageAlgebra F A₀ stage)))
    (source_pc : StacksDraft.PseudoCoherence.IsPseudoCoherent source)
    (target_tor : HasFiniteTorDimension tensor.tensor tensor.comparison tensor.isLeftDerived
      ((ModuleCat.restrictScalars (algebraMap (F.obj stage) (stageAlgebra F A₀
        stage))).mapDerivedCategory.obj target)) :
    IsColimit ((derivedHomFunctor.{max uR uA, uM} comp hcomp source target).mapCocone
      (stageTailUnderCocone c A₀ stage)) := by
  classical
  apply Classical.choice
  obtain ⟨sourceComplex, targetComplex, ⟨sourceIso⟩, ⟨targetIso⟩,
      ⟨upperSource, sourceBound⟩, sourceFree, ⟨lowerTarget, upperTarget, targetLower, targetUpper⟩,
      targetFlat⟩ :=
    exists_bounded_homComplex_representatives.{uR, max uR uA, uM}
      tensor source target source_pc target_tor
  refine ⟨?_⟩
  have := sourceBound
  have := targetLower
  have := targetUpper
  have (degree : ℤ) : Module.Finite (stageAlgebra F A₀ stage) (sourceComplex.X degree) :=
    (sourceFree degree).1
  have (degree : ℤ) : Module.Free (stageAlgebra F A₀ stage) (sourceComplex.X degree) :=
    (sourceFree degree).2
  have (degree : ℤ) := targetFlat degree
  have targetComparison (item : Under stage) :
      IsIso ((totalDerivedExtensionScalars.{max uR uA, max uR uA, uM}
        (stageMap F A₀ item.hom)).comparison.app targetComplex) :=
    isIso_stageMap_comparison_app_of_flat A₀ item.hom targetComplex upperTarget
  have : IsIso ((totalDerivedExtensionScalars.{max uR uA, max uR uA, uM}
      (stageTailUnderCocone c A₀ stage).pt.hom.hom).comparison.app targetComplex) := by
    change IsIso ((totalDerivedExtensionScalars.{max uR uA, max uR uA, uM}
      (stageToLimitMap c A₀ stage)).comparison.app targetComplex)
    exact isIso_stage_comparison_app_of_flat c A₀ stage targetComplex upperTarget
  apply isColimit_derivedHomFunctor_of_iso.{max uI uJ, uJ, max uR uA, uM} comp hcomp
    (stageTailUnderFunctor F A₀ stage) (stageTailUnderCocone c A₀ stage) sourceIso targetIso
  exact isColimit_derivedHomFunctor_of_representatives.{max uI uJ, uJ, max uR uA, uM} comp hcomp
    (stageTailUnderFunctor F A₀ stage) (stageTailUnderCocone c A₀ stage)
    (isColimit_stageTailUnderCocone_forget hc A₀ stage)
    sourceComplex targetComplex lowerTarget upperTarget upperSource targetComparison

section BaseMorphism

universe w

variable
    (compW : ∀ {A B C : Type w} [CommRing A] [CommRing B] [CommRing C]
      (f : A →+* B) (g : B →+* C),
      (totalDerivedExtensionScalars.{w, w, uM} f).functor ⋙
          (totalDerivedExtensionScalars.{w, w, uM} g).functor ≅
        (totalDerivedExtensionScalars.{w, w, uM} (g.comp f)).functor)
    (hcompW : ∀ {A B C : Type w} [CommRing A] [CommRing B] [CommRing C]
      (f : A →+* B) (g : B →+* C) (P : CochainComplex (ModuleCat.{max w uM} A) ℤ),
      (compW f g).hom.app (DerivedCategory.Q.obj P) ≫
          (totalDerivedExtensionScalars.{w, w, uM} (g.comp f)).comparison.app P =
        (totalDerivedExtensionScalars.{w, w, uM} g).functor.map
            ((totalDerivedExtensionScalars.{w, w, uM} f).comparison.app P) ≫
          (totalDerivedExtensionScalars.{w, w, uM} g).comparison.app
            (((ModuleCat.extendScalars.{w, w, max w uM} f).mapHomologicalComplex
              (.up ℤ)).obj P) ≫
          (extensionOfScalarsComplexComp.{w, uM} f g).inv.app P)

/-- The Hom diagram sends a morphism of algebras under the stage to the map induced on derived
Hom by extension of scalars along it. -/
private lemma derivedHomFunctor_map_baseMorphism
    {algebra : Type w} [CommRing algebra]
    {source target : DerivedCategory (ModuleCat.{max w uM} algebra)}
    {first second : Under (CommRingCat.of algebra)} (arrow : first ⟶ second)
    (morphism : source ⟶ target) :
    (derivedHomFunctor.{w, uM} compW hcompW source target).map arrow
        ((totalDerivedExtensionScalars.{w, w, uM}
          first.hom.hom).functor.map morphism) =
      (totalDerivedExtensionScalars.{w, w, uM}
        second.hom.hom).functor.map morphism :=
  NatIso.naturality_1
    (compW first.hom.hom arrow.right.hom ≪≫ derivedExtensionScalarsCongr.{w, uM}
      (congrArg CommRingCat.Hom.hom (Under.w arrow))) morphism

end BaseMorphism

include hcomp in
private theorem exists_stageTail_morphism
    {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I]
    (F : I ⥤ CommAlgCat.{uR} R₀) (c : Cocone F)
    (hc : IsColimit ((CommAlgCat.uliftFunctor.{max uI uJ, uR, uR} R₀).mapCocone c))
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀] [Module.Flat R₀ A₀]
    (stage : I) (tensor : DerivedTensoringDatum.{uR, max uR uA uM} (F.obj stage))
    (source target : DerivedCategory (ModuleCat.{max uR uA uM} (stageAlgebra F A₀ stage)))
    (source_pc : StacksDraft.PseudoCoherence.IsPseudoCoherent source)
    (target_tor : HasFiniteTorDimension tensor.tensor tensor.comparison tensor.isLeftDerived
      ((ModuleCat.restrictScalars (algebraMap (F.obj stage) (stageAlgebra F A₀
        stage))).mapDerivedCategory.obj target))
    (morphism : (totalDerivedExtensionScalars.{max uR uA, max uR uA, uM}
      (stageToLimitMap c A₀ stage)).functor.obj source ⟶
      (totalDerivedExtensionScalars.{max uR uA, max uR uA, uM}
        (stageToLimitMap c A₀ stage)).functor.obj target) :
    ∃ (later : I) (arrow : stage ⟶ later)
      (model : (totalDerivedExtensionScalars.{max uR uA, max uR uA, uM}
        (stageMap F A₀ arrow)).functor.obj source ⟶
        (totalDerivedExtensionScalars.{max uR uA, max uR uA, uM}
          (stageMap F A₀ arrow)).functor.obj target),
      derivedHomBaseChangeAlong comp (stageMap F A₀ arrow) (stageToLimitMap c A₀ later)
        (stageToLimitMap c A₀ stage) (RingHom.ext (stageToLimitMap_comp_stageMap c A₀ arrow)) model
          =
          morphism := by
  obtain ⟨item, model, equality⟩ := Types.jointly_surjective_of_isColimit
    (isColimit_stageTail_derivedHomFunctor.{uI, uJ, uR, uA, uM} comp hcomp
      F c hc A₀ stage tensor source target source_pc target_tor) morphism
  exact ⟨item.right, item.hom, model, equality⟩

include hcomp in
private theorem exists_stageTail_morphism_equal
    {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I]
    (F : I ⥤ CommAlgCat.{uR} R₀) (c : Cocone F)
    (hc : IsColimit ((CommAlgCat.uliftFunctor.{max uI uJ, uR, uR} R₀).mapCocone c))
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀] [Module.Flat R₀ A₀]
    (stage : I) (tensor : DerivedTensoringDatum.{uR, max uR uA uM} (F.obj stage))
    (source target : DerivedCategory (ModuleCat.{max uR uA uM} (stageAlgebra F A₀ stage)))
    (source_pc : StacksDraft.PseudoCoherence.IsPseudoCoherent source)
    (target_tor : HasFiniteTorDimension tensor.tensor tensor.comparison tensor.isLeftDerived
      ((ModuleCat.restrictScalars (algebraMap (F.obj stage) (stageAlgebra F A₀
        stage))).mapDerivedCategory.obj target))
    (first second : source ⟶ target)
    (equality : (totalDerivedExtensionScalars.{max uR uA, max uR uA, uM}
        (stageToLimitMap c A₀ stage)).functor.map first =
      (totalDerivedExtensionScalars.{max uR uA, max uR uA, uM}
        (stageToLimitMap c A₀ stage)).functor.map second) :
    ∃ (later : I) (arrow : stage ⟶ later),
      (totalDerivedExtensionScalars.{max uR uA, max uR uA, uM}
        (stageMap F A₀ arrow)).functor.map first =
      (totalDerivedExtensionScalars.{max uR uA, max uR uA, uM}
        (stageMap F A₀ arrow)).functor.map second := by
  let item : Under stage := Under.mk (𝟙 stage)
  let firstModel := (totalDerivedExtensionScalars.{max uR uA, max uR uA, uM}
    (stageTailUnderFunctor F A₀ stage |>.obj item).hom.hom).functor.map first
  let secondModel := (totalDerivedExtensionScalars.{max uR uA, max uR uA, uM}
    (stageTailUnderFunctor F A₀ stage |>.obj item).hom.hom).functor.map second
  have key {target' : Under (CommRingCat.of (stageAlgebra F A₀ stage))}
      (step : (stageTailUnderFunctor F A₀ stage).obj item ⟶ target') :
      (derivedHomFunctor.{max uR uA, uM} comp hcomp source target).map step firstModel =
        (derivedHomFunctor.{max uR uA, uM} comp hcomp source target).map step secondModel ↔
      (totalDerivedExtensionScalars.{max uR uA, max uR uA, uM}
        target'.hom.hom).functor.map first =
      (totalDerivedExtensionScalars.{max uR uA, max uR uA, uM}
        target'.hom.hom).functor.map second := by
    simp only [firstModel, secondModel, derivedHomFunctor_map_baseMorphism comp hcomp]
  obtain ⟨later, arrow, eventualEquality⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff'
      (isColimit_stageTail_derivedHomFunctor.{uI, uJ, uR, uA, uM} comp hcomp
        F c hc A₀ stage tensor source target source_pc target_tor)
      firstModel secondModel).mp ((key ((stageTailUnderCocone c A₀ stage).ι.app item)).mpr equality)
  exact ⟨later.right, later.hom, (key ((stageTailUnderFunctor F A₀ stage).map arrow)).mp
    eventualEquality⟩

end StageTailHomColimit

section LocalNaturalityBridge

universe u v

set_option backward.isDefEq.respectTransparency false in
private lemma derivedComparisonHom_naturality
    {Source Middle Target : Type u}
    [CommRing Source] [CommRing Middle] [CommRing Target]
    (first : Source →+* Middle) (second : Middle →+* Target)
    (comparisonComp :
      (totalDerivedExtensionScalars.{u, u, v} first).functor ⋙
        (totalDerivedExtensionScalars.{u, u, v} second).functor ≅
      (totalDerivedExtensionScalars.{u, u, v} (second.comp first)).functor)
    (factor : ∀ complex : CochainComplex (ModuleCat.{max u v} Source) ℤ,
      comparisonComp.hom.app (DerivedCategory.Q.obj complex) ≫
          (totalDerivedExtensionScalars.{u, u, v}
            (second.comp first)).comparison.app complex =
        (totalDerivedExtensionScalars.{u, u, v} second).functor.map
            ((totalDerivedExtensionScalars.{u, u, v} first).comparison.app complex) ≫
          (totalDerivedExtensionScalars.{u, u, v} second).comparison.app
            (((ModuleCat.extendScalars.{u, u, max u v} first).mapHomologicalComplex
              (.up ℤ)).obj complex) ≫
          (extensionOfScalarsComplexComp.{u, v} first second).inv.app complex)
    (source target : CochainComplex (ModuleCat.{max u v} Source) ℤ)
    (morphism :
      ((ModuleCat.extendScalars.{u, u, max u v} first).mapHomologicalComplex
        (.up ℤ)).obj source ⟶
      ((ModuleCat.extendScalars.{u, u, max u v} first).mapHomologicalComplex
        (.up ℤ)).obj target)
    [IsIso ((totalDerivedExtensionScalars.{u, u, v} first).comparison.app target)]
    [IsIso ((totalDerivedExtensionScalars.{u, u, v}
      (second.comp first)).comparison.app target)] :
    comparisonComp.inv.app (DerivedCategory.Q.obj source) ≫
        (totalDerivedExtensionScalars.{u, u, v} second).functor.map
          ((totalDerivedExtensionScalars.{u, u, v} first).comparison.app source ≫
            DerivedCategory.Q.map morphism ≫
            inv ((totalDerivedExtensionScalars.{u, u, v} first).comparison.app target)) ≫
        comparisonComp.hom.app (DerivedCategory.Q.obj target) =
      (totalDerivedExtensionScalars.{u, u, v}
        (second.comp first)).comparison.app source ≫
        (extensionOfScalarsComplexComp.{u, v} first second).hom.app source ≫
        DerivedCategory.Q.map
          (((ModuleCat.extendScalars.{u, u, max u v} second).mapHomologicalComplex
            (.up ℤ)).map morphism) ≫
        (extensionOfScalarsComplexComp.{u, v} first second).inv.app target ≫
        inv ((totalDerivedExtensionScalars.{u, u, v}
          (second.comp first)).comparison.app target) := by
  let next := totalDerivedExtensionScalars.{u, u, v} second
  let ordinary := extensionOfScalarsComplexComp.{u, v} first second
  have sourceFactor :
      comparisonComp.inv.app (DerivedCategory.Q.obj source) ≫
          next.functor.map
            ((totalDerivedExtensionScalars.{u, u, v} first).comparison.app source) ≫
          next.comparison.app
            (((ModuleCat.extendScalars.{u, u, max u v} first).mapHomologicalComplex
              (.up ℤ)).obj source) =
        (totalDerivedExtensionScalars.{u, u, v}
          (second.comp first)).comparison.app source ≫ ordinary.hom.app source := by
    apply (cancel_mono (ordinary.inv.app source)).mp
    simp only [Category.assoc, Iso.hom_inv_id_app]
    rw [← factor source]
    simp only [Functor.comp_obj, Iso.inv_hom_id_app_assoc]
    exact (Category.comp_id _).symm
  apply (cancel_mono ((totalDerivedExtensionScalars.{u, u, v}
    (second.comp first)).comparison.app target)).mp
  simp only [Functor.map_comp, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [factor target]
  simp only [← Functor.map_comp_assoc, IsIso.inv_hom_id,
    Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]
  erw [next.comparison.naturality_assoc morphism]
  simpa only [next, ordinary, extensionOfScalarsComplexGeneral,
    extensionOfScalarsComplex, Functor.comp_map, Category.assoc] using
    congrArg (fun value ↦ value ≫
      DerivedCategory.Q.map
        (((ModuleCat.extendScalars.{u, u, max u v} second).mapHomologicalComplex
          (.up ℤ)).map morphism) ≫ ordinary.inv.app target) sourceFactor

end LocalNaturalityBridge

namespace Strictification

open CategoryTheory.Bicategory

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe uIndex vIndex uObj vHom

variable {Index : Type uIndex} [Category.{vIndex} Index]
variable (diagram : LocallyDiscrete Index ⥤ᵖ Cat.{vHom, uObj})

/-- A presentation of an object at `stage`: an index `origin`, an arrow `origin ⟶ stage`, and an
object of the category of `diagram` at `origin`. -/
structure Presentation (stage : Index) where
  /-- The index at which the object is given. -/
  origin : Index
  /-- The arrow from the origin to the stage. -/
  arrow : origin ⟶ stage
  /-- The object of the category of `diagram` at the origin. -/
  object : diagram.obj ⟨origin⟩

/-- The object of `diagram` at `stage` presented by `object`: the image of its object under the
transition functor along its arrow. -/
abbrev evaluationObj {stage : Index} (object : Presentation diagram stage) :
    diagram.obj ⟨stage⟩ :=
  (diagram.map object.arrow.toLoc).toFunctor.obj object.object

/-- The category of presentations at `stage`, whose morphisms are those of `diagram` at `stage`
between the presented objects. -/
abbrev Stage (stage : Index) :=
  InducedCategory (diagram.obj ⟨stage⟩) (evaluationObj diagram (stage := stage))

/-- The fully faithful functor from `Stage diagram stage` to the category of `diagram` at `stage`
sending a presentation to the object it presents. -/
abbrev evaluation (stage : Index) : Stage diagram stage ⥤ diagram.obj ⟨stage⟩ :=
  inducedFunctor (evaluationObj diagram)

/-- Evaluation of presentations is full. -/
instance evaluation_full (stage : Index) : (evaluation diagram stage).Full :=
  inferInstanceAs (inducedFunctor (evaluationObj diagram (stage := stage))).Full

/-- Evaluation of presentations is faithful. -/
instance evaluation_faithful (stage : Index) : (evaluation diagram stage).Faithful :=
  inferInstanceAs (inducedFunctor (evaluationObj diagram (stage := stage))).Faithful

/-- Evaluation of presentations is essentially surjective: every object is presented by itself
along the identity of `stage`. -/
instance evaluation_essSurj (stage : Index) : (evaluation diagram stage).EssSurj where
  mem_essImage object := by
    refine ⟨⟨stage, 𝟙 stage, object⟩, ?_⟩
    exact ⟨(Cat.Hom.toNatIso (diagram.mapId ⟨stage⟩)).app object⟩

/-- The equivalence between `Stage diagram stage` and the category of `diagram` at `stage` given
by `evaluation`. -/
def stageEquivalence (stage : Index) : Stage diagram stage ≌ diagram.obj ⟨stage⟩ :=
  letI : (evaluation diagram stage).IsEquivalence :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  (evaluation diagram stage).asEquivalence

/-- The transport of a presentation along an arrow `source ⟶ target`, composing its arrow with
the given one. -/
abbrev pushObject {source target : Index} (arrow : source ⟶ target)
    (object : Stage diagram source) : Stage diagram target :=
  ⟨object.origin, object.arrow ≫ arrow, object.object⟩

/-- The isomorphism between the object presented by `pushObject diagram arrow object` and the
image under the transition functor along `arrow` of the object presented by `object`, given by
the composition isomorphism of `diagram`. -/
def comparison {source target : Index} (arrow : source ⟶ target)
    (object : Stage diagram source) :
    (evaluation diagram target).obj (pushObject diagram arrow object) ≅
      (diagram.map arrow.toLoc).toFunctor.obj ((evaluation diagram source).obj object) :=
  (Cat.Hom.toNatIso (diagram.mapComp object.arrow.toLoc arrow.toLoc)).app object.object

/-- The functor `Stage diagram source ⥤ Stage diagram target` induced by an arrow: `pushObject`
on objects, and the transition functor conjugated by `comparison` on morphisms. -/
def push {source target : Index} (arrow : source ⟶ target) :
    Stage diagram source ⥤ Stage diagram target where
  obj := pushObject diagram arrow
  map {first second} morphism := InducedCategory.homMk
    ((comparison diagram arrow first).hom ≫
      (diagram.map arrow.toLoc).toFunctor.map morphism.hom ≫
      (comparison diagram arrow second).inv)
  map_id object := by
    apply InducedCategory.hom_ext
    calc
      _ = (comparison diagram arrow object).hom ≫ 𝟙 _ ≫
          (comparison diagram arrow object).inv :=
        congrArg (fun value ↦ (comparison diagram arrow object).hom ≫ value ≫
          (comparison diagram arrow object).inv)
          ((diagram.map arrow.toLoc).toFunctor.map_id ((evaluation diagram source).obj object))
      _ = 𝟙 _ := by rw [Category.id_comp]; exact (comparison diagram arrow object).hom_inv_id
  map_comp first second := by
    apply InducedCategory.hom_ext
    simp

/-- Evaluation intertwines `push diagram arrow` with the transition functor of `diagram` along
`arrow`. -/
def pushEvaluationIso {source target : Index} (arrow : source ⟶ target) :
    push diagram arrow ⋙ evaluation diagram target ≅
      evaluation diagram source ⋙ (diagram.map arrow.toLoc).toFunctor :=
  NatIso.ofComponents (comparison diagram arrow) (by
    intro first second morphism
    dsimp [push, evaluation]
    simp)

/-- The underlying morphism of `eqToHom` in `Stage diagram stage` is `eqToHom` between the
presented objects. -/
lemma induced_eqToHom {stage : Index} {source target : Stage diagram stage}
    (equality : source = target) :
    (eqToHom equality).hom = eqToHom (congrArg (evaluationObj diagram) equality) := by
  subst target
  rfl

/-- Pushing a presentation along the identity returns it. -/
lemma pushObject_id (stage : Index) (object : Stage diagram stage) :
    pushObject diagram (𝟙 stage) object = object := by
  cases object
  simp [pushObject]

/-- Pushing a presentation along a composite is pushing it along each arrow in turn. -/
lemma pushObject_comp {source middle target : Index}
    (first : source ⟶ middle) (second : middle ⟶ target) (object : Stage diagram source) :
    pushObject diagram (first ≫ second) object =
      pushObject diagram second (pushObject diagram first object) := by
  simp [pushObject, Category.assoc]

/-- `push` along the identity is the identity functor. -/
lemma push_id (stage : Index) : push diagram (𝟙 stage) = 𝟭 (Stage diagram stage) := by
  refine CategoryTheory.Functor.ext (pushObject_id diagram stage) ?_
  intro source target morphism
  apply InducedCategory.hom_ext
  simp only [push, InducedCategory.homMk_hom, InducedCategory.comp_hom,
    induced_eqToHom, Functor.id_map]
  simp [comparison, Cat.Hom.toNatIso, diagram.mapComp_id_right_hom_app,
    diagram.mapComp_id_right_inv_app, Strict.rightUnitor_eqToIso,
    PrelaxFunctor.map₂_eqToHom, ← NatTrans.naturality_assoc]

/-- `push` along a composite is the composite of the `push` functors. -/
lemma push_comp {source middle target : Index}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    push diagram (first ≫ second) = push diagram first ⋙ push diagram second := by
  refine CategoryTheory.Functor.ext (pushObject_comp diagram first second) ?_
  intro sourceObject targetObject morphism
  apply InducedCategory.hom_ext
  simp only [push, Functor.comp_map, InducedCategory.homMk_hom,
    InducedCategory.comp_hom, induced_eqToHom]
  erw [← NatIso.naturality_2
    (Cat.Hom.toNatIso (diagram.mapComp first.toLoc second.toLoc)) morphism.hom]
  simp [comparison, Cat.Hom.toNatIso, diagram.mapComp_assoc_right_hom_app_assoc,
    diagram.mapComp_assoc_right_inv_app, Strict.associator_eqToIso,
    PrelaxFunctor.map₂_eqToHom, Category.assoc]

/-- The strictification of `diagram`: the functor `Index ⥤ Cat` sending a stage to
`Stage diagram stage` and an arrow to `push diagram arrow`. -/
def strictDiagram : Index ⥤ Cat.{vHom, max uIndex vIndex uObj} where
  obj stage := Cat.of (Stage diagram stage)
  map arrow := (push diagram arrow).toCatHom
  map_id stage := congrArg CategoryTheory.Functor.toCatHom (push_id diagram stage)
  map_comp first second :=
    congrArg CategoryTheory.Functor.toCatHom (push_comp diagram first second)

/-- Under the equivalences `stageEquivalence`, the transition functor of `strictDiagram diagram`
along `arrow` is isomorphic to that of `diagram`. -/
def strictTransitionIso {source target : Index} (arrow : source ⟶ target) :
    (stageEquivalence diagram source).inverse ⋙
        ((strictDiagram diagram).map arrow).toFunctor ⋙
        (stageEquivalence diagram target).functor ≅
      (diagram.map arrow.toLoc).toFunctor :=
  Functor.isoWhiskerLeft (stageEquivalence diagram source).inverse (pushEvaluationIso diagram
    arrow) ≪≫
    Functor.isoWhiskerRight (stageEquivalence diagram source).counitIso
      (diagram.map arrow.toLoc).toFunctor

/-- The functor from the category of `diagram` at `stage` to `Stage diagram stage` presenting each
object along the identity of `stage`. -/
def canonicalInverse (stage : Index) : diagram.obj ⟨stage⟩ ⥤ Stage diagram stage where
  obj object := ⟨stage, 𝟙 stage, object⟩
  map morphism := InducedCategory.homMk
    ((diagram.map (𝟙 (LocallyDiscrete.mk stage))).toFunctor.map morphism)
  map_id object := by
    apply InducedCategory.hom_ext
    exact (diagram.map (𝟙 (LocallyDiscrete.mk stage))).toFunctor.map_id object
  map_comp first second := by
    apply InducedCategory.hom_ext
    exact (diagram.map (𝟙 (LocallyDiscrete.mk stage))).toFunctor.map_comp first second

/-- The isomorphism from the identity of `Stage diagram stage` to `evaluation` followed by
`canonicalInverse`, given by the unit isomorphism of `diagram`. -/
def canonicalUnitIso (stage : Index) :
    𝟭 (Stage diagram stage) ≅ evaluation diagram stage ⋙ canonicalInverse diagram stage :=
  NatIso.ofComponents
    (fun object ↦ InducedCategory.isoMk
      (((Cat.Hom.toNatIso (diagram.mapId ⟨stage⟩)).app
        ((evaluation diagram stage).obj object)).symm)) (by
      intro source target morphism
      apply InducedCategory.hom_ext
      exact (Cat.Hom.toNatIso (diagram.mapId ⟨stage⟩)).inv.naturality morphism.hom)

/-- The equivalence between `Stage diagram stage` and the category of `diagram` at `stage` with
functor `evaluation`, inverse `canonicalInverse`, and counit the unit isomorphism of `diagram`. -/
def canonicalStageEquivalence (stage : Index) :
    Stage diagram stage ≌ diagram.obj ⟨stage⟩ where
  functor := evaluation diagram stage
  inverse := canonicalInverse diagram stage
  unitIso := canonicalUnitIso diagram stage
  counitIso := Cat.Hom.toNatIso (diagram.mapId ⟨stage⟩)
  functor_unitIso_comp object :=
    (Cat.Hom.toNatIso (diagram.mapId ⟨stage⟩)).inv_hom_id_app
      ((evaluation diagram stage).obj object)

/-- Under the equivalences `canonicalStageEquivalence`, the transition functor of
`strictDiagram diagram` along `arrow` is isomorphic to that of `diagram`. -/
def canonicalTransitionIso {source target : Index} (arrow : source ⟶ target) :
    (canonicalStageEquivalence diagram source).inverse ⋙
        ((strictDiagram diagram).map arrow).toFunctor ⋙
        (canonicalStageEquivalence diagram target).functor ≅
      (diagram.map arrow.toLoc).toFunctor :=
  Functor.isoWhiskerLeft (canonicalStageEquivalence diagram source).inverse
      (pushEvaluationIso diagram arrow) ≪≫
    Functor.isoWhiskerRight (canonicalStageEquivalence diagram source).counitIso
      (diagram.map arrow.toLoc).toFunctor

/-- Under the equivalences `canonicalStageEquivalence`, the transition functor of
`strictDiagram diagram` along `arrow` agrees on objects with that of `diagram`. -/
lemma canonicalTransitionObject {source target : Index} (arrow : source ⟶ target)
    (object : diagram.obj ⟨source⟩) :
    ((canonicalStageEquivalence diagram source).inverse ⋙
      ((strictDiagram diagram).map arrow).toFunctor ⋙
      (canonicalStageEquivalence diagram target).functor).obj object =
        (diagram.map arrow.toLoc).toFunctor.obj object := by
  change (diagram.map (𝟙 source ≫ arrow).toLoc).toFunctor.obj object = _
  simp

set_option linter.flexible false in
-- the rewrites below act on the goal `simp` has just unfolded
/-- The components of `canonicalTransitionIso` are the `eqToHom` of the equalities
`canonicalTransitionObject`. -/
lemma canonicalTransitionIso_hom_app {source target : Index} (arrow : source ⟶ target)
    (object : diagram.obj ⟨source⟩) :
    (canonicalTransitionIso diagram arrow).hom.app object =
      eqToHom (canonicalTransitionObject diagram arrow object) := by
  simp [canonicalTransitionIso, canonicalStageEquivalence, canonicalInverse,
    pushEvaluationIso, comparison, Cat.Hom.toNatIso,
    diagram.mapComp_id_left_hom_app, Strict.leftUnitor_eqToIso,
    PrelaxFunctor.map₂_eqToHom]
  rw [← Functor.map_comp]
  simp

/-- Under the equivalences `canonicalStageEquivalence`, the transition functor of
`strictDiagram diagram` along `arrow` equals that of `diagram`. -/
lemma canonicalTransition_eq {source target : Index} (arrow : source ⟶ target) :
    (canonicalStageEquivalence diagram source).inverse ⋙
      ((strictDiagram diagram).map arrow).toFunctor ⋙
      (canonicalStageEquivalence diagram target).functor =
        (diagram.map arrow.toLoc).toFunctor :=
  CategoryTheory.Functor.ext_of_iso (canonicalTransitionIso diagram arrow)
    (canonicalTransitionObject diagram arrow) (canonicalTransitionIso_hom_app diagram arrow)

set_option linter.flexible false in
-- the subsequent `rw` rewrites in the goal `simp` has just unfolded
/-- The unit coherence of `canonicalTransitionIso`: at the identity of `stage` it is the composite
of the identity transport of `strictDiagram diagram`, the counit of `canonicalStageEquivalence`
and the inverse unit isomorphism of `diagram`. -/
lemma canonicalTransition_id (stage : Index) (object : diagram.obj ⟨stage⟩) :
    let mapIdIso : ((strictDiagram diagram).map (𝟙 stage)).toFunctor ≅
        𝟭 ((strictDiagram diagram).obj stage) :=
      eqToIso (congrArg Cat.Hom.toFunctor ((strictDiagram diagram).map_id stage))
    (canonicalStageEquivalence diagram stage).functor.map
        (mapIdIso.hom.app ((canonicalStageEquivalence diagram stage).inverse.obj object)) ≫
      (canonicalStageEquivalence diagram stage).counitIso.hom.app object ≫
      (diagram.mapId ⟨stage⟩).inv.toNatTrans.app object =
        (canonicalTransitionIso diagram (𝟙 stage)).hom.app object := by
  dsimp only
  rw [canonicalTransitionIso_hom_app]
  simp [canonicalStageEquivalence, canonicalInverse]
  rw [induced_eqToHom]

/-- Conjugating the transport along an equality `first = alternate` by the composition
isomorphisms of `diagram` with `second` gives the transport along
`first ≫ second = alternate ≫ second`. -/
@[reassoc]
lemma mapComp_hom_transport {source middle target : LocallyDiscrete Index}
    {first alternate : source ⟶ middle} (equality : first = alternate)
    (second : middle ⟶ target) (object : diagram.obj source) :
    (diagram.mapComp first second).hom.toNatTrans.app object ≫
        (diagram.map second).toFunctor.map
          (eqToHom (congrArg (fun arrow ↦ (diagram.map arrow).toFunctor.obj object) equality)) ≫
        (diagram.mapComp alternate second).inv.toNatTrans.app object =
      eqToHom (congrArg (fun arrow ↦
        (diagram.map (arrow ≫ second)).toFunctor.obj object) equality) := by
  subst alternate
  simp

set_option linter.flexible false in
-- the rewrites below act on the goal `simp` has just unfolded
/-- The composition coherence of `canonicalTransitionIso`: along `first ≫ second` it is the
composite of the composition transport of `strictDiagram diagram`, the unit of
`canonicalStageEquivalence`, the isomorphisms along `second` and `first`, and the inverse
composition isomorphism of `diagram`. -/
lemma canonicalTransition_comp {source middle target : Index}
    (first : source ⟶ middle) (second : middle ⟶ target) (object : diagram.obj ⟨source⟩) :
    let mapCompIso : ((strictDiagram diagram).map (first ≫ second)).toFunctor ≅
        ((strictDiagram diagram).map first).toFunctor ⋙
          ((strictDiagram diagram).map second).toFunctor :=
      eqToIso (congrArg Cat.Hom.toFunctor ((strictDiagram diagram).map_comp first second))
    let representative := (canonicalStageEquivalence diagram source).inverse.obj object
    let intermediate := (canonicalStageEquivalence diagram middle).functor.obj
      (((strictDiagram diagram).map first).toFunctor.obj representative)
    (canonicalStageEquivalence diagram target).functor.map (mapCompIso.hom.app representative) ≫
      (canonicalStageEquivalence diagram target).functor.map
        (((strictDiagram diagram).map second).toFunctor.map
          ((canonicalStageEquivalence diagram middle).unitIso.hom.app
            (((strictDiagram diagram).map first).toFunctor.obj representative))) ≫
      (canonicalTransitionIso diagram second).hom.app intermediate ≫
      (diagram.map second.toLoc).toFunctor.map ((canonicalTransitionIso diagram first).hom.app
        object) ≫
      (diagram.mapComp first.toLoc second.toLoc).inv.toNatTrans.app object =
        (canonicalTransitionIso diagram (first ≫ second)).hom.app object := by
  dsimp only
  simp only [canonicalTransitionIso_hom_app]
  simp [canonicalStageEquivalence, canonicalInverse, canonicalUnitIso,
    strictDiagram, push, comparison, Cat.Hom.toNatIso,
    diagram.mapComp_id_left_inv_app, Strict.leftUnitor_eqToIso,
    PrelaxFunctor.map₂_eqToHom, Category.assoc, ← Functor.map_comp_assoc]
  rw [mapComp_hom_transport diagram (Strict.id_comp first.toLoc) second.toLoc object]
  simp


end Strictification

end PseudoCoherence

end

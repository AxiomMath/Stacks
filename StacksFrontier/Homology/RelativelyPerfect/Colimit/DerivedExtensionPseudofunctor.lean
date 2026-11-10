module

public import StacksFrontier.Homology.RelativelyPerfect.Colimit.HomComplexColimit
import all StacksFrontier.Homology.RelativelyPerfect.Colimit.ExtensionScalars
import all StacksFrontier.Homology.RelativelyPerfect.Colimit.RingColimit
import all StacksFrontier.Homology.RelativelyPerfect.Colimit.ComplexDescent
import all StacksFrontier.Homology.RelativelyPerfect.Colimit.HomComplexColimit

/-!
# Derived extension of scalars as a pseudofunctor

The stage colimit of derived morphism groups, derived extension of scalars as a pseudofunctor,
relative perfection under base change, and split pseudofunctors and their naturality.

This is part 7 of 10 of `StacksFrontier.Homology.RelativelyPerfect.Colimit`.
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

section StageHomColimit

attribute [local instance] CochainComplex.HomComplex.Cochain.isScalarTower

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


-- elaborating the composite natural transformations of derived functors below
set_option backward.isDefEq.respectTransparency false in
include hcomp in
private def isColimit_stage_derivedHomFunctor
    {R₀ : Type uR} [CommRing R₀]
    {I : Type uI} [Category.{uJ} I] [IsFiltered I]
    (F : I ⥤ CommAlgCat.{uR} R₀) (c : Cocone F)
    (hc : IsColimit ((CommAlgCat.uliftFunctor.{max uI uJ, uR, uR} R₀).mapCocone c))
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀] [Module.Flat R₀ A₀]
    (D₀ : DerivedTensoringDatum.{uR, max uR uA uM} R₀)
    (K₀ L₀ : DerivedCategory (ModuleCat.{max uR uA uM} A₀))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K₀)
    (hL : HasFiniteTorDimension D₀.tensor D₀.comparison D₀.isLeftDerived
      ((ModuleCat.restrictScalars (algebraMap R₀ A₀)).mapDerivedCategory.obj L₀)) :
    let W := (ModuleCat.restrictScalars.{max uR uA uM}
      (ULift.ringEquiv.toRingHom : ULift.{uR} A₀ →+* A₀)).mapDerivedCategory
    IsColimit ((derivedHomFunctor.{max uR uA, uM} comp hcomp (W.obj K₀) (W.obj L₀)).mapCocone
      (stageUnderCocone c A₀)) := by
  classical
  intro W
  apply Classical.choice
  obtain ⟨P, Q, ⟨eP⟩, ⟨eQ⟩, ⟨d, hPd⟩, hP, ⟨a, b, hQa, hQb⟩, hQ⟩ :=
    exists_bounded_homComplex_representatives.{uR, uA, uM} D₀ K₀ L₀ hK hL
  refine ⟨?_⟩
  let Res := ModuleCat.restrictScalars.{max uR uA uM}
    (ULift.ringEquiv.toRingHom : ULift.{uR} A₀ →+* A₀)
  let P' : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{uR} A₀)) ℤ :=
    (Res.mapHomologicalComplex (.up ℤ)).obj P
  let Q' : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{uR} A₀)) ℤ :=
    (Res.mapHomologicalComplex (.up ℤ)).obj Q
  have := hPd
  have := hQa
  have := hQb
  have : P'.IsStrictlyLE d := inferInstance
  have : Q'.IsStrictlyGE a := inferInstance
  have : Q'.IsStrictlyLE b := inferInstance
  have (n : ℤ) : Module.Free A₀ (P.X n) := (hP n).2
  have (n : ℤ) : Module.Finite A₀ (P.X n) := (hP n).1
  have (n : ℤ) : Module.Free (ULift.{uR} A₀) (P'.X n) :=
    free_restrictScalars_of_ringEquiv ULift.ringEquiv (P.X n)
  have (n : ℤ) : Module.Finite (ULift.{uR} A₀) (P'.X n) :=
    finite_restrictScalars_of_ringEquiv ULift.ringEquiv (P.X n)
  have (n : ℤ) : Module.Flat R₀ ((ModuleCat.restrictScalars
      (algebraMap R₀ (ULift.{uR} A₀))).obj (Q'.X n)) := by
    have := hQ n
    let e := ((ModuleCat.restrictScalarsComp'
      (algebraMap R₀ (ULift.{uR} A₀))
      (ULift.ringEquiv.toRingHom : ULift.{uR} A₀ →+* A₀)
      (algebraMap R₀ A₀) (by ext r; rfl)).symm.app (Q.X n))
    exact Module.Flat.of_linearEquiv e.toLinearEquiv
  let eP' : DerivedCategory.Q.obj P' ≅ W.obj K₀ :=
    (Res.mapDerivedCategoryFactors.app P).symm ≪≫ W.mapIso eP
  let eQ' : DerivedCategory.Q.obj Q' ≅ W.obj L₀ :=
    (Res.mapDerivedCategoryFactors.app Q).symm ≪≫ W.mapIso eQ
  have hF (i : I) : IsIso ((totalDerivedExtensionScalars.{max uR uA, max uR uA, uM}
      ((stageUnderFunctor F A₀).obj i).hom.hom).comparison.app Q') :=
    isIso_tensorBaseChange_comparison_app_of_flat.{uR, uA, uM} A₀ (F.obj i) Q' b
  have : IsIso ((totalDerivedExtensionScalars.{max uR uA, max uR uA, uM}
      (stageUnderCocone c A₀).pt.hom.hom).comparison.app Q') :=
    isIso_tensorBaseChange_comparison_app_of_flat.{uR, uA, uM} A₀ c.pt Q' b
  apply isColimit_derivedHomFunctor_of_iso.{uI, uJ, max uR uA, uM} comp hcomp
    (stageUnderFunctor F A₀) (stageUnderCocone c A₀) eP' eQ'
  exact isColimit_derivedHomFunctor_of_representatives.{uI, uJ, max uR uA, uM} comp hcomp
    (stageUnderFunctor F A₀) (stageUnderCocone c A₀)
    (isColimit_stageUnderCocone_forget hc A₀) P' Q' a b d hF

end StageHomColimit

section DerivedExtensionPseudofunctor

universe u v
open scoped CategoryTheory.Bicategory

variable
    (comp : ∀ {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
      (f : A →+* B) (g : B →+* C),
      (totalDerivedExtensionScalars.{u, u, v} f).functor ⋙
        (totalDerivedExtensionScalars.{u, u, v} g).functor ≅
        (totalDerivedExtensionScalars.{u, u, v} (g.comp f)).functor)
    (hcomp : ∀ {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
      (f : A →+* B) (g : B →+* C)
      (P : CochainComplex (ModuleCat.{max u v} A) ℤ),
      (comp f g).hom.app (DerivedCategory.Q.obj P) ≫
        (totalDerivedExtensionScalars.{u, u, v} (g.comp f)).comparison.app P =
        (totalDerivedExtensionScalars.{u, u, v} g).functor.map
          ((totalDerivedExtensionScalars.{u, u, v} f).comparison.app P) ≫
          (totalDerivedExtensionScalars.{u, u, v} g).comparison.app
            (((ModuleCat.extendScalars.{u, u, max u v} f).mapHomologicalComplex (.up ℤ)).obj P) ≫
          (extensionOfScalarsComplexComp.{u, v} f g).inv.app P)

include hcomp in
private theorem derivedExtensionScalarsComp_id_left
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (X : DerivedCategory (ModuleCat.{max u v} A)) :
    (totalDerivedExtensionScalars.{u, u, v} f).functor.map
        ((derivedExtensionScalarsId.{u, v} A).hom.app X) ≫
      (comp (RingHom.id A) f).hom.app X = 𝟙 _ := by
  let T := totalDerivedExtensionScalars.{u, u, v} f
  let U := totalDerivedExtensionScalars.{u, u, v} (RingHom.id A)
  let e := derivedExtensionScalarsId.{u, v} A
  have hc := derivedExtensionScalarsComp_assoc comp hcomp (RingHom.id A) (RingHom.id A) f X
  have hu := derivedExtensionScalarsComp_id comp hcomp (RingHom.id A) X
  have hη : U.functor.map (e.hom.app X) = e.hom.app (U.functor.obj X) := by
    apply (cancel_epi (e.hom.app X)).mp
    exact (e.hom.naturality (e.hom.app X)).symm
  have hL : (comp (RingHom.id A) f).hom.app (U.functor.obj X) =
      T.functor.map ((comp (RingHom.id A) (RingHom.id A)).hom.app X) :=
    ((cancel_mono ((comp (RingHom.id A) f).hom.app X)).mp hc).symm
  have hleft : (comp (RingHom.id A) f).hom.app X ≫ T.functor.map (e.hom.app X) = 𝟙 _ := by
    calc
      _ = T.functor.map (U.functor.map (e.hom.app X)) ≫
          (comp (RingHom.id A) f).hom.app (U.functor.obj X) :=
        ((comp (RingHom.id A) f).hom.naturality (e.hom.app X)).symm
      _ = T.functor.map (e.hom.app (U.functor.obj X) ≫
          (comp (RingHom.id A) (RingHom.id A)).hom.app X) := by
        rw [hη, hL, T.functor.map_comp]
      _ = 𝟙 _ := by rw [hu, T.functor.map_id]
  apply (cancel_mono (T.functor.map (e.hom.app X))).mp
  rw [Category.assoc, hleft]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

set_option backward.isDefEq.respectTransparency false in
include hcomp in
private def derivedExtensionScalarsPseudofunctor :
    LocallyDiscrete CommRingCat.{u} ⥤ᵖ Cat.{max u v + 1, max u v + 1} :=
  LocallyDiscrete.mkPseudofunctor
    (fun A : CommRingCat.{u} ↦ Cat.of (DerivedCategory (ModuleCat.{max u v} A)))
    (fun f ↦ (totalDerivedExtensionScalars.{u, u, v} f.hom).functor.toCatHom)
    (fun A ↦ Cat.Hom.isoMk (derivedExtensionScalarsId.{u, v} A).symm)
    (fun f g ↦ Cat.Hom.isoMk (comp f.hom g.hom).symm)
    (by
      intro A B C D f g h
      ext X
      change (comp (g.hom.comp f.hom) h.hom).inv.app X ≫
        (totalDerivedExtensionScalars.{u, u, v} h.hom).functor.map
          ((comp f.hom g.hom).inv.app X) ≫ 𝟙 _ ≫
        (comp g.hom h.hom).hom.app
          ((totalDerivedExtensionScalars.{u, u, v} f.hom).functor.obj X) ≫
        (comp f.hom (h.hom.comp g.hom)).hom.app X = 𝟙 _
      rw [Category.id_comp, ← derivedExtensionScalarsComp_assoc comp hcomp f.hom g.hom h.hom X]
      simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
      rw [(totalDerivedExtensionScalars.{u, u, v} h.hom).functor.map_id]
      simp only [Category.id_comp, Iso.inv_hom_id_app])
    (by
      intro A B f
      ext X
      change (comp (RingHom.id A) f.hom).inv.app X ≫
        (totalDerivedExtensionScalars.{u, u, v} f.hom).functor.map
          ((derivedExtensionScalarsId.{u, v} A).inv.app X) ≫ 𝟙 _ = 𝟙 _
      have hh := derivedExtensionScalarsComp_id_left comp hcomp f.hom X
      apply (cancel_epi ((totalDerivedExtensionScalars.{u, u, v} f.hom).functor.map
        ((derivedExtensionScalarsId.{u, v} A).hom.app X) ≫
          (comp (RingHom.id A) f.hom).hom.app X)).mp
      simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp,
        Iso.hom_inv_id_app, Category.comp_id]
      exact ((totalDerivedExtensionScalars.{u, u, v} f.hom).functor.map_id _).trans
        hh.symm)
    (by
      intro A B f
      ext X
      change (comp f.hom (RingHom.id B)).inv.app X ≫
        (derivedExtensionScalarsId.{u, v} B).inv.app
          ((totalDerivedExtensionScalars.{u, u, v} f.hom).functor.obj X) ≫ 𝟙 _ = 𝟙 _
      have hh := derivedExtensionScalarsComp_id comp hcomp f.hom X
      apply (cancel_epi ((derivedExtensionScalarsId.{u, v} B).hom.app
          ((totalDerivedExtensionScalars.{u, u, v} f.hom).functor.obj X) ≫
          (comp f.hom (RingHom.id B)).hom.app X)).mp
      simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app,
        Category.comp_id]
      exact hh.symm)

set_option backward.isDefEq.respectTransparency false in
include hcomp in
private lemma derivedDiagram_mapId_inv
    {Index : Type uI} [Category.{uJ} Index] (diagram : Index ⥤ CommRingCat.{u})
    (stage : Index) (object : DerivedCategory (ModuleCat.{max u v} (diagram.obj stage))) :
    (((diagram.toPseudofunctor.comp (derivedExtensionScalarsPseudofunctor comp hcomp)).mapId
      ⟨stage⟩).inv.toNatTrans.app object) =
      (derivedExtensionScalarsId.{u, v} (diagram.obj stage)).hom.app object ≫
        (derivedExtensionScalarsCongr.{u, v}
          (congrArg CommRingCat.Hom.hom (diagram.map_id stage).symm)).hom.app object := by
  change (derivedExtensionScalarsId.{u, v} (diagram.obj stage)).hom.app object ≫
      ((derivedExtensionScalarsPseudofunctor comp hcomp).map₂
        (diagram.toPseudofunctor.mapId ⟨stage⟩).inv).toNatTrans.app object = _
  congr 1
  dsimp [Functor.toPseudofunctor, pseudofunctorOfIsLocallyDiscrete]
  rw [PrelaxFunctor.map₂_eqToHom, Cat.Hom₂.eqToHom_toNatTrans]
  rfl

set_option backward.isDefEq.respectTransparency false in
include hcomp in
private lemma derivedDiagram_mapComp_inv
    {Index : Type uI} [Category.{uJ} Index] (diagram : Index ⥤ CommRingCat.{u})
    {source middle target : Index} (first : source ⟶ middle) (second : middle ⟶ target)
    (object : DerivedCategory (ModuleCat.{max u v} (diagram.obj source))) :
    (((diagram.toPseudofunctor.comp (derivedExtensionScalarsPseudofunctor comp hcomp)).mapComp
      first.toLoc second.toLoc).inv.toNatTrans.app object) =
      (comp (diagram.map first).hom (diagram.map second).hom).hom.app object ≫
        (derivedExtensionScalarsCongr.{u, v}
          (congrArg CommRingCat.Hom.hom (diagram.map_comp first second).symm)).hom.app object := by
  change (comp (diagram.map first).hom (diagram.map second).hom).hom.app object ≫
      ((derivedExtensionScalarsPseudofunctor comp hcomp).map₂
        (diagram.toPseudofunctor.mapComp first.toLoc second.toLoc).inv).toNatTrans.app object = _
  congr 1
  dsimp [Functor.toPseudofunctor, pseudofunctorOfIsLocallyDiscrete, Quiver.Hom.toLoc]
  rw [PrelaxFunctor.map₂_eqToHom, Cat.Hom₂.eqToHom_toNatTrans]
  rfl

end DerivedExtensionPseudofunctor

section RelativePerfectionBaseChange

universe uS uB

set_option backward.isDefEq.respectTransparency false in
private def extendScalarsAlgebraMapEquiv {A : Type uA} {B : Type uB}
    [CommRing A] [CommRing B] [Algebra A B] (M : ModuleCat.{uM} A) :
    (ModuleCat.extendScalars (algebraMap A B)).obj M ≃ₗ[B] B ⊗[A] M := by
  let eB : (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) ≃ₗ[A] B :=
    { AddEquiv.refl B with
      map_smul' := fun a b ↦ (Algebra.smul_def (R := A) (A := B) a b).symm }
  let e := TensorProduct.congr eB (LinearEquiv.refl A M)
  exact { e.toAddEquiv with
    map_smul' := by
      intro b x
      change e (b • x) = b • e x
      induction x using TensorProduct.inductionOn with
      | tmul c m => rw [ModuleCat.ExtendScalars.smul_tmul]; simp [e, eB, TensorProduct.smul_tmul']
      | add x y hx hy => simpa only [smul_add, map_add] using congrArg₂ (· + ·) hx hy }

private lemma finitePresentation_extendScalars {A : Type uA} {B : Type uB}
    [CommRing A] [CommRing B] (f : A →+* B)
    (M : ModuleCat.{uM} A) [Module.FinitePresentation A M] :
    Module.FinitePresentation B ((ModuleCat.extendScalars f).obj M) := by
  let := f.toAlgebra
  exact Module.FinitePresentation.of_equiv (extendScalarsAlgebraMapEquiv M).symm

set_option backward.isDefEq.respectTransparency false in
private lemma flat_extendScalars_of_isPushout {R : Type uR} {A : Type uA} {S : Type uS} {B : Type
  uB}
    [CommRing R] [CommRing A] [CommRing S] [CommRing B]
    [Algebra R A] [Algebra R S] [Algebra R B] [Algebra A B] [Algebra S B]
    [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B]
    (M : ModuleCat.{uM} A)
    [Module.Flat R ((ModuleCat.restrictScalars (algebraMap R A)).obj M)] :
    Module.Flat S ((ModuleCat.restrictScalars (algebraMap S B)).obj
      ((ModuleCat.extendScalars (algebraMap A B)).obj M)) := by
  let : Module R M := Module.compHom M (algebraMap R A)
  have : Module.Flat R M := inferInstanceAs
    (Module.Flat R ((ModuleCat.restrictScalars (algebraMap R A)).obj M))
  let : IsScalarTower R A M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let e := extendScalarsAlgebraMapEquiv (B := B) M
  let e' : ((ModuleCat.restrictScalars (algebraMap S B)).obj
      ((ModuleCat.extendScalars (algebraMap A B)).obj M)) ≃ₗ[S] B ⊗[A] M :=
    { e.toAddEquiv with
      map_smul' := by
        intro s x
        change e ((algebraMap S B s) • x) = s • e x
        simp only [map_smul, IsScalarTower.algebraMap_smul] }
  exact Module.Flat.of_linearEquiv
    (e'.trans (Algebra.IsPushout.cancelBaseChange R S A B M))


-- elaborating the composite natural transformations of derived functors below
set_option backward.isDefEq.respectTransparency false in
private theorem isRelativelyPerfect_derivedExtensionScalars_of_isPushout
    {R S : Type uR} {A B : Type uA}
    [CommRing R] [CommRing A] [CommRing S] [CommRing B]
    [Algebra R A] [Algebra R S] [Algebra R B] [Algebra A B] [Algebra S B]
    [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    [Module.Flat S B] [Algebra.FinitePresentation S B]
    (D : DerivedTensoringDatum.{uR, max uR uA uM} R)
    (D' : DerivedTensoringDatum.{uR, max uR uA uM} S)
    (L : DerivedCategory (ModuleCat.{max uR uA uM} A) ⥤
      DerivedCategory (ModuleCat.{max uR uA uM} B))
    (α : DerivedCategory.Q ⋙ L ⟶
      extensionOfScalarsComplexGeneral.{uA, max uR uM, uA} (algebraMap A B))
    [L.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} A) (.up ℤ))]
    (K : DerivedCategory (ModuleCat.{max uR uA uM} A))
    (hK : IsRelativelyPerfect.{uR, uA, uM} D.tensor D.comparison D.isLeftDerived K) :
    IsRelativelyPerfect.{uR, uA, uM} D'.tensor D'.comparison D'.isLeftDerived
      (L.obj K) := by
  obtain ⟨P, ⟨a, ha⟩, ⟨b, hb⟩, hP, ⟨eP⟩⟩ :=
    (isRelativelyPerfect_iff_exists_bounded_flat_finitePresentation_bundled.{uR, uA, uM}
      (toKFlatDerivedTensorProduct D) K).mp hK
  have := ha
  have := hb
  have (n : ℤ) : Module.Flat R ((ModuleCat.restrictScalars (algebraMap R A)).obj (P.X n)) :=
    (hP n).1
  have (n : ℤ) : Module.FinitePresentation A (P.X n) := (hP n).2
  let Ex := ModuleCat.extendScalars.{uA, uA, max uR uA uM} (algebraMap A B)
  let Q : CochainComplex (ModuleCat.{max uR uA uM} B) ℤ := (Ex.mapHomologicalComplex (.up ℤ)).obj P
  let LR := totalDerivedExtensionScalars.{uR, uR, max uA uM} (algebraMap R S)
  let Res := ModuleCat.restrictScalars.{max uR uA uM} (algebraMap R A)
  let PR : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ :=
    (Res.mapHomologicalComplex (.up ℤ)).obj P
  have : PR.IsStrictlyLE b := inferInstance
  have (n : ℤ) : Module.Flat R (PR.X n) := hP n |>.1
  have : IsIso (LR.comparison.app PR) :=
    isIso_comparison_app_of_isStrictlyLE_flat LR PR b
  have : Algebra.IsPushout R A S B := Algebra.IsPushout.symm inferInstance
  have : LR.functor.IsLeftDerivedFunctor LR.comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (.up ℤ)) := LR.isLeftDerived
  have : IsIso (α.app P) :=
    isIso_comparison_app_of_torIndependent.{uR, uA, uR, uA, uM}
      (torIndependent_of_flat (R := R) (A := A) (B := S))
      LR.functor L LR.comparison α P
  apply (isRelativelyPerfect_iff_exists_bounded_flat_finitePresentation_bundled.{uR, uA, uM}
    (toKFlatDerivedTensorProduct D') (L.obj K)).mpr
  refine ⟨Q, ⟨a, inferInstance⟩, ⟨b, inferInstance⟩, ?_,
    ⟨(asIso (α.app P)).symm ≪≫ L.mapIso eP⟩⟩
  intro n
  exact ⟨flat_extendScalars_of_isPushout (R := R) (S := S) (B := B) (P.X n),
    finitePresentation_extendScalars (algebraMap A B) (P.X n)⟩


set_option backward.isDefEq.respectTransparency false in
theorem isRelativelyPerfect_tensorProduct_map
    {R₀ S T : Type uR} [CommRing R₀] [CommRing S] [CommRing T]
    [Algebra R₀ S] [Algebra R₀ T] (f : S →ₐ[R₀] T)
    (A₀ : Type uA) [CommRing A₀] [Algebra R₀ A₀]
    [Module.Flat R₀ A₀] [Algebra.FinitePresentation R₀ A₀]
    (D : DerivedTensoringDatum.{uR, max uR uA uM} S)
    (D' : DerivedTensoringDatum.{uR, max uR uA uM} T)
    (K : DerivedCategory (ModuleCat.{max uR uA uM} (S ⊗[R₀] A₀)))
    (hK : IsRelativelyPerfect.{uR, max uR uA, uM}
      D.tensor D.comparison D.isLeftDerived K) :
    IsRelativelyPerfect.{uR, max uR uA, uM} D'.tensor D'.comparison D'.isLeftDerived
      ((totalDerivedExtensionScalars.{max uR uA, max uR uA, uM}
        (Algebra.TensorProduct.map f (AlgHom.id R₀ A₀)).toRingHom).functor.obj K) := by
  let A := S ⊗[R₀] A₀
  let B := T ⊗[R₀] A₀
  let g := (Algebra.TensorProduct.map f (AlgHom.id R₀ A₀)).toRingHom
  let : Algebra S T := f.toRingHom.toAlgebra
  let : IsScalarTower R₀ S T := IsScalarTower.of_algebraMap_eq fun x ↦ (f.commutes x).symm
  let : Algebra A B := g.toAlgebra
  let : IsScalarTower S A B := IsScalarTower.of_algebraMap_eq fun x ↦ by
    change f x ⊗ₜ[R₀] 1 = g (x ⊗ₜ[R₀] 1)
    simp [g]
  let : Algebra.IsPushout S T A B :=
    @Algebra.IsPushout.tensorProduct_tensorProduct R₀ A₀ S T
      _ _ _ _ _ _ _ _ _ g.toAlgebra inferInstance (by
        ext x
        change g (1 ⊗ₜ[R₀] x) = 1 ⊗ₜ[R₀] x
        simp [g])
  let L := totalDerivedExtensionScalars.{max uR uA, max uR uA, uM} g
  have : L.functor.IsLeftDerivedFunctor L.comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} A) (.up ℤ)) := L.isLeftDerived
  exact isRelativelyPerfect_derivedExtensionScalars_of_isPushout.{uR, max uR uA, uM}
    (R := S) (S := T) (A := A) (B := B) D D' L.functor L.comparison K hK


end RelativePerfectionBaseChange

section SplitFiberEvaluation

universe v₁ v₂ u₁ u₂

private def splitFiberEvaluation {C : Type u₁} {X : Type u₂}
    [Category.{v₁} C] [Category.{v₂} X] (p : X ⥤ C) [p.IsPreFibered] (V : C) :
    p.SplitFiber V ⥤ p.Fiber V where
  obj o := o.toFiber
  map f := Functor.SplitFiber.toFiberHom f

private def splitFiberEquivalence {C : Type u₁} {X : Type u₂}
    [Category.{v₁} C] [Category.{v₂} X] (p : X ⥤ C) [p.IsFibered] (V : C) :
    p.SplitFiber V ≌ p.Fiber V := by
  let E := splitFiberEvaluation p V
  let hE : E.FullyFaithful :=
    { preimage := fun f ↦ Functor.SplitFiber.ofFiberHom f }
  letI : E.Full := hE.full
  letI : E.Faithful := hE.faithful
  letI : E.EssSurj := ⟨fun x ↦ ⟨⟨V, x, 𝟙 V⟩, ⟨Functor.pullbackFiberIdIso x⟩⟩⟩
  letI : E.IsEquivalence := { }
  exact E.asEquivalence

end SplitFiberEvaluation

section SplitPseudofunctor
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Bicategory
universe vI u v
variable {I : Type uI} [Category.{vI} I]

private abbrev oppositePseudofunctor (F : LocallyDiscrete I ⥤ᵖ Cat.{v, u}) :
    LocallyDiscrete Iᵒᵖᵒᵖ ⥤ᵖ Cat.{v, u} :=
  (opOpEquivalence I).functor.toPseudofunctor.comp F

private abbrev pseudofunctorFibration (F : LocallyDiscrete I ⥤ᵖ Cat.{v, u}) :=
  Pseudofunctor.CoGrothendieck.forget (oppositePseudofunctor F)

private def splitPseudofunctor (F : LocallyDiscrete I ⥤ᵖ Cat.{v, u}) :
    I ⥤ Cat.{max vI v, max uI u vI} :=
  (opOpEquivalence I).inverse ⋙ Functor.splitPresheaf (pseudofunctorFibration F)

private def splitPseudofunctorEquivalence (F : LocallyDiscrete I ⥤ᵖ Cat.{v, u}) (i : I) :
    (splitPseudofunctor F).obj i ≌ F.obj ⟨i⟩ :=
  (splitFiberEquivalence (pseudofunctorFibration F) (op i)).trans
    (Functor.Fiber.inducedFunctor
      (Pseudofunctor.CoGrothendieck.comp_const (oppositePseudofunctor F) (op i))).asEquivalence.symm

end SplitPseudofunctor

section SplitFiberNaturality

open CategoryTheory.Functor

universe v₁ v₂ u₁ u₂
variable {C : Type u₁} {X : Type u₂} [Category.{v₁} C] [Category.{v₂} X]
    (p : X ⥤ C) [p.IsFibered]

set_option backward.isDefEq.respectTransparency false in
private lemma pullbackFiberProj_eq_compIso_inv
    {U V W : C} (x : p.Fiber U) (f : V ⟶ U) (g : W ⟶ V) :
    Functor.pullbackFiberProj x f g =
      Fiber.fiberInclusion.map (Functor.pullbackFiberCompIso x f g).inv ≫
        IsPreFibered.pullbackMap (Functor.pullbackFiber p x f).2 g := by
  symm
  have hh : p.IsHomLift (𝟙 W ≫ g)
      (Fiber.fiberInclusion.map (Functor.pullbackFiberCompIso x f g).inv ≫
        IsPreFibered.pullbackMap (Functor.pullbackFiber p x f).2 g) := inferInstance
  have : p.IsHomLift g
      (Fiber.fiberInclusion.map (Functor.pullbackFiberCompIso x f g).inv ≫
        IsPreFibered.pullbackMap (Functor.pullbackFiber p x f).2 g) := by simpa using hh
  apply Functor.pullbackFiberProj_uniq x f g
  rw [Category.assoc, Functor.pullbackFiberCompIso_inv_fac]

set_option backward.isDefEq.respectTransparency false in
private def splitFiberEvaluationRestrictIso {V W : C} (g : W ⟶ V) :
    splitFiberEvaluation p V ⋙ (Functor.chosenPullbacks p).pullbackFunctor g ≅
      Functor.SplitFiber.restrict p g ⋙ splitFiberEvaluation p W :=
  NatIso.ofComponents (fun o ↦ Functor.pullbackFiberCompIso o.obj o.hom g) (by
    intro o o' α
    change Functor.pullbackFiberHom (Functor.SplitFiber.toFiberHom α) g ≫
        (Functor.pullbackFiberCompIso o'.obj o'.hom g).hom =
      (Functor.pullbackFiberCompIso o.obj o.hom g).hom ≫
        Functor.SplitFiber.restrictHom g (Functor.SplitFiber.toFiberHom α)
    apply Functor.fiber_hom_ext_of_cartesian (g ≫ o'.hom)
      (IsPreFibered.pullbackMap o'.obj.2 (g ≫ o'.hom)) inferInstance
    simp only [Functor.map_comp, Category.assoc, Functor.pullbackFiberCompIso_hom_fac,
      Functor.SplitFiber.restrictHom_fac]
    rw [pullbackFiberProj_eq_compIso_inv]
    simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id]
    rw [(Fiber.fiberInclusion : p.Fiber W ⥤ X).map_id]
    simp only [Category.id_comp]
    simpa only [Category.assoc] using
      congrArg (fun t ↦ t ≫ o'.proj)
        (Functor.pullbackFiberHom_fac (Functor.SplitFiber.toFiberHom α) g))

end SplitFiberNaturality


section CoGrothendieckNaturality

open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite
open scoped CategoryTheory.Bicategory
universe u v w t
variable {I : Type u} [Category.{v} I] (F : LocallyDiscrete Iᵒᵖ ⥤ᵖ Cat.{w, t})

set_option backward.isDefEq.respectTransparency false in
private lemma coGrothendieck_cartesianLift_naturality {V W : I} (f : W ⟶ V)
    {X Y : F.obj ⟨op V⟩} (α : X ⟶ Y) :
    (CoGrothendieck.ι F W).map ((F.map f.op.toLoc).toFunctor.map α) ≫
        CoGrothendieck.cartesianLift Y f =
      CoGrothendieck.cartesianLift X f ≫ (CoGrothendieck.ι F V).map α := by
  ext
  · change 𝟙 W ≫ f = f ≫ 𝟙 V
    exact (Category.id_comp f).trans (Category.comp_id f).symm
  · simp only [CoGrothendieck.ι, CoGrothendieck.categoryStruct_comp_base, op_comp,
      Quiver.Hom.comp_toLoc, CoGrothendieck.categoryStruct_comp_fiber,
      op_id, Quiver.Hom.id_toLoc, Cat.Hom.id_toFunctor,
      Category.assoc, map_comp]
    rw [F.whiskerRight_mapId_inv_app, F.whiskerLeft_mapId_inv_app]
    simp [Bicategory.Strict.leftUnitor_eqToIso, Bicategory.Strict.rightUnitor_eqToIso,
      PrelaxFunctor.map₂_eqToHom]

set_option backward.isDefEq.respectTransparency false in
private def coGrothendieckPullbackObjIso {V W : I} (f : W ⟶ V) (X : F.obj ⟨op V⟩) :
    Functor.pullbackFiber (CoGrothendieck.forget F)
        ((Fiber.inducedFunctor (CoGrothendieck.comp_const F V)).obj X) f ≅
      (Fiber.inducedFunctor (CoGrothendieck.comp_const F W)).obj
        ((F.map f.op.toLoc).toFunctor.obj X) := by
  letI := CoGrothendieck.isStronglyCartesian_homCartesianLift X f
  exact Functor.fiberIsoOfCartesian f
    (IsPreFibered.pullbackMap ((Fiber.inducedFunctor (CoGrothendieck.comp_const F V)).obj X).2 f)
    (CoGrothendieck.cartesianLift X f) inferInstance inferInstance

set_option backward.isDefEq.respectTransparency false in
private lemma coGrothendieckPullbackObjIso_fac {V W : I} (f : W ⟶ V) (X : F.obj ⟨op V⟩) :
    Fiber.fiberInclusion.map (coGrothendieckPullbackObjIso F f X).hom ≫
        CoGrothendieck.cartesianLift X f =
      IsPreFibered.pullbackMap ((Fiber.inducedFunctor (CoGrothendieck.comp_const F V)).obj X).2 f :=
  Functor.fiberIsoOfCartesian_hom_fac _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
private def coGrothendieckPullbackIso {V W : I} (f : W ⟶ V) :
    Fiber.inducedFunctor (CoGrothendieck.comp_const F V) ⋙
        (Functor.chosenPullbacks (CoGrothendieck.forget F)).pullbackFunctor f ≅
      (F.map f.op.toLoc).toFunctor ⋙ Fiber.inducedFunctor (CoGrothendieck.comp_const F W) :=
  NatIso.ofComponents (coGrothendieckPullbackObjIso F f) (by
    intro X Y α
    let := CoGrothendieck.isStronglyCartesian_homCartesianLift Y f
    apply Functor.fiber_hom_ext_of_cartesian f (CoGrothendieck.cartesianLift Y f) inferInstance
    change Fiber.fiberInclusion.map
        (Functor.pullbackFiberHom ((Fiber.inducedFunctor (CoGrothendieck.comp_const F V)).map α) f ≫
          (coGrothendieckPullbackObjIso F f Y).hom) ≫ CoGrothendieck.cartesianLift Y f =
      Fiber.fiberInclusion.map ((coGrothendieckPullbackObjIso F f X).hom ≫
        (Fiber.inducedFunctor (CoGrothendieck.comp_const F W)).map
          ((F.map f.op.toLoc).toFunctor.map α)) ≫ CoGrothendieck.cartesianLift Y f
    simp only [Functor.map_comp, Category.assoc, coGrothendieckPullbackObjIso_fac]
    rw [Functor.pullbackFiberHom_fac]
    change _ = Fiber.fiberInclusion.map (coGrothendieckPullbackObjIso F f X).hom ≫
      (CoGrothendieck.ι F W).map ((F.map f.op.toLoc).toFunctor.map α) ≫
      CoGrothendieck.cartesianLift Y f
    rw [coGrothendieck_cartesianLift_naturality, ← Category.assoc,
      coGrothendieckPullbackObjIso_fac]
    rfl)


end CoGrothendieckNaturality

section SplitPseudofunctorNaturality
open CategoryTheory CategoryTheory.Functor CategoryTheory.Pseudofunctor Opposite
open scoped CategoryTheory.Bicategory
universe vI u v
variable {I : Type uI} [Category.{vI} I]
set_option backward.isDefEq.respectTransparency false in
private def splitPseudofunctorMapIso (F : LocallyDiscrete I ⥤ᵖ Cat.{v, u})
    {i j : I} (f : i ⟶ j) :
    (splitPseudofunctorEquivalence F i).functor ⋙ (F.map f.toLoc).toFunctor ≅
      ((splitPseudofunctor F).map f).toFunctor ⋙
        (splitPseudofunctorEquivalence F j).functor := by
  let p := pseudofunctorFibration F
  let ei := (Fiber.inducedFunctor
    (CoGrothendieck.comp_const (oppositePseudofunctor F) (op i))).asEquivalence
  let ej := (Fiber.inducedFunctor
    (CoGrothendieck.comp_const (oppositePseudofunctor F) (op j))).asEquivalence
  let h := coGrothendieckPullbackIso (oppositePseudofunctor F) f.op
  let T := (F.map f.toLoc).toFunctor
  let B := (Functor.chosenPullbacks p).pullbackFunctor f.op
  let Ei := splitFiberEvaluation p (op i)
  let Ej := splitFiberEvaluation p (op j)
  let R := Functor.SplitFiber.restrict p f.op
  let h' := ((h.isoInverseComp (G := ei)) ≪≫
    (Functor.associator ei.inverse T ej.functor).symm).compInverseIso (H := ej)
  exact (Functor.associator Ei ei.inverse T) ≪≫
    (isoWhiskerLeft Ei h'.symm) ≪≫
    (Functor.associator Ei B ej.inverse).symm ≪≫
    (isoWhiskerRight (splitFiberEvaluationRestrictIso p f.op) ej.inverse) ≪≫
    (Functor.associator R Ej ej.inverse)
end SplitPseudofunctorNaturality

section SmallSplitPseudofunctorNaturality
open CategoryTheory CategoryTheory.Functor
open scoped CategoryTheory.Bicategory
universe vI u v w
variable {I : Type uI} [Category.{vI} I]
set_option backward.isDefEq.respectTransparency false in
private def smallSplitPseudofunctorMapIso (F : LocallyDiscrete I ⥤ᵖ Cat.{v, u})
    {i j : I} (f : i ⟶ j) :
    (AsSmall.equiv.{max vI v, max uI u vI, w} (C := (splitPseudofunctor F).obj i)).symm.functor ⋙
      (splitPseudofunctorEquivalence F i).functor ⋙ (F.map f.toLoc).toFunctor ≅
    (((splitPseudofunctor F) ⋙ Cat.asSmallFunctor.{w}).map f).toFunctor ⋙
      (AsSmall.equiv.{max vI v, max uI u vI, w} (C := (splitPseudofunctor F).obj j)).symm.functor ⋙
        (splitPseudofunctorEquivalence F j).functor :=
  isoWhiskerLeft AsSmall.down (splitPseudofunctorMapIso F f)

end SmallSplitPseudofunctorNaturality

end PseudoCoherence

end

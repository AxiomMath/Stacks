module

public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothScheme
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.FormallySmoothOnObjectsAlong
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeSmooth
public import StacksFrontier.Deformation.Artin.Versality.Openness
public import StacksFrontier.Deformation.ArtinCriteria.Predeformation
public import StacksFrontier.Deformation.SchlessingerConditions.SmoothMorphisms
import all StacksFrontier.Deformation.Artin.Versality.SmoothPredeformation

/-!
# Smoothness on predeformation categories from formal smoothness on Artinian test objects

A 1-morphism `p : 𝒳 ⟶ 𝒴` of categories fibred in groupoids over the big fppf category of a
scheme `S` which is formally smooth on objects *along the spectra of Artinian local rings* —
the first-order lifting condition of Stacks 06D0 asked only for thickenings whose larger member
is the spectrum of an Artinian local ring — induces, at every finite type field-valued point of
`𝒳`, a smooth functor of predeformation categories.

Smoothness of a functor of predeformation categories is tested on small extensions in `𝒞_Λ`,
whose spectra are such thickenings; so this is the form of Stacks 07WK, case (1), whose
hypothesis is exactly what its proof uses.

## Main results

* `Deformation.Artin.isSmoothOnPredeformationCategories_of_isFormallySmoothOnObjectsAlong`:
  **Stacks 07WK**, case (1), with formal smoothness on objects asked only along the spectra of
  Artinian local rings.

## Implementation notes

The proof is the one of
`Deformation.Artin.isSmoothOnPredeformationCategories_of_isFormallySmoothOnObjects` in
`StacksFrontier/Deformation/Artin/Versality/SmoothPredeformation.lean`, with the lifting condition
applied at an Artinian test object; that file's private helper lemmas are used directly, through
`import all`. The declaration there is the special case of the one here at the full lifting
condition.

## References

* [Stacks Project, Tag 06D0](https://stacks.math.columbia.edu/tag/06D0)
* [Stacks Project, Tag 07WK](https://stacks.math.columbia.edu/tag/07WK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.Thickenings

namespace Deformation.Artin

attribute [local implicit_reducible] CategoryTheory.Bicategory.InducedBicategory
  CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.Fiber.mapOfComp CategoryTheory.Functor.Fiber.inducedFunctor
  CategoryTheory.instCategoryObj

section Main

universe u v w

attribute [local instance] categoryOfConstruction

section Base

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {iΛ : Spec (.of Λ) ⟶ S} {y₀ : 𝒴.val.obj}
  {hy₀ : (𝒴.val.p ⋙ Over.post B.inclusion).obj y₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}

/-- The scheme underlying the base of a deformation is the spectrum of its Artinian algebra. -/
theorem toScheme_obj_obj_point
    (d : DeformationObject iΛ (𝒴.val.p ⋙ Over.post B.inclusion) y₀ hy₀) :
    (BigFppfOver.toScheme B S hS).obj (𝒴.val.p.obj d.point) = Spec (.of (↑d.algebra)) := by
  show B.inclusion.obj (𝒴.val.p.obj d.point).left = _
  simpa [BigFppfOver.toScheme, BigFppfOver.forget] using congrArg (fun z => z.left) d.base

/-- The scheme underlying the base of a deformation is affine. -/
theorem isAffine_toScheme_obj_obj_point
    (d : DeformationObject iΛ (𝒴.val.p ⋙ Over.post B.inclusion) y₀ hy₀) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒴.val.p.obj d.point)) :=
  toScheme_obj_obj_point B S hS d ▸ (inferInstance : IsAffine (Spec (.of (↑d.algebra))))

/-- The base of a deformation is the spectrum of an Artinian local ring. -/
theorem isSpecArtinianLocal_obj_point
    (d : DeformationObject iΛ (𝒴.val.p ⋙ Over.post B.inclusion) y₀ hy₀) :
    BigFppfOver.IsSpecArtinianLocal B S hS (𝒴.val.p.obj d.point) :=
  ⟨.of (↑d.algebra), inferInstanceAs (IsLocalRing d.algebra),
    inferInstanceAs (IsArtinianRing d.algebra), ⟨eqToIso (toScheme_obj_obj_point B S hS d)⟩⟩

end Base

/-- **Stacks 07WK, case (1), along the spectra of Artinian local rings.** A 1-morphism of
categories fibred in groupoids over the big fppf category of a locally Noetherian scheme `S`
which is formally smooth on objects along the objects whose underlying scheme is the spectrum of
an Artinian local ring induces a smooth functor of predeformation categories at every finite type
field-valued point of the source.

This is `Deformation.Artin.isSmoothOnPredeformationCategories_of_isFormallySmoothOnObjects` with
its hypothesis weakened to the test objects the predeformation categories see; the proof is that
proof, the lifting condition being applied once, to the thickening of spectra of Artinian local
algebras underlying a small extension. -/
public theorem isSmoothOnPredeformationCategories_of_isFormallySmoothOnObjectsAlong
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) [IsLocallyNoetherian S]
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (p : 𝒳 ⟶ 𝒴)
    (hp : Stack.IsFormallySmoothOnObjectsAlong B S hS
      (BigFppfOver.IsSpecArtinianLocal B S hS) 𝒳 𝒴 p) :
    IsSmoothOnPredeformationCategories B S hS 𝒳.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor p)
      (CatFiberedInGroupoids.homFunctor_comp_p p) := by
  classical
  dsimp [IsSmoothOnPredeformationCategories]
  intro Λ k instComm instField instAlg iΛ x₀ hx₀ hLFT hQC hOpen
  let : CommRing Λ := instComm
  let : Field k := instField
  let : Algebra Λ k := instAlg
  let qX := 𝒳.val.p ⋙ Over.post B.inclusion
  let qY := 𝒴.val.p ⋙ Over.post B.inclusion
  let F := CatFiberedInGroupoids.homFunctor p
  let hF' : F ⋙ qY = qX := by
    dsimp [qX, qY]
    simpa only [Functor.assoc] using
      congrArg (fun q => q ⋙ Over.post B.inclusion)
        (CatFiberedInGroupoids.homFunctor_comp_p p)
  let Cx := predeformationCategory iΛ qX x₀ hx₀
  let hy₀ := imageBasePoint (qY := qY) iΛ qX F hF' x₀ hx₀
  let Cy := predeformationCategory iΛ qY (F.obj x₀) hy₀
  let G := mapPredeformationCategory iΛ qX qY F hF' x₀ hx₀
  have hpreX := predeformationCategory_isPredeformationCategory B hS iΛ 𝒳.val.p x₀ hx₀
    𝒳.isFiberedInGroupoids
  have hcofX : Deformation.IsCofiberedInGroupoids Cx.projection := by
    simpa [Cx, qX] using hpreX.cofibered
  have hpreY := predeformationCategory_isPredeformationCategory B hS iΛ 𝒴.val.p (F.obj x₀) hy₀
    𝒴.isFiberedInGroupoids
  have hcofY : Deformation.IsCofiberedInGroupoids Cy.projection := by
    simpa [Cy, qY, F, hy₀] using hpreY.cofibered
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  have hsmall : ∀ ⦃A₁ A₂ : ArtinianLocalAlgCat.{u, u, u} Λ k⦄ (f : A₁ ⟶ A₂),
      InfinitesimalLifting.IsSmallExtension (CommRingCat.ofHom f.hom.toRingHom) →
      ∀ (y : Cy.carrier) (x : Cx.carrier) (g : y ⟶ G.toFunctor.obj x),
        Cy.projection.IsHomLift f g →
          ∃ (x' : Cx.carrier) (lift : x' ⟶ x) (a : G.toFunctor.obj x' ⟶ y),
            Cx.projection.IsHomLift f lift ∧
              Cy.projection.IsHomLift (𝟙 A₁) a ∧ G.toFunctor.map lift = a ≫ g := by
    intro A₁ A₂ f hf y x g hg
    let dx := Cx.objects x
    let dFx := Cy.objects (G.toFunctor.obj x)
    let dy := Cy.objects y
    let m := Cy.morphisms y (G.toFunctor.obj x) g
    have hpoint : dFx.point = F.obj dx.point := G.object_point x
    have hAlg : dFx.algebra = dx.algebra :=
      inducedFunctor_algebra iΛ qX qY F hF' x₀ hx₀ G x
    -- The arrow of `𝒞_Λ` carried by `m` is a surjection with square-zero kernel.
    let eDy : Cy.projection.obj y ≅ dy.algebra := eqToIso (Cy.object_projection y)
    let eFx : Cy.projection.obj (G.toFunctor.obj x) ≅ dFx.algebra :=
      eqToIso (Cy.object_projection (G.toFunctor.obj x))
    have hdomA : Cy.projection.obj y = A₁ := IsHomLift.domain_eq Cy.projection f g
    have hcodA : Cy.projection.obj (G.toFunctor.obj x) = A₂ :=
      IsHomLift.codomain_eq Cy.projection f g
    have hA1 : dy.algebra = A₁ := (Cy.object_projection y).symm.trans hdomA
    have hAFx : dFx.algebra = A₂ :=
      (Cy.object_projection (G.toFunctor.obj x)).symm.trans hcodA
    have hA2 : dx.algebra = A₂ := hAlg.symm.trans hAFx
    have hring : m.ringHom = eDy.inv ≫ Cy.projection.map g ≫ eFx.hom := by
      simpa [m, eDy, eFx] using (Cy.morphism_projection g).symm
    have hringf : m.ringHom = eqToHom hA1 ≫ f ≫ eqToHom hAFx.symm := by
      rw [hring, IsHomLift.fac' Cy.projection f g]
      simp only [eDy, eFx, eqToIso.inv, eqToIso.hom]
      exact eqToHom_conj_collapse _ _ f _ _ _ _
    obtain ⟨hsurj, hkerSq⟩ := surjective_and_ker_sq_of_eq_iso_comp hf
      (eqToIso hA1) (eqToIso hAFx.symm) hringf
    -- The lifting problem in the site.
    let U := 𝒴.val.p.obj dFx.point
    let U' := 𝒴.val.p.obj dy.point
    let i : U ⟶ U' := 𝒴.val.p.map m.arrow
    have hUfiber : U = 𝒳.val.p.obj dx.point := by
      dsimp only [U]
      calc
        𝒴.val.p.obj dFx.point = 𝒴.val.p.obj (F.obj dx.point) :=
          congrArg (fun z => 𝒴.val.p.obj z) hpoint
        _ = 𝒳.val.p.obj dx.point :=
          congrArg (fun H => H.obj dx.point) (CatFiberedInGroupoids.homFunctor_comp_p p)
    let xFiber : 𝒳.val.p.Fiber U := ⟨dx.point, hUfiber.symm⟩
    let yFiber : 𝒴.val.p.Fiber U' := ⟨dy.point, rfl⟩
    let pU := Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p F
      (CatFiberedInGroupoids.homFunctor_comp_p p) U
    let pU' := Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p F
      (CatFiberedInGroupoids.homFunctor_comp_p p) U'
    have hmapObj : pU.obj xFiber = ⟨dFx.point, rfl⟩ := Subtype.ext hpoint.symm
    let : 𝒴.val.p.IsHomLift i m.arrow := inferInstance
    let : 𝒴.val.p.IsStronglyCartesian i m.arrow :=
      𝒴.isFiberedInGroupoids.isStronglyCartesian_homLift i m.arrow
    let targetCompare : Functor.pullbackFiber 𝒴.val.p yFiber i ≅ ⟨dFx.point, rfl⟩ :=
      Functor.fiberIsoOfCartesian i (Functor.IsPreFibered.pullbackMap yFiber.2 i) m.arrow
        inferInstance inferInstance
    let gamma : pU.obj xFiber ≅ Functor.pullbackFiber 𝒴.val.p yFiber i :=
      eqToIso hmapObj ≪≫ targetCompare.symm
    have hi : IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map i) :=
      isFirstOrderThickening_map_arrow B S hS 𝒴 m hsurj hkerSq
    unfold Stack.IsFormallySmoothOnObjectsAlong at hp
    obtain ⟨x', β, γ', hsq⟩ := hp U U' i (isAffine_toScheme_obj_obj_point B S hS dFx)
      (isAffine_toScheme_obj_obj_point B S hS dy) (isSpecArtinianLocal_obj_point B S hS dy) hi
      xFiber yFiber gamma
    -- The lifted arrow upstairs and its base.
    let pbXMap := Functor.IsPreFibered.pullbackMap x'.2 i
    let liftArrow : dx.point ⟶ x'.1 := Functor.Fiber.fiberInclusion.map β.inv ≫ pbXMap
    have hpbX : 𝒳.val.p.IsHomLift i pbXMap :=
      (Functor.IsPreFibered.pullbackMap.IsCartesian x'.2 i).toIsHomLift
    have hLift : 𝒳.val.p.IsHomLift i liftArrow := by
      have hcomp := @IsHomLift.comp _ _ _ _ 𝒳.val.p U U U'
        xFiber.1 (Functor.pullbackFiber 𝒳.val.p x' i).1 x'.1
        (𝟙 U) i (Functor.Fiber.fiberInclusion.map β.inv) pbXMap β.inv.2 hpbX
      simpa [liftArrow, Category.id_comp, Functor.Fiber.fiberInclusion] using hcomp
    have hnewBase : qX.obj x'.1 =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ dy.algebra)) ≫ iΛ) := by
      calc
        qX.obj x'.1 = (Over.post B.inclusion).obj U' :=
          congrArg (Over.post B.inclusion).obj x'.2
        _ = qY.obj dy.point := rfl
        _ = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ dy.algebra)) ≫ iΛ) := dy.base
    have hSpecAlg : Spec (.of (↑dFx.algebra)) = Spec (.of (↑dx.algebra)) :=
      congrArg (fun A : ArtinianLocalAlgCat.{u, u, u} Λ k => Spec (.of (↑A))) hAlg
    have hpostEq : qX.map liftArrow = (Over.post B.inclusion).map
        (eqToHom (IsHomLift.domain_eq 𝒳.val.p i liftArrow) ≫ i ≫
          eqToHom (IsHomLift.codomain_eq 𝒳.val.p i liftArrow).symm) := by
      show (Over.post B.inclusion).map (𝒳.val.p.map liftArrow) = _
      exact congrArg (fun t : 𝒳.val.p.obj dx.point ⟶ 𝒳.val.p.obj x'.1 =>
        (Over.post B.inclusion).map t) (IsHomLift.fac' 𝒳.val.p i liftArrow)
    have hmleft : (qY.map m.arrow).left =
        eqToHom (congrArg Over.left dFx.base) ≫
          Spec.map (CommRingCat.ofHom m.ringHom.hom.toRingHom) ≫
          eqToHom (congrArg Over.left dy.base).symm := by
      rw [← m.arrow_base]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
        Category.id_comp, Category.comp_id]
    have hLiftBase :
        eqToHom (congrArg Over.left dx.base).symm ≫ (qX.map liftArrow).left ≫
            eqToHom (congrArg Over.left hnewBase) =
          eqToHom hSpecAlg.symm ≫ Spec.map (CommRingCat.ofHom m.ringHom.hom.toRingHom) := by
      rw [hpostEq, Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map,
        show (Over.post B.inclusion).map i = qY.map m.arrow from rfl]
      simp only [Over.comp_left, Over.eqToHom_left, Category.assoc]
      rw [hmleft]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
        Category.comp_id]
    have hcast : Spec.map (CommRingCat.ofHom (m.ringHom ≫ eqToHom hAlg).hom.toRingHom) =
        eqToHom hSpecAlg.symm ≫ Spec.map (CommRingCat.ofHom m.ringHom.hom.toRingHom) := by
      have hc : ((eqToHom hAlg).hom.comp m.ringHom.hom).toRingHom =
          (eqToHom hAlg).hom.toRingHom.comp m.ringHom.hom.toRingHom :=
        rfl
      rw [← specMap_eqToHom_hom hAlg, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ArtinianLocalAlgCat.comp_hom, hc]
    have hLiftBase' :
        eqToHom (congrArg Over.left dx.base).symm ≫ (qX.map liftArrow).left ≫
            eqToHom (congrArg Over.left hnewBase) =
          Spec.map (CommRingCat.ofHom (m.ringHom ≫ eqToHom hAlg).hom.toRingHom) :=
      hLiftBase.trans hcast.symm
    -- The new deformation and the morphism down to the given one.
    let newDeformation : DeformationObject iΛ qX x₀ hx₀ :=
      dx.extend dy.algebra (m.ringHom ≫ eqToHom hAlg) x'.1 liftArrow hnewBase hLiftBase'
    let liftDataNew : DeformationMorphism iΛ qX x₀ hx₀ newDeformation dx :=
      dx.extendHom dy.algebra (m.ringHom ≫ eqToHom hAlg) x'.1 liftArrow hnewBase hLiftBase'
    let xNew : Cx.carrier := Cx.objects.symm newDeformation
    have hxNew : Cx.objects xNew = newDeformation := Cx.objects.apply_symm_apply _
    let liftData : DeformationMorphism iΛ qX x₀ hx₀ (Cx.objects xNew) dx :=
      hxNew.symm ▸ liftDataNew
    let lift : xNew ⟶ x := (Cx.morphisms xNew x).symm liftData
    have hliftData : Cx.morphisms xNew x lift = liftData := (Cx.morphisms xNew x).apply_symm_apply _
    have hAlgNew : (Cx.objects xNew).algebra = newDeformation.algebra :=
      congrArg DeformationObject.algebra hxNew
    have hdomX : (Cx.objects xNew).algebra = A₁ := hAlgNew.trans hA1
    have hliftRing0 : (Cx.morphisms xNew x lift).ringHom =
        eqToHom hAlgNew ≫ m.ringHom ≫ eqToHom hAlg := by
      rw [hliftData]
      exact deformationMorphism_ringHom_cast hxNew liftDataNew
    have hliftRing : (Cx.morphisms xNew x lift).ringHom =
        eqToHom hdomX ≫ f ≫ eqToHom hA2.symm := by
      rw [hliftRing0, hringf]
      exact eqToHom_conj_collapse _ _ f _ _ _ _
    have hLiftProp : Cx.projection.IsHomLift f lift :=
      isHomLift_of_ringHom_eq Cx f lift hdomX hA2 hliftRing
    -- The comparison isomorphism downstairs.
    have hEqPoint : Functor.Fiber.fiberInclusion.map (eqToIso hmapObj).hom =
        eqToHom hpoint.symm := by
      rw [eqToIso.hom, eqToHom_map]
    have himage : eqToHom hpoint.symm ≫ m.arrow =
        F.map liftArrow ≫ Functor.Fiber.fiberInclusion.map γ'.hom := by
      have htc : Functor.Fiber.fiberInclusion.map targetCompare.inv ≫
          Functor.IsPreFibered.pullbackMap yFiber.2 i = m.arrow :=
        Functor.fiberIsoOfCartesian_inv_fac (p := 𝒴.val.p) (b := i) (a := dy.point)
          (z := Functor.pullbackFiber 𝒴.val.p yFiber i) (z' := ⟨dFx.point, rfl⟩)
          (φ := Functor.IsPreFibered.pullbackMap yFiber.2 i) (φ' := m.arrow)
          (hφ := Functor.IsPreFibered.pullbackMap.IsCartesian _ _) (hφ' := inferInstance)
      have hfac : Functor.Fiber.fiberInclusion.map gamma.hom ≫
          Functor.IsPreFibered.pullbackMap yFiber.2 i =
            F.map (Functor.Fiber.fiberInclusion.map β.inv ≫ pbXMap) ≫
              Functor.Fiber.fiberInclusion.map γ'.hom := by
        refine pullbackMap_fac_of_compare B S hS 𝒳 𝒴 p i ?_ hsq
        apply Functor.fiberIsoOfCartesian_hom_fac
      calc
        eqToHom hpoint.symm ≫ m.arrow = Functor.Fiber.fiberInclusion.map gamma.hom ≫
            Functor.IsPreFibered.pullbackMap yFiber.2 i := by
          rw [← hEqPoint]
          dsimp only [gamma]
          rw [Iso.trans_hom, Iso.symm_hom, Functor.Fiber.fiberInclusion.map_comp,
            Category.assoc, htc]
        _ = F.map (Functor.Fiber.fiberInclusion.map β.inv ≫ pbXMap) ≫
            Functor.Fiber.fiberInclusion.map γ'.hom := hfac
        _ = F.map liftArrow ≫ Functor.Fiber.fiberInclusion.map γ'.hom := rfl
    -- The comparison morphism `G xNew ⟶ y`.
    let dFNew := Cy.objects (G.toFunctor.obj xNew)
    have hpointCx : (Cx.objects xNew).point = x'.1 :=
      congrArg DeformationObject.point hxNew
    have hpointNew : dFNew.point = F.obj x'.1 :=
      (G.object_point xNew).trans (congrArg F.obj hpointCx)
    have hcastPoint : eqToHom (congrArg F.obj hpointCx).symm ≫
        eqToHom (G.object_point xNew).symm = eqToHom hpointNew.symm :=
      eqToHom_trans _ _
    have hAlgImage : dFNew.algebra = dy.algebra :=
      (inducedFunctor_algebra iΛ qX qY F hF' x₀ hx₀ G xNew).trans hAlgNew
    have himage' : eqToHom hpoint.symm ≫ m.arrow ≫ Functor.Fiber.fiberInclusion.map γ'.inv =
        F.map liftArrow := by
      rw [← Category.assoc, himage, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
        CategoryTheory.Functor.map_id]
      exact Category.comp_id _
    let aArrow : dy.point ⟶ dFNew.point :=
      Functor.Fiber.fiberInclusion.map γ'.inv ≫ eqToHom hpointNew.symm
    have hFxArrow : dFx.arrow = F.map dx.arrow ≫ eqToHom hpoint.symm := G.object_arrow x
    have hnewArrow : dFNew.arrow =
        F.map dx.arrow ≫ F.map liftArrow ≫ eqToHom hpointNew.symm := by
      have hmapArrow : F.map ((Cx.objects xNew).arrow) ≫ eqToHom (congrArg F.obj hpointCx) =
          F.map (dx.arrow ≫ liftArrow) := by
        have h := congrArg F.map (deformationObject_arrow_comp_eqToHom hxNew)
        rwa [Functor.map_comp, eqToHom_map] at h
      rw [G.object_arrow xNew]
      calc
        F.map ((Cx.objects xNew).arrow) ≫ eqToHom (G.object_point xNew).symm =
            (F.map ((Cx.objects xNew).arrow) ≫ eqToHom (congrArg F.obj hpointCx)) ≫
              eqToHom (congrArg F.obj hpointCx).symm ≫
                eqToHom (G.object_point xNew).symm := by
          simp [Category.assoc]
        _ = F.map (dx.arrow ≫ liftArrow) ≫ eqToHom hpointNew.symm := by
          rw [hmapArrow, hcastPoint]
        _ = F.map dx.arrow ≫ F.map liftArrow ≫ eqToHom hpointNew.symm := by
          rw [Functor.map_comp, Category.assoc]
    let aData : DeformationMorphism iΛ qY (F.obj x₀) hy₀ dFNew dy :=
      { ringHom := eqToHom hAlgImage
        arrow := aArrow
        triangle := by
          rw [← m.triangle, hFxArrow, hnewArrow]
          simp only [aArrow, Category.assoc]
          exact congrArg (F.map dx.arrow ≫ ·)
            (by simpa using congrArg (· ≫ eqToHom hpointNew.symm) himage')
        arrow_base :=
          arrow_base_of_isHomLift_id B S hS 𝒴 (Functor.Fiber.fiberInclusion.map γ'.inv)
            γ'.inv.2 hpointNew.symm hAlgImage dy.base dFNew.base }
    let a : G.toFunctor.obj xNew ⟶ y := (Cy.morphisms (G.toFunctor.obj xNew) y).symm aData
    have haData : Cy.morphisms (G.toFunctor.obj xNew) y a = aData :=
      (Cy.morphisms (G.toFunctor.obj xNew) y).apply_symm_apply _
    have haLift : Cy.projection.IsHomLift (𝟙 A₁) a := by
      refine isHomLift_of_ringHom_eq Cy (𝟙 A₁) a (hAlgImage.trans hA1) hA1 ?_
      rw [haData]
      exact eqToHom_eq_id_conj hAlgImage (hAlgImage.trans hA1) hA1
    refine ⟨xNew, lift, a, hLiftProp, haLift, ?_⟩
    -- The two morphisms `G xNew ⟶ G x` agree.
    apply (Cy.morphisms (G.toFunctor.obj xNew) (G.toFunctor.obj x)).injective
    apply DeformationMorphism.ext_of_components
    · rw [inducedFunctor_ringHom iΛ qX qY F hF' x₀ hx₀ G lift,
        morphisms_comp_ringHom Cy a g, hliftRing0, haData]
      exact eqToHom_conj_collapse_comp _ _ m.ringHom _ _ hAlgImage
    · have hliftArrow : (Cx.morphisms xNew x lift).arrow =
          liftArrow ≫ eqToHom hpointCx.symm := by
        rw [hliftData]
        exact deformationMorphism_arrow_cast hxNew liftDataNew
      have hpointEq : G.object_point x = hpoint := Subsingleton.elim _ _
      have hMArrow : m.arrow ≫ Functor.Fiber.fiberInclusion.map γ'.inv =
          eqToHom hpoint ≫ F.map liftArrow := by
        rw [← himage']
        simp
      calc
        (Cy.morphisms (G.toFunctor.obj xNew) (G.toFunctor.obj x)
              (G.toFunctor.map lift)).arrow =
            eqToHom hpoint ≫ F.map (liftArrow ≫ eqToHom hpointCx.symm) ≫
              eqToHom (G.object_point xNew).symm := by
          rw [G.morphism_arrow lift, hpointEq, hliftArrow]
        _ = eqToHom hpoint ≫ F.map liftArrow ≫ eqToHom (congrArg F.obj hpointCx).symm ≫
            eqToHom (G.object_point xNew).symm := by
          rw [Functor.map_comp, eqToHom_map]
          simp [Category.assoc]
        _ = (m.arrow ≫ Functor.Fiber.fiberInclusion.map γ'.inv) ≫
            eqToHom (congrArg F.obj hpointCx).symm ≫
              eqToHom (G.object_point xNew).symm := by
          rw [hMArrow]
          simp [Category.assoc]
        _ = m.arrow ≫ aData.arrow := by simp [aData, aArrow, Category.assoc]
        _ = (Cy.morphisms (G.toFunctor.obj xNew) (G.toFunctor.obj x) (a ≫ g)).arrow := by
          rw [Cy.reversed_composition (f := a) (g := g), haData]
  exact Deformation.isSmooth_of_lifts_smallExtensions hcofX hcofY G.toBasedFunctor hsmall

end Main

end Deformation.Artin

end

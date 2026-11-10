module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoOver
public import StacksFrontier.CategoryTheory.FiberedCategory.PairIsoClassPresheaf
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Comp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceProduct
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.Deformation.Artin.FormalObject.Versal
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.Artin.Versality
public import StacksFrontier.Deformation.Smooth.Basic
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFirstFactor
public import StacksFrontier.Deformation.Artin.Predeformation.FibreProduct
public import StacksFrontier.Deformation.Artin.Versality.Openness.Basic

/-!
# Composition of morphisms smooth on predeformation categories

The composite of two morphisms of categories over the big fppf site which are smooth on
predeformation categories is again smooth on predeformation categories (Tag 07XU).
-/

@[expose] public section

namespace Deformation.Artin

/-! ### Composition of smooth morphisms on predeformation categories -/

noncomputable section
open AlgebraicGeometry CategoryTheory

universe u v₁ v₂ v₃ w₁ w₂ w₃

-- The category structure on a predeformation category's carrier is
-- `Deformation.Artin.versal_predeformationCategory_category`, public in
-- `StacksFrontier.Deformation.Artin.FormalObject.Versal`.

-- A based functor is determined by its underlying functor:
-- `CategoryTheory.BasedCategory.BasedFunctor.ext'`, public in
-- `StacksFrontier.CategoryTheory.FiberedCategory.IsoOver`. A `private` re-declaration,
-- one of ten across the library, stood here.

private theorem mapPredeformationCategory_comp_obj_data
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}}
    {X : Type v₁} [Category.{w₁} X]
    {Y : Type v₂} [Category.{w₂} Y]
    {Z : Type v₃} [Category.{w₃} Z]
    (iΛ : Spec (.of Λ) ⟶ S)
    (qX : X ⥤ Over S) (qY : Y ⥤ Over S) (qZ : Z ⥤ Over S)
    (F : X ⥤ Y) (G : Y ⥤ Z)
    (hF : F ⋙ qY = qX) (hG : G ⋙ qZ = qY)
    (x₀ : X)
    (hx₀ : qX.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (a : (predeformationCategory iΛ qX x₀ hx₀).carrier) :
    (predeformationCategory iΛ qZ
      ((F ⋙ G).obj x₀)
      (imageBasePoint iΛ qX qZ (F ⋙ G)
        (by rw [Functor.assoc, hG, hF]) x₀ hx₀)).objects
        ((mapPredeformationCategory iΛ qX qZ (F ⋙ G)
          (by rw [Functor.assoc, hG, hF]) x₀ hx₀).toFunctor.obj a) =
      (predeformationCategory iΛ qZ (G.obj (F.obj x₀))
        (imageBasePoint iΛ qY qZ G hG (F.obj x₀)
          (imageBasePoint iΛ qX qY F hF x₀ hx₀))).objects
        (((mapPredeformationCategory iΛ qX qY F hF x₀ hx₀).toFunctor ⋙
          (mapPredeformationCategory iΛ qY qZ G hG (F.obj x₀)
            (imageBasePoint iΛ qX qY F hF x₀ hx₀)).toFunctor).obj a) := by
  have hcompObj : (F ⋙ G).obj x₀ = G.obj (F.obj x₀) := rfl
  cases hcompObj
  let Cx := predeformationCategory iΛ qX x₀ hx₀
  let hxF := imageBasePoint iΛ qX qY F hF x₀ hx₀
  let Cy := predeformationCategory iΛ qY (F.obj x₀) hxF
  let hxG := imageBasePoint iΛ qY qZ G hG (F.obj x₀) hxF
  let Cz := predeformationCategory iΛ qZ (G.obj (F.obj x₀)) hxG
  let hFG : (F ⋙ G) ⋙ qZ = qX := by rw [Functor.assoc, hG, hF]
  let hxFG := imageBasePoint iΛ qX qZ (F ⋙ G) hFG x₀ hx₀
  let Cfg := predeformationCategory iΛ qZ ((F ⋙ G).obj x₀) hxFG
  let mF := mapPredeformationCategory iΛ qX qY F hF x₀ hx₀
  let mG := mapPredeformationCategory iΛ qY qZ G hG (F.obj x₀) hxF
  let mFG := mapPredeformationCategory iΛ qX qZ (F ⋙ G) hFG x₀ hx₀
  let d₁ := Cfg.objects (mFG.toFunctor.obj a)
  let d₂ := Cz.objects ((mF.toFunctor ⋙ mG.toFunctor).obj a)
  change d₁ = d₂
  have hp : d₁.point = d₂.point := by
    calc
      d₁.point = (F ⋙ G).obj (Cx.objects a).point := mFG.object_point a
      _ = G.obj (F.obj (Cx.objects a).point) := rfl
      _ = G.obj (Cy.objects (mF.toFunctor.obj a)).point :=
        congrArg G.obj (mF.object_point a).symm
      _ = d₂.point := (mG.object_point (mF.toFunctor.obj a)).symm
  refine deformationObject_ext_of_arrow_comp ?_ hp ?_
  · calc
      d₁.algebra = Cfg.projection.obj (mFG.toFunctor.obj a) :=
        (Cfg.object_projection _).symm
      _ = Cx.projection.obj a := by
        have h := congrArg (fun P => P.obj a) mFG.projection_comm
        change (mFG.toFunctor ⋙ Cfg.projection).obj a = Cx.projection.obj a
        exact h
      _ = Cy.projection.obj (mF.toFunctor.obj a) := by
        have h := congrArg (fun P => P.obj a) mF.projection_comm
        change Cx.projection.obj a = (mF.toFunctor ⋙ Cy.projection).obj a
        exact h.symm
      _ = Cfg.projection.obj ((mF.toFunctor ⋙ mG.toFunctor).obj a) := by
        have h := congrArg (fun P => P.obj (mF.toFunctor.obj a)) mG.projection_comm
        change Cy.projection.obj (mF.toFunctor.obj a) =
          (mG.toFunctor ⋙ Cfg.projection).obj (mF.toFunctor.obj a)
        exact h.symm
      _ = d₂.algebra := Cfg.object_projection _
  · rw [mFG.object_arrow]
    change ((F ⋙ G).map (Cx.objects a).arrow ≫
      eqToHom (mFG.object_point a).symm) ≫ eqToHom hp =
      (Cz.objects (mG.toFunctor.obj (mF.toFunctor.obj a))).arrow
    rw [mG.object_arrow, mF.object_arrow]
    simp only [Category.assoc, CategoryTheory.Functor.comp_map,
      CategoryTheory.Functor.map_comp, CategoryTheory.eqToHom_map,
      CategoryTheory.eqToHom_trans]
    congr 1

private theorem mapPredeformationCategory_comp_obj
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}}
    {X : Type v₁} [Category.{w₁} X]
    {Y : Type v₂} [Category.{w₂} Y]
    {Z : Type v₃} [Category.{w₃} Z]
    (iΛ : Spec (.of Λ) ⟶ S)
    (qX : X ⥤ Over S) (qY : Y ⥤ Over S) (qZ : Z ⥤ Over S)
    (F : X ⥤ Y) (G : Y ⥤ Z)
    (hF : F ⋙ qY = qX) (hG : G ⋙ qZ = qY)
    (x₀ : X)
    (hx₀ : qX.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (a : (predeformationCategory iΛ qX x₀ hx₀).carrier) :
    (mapPredeformationCategory iΛ qX qZ (F ⋙ G)
      (by rw [Functor.assoc, hG, hF]) x₀ hx₀).toFunctor.obj a =
      ((mapPredeformationCategory iΛ qX qY F hF x₀ hx₀).toFunctor ⋙
        (mapPredeformationCategory iΛ qY qZ G hG (F.obj x₀)
          (imageBasePoint iΛ qX qY F hF x₀ hx₀)).toFunctor).obj a := by
  apply (predeformationCategory iΛ qZ _ _).objects.injective
  exact mapPredeformationCategory_comp_obj_data iΛ qX qY qZ F G hF hG x₀ hx₀ a

private theorem mapPredeformationCategory_comp
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}}
    {X : Type v₁} [Category.{w₁} X]
    {Y : Type v₂} [Category.{w₂} Y]
    {Z : Type v₃} [Category.{w₃} Z]
    (iΛ : Spec (.of Λ) ⟶ S)
    (qX : X ⥤ Over S) (qY : Y ⥤ Over S) (qZ : Z ⥤ Over S)
    (F : X ⥤ Y) (G : Y ⥤ Z)
    (hF : F ⋙ qY = qX) (hG : G ⋙ qZ = qY)
    (x₀ : X)
    (hx₀ : qX.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    (mapPredeformationCategory iΛ qX qZ (F ⋙ G)
      (by rw [Functor.assoc, hG, hF]) x₀ hx₀).toBasedFunctor =
      BasedFunctor.comp
        (mapPredeformationCategory iΛ qX qY F hF x₀ hx₀).toBasedFunctor
        (mapPredeformationCategory iΛ qY qZ G hG (F.obj x₀)
          (imageBasePoint iΛ qX qY F hF x₀ hx₀)).toBasedFunctor := by
  apply BasedCategory.BasedFunctor.ext'
  have hcompObj : (F ⋙ G).obj x₀ = G.obj (F.obj x₀) := rfl
  cases hcompObj
  let Cx := predeformationCategory iΛ qX x₀ hx₀
  let hxF := imageBasePoint iΛ qX qY F hF x₀ hx₀
  let Cy := predeformationCategory iΛ qY (F.obj x₀) hxF
  let hxG := imageBasePoint iΛ qY qZ G hG (F.obj x₀) hxF
  let Cz := predeformationCategory iΛ qZ (G.obj (F.obj x₀)) hxG
  let hFG : (F ⋙ G) ⋙ qZ = qX := by rw [Functor.assoc, hG, hF]
  let hxFG := imageBasePoint iΛ qX qZ (F ⋙ G) hFG x₀ hx₀
  let Cfg := predeformationCategory iΛ qZ ((F ⋙ G).obj x₀) hxFG
  let : Category Cx.carrier := Cx.category
  let : Category Cy.carrier := Cy.category
  let : Category Cz.carrier := Cz.category
  let : Category Cfg.carrier := Cfg.category
  let mF := mapPredeformationCategory iΛ qX qY F hF x₀ hx₀
  let mG := mapPredeformationCategory iΛ qY qZ G hG (F.obj x₀) hxF
  let mFG := mapPredeformationCategory iΛ qX qZ (F ⋙ G) hFG x₀ hx₀
  have hCfg : Cfg = Cz := rfl
  have hprojCfg : Cfg.projection = Cz.projection := by
    cases hCfg
    rfl
  have hobj : ∀ a : Cx.carrier,
      mFG.toFunctor.obj a = (mF.toFunctor ⋙ mG.toFunctor).obj a := by
    intro a
    exact mapPredeformationCategory_comp_obj iΛ qX qY qZ F G hF hG x₀ hx₀ a
  refine CategoryTheory.Functor.ext (h_obj := hobj) (h_map := ?_)
  intro a b f
  change mFG.toFunctor.map f =
    eqToHom _ ≫ (mF.toFunctor ⋙ mG.toFunctor).map f ≫ eqToHom _
  let a' : Cx.carrier := a
  let b' : Cx.carrier := b
  let f' : a' ⟶ b' := f
  have hprojFG := CategoryTheory.Functor.congr_hom mFG.projection_comm f'
  have hprojCompFunctor :
      (mF.toFunctor ⋙ mG.toFunctor) ⋙ Cfg.projection = Cx.projection := by
    rw [Functor.assoc, hprojCfg, mG.projection_comm, mF.projection_comm]
  have hprojComp := CategoryTheory.Functor.congr_hom hprojCompFunctor f'
  have hprojFGMap := hprojFG
  simp only [Functor.comp_map] at hprojFGMap
  have hprojCompMap := hprojComp
  simp only [Functor.comp_map] at hprojCompMap
  have hprojFGMapF : Cfg.projection.map (mFG.toFunctor.map f') =
      eqToHom (CategoryTheory.Functor.congr_obj mFG.projection_comm a') ≫
        Cx.projection.map f' ≫
        eqToHom (CategoryTheory.Functor.congr_obj mFG.projection_comm b').symm := by
    simpa [Cfg, f'] using hprojFGMap
  have hprojCompMapF : Cfg.projection.map (mG.toFunctor.map (mF.toFunctor.map f')) =
      eqToHom (CategoryTheory.Functor.congr_obj hprojCompFunctor a') ≫
        Cx.projection.map f' ≫
        eqToHom (CategoryTheory.Functor.congr_obj hprojCompFunctor b').symm := by
    simpa [Cfg, f'] using hprojCompMap
  apply (Cfg.morphisms (mFG.toFunctor.obj a') (mFG.toFunctor.obj b')).injective
  let d₁ := Cfg.morphisms (mFG.toFunctor.obj a') (mFG.toFunctor.obj b')
    (mFG.toFunctor.map f)
  let d₂ := Cfg.morphisms (mFG.toFunctor.obj a') (mFG.toFunctor.obj b')
    (eqToHom (hobj a') ≫ (mF.toFunctor ⋙ mG.toFunctor).map f ≫
      eqToHom (hobj b').symm)
  change d₁ = d₂
  have hRing : d₁.ringHom = d₂.ringHom := by
    change (Cfg.morphisms (mFG.toFunctor.obj a') (mFG.toFunctor.obj b')
        (mFG.toFunctor.map f')).ringHom =
      (Cfg.morphisms (mFG.toFunctor.obj a') (mFG.toFunctor.obj b')
        (eqToHom (hobj a') ≫ (mF.toFunctor ⋙ mG.toFunctor).map f' ≫
          eqToHom (hobj b').symm)).ringHom
    rw [← Cfg.morphism_projection, ← Cfg.morphism_projection]
    simp only [Category.assoc, Functor.comp_map, Functor.map_comp,
      CategoryTheory.eqToHom_map, CategoryTheory.eqToHom_trans]
    rw [hprojFGMapF, hprojCompMapF]
    simp only [Category.assoc, CategoryTheory.eqToHom_trans]
    congr 1
  have hArrow : d₁.arrow = d₂.arrow := by
    change (Cfg.morphisms (mFG.toFunctor.obj a') (mFG.toFunctor.obj b')
        (mFG.toFunctor.map f')).arrow =
      (Cfg.morphisms (mFG.toFunctor.obj a') (mFG.toFunctor.obj b')
        (eqToHom (hobj a') ≫ (mF.toFunctor ⋙ mG.toFunctor).map f' ≫
          eqToHom (hobj b').symm)).arrow
    let a₁ := mFG.toFunctor.obj a'
    let b₁ := mFG.toFunctor.obj b'
    let a₂ := (mF.toFunctor ⋙ mG.toFunctor).obj a'
    let b₂ := (mF.toFunctor ⋙ mG.toFunctor).obj b'
    let p : a₁ ⟶ a₂ := eqToHom (hobj a')
    let q : b₂ ⟶ b₁ := eqToHom (hobj b').symm
    let v : a₂ ⟶ b₂ := (mF.toFunctor ⋙ mG.toFunctor).map f'
    have hmid : (Cfg.morphisms a₂ b₂ v).arrow =
        (Cz.morphisms (mG.toFunctor.obj (mF.toFunctor.obj a'))
          (mG.toFunctor.obj (mF.toFunctor.obj b'))
          (mG.toFunctor.map (mF.toFunctor.map f'))).arrow := by
      cases hCfg
      rfl
    have hEqToHom {a b : Cfg.carrier} (h : a = b) :
        (Cfg.morphisms a b (eqToHom h)).arrow =
          eqToHom (congrArg (fun c => (Cfg.objects c).point) h).symm := by
      cases h
      simpa using Cfg.reversed_identity a
    have hroute :
        (Cfg.morphisms a₁ b₁ ((p ≫ v) ≫ q)).arrow =
          (Cfg.morphisms b₂ b₁ q).arrow ≫
            (Cfg.morphisms a₂ b₂ v).arrow ≫ (Cfg.morphisms a₁ a₂ p).arrow := by
      calc
        _ = (Cfg.morphisms b₂ b₁ q).arrow ≫
            (Cfg.morphisms a₁ b₂ (p ≫ v)).arrow :=
          Cfg.reversed_composition (p ≫ v) q
        _ = (Cfg.morphisms b₂ b₁ q).arrow ≫
            ((Cfg.morphisms a₂ b₂ v).arrow ≫ (Cfg.morphisms a₁ a₂ p).arrow) := by
          rw [Cfg.reversed_composition p v]
        _ = _ := rfl
    rw [mFG.morphism_arrow]
    conv_rhs =>
      rw [← Category.assoc]
      rw [hroute]
    rw [hEqToHom (hobj b').symm, hEqToHom (hobj a')]
    rw [hmid]
    rw [mG.morphism_arrow]
    rw [mF.morphism_arrow]
    simp [a₁, b₁, a₂, b₂, Category.assoc, Functor.comp_map,
      Functor.map_comp, CategoryTheory.eqToHom_map, CategoryTheory.eqToHom_trans]
  exact DeformationMorphism.ext_of_components _ _ _ _ hRing hArrow

/-- The composite of two morphisms smooth on predeformation categories is
smooth on predeformation categories. -/
@[stacks 07XU]
public theorem isSmoothOnPredeformationCategories_comp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : Type v₁} [Category.{w₁} X]
    {Y : Type v₂} [Category.{w₂} Y]
    {Z : Type v₃} [Category.{w₃} Z]
    (pX : X ⥤ BigFppfOver B S hS)
    (pY : Y ⥤ BigFppfOver B S hS)
    (pZ : Z ⥤ BigFppfOver B S hS)
    (F : X ⥤ Y) (G : Y ⥤ Z)
    (hF : F ⋙ pY = pX) (hG : G ⋙ pZ = pY)
    (hSmoothF : IsSmoothOnPredeformationCategories B S hS pX pY F hF)
    (hSmoothG : IsSmoothOnPredeformationCategories B S hS pY pZ G hG) :
    IsSmoothOnPredeformationCategories B S hS pX pZ (F ⋙ G)
      (by rw [Functor.assoc, hG, hF]) := by
  dsimp [IsSmoothOnPredeformationCategories]
  intro Λ k _ _ _ iΛ x₀ hx₀ hLFT hQC hOpen
  let qX := pX ⋙ Over.post B.inclusion
  let qY := pY ⋙ Over.post B.inclusion
  let qZ := pZ ⋙ Over.post B.inclusion
  let hF' : F ⋙ qY = qX := by
    dsimp [qX, qY]
    simpa only [Functor.assoc] using
      congrArg (fun p => p ⋙ Over.post B.inclusion) hF
  let hG' : G ⋙ qZ = qY := by
    dsimp [qY, qZ]
    simpa only [Functor.assoc] using
      congrArg (fun p => p ⋙ Over.post B.inclusion) hG
  let hFG' : (F ⋙ G) ⋙ qZ = qX := by
    rw [Functor.assoc, hG', hF']
  have hFsm := hSmoothF iΛ x₀ hx₀ hLFT hQC hOpen
  have hGsm := hSmoothG iΛ (F.obj x₀)
    (imageBasePoint iΛ qX qY F hF' x₀ hx₀) hLFT hQC hOpen
  have hcomp := Deformation.isSmooth_comp
    (mapPredeformationCategory iΛ qX qY F hF' x₀ hx₀).toBasedFunctor
    (mapPredeformationCategory iΛ qY qZ G hG'
      (F.obj x₀) (imageBasePoint iΛ qX qY F hF' x₀ hx₀)).toBasedFunctor
    hFsm hGsm
  have heq := mapPredeformationCategory_comp iΛ qX qY qZ F G hF' hG' x₀ hx₀
  simpa [qX, qY, qZ] using (heq.symm ▸ hcomp)

end

end Deformation.Artin

module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.PointComparisonZariskiReading
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.RepresentedPullbackTensorMate

/-!
# The mate of a square of left adjoints through two equivalences

For adjunctions `gs ⊣ gp`, `φs ⊣ φp`, equivalences `E`, `E'` and a square
`θ : gs ⋙ E' ⟶ E ⋙ φs` of left adjoints, the mate `gs (E⁻¹ N) ⟶ E'⁻¹ (φs N)` of `θ` satisfies a
unit identity against the conjugate `κ : φp ⋙ E⁻¹ ⟶ E'⁻¹ ⋙ gp` of `θ`.  This turns the abstract
mate computation `CategoryTheory.Adjunction.comp_homEquiv_symm_eq_of_rightAdjointSquare` into a
description of a transposed comparison through `θ`, granted a comparison of the right adjoints
with `κ`.  At the square of a morphism `h` of test objects the conjugate of
`AlgebraicGeometry.Space.representedSquareModulePullbackIso` is computed as the composite of the
comparisons of direct images it is built from.

## Main definitions

* `CategoryTheory.Adjunction.equivalenceMateApp`: the mate of `θ` through `E` and `E'`.
* `CategoryTheory.Adjunction.EquivalenceMateCompat`: the compatibility of a comparison of
  readings of direct images with `κ`.

## Main results

* `CategoryTheory.Adjunction.unit_comp_map_equivalenceMateApp`: the unit identity of the mate.
* `CategoryTheory.Adjunction.comp_homEquiv_symm_eq_of_equivalenceMate`: the mate computation
  through two equivalences.
* `CategoryTheory.Adjunction.conjugateEquiv_factorizationIso_hom_equivalence`: the conjugate of a
  comparison of two factorizations whose outer left adjoints are functors of equivalences.
* `AlgebraicGeometry.Space.conjugateEquiv_representedSquareFactorizationIso_hom_eq_comp`: the
  conjugate of `representedSquareModulePullbackIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Adjunction

variable {𝒵 𝒴₁ 𝒴₂ 𝒳 : Type*} [Category 𝒵] [Category 𝒴₁] [Category 𝒴₂] [Category 𝒳]
  {gs : 𝒵 ⥤ 𝒴₁} {gp : 𝒴₁ ⥤ 𝒵} {φs : 𝒴₂ ⥤ 𝒳} {φp : 𝒳 ⥤ 𝒴₂}
  (ag : gs ⊣ gp) (aφ : φs ⊣ φp) (E : 𝒵 ≌ 𝒴₂) (E' : 𝒴₁ ≌ 𝒳)
  (θ : gs ⋙ E'.functor ⟶ E.functor ⋙ φs) (κ : φp ⋙ E.inverse ⟶ E'.inverse ⋙ gp)

/-- The mate of `θ` read through the two equivalences: the component at `N` of the comparison
`gs (E⁻¹ N) ⟶ E'⁻¹ (φs N)`. -/
def equivalenceMateApp (N : 𝒴₂) : gs.obj (E.inverse.obj N) ⟶ E'.inverse.obj (φs.obj N) :=
  E'.unit.app (gs.obj (E.inverse.obj N)) ≫
    E'.inverse.map (θ.app (E.inverse.obj N) ≫ φs.map (E.counit.app N))

/-- The transpose along `E'` of `equivalenceMateApp`. -/
theorem map_equivalenceMateApp_comp_counit (N : 𝒴₂) :
    E'.functor.map (equivalenceMateApp E E' θ N) ≫ E'.counit.app (φs.obj N) =
      θ.app (E.inverse.obj N) ≫ φs.map (E.counit.app N) := by
  simp [equivalenceMateApp]

/-- **The unit identity of the mate of `θ` through two equivalences**, with `κ` the conjugate of
`θ`: the unit of `E⁻¹ ⊣ E`, followed by `E` of the unit of `gs ⊣ gp` and of `gp` of the mate,
is the unit of `φs ⊣ φp` followed by `E` of `κ`. -/
theorem unit_comp_map_equivalenceMateApp
    (hκ : conjugateEquiv (E.toAdjunction.comp aφ) (ag.comp E'.toAdjunction) θ = κ) (N : 𝒴₂) :
    E.symm.toAdjunction.unit.app N ≫ E.functor.map (ag.unit.app (E.inverse.obj N) ≫
      gp.map (equivalenceMateApp E E' θ N)) =
    aφ.unit.app N ≫ E.counitInv.app (φp.obj (φs.obj N)) ≫
      E.functor.map (κ.app (φs.obj N)) := by
  have hu := unit_conjugateEquiv (E.toAdjunction.comp aφ) (ag.comp E'.toAdjunction) θ
    (E.inverse.obj N)
  rw [hκ] at hu
  simp only [comp_unit_app, Functor.comp_obj, Functor.comp_map, Category.assoc] at hu
  have hn := κ.naturality (φs.map (E.counit.app N))
  simp only [Functor.comp_obj, Functor.comp_map] at hn
  have hη := aφ.unit.naturality (E.counit.app N)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at hη
  have key : ag.unit.app (E.inverse.obj N) ≫ gp.map (equivalenceMateApp E E' θ N) =
      E.unit.app (E.inverse.obj N) ≫ E.inverse.map (E.counit.app N) ≫ E.inverse.map
        (aφ.unit.app N) ≫ κ.app (φs.obj N) := by
    calc ag.unit.app (E.inverse.obj N) ≫ gp.map (equivalenceMateApp E E' θ N)
        = (ag.unit.app (E.inverse.obj N) ≫
            gp.map (E'.toAdjunction.unit.app (gs.obj (E.inverse.obj N))) ≫
              gp.map (E'.inverse.map (θ.app (E.inverse.obj N)))) ≫
            gp.map (E'.inverse.map (φs.map (E.counit.app N))) := by
          simp [equivalenceMateApp]
      _ = (E.toAdjunction.unit.app (E.inverse.obj N) ≫
            E.inverse.map (aφ.unit.app (E.functor.obj (E.inverse.obj N))) ≫
              κ.app (φs.obj (E.functor.obj (E.inverse.obj N)))) ≫
            gp.map (E'.inverse.map (φs.map (E.counit.app N))) := by rw [hu]
      _ = E.toAdjunction.unit.app (E.inverse.obj N) ≫
            E.inverse.map (aφ.unit.app (E.functor.obj (E.inverse.obj N)) ≫
              φp.map (φs.map (E.counit.app N))) ≫ κ.app (φs.obj N) := by
          rw [Category.assoc, Category.assoc, ← hn, Functor.map_comp, Category.assoc]
          rfl
      _ = _ := by
          rw [← hη, Functor.map_comp]
          simp
  rw [key]
  simp

/-- `E⁻¹` of the transpose along `E⁻¹ ⊣ E` of a morphism `f`, followed by the counit, is `f`. -/
theorem equivalence_inverse_map_counitInv_comp_map_comp_unitInv {X : 𝒴₂} {Y : 𝒵}
    (f : E.inverse.obj X ⟶ Y) :
    E.symm.functor.map (E.counitInv.app X ≫ E.functor.map f) ≫
      E.symm.toAdjunction.counit.app Y = f := by
  simp

section MateCompat

variable {Ec' Z Z' : Type*} [Category Ec'] [Category Z] [Category Z'] {gs : 𝒵 ⥤ Ec'}
  {gp : Ec' ⥤ 𝒵} {τs : Z ⥤ Z'} {τp : Z' ⥤ Z} {zR : 𝒴₂ ⥤ Z} {zR' : 𝒳 ⥤ Z'}
  (ag : gs ⊣ gp) (aτ : τs ⊣ τp) (E' : Ec' ≌ 𝒳)
  (θ : gs ⋙ E'.functor ⟶ E.functor ⋙ φs) (r : 𝒵 ⥤ Z) (r' : Ec' ⥤ Z')
  (ι : E.inverse ⋙ r ≅ zR) (ι' : E'.inverse ⋙ r' ≅ zR') (zDI : φp ⋙ zR ⟶ zR' ⋙ τp)
  (R1 : gp ⋙ r ≅ r' ⋙ τp)

/-- The compatibility of a comparison `zDI` of readings of direct images with a comparison `κ` of
right adjoints and a comparison `R1` of two routes of direct images. -/
def EquivalenceMateCompat (κ : φp ⋙ E.inverse ⟶ E'.inverse ⋙ gp) : Prop :=
  ∀ M₀ : 𝒳, ι.hom.app (φp.obj M₀) ≫ zDI.app M₀ =
    r.map (κ.app M₀) ≫ R1.hom.app (E'.inverse.obj M₀) ≫ τp.map (ι'.hom.app M₀)

/-- **The mate computation through two equivalences.**
`CategoryTheory.Adjunction.comp_homEquiv_symm_eq_of_rightAdjointSquare` with `E⁻¹ ⊣ E` for the
middle adjunction, the comparison `μ` the mate `equivalenceMateApp` of a square `θ` of left
adjoints, and the comparison of right adjoints read off the conjugate of `θ`. -/
theorem comp_homEquiv_symm_eq_of_equivalenceMate (κ : φp ⋙ E.inverse ⟶ E'.inverse ⋙ gp)
    (hκ : conjugateEquiv (E.toAdjunction.comp aφ) (ag.comp E'.toAdjunction) θ = κ)
    (hH : EquivalenceMateCompat E E' r r' ι ι' zDI R1 κ)
    (N : 𝒴₂) (c : τs.obj (r.obj (E.inverse.obj N)) ⟶ r'.obj (gs.obj (E.inverse.obj N)))
    (hA : aτ.homEquiv _ _ c =
      r.map (ag.unit.app (E.inverse.obj N)) ≫ R1.hom.app (gs.obj (E.inverse.obj N))) :
    τs.map (ι.hom.app N) ≫
        (aτ.homEquiv _ _).symm (zR.map (aφ.unit.app N) ≫ zDI.app (φs.obj N)) =
      c ≫ r'.map (equivalenceMateApp E E' θ N) ≫ ι'.hom.app (φs.obj N) :=
  comp_homEquiv_symm_eq_of_rightAdjointSquare aφ ag aτ E.symm.toAdjunction r r' ι ι' zDI R1
    (fun M₀ => E.counitInv.app (φp.obj M₀) ≫
      E.functor.map ((conjugateEquiv (E.toAdjunction.comp aφ) (ag.comp E'.toAdjunction) θ).app M₀))
    (fun M₀ => (hH M₀).trans (congrArg (fun k => r.map k ≫ R1.hom.app (E'.inverse.obj M₀) ≫
      τp.map (ι'.hom.app M₀)) ((congrArg (fun k => k.app M₀) hκ).symm.trans
        (equivalence_inverse_map_counitInv_comp_map_comp_unitInv E _).symm)))
    N c hA (equivalenceMateApp E E' θ N)
    (unit_comp_map_equivalenceMateApp ag aφ E E' θ _ rfl N)

end MateCompat

section Factorization

variable {𝒵 𝒴₁ 𝒴₂ 𝒳 : Type*} [Category 𝒵] [Category 𝒴₁] [Category 𝒴₂] [Category 𝒳]
  {χs : 𝒵 ⥤ 𝒳} {χr : 𝒳 ⥤ 𝒵} {ψ₁s : 𝒵 ⥤ 𝒴₁} {ψ₁r : 𝒴₁ ⥤ 𝒵} {φ₁s : 𝒴₁ ⥤ 𝒳} {φ₁r : 𝒳 ⥤ 𝒴₁}
  {ψ₂s : 𝒵 ⥤ 𝒴₂} {ψ₂r : 𝒴₂ ⥤ 𝒵} {φ₂s : 𝒴₂ ⥤ 𝒳} {φ₂r : 𝒳 ⥤ 𝒴₂} {pb : 𝒵 ⥤ 𝒴₁} {pbr : 𝒴₁ ⥤ 𝒵}
  (aχ : χs ⊣ χr) (aψ₁ : ψ₁s ⊣ ψ₁r) (aφ₁ : φ₁s ⊣ φ₁r) (aψ₂ : ψ₂s ⊣ ψ₂r) (aφ₂ : φ₂s ⊣ φ₂r)
  (aPb : pb ⊣ pbr) (E : 𝒵 ≌ 𝒴₂) (E' : 𝒴₁ ≌ 𝒳)
  (c₁ : χs ≅ ψ₁s ⋙ φ₁s) (c₂ : χs ≅ ψ₂s ⋙ φ₂s) (τ₁ : φ₁r ⋙ ψ₁r ≅ χr) (τ₂ : φ₂r ⋙ ψ₂r ≅ χr)
  (αψ₁ : ψ₁s ≅ pb) (αφ₁ : φ₁s ≅ E'.functor) (αψ₂ : ψ₂s ≅ E.functor)
  (Pψ₁ : ψ₁r ≅ pbr) (Pφ₁ : φ₁r ≅ E'.inverse) (Pψ₂ : ψ₂r ≅ E.inverse)

/-- `Stacks.Mates.conjugateEquiv_factorizationIso_hom` with the two outer left adjoints the
functors of equivalences. -/
theorem conjugateEquiv_factorizationIso_hom_equivalence
    (hc₁ : conjugateEquiv (aψ₁.comp aφ₁) aχ c₁.hom = τ₁.hom)
    (hc₂ : conjugateEquiv (aψ₂.comp aφ₂) aχ c₂.hom = τ₂.hom)
    (hψ₁ : conjugateEquiv aPb aψ₁ αψ₁.hom = Pψ₁.inv)
    (hφ₁ : conjugateEquiv E'.toAdjunction aφ₁ αφ₁.hom = Pφ₁.inv)
    (hψ₂ : conjugateEquiv E.toAdjunction aψ₂ αψ₂.hom = Pψ₂.inv) :
    conjugateEquiv (E.toAdjunction.comp aφ₂) (aPb.comp E'.toAdjunction)
        (Functor.isoWhiskerLeft pb αφ₁.symm ≪≫ Functor.isoWhiskerRight αψ₁.symm φ₁s ≪≫
          c₁.symm ≪≫ c₂ ≪≫ Functor.isoWhiskerRight αψ₂ φ₂s).hom =
      Functor.whiskerLeft φ₂r Pψ₂.inv ≫ τ₂.hom ≫ τ₁.inv ≫ Functor.whiskerLeft φ₁r Pψ₁.hom ≫
        Functor.whiskerRight Pφ₁.hom pbr :=
  Stacks.Mates.conjugateEquiv_factorizationIso_hom aχ aψ₁ aφ₁ aψ₂ aφ₂ c₁ c₂ τ₁ τ₂ aPb
    E'.toAdjunction E.toAdjunction αψ₁ αφ₁ αψ₂ Pψ₁ Pφ₁ Pψ₂ hc₁ hc₂ hψ₁ hφ₁ hψ₂

end Factorization

end CategoryTheory.Adjunction

universe u

namespace AlgebraicGeometry.Space

open Stacks.Sheaves.RingedToposModules

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T T' : BigFppfOver B S hS}
  (h : T' ⟶ T)

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (ringedSpaceHom)

set_option maxHeartbeats 400000 in
-- The statement and the proof each elaborate the long composite term once.
/-- The conjugate of `representedSquareModulePullbackIso` as the composite of the comparisons of
direct images round the square of `h`, as a term whose type fixes the spelling of the categories
of modules. -/
theorem conjugateEquivRepresentedSquareAux :
    type_of% (Adjunction.conjugateEquiv_factorizationIso_hom_equivalence
      (pullbackAdjPushforwardModules (representedSquareHom B S hS h))
      (pullbackAdjPushforwardModules (representedSchemeBaseChangeHom B S hS h))
      (pullbackAdjPushforwardModules (representedReindexHom B S hS T'))
      (pullbackAdjPushforwardModules (representedReindexHom B S hS T))
      (pullbackAdjPushforwardModules
        (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS h)))
      (smallEtaleRingedSiteHom (associatedBigEtaleSite B)
        h.left).toRingedToposSiteHom.pullbackPushforwardAdjunctionToposGeneral
      (representedReindexEquivalence B S hS T) (representedReindexEquivalence B S hS T')
      (representedSchemeRoutePullbackCompIso B S hS h)
      (representedSpaceRoutePullbackCompIso B S hS h (relativelyRepresentable_yoneda_map B S hS h))
      (pushforwardModulesCompIso (representedReindexHom B S hS T')
        (representedSchemeBaseChangeHom B S hS h) (representedSquareHom B S hS h) (Iso.refl _)
        (fSharpSetComp_representedSquareHom B S hS h))
      (pushforwardModulesCompIso
        (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS h))
        (representedReindexHom B S hS T) (representedSquareHom B S hS h)
        (representedSquareDirectImageIso B S hS h (relativelyRepresentable_yoneda_map B S hS h))
        (fSharpSetComp_representedSquareDirectImageIso B S hS h
          (relativelyRepresentable_yoneda_map B S hS h)))
      (representedSchemeBaseChangePullbackIso B S hS h)
      (representedReindexPullbackIso B S hS T') (representedReindexPullbackIso B S hS T)
      (representedSchemeBaseChangePushforwardIso B S hS h)
      (representedReindexPushforwardIso B S hS T') (representedReindexPushforwardIso B S hS T)
      (conjugateEquiv_representedSchemeRoutePullbackCompIso_hom B S hS h)
      (conjugateEquiv_representedSpaceRoutePullbackCompIso_hom B S hS h
        (relativelyRepresentable_yoneda_map B S hS h))
      (conjugateEquiv_pullbackModulesBaseChangeIso_hom B S hS h)
      (conjugateEquiv_representedReindexPullbackIso_hom B S hS T')
      (conjugateEquiv_representedReindexPullbackIso_hom B S hS T)) := by
  have key := Adjunction.conjugateEquiv_factorizationIso_hom_equivalence
    (pullbackAdjPushforwardModules (representedSquareHom B S hS h))
    (pullbackAdjPushforwardModules (representedSchemeBaseChangeHom B S hS h))
    (pullbackAdjPushforwardModules (representedReindexHom B S hS T'))
    (pullbackAdjPushforwardModules (representedReindexHom B S hS T))
    (pullbackAdjPushforwardModules
      (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS h)))
    (smallEtaleRingedSiteHom (associatedBigEtaleSite B)
      h.left).toRingedToposSiteHom.pullbackPushforwardAdjunctionToposGeneral
    (representedReindexEquivalence B S hS T) (representedReindexEquivalence B S hS T')
    (representedSchemeRoutePullbackCompIso B S hS h)
    (representedSpaceRoutePullbackCompIso B S hS h (relativelyRepresentable_yoneda_map B S hS h))
    (pushforwardModulesCompIso (representedReindexHom B S hS T')
      (representedSchemeBaseChangeHom B S hS h) (representedSquareHom B S hS h) (Iso.refl _)
      (fSharpSetComp_representedSquareHom B S hS h))
    (pushforwardModulesCompIso
      (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS h))
      (representedReindexHom B S hS T) (representedSquareHom B S hS h)
      (representedSquareDirectImageIso B S hS h (relativelyRepresentable_yoneda_map B S hS h))
      (fSharpSetComp_representedSquareDirectImageIso B S hS h
        (relativelyRepresentable_yoneda_map B S hS h)))
    (representedSchemeBaseChangePullbackIso B S hS h)
    (representedReindexPullbackIso B S hS T') (representedReindexPullbackIso B S hS T)
    (representedSchemeBaseChangePushforwardIso B S hS h)
    (representedReindexPushforwardIso B S hS T') (representedReindexPushforwardIso B S hS T)
    (conjugateEquiv_representedSchemeRoutePullbackCompIso_hom B S hS h)
    (conjugateEquiv_representedSpaceRoutePullbackCompIso_hom B S hS h
      (relativelyRepresentable_yoneda_map B S hS h))
    (conjugateEquiv_pullbackModulesBaseChangeIso_hom B S hS h)
    (conjugateEquiv_representedReindexPullbackIso_hom B S hS T')
    (conjugateEquiv_representedReindexPullbackIso_hom B S hS T)
  exact key

/-- **The conjugate of `representedSquareModulePullbackIso`** is the composite of the comparisons
of direct images round the square of `h`. -/
theorem conjugateEquiv_representedSquareFactorizationIso_hom_eq_comp :
    type_of% (conjugateEquivRepresentedSquareAux h) :=
  conjugateEquivRepresentedSquareAux h

end AlgebraicGeometry.Space

module

public import StacksFrontier.AlgebraicGeometry.Quot.ContractionUniquenessNearPoint
public import StacksFrontier.AlgebraicGeometry.Quot.ExtendsFibreIsoNearPoint

/-!
# Stacks 0E89 for families of curves

This file derives `AlgebraicGeometry.CurveFamily.ExtendsFibreIsoNearPoint`, the statement of
[Stacks, Tag 0E89] in the form used by the uniqueness of the stabilization ([Stacks, Tag 0E8A]),
from `AlgebraicGeometry.Space.exists_iso_near_point_of_iso_fibre`. The two differ only in
packaging: the families are `AlgebraicGeometry.CurveFamily`s with bases equal to that of `X`
(rather than presheaves with morphisms to one base), the fibres are presented by cartesian squares
of algebraic spaces over the residue field point
`AlgebraicGeometry.CurveFamily.residueFieldValuedPoint` (rather than isomorphisms with the fibre
products over `AlgebraicGeometry.Space.pointFieldMap`), the isomorphism of fibres is one of the
presenting schemes, the higher direct image is Mathlib's `ℕ`-indexed right derived functor, and
the conclusion is stated with `AlgebraicGeometry.AlgebraicSpaces.fiberProduct` and
`AlgebraicGeometry.Space.structureContractionBaseChange`.

## Main results

* `AlgebraicGeometry.CurveFamily.extendsFibreIsoNearPoint`: the proposition
  `AlgebraicGeometry.CurveFamily.ExtendsFibreIsoNearPoint` holds.

## References

* [Stacks Project, Tag 0E89](https://stacks.math.columbia.edu/tag/0E89)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The base change of `c` over `Z` along `h`, as a morphism of presheaves, is the morphism of
fibre products induced by `c`. -/
theorem structureContractionBaseChange_hom {X Y Z Z' : AlgebraicSpaces B S hS} {f : X ⟶ Z}
    {g : Y ⟶ Z} (c : X ⟶ Y) (hc : c ≫ g = f) (h : Z' ⟶ Z) :
    (structureContractionBaseChange B S hS c hc h).hom =
      pullback.map f.hom h.hom g.hom h.hom c.hom (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, ← hc]; rfl) (by simp) := by
  apply pullback.hom_ext
  · have h₁ : (structureContractionBaseChange B S hS c hc h).hom ≫ pullback.fst g.hom h.hom =
        pullback.fst f.hom h.hom ≫ c.hom :=
      congrArg (fun m => m.hom) (structureContractionBaseChange_fst B S hS c hc h)
    exact h₁.trans (pullback.lift_fst _ _ _).symm
  · have h₂ : (structureContractionBaseChange B S hS c hc h).hom ≫ pullback.snd g.hom h.hom =
        pullback.snd f.hom h.hom :=
      congrArg (fun m => m.hom) (structureContractionBaseChange_snd B S hS c hc h)
    exact h₂.trans ((pullback.lift_snd _ _ _).trans (Category.comp_id _)).symm

end Space

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- The structure morphism of a family of curves, transported to an equal base, is flat,
proper, of finite presentation and of relative dimension at most one. -/
theorem curveFamilyConditions_toBase_comp_eqToHom (Y : CurveFamily B hZ)
    {Q : BigFppfOver B integerBase hZ} (hb : Y.base = Q) :
    Space.IsFlat B integerBase hZ (Y.toBase ≫ eqToHom (congrArg schemeSpace hb)).hom ∧
      Space.IsProper B integerBase hZ (Y.toBase ≫ eqToHom (congrArg schemeSpace hb)).hom ∧
      Space.IsFinitePresentation B integerBase hZ
        (Y.toBase ≫ eqToHom (congrArg schemeSpace hb)).hom ∧
      Space.HasRelativeDimensionLE 1 B integerBase hZ
        (Y.toBase ≫ eqToHom (congrArg schemeSpace hb)).hom := by
  subst hb
  simpa only [eqToHom_refl, Category.comp_id] using
    ⟨Y.flat, Y.proper, Y.finitePresentation, Y.relativeDimensionLE⟩

/-- The object of the residue field point of `s` is the spectrum of the residue field over the
integers. -/
def pointFieldObjectIso (Q : BigFppfOver B integerBase hZ) (s : Q.left.1) :
    Space.pointFieldObject Q s ≅ (residueFieldValuedPoint B hZ Q s).siteObject :=
  Over.isoMk (Iso.refl _) (ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _))

/-- The residue field point of `s` is `Space.pointFieldMap` through `pointFieldObjectIso`. -/
theorem pointFieldObjectIso_hom_value (Q : BigFppfOver B integerBase hZ) (s : Q.left.1) :
    (pointFieldObjectIso Q s).hom ≫ (residueFieldValuedPoint B hZ Q s).value =
      Space.pointFieldMap Q s := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  show 𝟙 _ ≫ Q.left.1.fromSpecResidueField s = Q.left.1.fromSpecResidueField s
  exact Category.id_comp _

/-- A presentation of the fibre over the residue field point by a cartesian square is a
presentation of the fibre over `Space.pointFieldMap`. -/
theorem isPullback_pointFieldMap_of_isPullback {Q : BigFppfOver B integerBase hZ} (s : Q.left.1)
    {Z : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} (g : Z ⟶ yoneda.obj Q)
    {V : BigFppfOver B integerBase hZ} {v : V ⟶ (residueFieldValuedPoint B hZ Q s).siteObject}
    {q : yoneda.obj V ⟶ Z}
    (h : IsPullback q (yoneda.map v) g (yoneda.map (residueFieldValuedPoint B hZ Q s).value)) :
    IsPullback q (yoneda.map (v ≫ (pointFieldObjectIso Q s).inv)) g
      (yoneda.map (Space.pointFieldMap Q s)) := by
  refine IsPullback.of_iso h (Iso.refl _) (Iso.refl _)
    (yoneda.mapIso (pointFieldObjectIso Q s).symm) (Iso.refl _) (by simp) (by simp) (by simp) ?_
  simp only [Iso.refl_hom, Category.comp_id, Functor.mapIso_hom, Iso.symm_hom]
  rw [← Functor.map_comp, ← pointFieldObjectIso_hom_value]
  exact congrArg yoneda.map (Iso.inv_hom_id_assoc _ _).symm

/-- **The fibre of `c` read on presentations of the fibres.** If `a : V_X ⟶ V` presents the
fibre of `c` on presentations of the fibres of `X` and `Y` over `p`, then it is the morphism of
fibre products induced by `c`, through the isomorphisms of the presentations with the fibre
products. -/
theorem yoneda_map_comp_isoPullback_hom {Q k : BigFppfOver B integerBase hZ}
    (p : k ⟶ Q) {X Y : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} {f : X ⟶ yoneda.obj Q}
    {g : Y ⟶ yoneda.obj Q} (c : X ⟶ Y) (hc : c ≫ g = f) {VX V : BigFppfOver B integerBase hZ}
    {qX : yoneda.obj VX ⟶ X} {q : yoneda.obj V ⟶ Y} {vX : VX ⟶ k} {v : V ⟶ k}
    (sX : IsPullback qX (yoneda.map vX) f (yoneda.map p))
    (sY : IsPullback q (yoneda.map v) g (yoneda.map p)) (a : VX ⟶ V) (hav : a ≫ v = vX)
    (hqa : qX ≫ c = yoneda.map a ≫ q) :
    yoneda.map a ≫ sY.isoPullback.hom =
      sX.isoPullback.hom ≫ pullback.map f (yoneda.map p) g (yoneda.map p) c (𝟙 _) (𝟙 _)
        (by simp [hc]) (by simp) := by
  apply pullback.hom_ext
  · simp [hqa]
  · simp [← hav]

/-- **Stacks 0E89 with the fibres presented over the residue field point.** This is
`AlgebraicGeometry.Space.exists_iso_near_point_of_iso_fibre` with the fibres of `X`, `Y₁`, `Y₂`
presented by cartesian squares over `residueFieldValuedPoint`, the fibres `aᵢ` of the `cᵢ` and
the isomorphism `φ` of fibres given on the presenting schemes, and the higher direct image in
Mathlib's `ℕ`-indexed convention. -/
theorem exists_iso_near_point_of_isPullback_fibres (Q : BigFppfOver B integerBase hZ)
    {X Y₁ Y₂ : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B integerBase hZ X) (hY₁ : IsAlgebraicSpace B integerBase hZ Y₁)
    (hY₂ : IsAlgebraicSpace B integerBase hZ Y₂)
    (f : X ⟶ yoneda.obj Q) (g₁ : Y₁ ⟶ yoneda.obj Q) (g₂ : Y₂ ⟶ yoneda.obj Q)
    (hfl : Space.IsFlat B integerBase hZ f) (hpr : Space.IsProper B integerBase hZ f)
    (hfp : Space.IsFinitePresentation B integerBase hZ f)
    (hd : Space.HasRelativeDimensionLE 1 B integerBase hZ f)
    (hfl₁ : Space.IsFlat B integerBase hZ g₁) (hpr₁ : Space.IsProper B integerBase hZ g₁)
    (hfp₁ : Space.IsFinitePresentation B integerBase hZ g₁)
    (hd₁ : Space.HasRelativeDimensionLE 1 B integerBase hZ g₁)
    (hfl₂ : Space.IsFlat B integerBase hZ g₂) (hpr₂ : Space.IsProper B integerBase hZ g₂)
    (hfp₂ : Space.IsFinitePresentation B integerBase hZ g₂)
    (hd₂ : Space.HasRelativeDimensionLE 1 B integerBase hZ g₂)
    (c₁ : X ⟶ Y₁) (c₂ : X ⟶ Y₂) (hc₁ : c₁ ≫ g₁ = f) (hc₂ : c₂ ≫ g₂ = f)
    (s : Q.left.1) {VX V₁ V₂ : BigFppfOver B integerBase hZ}
    (vX : VX ⟶ (residueFieldValuedPoint B hZ Q s).siteObject)
    (v₁ : V₁ ⟶ (residueFieldValuedPoint B hZ Q s).siteObject)
    (v₂ : V₂ ⟶ (residueFieldValuedPoint B hZ Q s).siteObject)
    (qX : yoneda.obj VX ⟶ X) (q₁ : yoneda.obj V₁ ⟶ Y₁) (q₂ : yoneda.obj V₂ ⟶ Y₂)
    (hqX : IsPullback qX (yoneda.map vX) f (yoneda.map (residueFieldValuedPoint B hZ Q s).value))
    (hq₁ : IsPullback q₁ (yoneda.map v₁) g₁ (yoneda.map (residueFieldValuedPoint B hZ Q s).value))
    (hq₂ : IsPullback q₂ (yoneda.map v₂) g₂ (yoneda.map (residueFieldValuedPoint B hZ Q s).value))
    (a₁ : VX ⟶ V₁) (a₂ : VX ⟶ V₂) (hav₁ : a₁ ≫ v₁ = vX) (hav₂ : a₂ ≫ v₂ = vX)
    (hqa₁ : qX ≫ c₁ = yoneda.map a₁ ≫ q₁) (hqa₂ : qX ≫ c₂ = yoneda.map a₂ ≫ q₂)
    (φ : V₁ ≅ V₂) (hφv : φ.hom ≫ v₂ = v₁) (hφa : a₁ ≫ φ.hom = a₂)
    (h0 : IsIso (SheafOfModules.unitToPushforwardObjUnit ((𝒯).map a₁).toRingCatSheafHom))
    (hR : IsZero (((Scheme.Modules.pushforward ((𝒯).map a₁)).rightDerived 1).obj
      (SheafOfModules.unit ((𝒯).obj VX).ringCatSheaf))) :
    ∃ (W : BigFppfOver B integerBase hZ) (j : W ⟶ Q),
      IsOpenImmersion ((𝒯).map j) ∧ s ∈ Set.range ((𝒯).map j) ∧
      ∃ ψ : pullback g₁ (yoneda.map j) ≅ pullback g₂ (yoneda.map j),
        ψ.hom ≫ pullback.snd g₂ (yoneda.map j) = pullback.snd g₁ (yoneda.map j) ∧
        pullback.map f (yoneda.map j) g₁ (yoneda.map j) c₁ (𝟙 _) (𝟙 _) (by simp [hc₁])
            (by simp) ≫ ψ.hom =
          pullback.map f (yoneda.map j) g₂ (yoneda.map j) c₂ (𝟙 _) (𝟙 _) (by simp [hc₂])
            (by simp) := by
  have sX := isPullback_pointFieldMap_of_isPullback s f hqX
  have s₁ := isPullback_pointFieldMap_of_isPullback s g₁ hq₁
  have s₂ := isPullback_pointFieldMap_of_isPullback s g₂ hq₂
  have ha₁ := yoneda_map_comp_isoPullback_hom (Space.pointFieldMap Q s) c₁ hc₁ sX s₁ a₁
    (by rw [← Category.assoc, hav₁]) hqa₁
  have ha₂ := yoneda_map_comp_isoPullback_hom (Space.pointFieldMap Q s) c₂ hc₂ sX s₂ a₂
    (by rw [← Category.assoc, hav₂]) hqa₂
  have hR' : IsZero (Stacks.AlgebraicGeometry.TopDegreeBaseChange.firstDirectImageStructureSheaf
      ((𝒯).map a₁)) := by
    let := HasDerivedCategory.standard ((𝒯).obj VX).Modules
    let := HasDerivedCategory.standard ((𝒯).obj V₁).Modules
    exact (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff
      (Scheme.Modules.pushforward ((𝒯).map a₁)) (m := (1 : ℤ)) (n := 1) rfl _).2 hR
  let φ' := s₁.isoPullback.symm ≪≫ yoneda.mapIso φ ≪≫ s₂.isoPullback
  have hφ' : φ'.hom ≫ pullback.snd g₂ (yoneda.map (Space.pointFieldMap Q s)) =
      pullback.snd g₁ (yoneda.map (Space.pointFieldMap Q s)) := by
    simp only [φ', Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
      IsPullback.isoPullback_hom_snd]
    rw [← Functor.map_comp, ← Category.assoc φ.hom, hφv, IsPullback.isoPullback_inv_snd]
  have hφc' : pullback.map f (yoneda.map (Space.pointFieldMap Q s)) g₁
        (yoneda.map (Space.pointFieldMap Q s)) c₁ (𝟙 _) (𝟙 _) (by simp [hc₁]) (by simp) ≫
        φ'.hom =
      pullback.map f (yoneda.map (Space.pointFieldMap Q s)) g₂
        (yoneda.map (Space.pointFieldMap Q s)) c₂ (𝟙 _) (𝟙 _) (by simp [hc₂]) (by simp) := by
    rw [← Iso.cancel_iso_hom_left sX.isoPullback, ← reassoc_of% ha₁, ← ha₂, ← hφa]
    simp [φ']
  obtain ⟨W, j, hj, hs, ψ, -, hψs, hψc, -⟩ := Space.exists_iso_near_point_of_iso_fibre Q s hX hY₁
    hY₂ f g₁ g₂ hfl hpr hfp hd hfl₁ hpr₁ hfp₁ hd₁ hfl₂ hpr₂ hfp₂ hd₂ c₁ c₂ hc₁ hc₂ sX.isoPullback
    s₁.isoPullback (vX ≫ (pointFieldObjectIso Q s).inv) (v₁ ≫ (pointFieldObjectIso Q s).inv)
    sX.isoPullback_hom_snd s₁.isoPullback_hom_snd a₁ ha₁ h0 hR' φ' hφ' hφc'
  exact ⟨W, j, hj, hs, ψ, hψs, hψc⟩

/-- **Stacks 0E89 for families of curves**, in the form of
`AlgebraicGeometry.CurveFamily.ExtendsFibreIsoNearPoint`; it is
`AlgebraicGeometry.Space.exists_iso_near_point_of_iso_fibre`. -/
theorem extendsFibreIsoNearPoint : ExtendsFibreIsoNearPoint B hZ := by
  intro X Y₁ Y₂ hb₁ hb₂ c₁ c₂ hc₁ hc₂ s VX V₁ V₂ vX v₁ v₂ qX q₁ q₂ hqX hq₁ hq₂ a₁ a₂ hav₁ hav₂
    hqa₁ hqa₂ φ hφv hφa h0 hR
  obtain ⟨hfl₁, hpr₁, hfp₁, hd₁⟩ := curveFamilyConditions_toBase_comp_eqToHom Y₁ hb₁
  obtain ⟨hfl₂, hpr₂, hfp₂, hd₂⟩ := curveFamilyConditions_toBase_comp_eqToHom Y₂ hb₂
  obtain ⟨W, j, hj, hs, ψ, hψs, hψc⟩ := exists_iso_near_point_of_isPullback_fibres X.base
    X.total.2 Y₁.total.2 Y₂.total.2 X.toBase.hom
    (Y₁.toBase ≫ eqToHom (congrArg schemeSpace hb₁)).hom
    (Y₂.toBase ≫ eqToHom (congrArg schemeSpace hb₂)).hom X.flat X.proper X.finitePresentation
    X.relativeDimensionLE hfl₁ hpr₁ hfp₁ hd₁ hfl₂ hpr₂ hfp₂ hd₂ c₁.hom c₂.hom
    (congrArg (fun m => m.hom) hc₁) (congrArg (fun m => m.hom) hc₂) s vX v₁ v₂ qX.hom q₁.hom
    q₂.hom (AlgebraicSpaces.isPullback_hom B integerBase hZ hqX)
    (AlgebraicSpaces.isPullback_hom B integerBase hZ hq₁)
    (AlgebraicSpaces.isPullback_hom B integerBase hZ hq₂) a₁ a₂ hav₁ hav₂
    (congrArg (fun m => m.hom) hqa₁) (congrArg (fun m => m.hom) hqa₂) φ hφv hφa h0 hR
  refine ⟨W, j, hj, hs, (ObjectProperty.fullyFaithfulι _).preimageIso ψ,
    ObjectProperty.hom_ext _ hψs, ObjectProperty.hom_ext _ ?_⟩
  show (Space.structureContractionBaseChange B integerBase hZ c₁ hc₁ (schemeSpaceMap j)).hom ≫
      ψ.hom = (Space.structureContractionBaseChange B integerBase hZ c₂ hc₂ (schemeSpaceMap j)).hom
  rw [Space.structureContractionBaseChange_hom, Space.structureContractionBaseChange_hom]
  exact hψc

end CurveFamily

end AlgebraicGeometry

end

module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalConnectionCrisTransition

/-!
# The canonical connection of a crystal on `Cris(X/S)` is integrable

Fix a global crystalline situation of [Stacks, Tag 07MF] and a crystal `F` in `𝒪_{X/S}`-modules
on `Cris(X/S)`, with its canonical connection `∇ : F ⟶ F ⊗ Ω_{X/S}`
(`...SmallSite.crystalConnectionCris`).  This module builds the extension

`∇ : F ⊗_{𝒪_{X/S}} Ω_{X/S} ⟶ F ⊗_{𝒪_{X/S}} Ω²_{X/S}`

of [Stacks, Section 60.15, Tag 07J5] as a morphism of abelian sheaves on `Cris(X/S)`
(`crystalExtensionCris`), proves that it is given by the rule `∇(s ⊗ ω) = ∇(s) ∧ ω + s ⊗ d ω`
(`crystalExtensionCris_tmul`), and that the composite

`F ⟶ F ⊗ Ω_{X/S} ⟶ F ⊗ Ω²_{X/S}`

vanishes (`crystalConnectionCris_comp_crystalExtensionCris`): the connection is integrable.

## Main definitions

* `crystalExtensionCris` — the extension `F ⊗ Ω ⟶ F ⊗ Ω²`.
* `crystalWedgeCris` — the exterior multiplication `z ↦ z ∧ ω` on the sections of `F ⊗ Ω_{X/S}`
  over an object, by a section `ω` of `Ω_{X/S}` there.

## Main results

* `crystalWedgeCris_toSheafify` — the exterior multiplication is `(x ⊗ η) ∧ ω = x ⊗ (η ∧ ω)`.
* `crystalExtensionCris_tmul` — **the rule of [Stacks, Tag 07I0]**.
* `crystalConnectionCris_comp_crystalExtensionCris` — **integrability**.

## References

* [Stacks Project, Lemma 60.15.1, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Section 60.15, Tag 07J5](https://stacks.math.columbia.edu/tag/07J5)
* [Stacks Project, Tag 07I0](https://stacks.math.columbia.edu/tag/07I0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
open TopologicalSpace
open scoped TensorProduct

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

attribute [local instance] monoidalCategorySchemeModules moduleCrysFormRingSections

variable {S : GlobalCrystallineSituation.{u}} {F : SheafOfModules.{u} (structureSheaf S)}
  (hF : IsSheafCrystal F)

/-! ### The transition maps, read back from the sheaves -/

/-- `τ_g` read back from the restriction of `F ⊗ Ω_{X/S}` along `g`. -/
theorem tensorFormsAmbientIsoOne_hom_map {A B : CrystallineThickening S} (g : B ⟶ A)
    (q : (tensorDifferentialFormsSheaf F 1).obj.obj (op (A.restrictOpen ⊤))) :
    ((tensorFormsAmbientIsoOne B).hom.app (op (g.hom.targetHom.hom ⁻¹ᵁ ⊤))
        ((tensorDifferentialFormsSheaf F 1).obj.map
          (CrystallineThickening.restrictOpenMap g ⊤).op q)).down =
      crystalTensorTransition g hF ⊤ ((tensorFormsAmbientIsoOne A).hom.app (op ⊤) q).down := by
  have hq : (tensorFormsAmbientIsoOne A).inv.app (op ⊤)
      (ULift.up ((tensorFormsAmbientIsoOne A).hom.app (op ⊤) q).down) = q :=
    Iso.hom_inv_id_apply ((tensorFormsAmbientIsoOne (F := F) A).app (op ⊤)) q
  have h := tensorFormsAmbientIsoOne_map g hF ⊤ ((tensorFormsAmbientIsoOne A).hom.app (op ⊤) q).down
  rw [hq] at h
  rw [h]
  exact congrArg ULift.down (Iso.inv_hom_id_apply
    ((tensorFormsAmbientIsoOne (F := F) B).app (op (g.hom.targetHom.hom ⁻¹ᵁ ⊤))) _)

/-! ### The extension -/

/-- **The extension `F ⊗ Ω_{X/S} ⟶ F ⊗ Ω²_{X/S}` on the sections over an object `A`**: a section
is read on the ambient scheme `T` in `F_T ⊗ Ω_{T/S,δ}`, sent to `F_T ⊗ Ω²_{T/S,δ}` by the
extension of [Stacks, Tag 07I0] of the canonical connection
(`...SmallSite.crystalConnectionExtensionApp`), and read back. -/
def crystalExtensionCrisApp (A : CrystallineThickening S) :
    (tensorDifferentialFormsSheaf F 1).obj.obj (op A) ⟶
      (tensorDifferentialFormsSheaf F 2).obj.obj (op A) :=
  (tensorDifferentialFormsSheaf F 1).obj.map (A.restrictOpenHom ⊤).op ≫
    (tensorFormsAmbientIsoOne A).hom.app (op ⊤) ≫
      AddCommGrpCat.uliftFunctor.{u + 1, u}.map
        (AddCommGrpCat.ofHom (crystalConnectionExtensionApp A hF ⊤)) ≫
      (tensorFormsAmbientIsoTwo A).inv.app (op ⊤) ≫
        (restrictTopIso (tensorDifferentialFormsSheaf F 2).obj A).inv

/-- The defining property of `crystalExtensionCrisApp`. -/
theorem crystalExtensionCrisApp_restrict (A : CrystallineThickening S)
    (t : (tensorDifferentialFormsSheaf F 1).obj.obj (op A)) :
    (tensorDifferentialFormsSheaf F 2).obj.map (A.restrictOpenHom ⊤).op
        (crystalExtensionCrisApp hF A t) =
      (tensorFormsAmbientIsoTwo A).inv.app (op ⊤) (ULift.up (crystalConnectionExtensionApp A hF ⊤
        ((tensorFormsAmbientIsoOne A).hom.app (op ⊤)
          ((tensorDifferentialFormsSheaf F 1).obj.map (A.restrictOpenHom ⊤).op t)).down)) :=
  Iso.inv_hom_id_apply (restrictTopIso (tensorDifferentialFormsSheaf F 2).obj A) _

/-- Restriction to `B|_T` after `g` is restriction to `A|_T` followed by `restrictOpenMap g ⊤`. -/
theorem map_restrictOpenHom_map_eq {A B : CrystallineThickening S} (g : B ⟶ A)
    (G : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (t : G.obj (op A)) :
    G.map (B.restrictOpenHom ⊤).op (G.map g.op t) =
      G.map (CrystallineThickening.restrictOpenMap g ⊤).op (G.map (A.restrictOpenHom ⊤).op t) :=
  (presheaf_map_comp_apply _ _ _ _).symm.trans
    ((congrArg (fun k ↦ G.map k.op t)
      (CrystallineThickening.restrictOpenMap_restrictOpenHom g ⊤).symm).trans
      (presheaf_map_comp_apply _ _ _ _))

/-- **The extension is natural in the object of `Cris(X/S)`.** -/
theorem crystalExtensionCrisApp_naturality {A B : CrystallineThickening S} (g : B ⟶ A)
    (t : (tensorDifferentialFormsSheaf F 1).obj.obj (op A)) :
    crystalExtensionCrisApp hF B ((tensorDifferentialFormsSheaf F 1).obj.map g.op t) =
      (tensorDifferentialFormsSheaf F 2).obj.map g.op (crystalExtensionCrisApp hF A t) := by
  apply injective_restrictTop (tensorDifferentialFormsSheaf F 2).obj B
  refine (crystalExtensionCrisApp_restrict hF B _).trans
    (Eq.trans ?_ (map_restrictOpenHom_map_eq g _ _).symm)
  refine Eq.trans ?_ (congrArg ((tensorDifferentialFormsSheaf F 2).obj.map
    (CrystallineThickening.restrictOpenMap g ⊤).op) (crystalExtensionCrisApp_restrict hF A t)).symm
  refine Eq.trans ?_ (tensorFormsAmbientIsoTwo_map g ⊤ _).symm
  refine Eq.trans ?_ (congrArg (fun w ↦ (tensorFormsAmbientIsoTwo B).inv.app
    (op (g.hom.targetHom.hom ⁻¹ᵁ ⊤)) (ULift.up w))
    (tensorTransitionTwo_crystalConnectionExtensionApp hF g ⊤ _)).symm
  refine congrArg (fun w ↦ (tensorFormsAmbientIsoTwo B).inv.app
    (op (g.hom.targetHom.hom ⁻¹ᵁ ⊤)) (ULift.up (crystalConnectionExtensionApp B hF _ w))) ?_
  refine Eq.trans ?_ (tensorFormsAmbientIsoOne_hom_map hF g _)
  exact congrArg (fun q ↦ ((tensorFormsAmbientIsoOne B).hom.app
    (op (g.hom.targetHom.hom ⁻¹ᵁ ⊤)) q).down) (map_restrictOpenHom_map_eq g _ t)

/-- **The extension `∇ : F ⊗ Ω_{X/S} ⟶ F ⊗ Ω²_{X/S}` of the canonical connection**, as a morphism
of abelian sheaves on `Cris(X/S)`. -/
def crystalExtensionCris : tensorDifferentialFormsSheaf F 1 ⟶ tensorDifferentialFormsSheaf F 2 :=
  ⟨{ app := fun A ↦ crystalExtensionCrisApp hF A.unop
     naturality := fun {A B} g ↦ by
       ext t
       exact crystalExtensionCrisApp_naturality hF g.unop t }⟩

/-- The identification of degree one carries `∇` read on `A|_T` back to the connection on `T`. -/
theorem tensorFormsAmbientIsoOne_hom_restrict_crystalConnectionCrisApp (A : CrystallineThickening S)
    (s : (abelianSheaf F).obj.obj (op A)) :
    (tensorFormsAmbientIsoOne A).hom.app (op ⊤)
        ((tensorDifferentialFormsSheaf F 1).obj.map (A.restrictOpenHom ⊤).op
          (crystalConnectionCrisApp hF A s)) =
      ULift.up (crystalConnectionApp A hF ⊤ (F.val.map (A.restrictOpenHom ⊤).op s.down)) :=
  (congrArg ((tensorFormsAmbientIsoOne A).hom.app (op ⊤))
    (crystalConnectionCrisApp_restrict hF A s)).trans
    (Iso.inv_hom_id_apply ((tensorFormsAmbientIsoOne (F := F) A).app (op ⊤)) _)

/-- **Integrability, on sections**: `∇(∇(s)) = 0`. -/
theorem crystalExtensionCrisApp_crystalConnectionCrisApp (A : CrystallineThickening S)
    (s : (abelianSheaf F).obj.obj (op A)) :
    crystalExtensionCrisApp hF A (crystalConnectionCrisApp hF A s) = 0 := by
  apply injective_restrictTop (tensorDifferentialFormsSheaf F 2).obj A
  refine (crystalExtensionCrisApp_restrict hF A _).trans (Eq.trans ?_ (map_zero _).symm)
  have e2 : crystalConnectionExtensionApp A hF ⊤ ((tensorFormsAmbientIsoOne A).hom.app (op ⊤)
      ((tensorDifferentialFormsSheaf F 1).obj.map (A.restrictOpenHom ⊤).op
        (crystalConnectionCrisApp hF A s))).down = 0 := by
    rw [tensorFormsAmbientIsoOne_hom_restrict_crystalConnectionCrisApp hF A s]
    exact crystalConnectionExtensionApp_crystalConnectionApp A hF ⊤ _
  rw [e2]
  exact map_zero _

/-- **Integrability**: `∇ ∘ ∇ = 0` as morphisms of sheaves `F ⟶ F ⊗ Ω²_{X/S}`. -/
theorem crystalConnectionCris_comp_crystalExtensionCris :
    crystalConnectionCris hF ≫ crystalExtensionCris hF = 0 :=
  Sheaf.hom_ext (NatTrans.ext (funext fun A ↦ AddCommGrpCat.hom_ext (AddMonoidHom.ext fun s ↦
    crystalExtensionCrisApp_crystalConnectionCrisApp hF A.unop s)))

/-! ### The rule of [Stacks, Tag 07I0] -/

/-- The exterior product `η ∧ ω ∈ Ω²_{X/S}(B)` of two sections of `Ω^1_{X/S}`. -/
def formsWedgeOne {B : CrystallineThickening S} (η ω : (crysDifferentialForms S 1).obj (op B)) :
    (crysDifferentialForms S 2).obj (op B) :=
  formsWedge (formsOneEquiv B η) (formsOneEquiv B ω)

/-- The exterior product of two sections of `Ω^1_{X/S}` is natural in the object. -/
theorem formsWedgeOne_map {B B' : CrystallineThickening S} (k : B ⟶ B')
    (η ω : (crysDifferentialForms S 1).obj (op B')) :
    (crysDifferentialForms S 2).map k.op (formsWedgeOne η ω) =
      formsWedgeOne ((crysDifferentialForms S 1).map k.op η)
        ((crysDifferentialForms S 1).map k.op ω) :=
  (formsWedge_map k _ _).trans (congrArg₂ formsWedge (formsOneEquiv_map k η).symm
    (formsOneEquiv_map k ω).symm)

/-- The comparison of degree-two forms on an exterior product of degree-one forms. -/
theorem formsComparisonTwo_formsWedgeOne (A : CrystallineThickening S)
    (V : A.obj.thickening.target.scheme.Opens)
    (η ω : (crysDifferentialForms S 1).obj (op (A.restrictOpen V))) :
    (formsComparisonTwo A).toFun V (formsWedgeOne η ω) =
      (dpWedge A.obj.thickening.target S.S.scheme A.obj.toBase.hom).app (op V)
        (formsCompOne A V η) (formsCompOne A V ω) :=
  formsComparisonTwo_formsWedge A V _ _

variable (F) in
/-- **The exterior multiplication `z ↦ z ∧ ω` on `(F ⊗ Ω_{X/S})(A)`** by a section `ω` of
`Ω^1_{X/S}` over `A`: on the ambient scheme `T` it is `(x ⊗ η) ∧ ω = x ⊗ (η ∧ ω)` on
`F_T ⊗ Ω_{T/S,δ}`. -/
def crystalWedgeCrisApp (A : CrystallineThickening S)
    (ω : (crysDifferentialForms S 1).obj (op A)) :
    (tensorDifferentialFormsSheaf F 1).obj.obj (op A) ⟶
      (tensorDifferentialFormsSheaf F 2).obj.obj (op A) :=
  (tensorDifferentialFormsSheaf F 1).obj.map (A.restrictOpenHom ⊤).op ≫
    (tensorFormsAmbientIsoOne A).hom.app (op ⊤) ≫
      AddCommGrpCat.uliftFunctor.{u + 1, u}.map
        (AddCommGrpCat.ofHom (crystalWedgeHom (M := F) A ⊤ (formsCompOne A ⊤
          ((crysDifferentialForms S 1).map (A.restrictOpenHom ⊤).op ω)))) ≫
      (tensorFormsAmbientIsoTwo A).inv.app (op ⊤) ≫
        (restrictTopIso (tensorDifferentialFormsSheaf F 2).obj A).inv

/-- The defining property of `crystalWedgeCrisApp`. -/
theorem crystalWedgeCrisApp_restrict (A : CrystallineThickening S)
    (ω : (crysDifferentialForms S 1).obj (op A))
    (t : (tensorDifferentialFormsSheaf F 1).obj.obj (op A)) :
    (tensorDifferentialFormsSheaf F 2).obj.map (A.restrictOpenHom ⊤).op
        (crystalWedgeCrisApp F A ω t) =
      (tensorFormsAmbientIsoTwo A).inv.app (op ⊤) (ULift.up (crystalWedge F A ⊤
        ((tensorFormsAmbientIsoOne A).hom.app (op ⊤)
          ((tensorDifferentialFormsSheaf F 1).obj.map (A.restrictOpenHom ⊤).op t)).down
        (formsCompOne A ⊤ ((crysDifferentialForms S 1).map (A.restrictOpenHom ⊤).op ω)))) :=
  Iso.inv_hom_id_apply (restrictTopIso (tensorDifferentialFormsSheaf F 2).obj A) _

/-- Restriction to `A|_T` commutes with the map to the sheafification of `F ⊗ Ω^n`. -/
private theorem restrictOpenHom_toSheafify (n : ℕ) (A : CrystallineThickening S)
    (u : (tensorDifferentialFormsPresheaf F n).obj (op A)) :
    (CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F n)).app
        (op (A.restrictOpen ⊤)) ((tensorDifferentialFormsPresheaf F n).map
          (A.restrictOpenHom ⊤).op u) =
      (tensorDifferentialFormsSheaf F n).obj.map (A.restrictOpenHom ⊤).op
        ((CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F n)).app
          (op A) u) :=
  ConcreteCategory.congr_hom ((CategoryTheory.toSheafify (smallTopology S)
    (tensorDifferentialFormsPresheaf F n)).naturality (A.restrictOpenHom ⊤).op) u

/-- The identification of degree one on the image of a pure tensor over `A`, read on `A|_T`. -/
theorem tensorFormsAmbientIsoOne_hom_restrict_toSheafify (A : CrystallineThickening S)
    (x : F.val.obj (op A)) (η : (crysDifferentialForms S 1).obj (op A)) :
    ((tensorFormsAmbientIsoOne A).hom.app (op ⊤)
      ((tensorDifferentialFormsSheaf F 1).obj.map (A.restrictOpenHom ⊤).op
        ((CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F 1)).app
          (op A) (ULift.up (formsTmul F x η))))).down =
      firstOrderTensorTmul F A ⊤ (F.val.map (A.restrictOpenHom ⊤).op x)
        (formsCompOne A ⊤ ((crysDifferentialForms S 1).map (A.restrictOpenHom ⊤).op η)) := by
  exact (congrArg (fun q ↦ ((tensorFormsAmbientIsoOne A).hom.app (op ⊤) q).down)
    (restrictOpenHom_toSheafify 1 A (ULift.up (formsTmul F x η))).symm).trans
    (congrArg ULift.down (tensorFormsAmbientIso_hom_app_toSheafify F (formsComparisonOne A) ⊤
      (F.val.map (A.restrictOpenHom ⊤).op x) ((crysDifferentialForms S 1).map
        (A.restrictOpenHom ⊤).op η)))

/-- The inverse identification of degree two on a pure tensor, written over `A`. -/
theorem tensorFormsAmbientIsoTwo_inv_restrict (A : CrystallineThickening S)
    (x : F.val.obj (op A)) (θ : (crysDifferentialForms S 2).obj (op A)) :
    (tensorFormsAmbientIsoTwo A).inv.app (op ⊤) (ULift.up (secondOrderTensorTmul F A ⊤
        (F.val.map (A.restrictOpenHom ⊤).op x)
        ((formsComparisonTwo A).toFun ⊤ ((crysDifferentialForms S 2).map
          (A.restrictOpenHom ⊤).op θ)))) =
      (tensorDifferentialFormsSheaf F 2).obj.map (A.restrictOpenHom ⊤).op
        ((CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F 2)).app
          (op A) (ULift.up (formsTmul F x θ))) :=
  (tensorFormsAmbientIso_inv_tmul F (formsComparisonTwo A) ⊤ _ _).trans
    (restrictOpenHom_toSheafify 2 A (ULift.up (formsTmul F x θ)))

/-- **The exterior multiplication is `(x ⊗ η) ∧ ω = x ⊗ (η ∧ ω)`.** -/
theorem crystalWedgeCrisApp_toSheafify (A : CrystallineThickening S)
    (ω : (crysDifferentialForms S 1).obj (op A)) (x : F.val.obj (op A))
    (η : (crysDifferentialForms S 1).obj (op A)) :
    crystalWedgeCrisApp F A ω
        ((CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F 1)).app
          (op A) (ULift.up (formsTmul F x η))) =
      (CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F 2)).app
        (op A) (ULift.up (formsTmul F x (formsWedgeOne η ω))) := by
  apply injective_restrictTop (tensorDifferentialFormsSheaf F 2).obj A
  refine (crystalWedgeCrisApp_restrict A ω _).trans ?_
  have h2 : crystalWedge F A ⊤ ((tensorFormsAmbientIsoOne A).hom.app (op ⊤)
      ((tensorDifferentialFormsSheaf F 1).obj.map (A.restrictOpenHom ⊤).op
        ((CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F 1)).app
          (op A) (ULift.up (formsTmul F x η))))).down
        (formsCompOne A ⊤ ((crysDifferentialForms S 1).map (A.restrictOpenHom ⊤).op ω)) =
      secondOrderTensorTmul F A ⊤ (F.val.map (A.restrictOpenHom ⊤).op x)
        ((formsComparisonTwo A).toFun ⊤ ((crysDifferentialForms S 2).map
          (A.restrictOpenHom ⊤).op (formsWedgeOne η ω))) := by
    refine (congrArg (fun z ↦ crystalWedge F A ⊤ z
      (formsCompOne A ⊤ ((crysDifferentialForms S 1).map (A.restrictOpenHom ⊤).op ω)))
      (tensorFormsAmbientIsoOne_hom_restrict_toSheafify A x η)).trans ?_
    refine (crystalWedge_tmul F A ⊤ (F.val.map (A.restrictOpenHom ⊤).op x) _ _).trans ?_
    exact congrArg (secondOrderTensorTmul F A ⊤ (F.val.map (A.restrictOpenHom ⊤).op x))
      ((formsComparisonTwo_formsWedgeOne A ⊤ _ _).symm.trans
        (congrArg ((formsComparisonTwo A).toFun ⊤) (formsWedgeOne_map _ η ω).symm))
  rw [h2]
  exact tensorFormsAmbientIsoTwo_inv_restrict A x _

/-- The extension on the image of a pure tensor, read on `A|_T`. -/
theorem crystalConnectionExtensionApp_restrict_toSheafify (A : CrystallineThickening S)
    (s : F.val.obj (op A)) (ω : (crysDifferentialForms S 1).obj (op A)) :
    crystalConnectionExtensionApp A hF ⊤ ((tensorFormsAmbientIsoOne A).hom.app (op ⊤)
      ((tensorDifferentialFormsSheaf F 1).obj.map (A.restrictOpenHom ⊤).op
        ((CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F 1)).app
          (op A) (ULift.up (formsTmul F s ω))))).down =
      crystalWedge F A ⊤ (crystalConnectionApp A hF ⊤ (F.val.map (A.restrictOpenHom ⊤).op s))
          (formsCompOne A ⊤ ((crysDifferentialForms S 1).map (A.restrictOpenHom ⊤).op ω)) +
        secondOrderTensorTmul F A ⊤ (F.val.map (A.restrictOpenHom ⊤).op s)
          ((formsComparisonTwo A).toFun ⊤
            ((crysDifferentialForms S 2).map (A.restrictOpenHom ⊤).op (formsDeRham A ω))) := by
  refine (congrArg (crystalConnectionExtensionApp A hF ⊤)
    (tensorFormsAmbientIsoOne_hom_restrict_toSheafify A s ω)).trans ?_
  refine (crystalConnectionExtensionApp_tmul A hF ⊤ _ _).trans ?_
  refine congrArg (crystalWedge F A ⊤ (crystalConnectionApp A hF ⊤
    (F.val.map (A.restrictOpenHom ⊤).op s)) (formsCompOne A ⊤
      ((crysDifferentialForms S 1).map (A.restrictOpenHom ⊤).op ω)) + ·)
    (congrArg (secondOrderTensorTmul F A ⊤ (F.val.map (A.restrictOpenHom ⊤).op s)) ?_)
  refine (formsComparisonTwo_formsDeRham A ⊤ _).symm.trans ?_
  exact congrArg ((formsComparisonTwo A).toFun ⊤)
    (crysDeRhamDifferential_naturality S 1 (A.restrictOpenHom ⊤) ω).symm

/-- **Stacks Project, Tag 07I0: the extension is given by `∇(s ⊗ ω) = ∇(s) ∧ ω + s ⊗ d ω`**, for
a section `s` of `F` and a section `ω` of `Ω^1_{X/S}` over an object of `Cris(X/S)`. -/
theorem crystalExtensionCrisApp_toSheafify (A : CrystallineThickening S) (s : F.val.obj (op A))
    (ω : (crysDifferentialForms S 1).obj (op A)) :
    crystalExtensionCrisApp hF A
        ((CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F 1)).app
          (op A) (ULift.up (formsTmul F s ω))) =
      crystalWedgeCrisApp F A ω (crystalConnectionCrisApp hF A (ULift.up s)) +
        (show (tensorDifferentialFormsSheaf F 2).obj.obj (op A) from
          (CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F 2)).app
            (op A) (ULift.up (formsTmul F s (formsDeRham A ω)))) := by
  apply injective_restrictTop (tensorDifferentialFormsSheaf F 2).obj A
  refine (crystalExtensionCrisApp_restrict hF A _).trans ?_
  rw [crystalConnectionExtensionApp_restrict_toSheafify hF A s ω, map_add]
  refine (map_add (ConcreteCategory.hom ((tensorFormsAmbientIsoTwo (F := F) A).inv.app (op ⊤)))
    (ULift.up _) (ULift.up _)).trans ?_
  refine congrArg₂ (· + ·) ?_ (tensorFormsAmbientIsoTwo_inv_restrict A s (formsDeRham A ω))
  refine Eq.trans ?_ (crystalWedgeCrisApp_restrict A ω _).symm
  rw [tensorFormsAmbientIsoOne_hom_restrict_crystalConnectionCrisApp hF A (ULift.up s)]
  rfl

/-- The components of `crystalExtensionCris`. -/
theorem crystalExtensionCris_app (A : CrystallineThickening S) :
    (crystalExtensionCris hF).hom.app (op A) = crystalExtensionCrisApp hF A := rfl

/-- The components of `crystalConnectionCris`. -/
theorem crystalConnectionCris_app (A : CrystallineThickening S) :
    (crystalConnectionCris hF).hom.app (op A) = crystalConnectionCrisApp hF A := rfl

/-- **The rule of [Stacks, Tag 07I0] determines the extension**: a morphism of sheaves
`F ⊗ Ω_{X/S} ⟶ F ⊗ Ω²_{X/S}` which on local pure tensors is `s ⊗ ω ↦ ∇(s) ∧ ω + s ⊗ d ω` is
`crystalExtensionCris`. -/
theorem eq_crystalExtensionCris
    (E : tensorDifferentialFormsSheaf F 1 ⟶ tensorDifferentialFormsSheaf F 2)
    (hE : ∀ (A : CrystallineThickening S) (s : F.val.obj (op A))
      (ω : (crysDifferentialForms S 1).obj (op A)),
      E.hom.app (op A)
          ((CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F 1)).app
            (op A) (ULift.up (formsTmul F s ω))) =
        crystalWedgeCrisApp F A ω (crystalConnectionCrisApp hF A (ULift.up s)) +
          (show (tensorDifferentialFormsSheaf F 2).obj.obj (op A) from
            (CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F 2)).app
              (op A) (ULift.up (formsTmul F s (formsDeRham A ω))))) :
    E = crystalExtensionCris hF := by
  refine Sheaf.hom_ext (sheafify_hom_ext (smallTopology S) _ _
    (tensorDifferentialFormsSheaf F 2).property ?_)
  refine NatTrans.ext (funext fun A ↦ AddCommGrpCat.hom_ext (AddMonoidHom.ext fun p ↦ ?_))
  induction A with | op A => ?_
  obtain ⟨p⟩ := p
  change F.val.obj (op A) ⊗[crysFormRing S A] (crysDifferentialForms S 1).obj (op A) at p
  let L := (E.hom.app (op A)).hom.comp ((CategoryTheory.toSheafify (smallTopology S)
    (tensorDifferentialFormsPresheaf F 1)).app (op A)).hom
  let R := ((crystalExtensionCris hF).hom.app (op A)).hom.comp ((CategoryTheory.toSheafify
    (smallTopology S) (tensorDifferentialFormsPresheaf F 1)).app (op A)).hom
  have key : ∀ q : F.val.obj (op A) ⊗[crysFormRing S A] (crysDifferentialForms S 1).obj (op A),
      L (ULift.up q) = R (ULift.up q) := by
    intro q
    induction q using TensorProduct.inductionOn with
    | tmul s ω =>
      exact (hE A s ω).trans (crystalExtensionCrisApp_toSheafify hF A s ω).symm
    | add q q' hq hq' =>
      have e : (ULift.up (q + q') : (tensorDifferentialFormsPresheaf F 1).obj (op A)) =
          ULift.up q + ULift.up q' := rfl
      exact (congrArg L e).trans ((L.map_add _ _).trans ((congrArg₂ (· + ·) hq hq').trans
        ((R.map_add _ _).symm.trans (congrArg R e).symm)))
  exact key p

end Crystalline.GlobalCrystallineSituation.SmallSite

end

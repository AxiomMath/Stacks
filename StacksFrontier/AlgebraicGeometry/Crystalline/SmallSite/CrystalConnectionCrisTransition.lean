module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalTensorFormsWedge

/-!
# The degree-one extension of the canonical connection commutes with the transition maps

Fix a global crystalline situation of [Stacks, Tag 07MF], a crystal `F` in `𝒪_{X/S}`-modules on
`Cris(X/S)` and a morphism `g : B ⟶ A` of `Cris(X/S)`.  On the ambient scheme `T_A` the sheaf
`F ⊗ Ω²_{X/S}` is `F_{T_A} ⊗ Ω²_{T_A/S,δ}` (`...SmallSite.tensorFormsAmbientIso`), and the
transition map of `F ⊗ Ω²_{X/S}` along `g` becomes a map
`τ²_g : F_{T_A} ⊗ Ω²_{T_A/S,δ} ⟶ g_*(F_{T_B} ⊗ Ω²_{T_B/S,δ})` (`tensorTransitionTwo`).  This module
proves that it is `x ⊗ (η ∧ ω) ↦ g^* x ⊗ (g^* η ∧ g^* ω)` and `x ⊗ d ω ↦ g^* x ⊗ d (g^* ω)`, and
deduces that the degree-one extension `F_T ⊗ Ω ⟶ F_T ⊗ Ω²` of [Stacks, Tag 07I0] of the canonical
connection commutes with the transition maps:

`τ²_g ∘ ∇ = ∇ ∘ τ_g`.

## Main results

* `tensorTransitionTwo_crystalWedge`, `tensorTransitionTwo_tmul_dpDeRham` — the transition maps of
  `F ⊗ Ω²_{X/S}` on the two kinds of sections.
* `tensorTransitionTwo_crystalConnectionExtensionApp` — **the extension commutes with the
  transition maps.**

## References

* [Stacks Project, Lemma 60.15.1, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Section 60.15, Tag 07J5](https://stacks.math.columbia.edu/tag/07J5)
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

/-- The identification `(F ⊗ Ω²_{X/S})_{T_A} ≅ F_{T_A} ⊗ Ω²_{T_A/S,δ}`. -/
abbrev tensorFormsAmbientIsoTwo (A : CrystallineThickening S) :=
  tensorFormsAmbientIso F (formsComparisonTwo A)

/-- The exterior product of two sections of `Ω_{X/S}` is natural in the object. -/
theorem formsWedge_map {B B' : CrystallineThickening S} (k : B ⟶ B')
    (η ω : (crysDifferentials S).obj (op B')) :
    (crysDifferentialForms S 2).map k.op (formsWedge η ω) =
      formsWedge ((crysDifferentials S).map k.op η) ((crysDifferentials S).map k.op ω) := by
  apply crysFormVal_injective
  refine (PresheafOfModules.extPowSections_map 2 (crysDifferentials S) k.op _).trans ?_
  change ExteriorAlgebra.mapₛₗ _ _ (ExteriorAlgebra.ι _ η * ExteriorAlgebra.ι _ ω) = _
  rw [map_mul, ExteriorAlgebra.mapₛₗ_ι, ExteriorAlgebra.mapₛₗ_ι]
  rfl

/-- **The degree-one forms are locally in the image of `Ω_{X/S}`**: every section of
`Ω_{T/S,δ}` is, on a neighbourhood of every point, the image of a section of `Ω_{X/S}`. -/
theorem exists_restrictedToSheaf_eq (A : CrystallineThickening S)
    {V : A.obj.thickening.target.scheme.Opens}
    (b : (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.obj (op V))
    (x : A.obj.thickening.target.scheme) (hx : x ∈ V) :
    ∃ (V' : A.obj.thickening.target.scheme.Opens) (h : V' ≤ V), x ∈ V' ∧
      ∃ ω : (crysDifferentials S).obj (op (A.restrictOpen V')),
        (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.map
          (homOfLE h).op b = ((restrictedToSheaf A.obj).app (op V')).hom ω := by
  obtain ⟨V', ⟨hV', W, hW, hle⟩, hxV', h⟩ := exists_isAffineOverAffineOpen A.obj V x hx
  obtain ⟨ω, hω⟩ := (bijective_restrictedToSheaf_app S A.obj hV' hle hW).2
    ((dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.map
      (homOfLE h).op b)
  exact ⟨V', h, hxV', ω, hω.symm⟩

section Transition

variable (hF : IsSheafCrystal F) {A B : CrystallineThickening S} (g : B ⟶ A)

/-- The sheaf `F_{T_B} ⊗ Ω²_{T_B/S,δ}`. -/
abbrev tensorTwo (A : CrystallineThickening S) : A.obj.thickening.target.scheme.Modules :=
  secondOrderThickeningTensorSecondExterior A.obj.thickening.target S.S.scheme A.obj.toBase.hom
    (crysAmbientSchemeModules F A)

/-- The sheaf `F_{T_B} ⊗ Ω_{T_B/S,δ}`. -/
abbrev tensorOne (A : CrystallineThickening S) : A.obj.thickening.target.scheme.Modules :=
  firstOrderThickeningTensorDifferentials A.obj.thickening.target S.S.scheme A.obj.toBase.hom
    (crysAmbientSchemeModules F A)

variable (F) in
/-- **The transition map of `F ⊗ Ω²_{X/S}` along `g`, on the ambient scheme of `A`**: a section of
`F_{T_A} ⊗ Ω²_{T_A/S,δ}` over `V` is read in `(F ⊗ Ω²_{X/S})(A|_V)`, restricted along `g`, and
read back in `F_{T_B} ⊗ Ω²_{T_B/S,δ}` over `g⁻¹ V`. -/
def tensorTransitionTwo (V : A.obj.thickening.target.scheme.Opens) :
    (tensorTwo (F := F) A).val.obj (op V) →+
      (tensorTwo (F := F) B).val.obj (op (g.hom.targetHom.hom ⁻¹ᵁ V)) :=
  AddEquiv.ulift.toAddMonoidHom.comp
    (((tensorFormsAmbientIsoTwo B).hom.app (op (g.hom.targetHom.hom ⁻¹ᵁ V))).hom.comp
      (((tensorDifferentialFormsSheaf F 2).obj.map
        (CrystallineThickening.restrictOpenMap g V).op).hom.comp
        (((tensorFormsAmbientIsoTwo A).inv.app (op V)).hom.comp
          AddEquiv.ulift.symm.toAddMonoidHom)))

/-- `τ²_g` is the restriction of `F ⊗ Ω²_{X/S}` along `g`, read through the identifications. -/
theorem tensorFormsAmbientIsoTwo_map (V : A.obj.thickening.target.scheme.Opens)
    (z : (tensorTwo (F := F) A).val.obj (op V)) :
    (tensorDifferentialFormsSheaf F 2).obj.map (CrystallineThickening.restrictOpenMap g V).op
        ((tensorFormsAmbientIsoTwo A).inv.app (op V) (ULift.up z)) =
      (tensorFormsAmbientIsoTwo B).inv.app (op (g.hom.targetHom.hom ⁻¹ᵁ V))
        (ULift.up (tensorTransitionTwo F g V z)) :=
  (ConcreteCategory.congr_hom
    (NatTrans.congr_app (tensorFormsAmbientIsoTwo (F := F) B).hom_inv_id
      (op (g.hom.targetHom.hom ⁻¹ᵁ V))) _).symm

/-- **`τ²_g` on a local pure tensor of the comparison**: `x ⊗ θ ↦ g^* x ⊗ g^* θ`. -/
theorem tensorTransitionTwo_tmul (V : A.obj.thickening.target.scheme.Opens)
    (x : (crysAmbientSchemeModules F A).val.obj (op V))
    (θ : (crysDifferentialForms S 2).obj (op (A.restrictOpen V))) :
    tensorTransitionTwo F g V (secondOrderTensorTmul F A V x ((formsComparisonTwo A).toFun V θ)) =
      secondOrderTensorTmul F B (g.hom.targetHom.hom ⁻¹ᵁ V)
        (crystalRestrict F (CrystallineThickening.restrictOpenMap g V) x)
        ((formsComparisonTwo B).toFun (g.hom.targetHom.hom ⁻¹ᵁ V)
          ((crysDifferentialForms S 2).map (CrystallineThickening.restrictOpenMap g V).op θ)) := by
  change ((tensorFormsAmbientIsoTwo B).hom.app (op (g.hom.targetHom.hom ⁻¹ᵁ V))
    ((tensorDifferentialFormsSheaf F 2).obj.map (CrystallineThickening.restrictOpenMap g V).op
      ((tensorFormsAmbientIsoTwo A).inv.app (op V) (ULift.up _)))).down = _
  rw [tensorFormsAmbientIso_inv_tmul F (formsComparisonTwo A) V x θ]
  refine (congrArg (fun q ↦ ((tensorFormsAmbientIsoTwo B).hom.app
    (op (g.hom.targetHom.hom ⁻¹ᵁ V)) q).down)
    (ConcreteCategory.congr_hom ((CategoryTheory.toSheafify (smallTopology S)
      (tensorDifferentialFormsPresheaf F 2)).naturality
        (CrystallineThickening.restrictOpenMap g V).op) _).symm).trans ?_
  exact congrArg ULift.down (tensorFormsAmbientIso_hom_app_toSheafify F (formsComparisonTwo B)
    (g.hom.targetHom.hom ⁻¹ᵁ V) _ _)

/-- **`τ²_g` commutes with restriction to smaller opens.** -/
theorem tensorTransitionTwo_naturality {V V' : A.obj.thickening.target.scheme.Opens} (h : V' ≤ V)
    (z : (tensorTwo (F := F) A).val.obj (op V)) :
    (tensorTwo (F := F) B).val.map (homOfLE (g.hom.targetHom.hom.preimage_mono h)).op
        (tensorTransitionTwo F g V z) =
      tensorTransitionTwo F g V' ((tensorTwo (F := F) A).val.map (homOfLE h).op z) := by
  change ((ambientTensorSheafULift F _).map (homOfLE (g.hom.targetHom.hom.preimage_mono h)).op
    ((tensorFormsAmbientIsoTwo B).hom.app (op (g.hom.targetHom.hom ⁻¹ᵁ V))
      ((tensorDifferentialFormsSheaf F 2).obj.map (CrystallineThickening.restrictOpenMap g V).op
        ((tensorFormsAmbientIsoTwo A).inv.app (op V) (ULift.up z))))).down = _
  let t := (tensorFormsAmbientIsoTwo A).inv.app (op V) (ULift.up z)
  have key : (tensorDifferentialFormsSheaf F 2).obj.map
      (CrystallineThickening.restrictOpenLE B (g.hom.targetHom.hom.preimage_mono h)).op
        ((tensorDifferentialFormsSheaf F 2).obj.map
          (CrystallineThickening.restrictOpenMap g V).op t) =
      (tensorDifferentialFormsSheaf F 2).obj.map (CrystallineThickening.restrictOpenMap g V').op
        ((tensorFormsAmbientIsoTwo A).inv.app (op V')
          (ULift.up ((tensorTwo (F := F) A).val.map (homOfLE h).op z))) :=
    (presheaf_map_comp_apply _ _ _ _).symm.trans
      ((congrArg (fun k ↦ (tensorDifferentialFormsSheaf F 2).obj.map k.op t)
        (CrystallineThickening.restrictOpenLE_restrictOpenMap g h)).trans
        ((presheaf_map_comp_apply _ _ _ _).trans
          (congrArg ((tensorDifferentialFormsSheaf F 2).obj.map
            (CrystallineThickening.restrictOpenMap g V').op)
            (tensorFormsAmbientIso_inv_naturality F (formsComparisonTwo A) h (ULift.up z)).symm)))
  exact (congrArg ULift.down (tensorFormsAmbientIso_hom_naturality F (formsComparisonTwo B)
    (g.hom.targetHom.hom.preimage_mono h) _).symm).trans
    (congrArg (fun q ↦ ((tensorFormsAmbientIsoTwo B).hom.app
      (op (g.hom.targetHom.hom ⁻¹ᵁ V')) q).down) key)

/-- Restriction of a section of `Ω_{X/S}` along two composable morphisms of `Cris(X/S)`. -/
theorem crysDifferentials_map_comp_apply {B₁ B₂ B₃ : CrystallineThickening S} (a : B₁ ⟶ B₂)
    (b : B₂ ⟶ B₃) (ω : (crysDifferentials S).obj (op B₃)) :
    (crysDifferentials S).map (a ≫ b).op ω =
      (crysDifferentials S).map a.op ((crysDifferentials S).map b.op ω) :=
  (crysDifferentials S).map_comp_apply b.op a.op ω

/-- Restricting a section of `Ω_{X/S}` along `g` and then to a smaller open is restricting it to
the smaller open and then along `g`. -/
theorem crysDifferentials_map_restrictOpenLE_restrictOpenMap
    {V V' : A.obj.thickening.target.scheme.Opens} (h : V' ≤ V)
    (ω : (crysDifferentials S).obj (op (A.restrictOpen V))) :
    (crysDifferentials S).map
        (CrystallineThickening.restrictOpenLE B (g.hom.targetHom.hom.preimage_mono h)).op
        ((crysDifferentials S).map (CrystallineThickening.restrictOpenMap g V).op ω) =
      (crysDifferentials S).map (CrystallineThickening.restrictOpenMap g V').op
        ((crysDifferentials S).map (CrystallineThickening.restrictOpenLE A h).op ω) := by
  rw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply, ← op_comp, ← op_comp,
    CrystallineThickening.restrictOpenLE_restrictOpenMap]

/-- The comparison `κ` of [Stacks, Tag 07IZ] commutes with restriction to smaller opens. -/
theorem restrictedToSheaf_restrictOpenLE {V V' : A.obj.thickening.target.scheme.Opens}
    (h : V' ≤ V) (ω : (crysDifferentials S).obj (op (A.restrictOpen V))) :
    ((restrictedToSheaf A.obj).app (op V')).hom
        ((crysDifferentials S).map (CrystallineThickening.restrictOpenLE A h).op ω) =
      (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.map
        (homOfLE h).op (((restrictedToSheaf A.obj).app (op V)).hom ω) :=
  PresheafOfModules.naturality_apply (restrictedToSheaf A.obj) (homOfLE h).op ω

variable (F) in
/-- The sheaf `g_*(F_{T_B} ⊗ Ω²_{T_B/S,δ})` on `T_A`. -/
abbrev pushforwardTensorTwo : A.obj.thickening.target.scheme.Modules :=
  (Scheme.Modules.pushforward g.hom.targetHom.hom).obj (tensorTwo (F := F) B)

/-- The left side of `tensorTransitionTwo_crystalWedge` as an additive map. -/
def wedgeTransL (V : A.obj.thickening.target.scheme.Opens)
    (ω : (crysDifferentials S).obj (op (A.restrictOpen V))) :
    ((SheafOfModules.toSheaf _).obj (ambientTensor F (dpDifferentialsSheaf
        A.obj.thickening.target S.S.scheme A.obj.toBase.hom))).obj.obj (op V) →+
      ((SheafOfModules.toSheaf _).obj (pushforwardTensorTwo F g)).obj.obj (op V) :=
  (tensorTransitionTwo F g V).comp
    (crystalWedgeHom (M := F) A V (((restrictedToSheaf A.obj).app (op V)).hom ω))

/-- `wedgeTransL g V ω` sends `z` to `τ²_g (z ∧ ω)`. -/
theorem wedgeTransL_apply (V : A.obj.thickening.target.scheme.Opens)
    (ω : (crysDifferentials S).obj (op (A.restrictOpen V)))
    (z : (tensorOne (F := F) A).val.obj (op V)) :
    wedgeTransL g V ω z = tensorTransitionTwo F g V
      (crystalWedge F A V z (((restrictedToSheaf A.obj).app (op V)).hom ω)) := rfl

/-- The right side of `tensorTransitionTwo_crystalWedge` as an additive map. -/
def wedgeTransR (V : A.obj.thickening.target.scheme.Opens)
    (ω : (crysDifferentials S).obj (op (A.restrictOpen V))) :
    ((SheafOfModules.toSheaf _).obj (ambientTensor F (dpDifferentialsSheaf
        A.obj.thickening.target S.S.scheme A.obj.toBase.hom))).obj.obj (op V) →+
      ((SheafOfModules.toSheaf _).obj (pushforwardTensorTwo F g)).obj.obj (op V) :=
  (crystalWedgeHom (M := F) B (g.hom.targetHom.hom ⁻¹ᵁ V)
    (((restrictedToSheaf B.obj).app (op (g.hom.targetHom.hom ⁻¹ᵁ V))).hom
      ((crysDifferentials S).map (CrystallineThickening.restrictOpenMap g V).op ω))).comp
    (crystalTensorTransition g hF V)

/-- `wedgeTransR hF g V ω` sends `z` to `τ_g(z) ∧ g^* ω`. -/
theorem wedgeTransR_apply (V : A.obj.thickening.target.scheme.Opens)
    (ω : (crysDifferentials S).obj (op (A.restrictOpen V)))
    (z : (tensorOne (F := F) A).val.obj (op V)) :
    wedgeTransR hF g V ω z = crystalWedge F B (g.hom.targetHom.hom ⁻¹ᵁ V)
      (crystalTensorTransition g hF V z)
      (((restrictedToSheaf B.obj).app (op (g.hom.targetHom.hom ⁻¹ᵁ V))).hom
        ((crysDifferentials S).map (CrystallineThickening.restrictOpenMap g V).op ω)) := rfl

/-- **`τ²_g` on an exterior product**: `τ²(y ∧ ω) = τ(y) ∧ g^* ω` for a section `y` of
`F_T ⊗ Ω_{T/S,δ}` and a section `ω` of `Ω_{X/S}`. -/
theorem tensorTransitionTwo_crystalWedge (W : A.obj.thickening.target.scheme.Opens)
    (ω : (crysDifferentials S).obj (op (A.restrictOpen W)))
    (y : (tensorOne (F := F) A).val.obj (op W)) :
    tensorTransitionTwo F g W
        (crystalWedge F A W y (((restrictedToSheaf A.obj).app (op W)).hom ω)) =
      crystalWedge F B (g.hom.targetHom.hom ⁻¹ᵁ W) (crystalTensorTransition g hF W y)
        (((restrictedToSheaf B.obj).app (op (g.hom.targetHom.hom ⁻¹ᵁ W))).hom
          ((crysDifferentials S).map (CrystallineThickening.restrictOpenMap g W).op ω)) := by
  refine zariski_eq_of_tmul F (formsComparisonOne A)
    ((SheafOfModules.toSheaf _).obj (pushforwardTensorTwo F g)).property
    (Ω := fun V ↦ (crysDifferentials S).obj (op (A.restrictOpen V)))
    (fun h ω ↦ (crysDifferentials S).map (CrystallineThickening.restrictOpenLE A h).op ω)
    (wedgeTransL g) (wedgeTransR hF g) ?_ ?_ ?_ W ω y
  · intro V V' h ω z
    refine (congrArg _ (wedgeTransL_apply g V ω z)).trans ?_
    refine Eq.trans ?_ (wedgeTransL_apply g V' _ _).symm
    refine (tensorTransitionTwo_naturality g h _).trans ?_
    refine congrArg (tensorTransitionTwo F g V') ((crystalWedge_restrict F A h z _).trans ?_)
    exact congrArg (crystalWedge F A V' ((tensorOne (F := F) A).val.map (homOfLE h).op z))
      (restrictedToSheaf_restrictOpenLE h ω).symm
  · intro V V' h ω z
    refine (congrArg _ (wedgeTransR_apply hF g V ω z)).trans ?_
    refine Eq.trans ?_ (wedgeTransR_apply hF g V' _ _).symm
    refine (crystalWedge_restrict F B (g.hom.targetHom.hom.preimage_mono h) _ _).trans ?_
    refine congrArg₂ (crystalWedge F B (g.hom.targetHom.hom ⁻¹ᵁ V'))
      (crystalTensorTransition_naturality g hF h z) ?_
    refine (restrictedToSheaf_restrictOpenLE (g.hom.targetHom.hom.preimage_mono h) _).symm.trans ?_
    refine congrArg ((restrictedToSheaf B.obj).app (op (g.hom.targetHom.hom ⁻¹ᵁ V'))).hom ?_
    exact crysDifferentials_map_restrictOpenLE_restrictOpenMap g h ω
  · intro V ω x ω'
    let y' := formsOneEquiv (A.restrictOpen V) ω'
    let rV := CrystallineThickening.restrictOpenMap g V
    let x' : (crysAmbientSchemeModules F A).val.obj (op V) := x
    have hx : tensorFormsAmbientUnitApp F (formsComparisonOne A) V (restrTmul V x ω') =
        firstOrderTensorTmul F A V x' (formsCompOne A V ω') :=
      tensorFormsAmbientUnitApp_tmul F (formsComparisonOne A) V x ω'
    rw [hx]
    have hL : wedgeTransL g V ω (firstOrderTensorTmul F A V x' (formsCompOne A V ω')) =
        secondOrderTensorTmul F B (g.hom.targetHom.hom ⁻¹ᵁ V)
          (crystalRestrict F rV x')
          ((dpWedge B.obj.thickening.target S.S.scheme B.obj.toBase.hom).app
            (op (g.hom.targetHom.hom ⁻¹ᵁ V))
            (((restrictedToSheaf B.obj).app (op (g.hom.targetHom.hom ⁻¹ᵁ V))).hom
              ((crysDifferentials S).map rV.op y'))
            (((restrictedToSheaf B.obj).app (op (g.hom.targetHom.hom ⁻¹ᵁ V))).hom
              ((crysDifferentials S).map rV.op ω))) := by
      refine (wedgeTransL_apply g V ω _).trans ?_
      refine (congrArg (tensorTransitionTwo F g V) (crystalWedge_tmul F A V x' _ _)).trans ?_
      refine (congrArg (fun θ ↦ tensorTransitionTwo F g V (secondOrderTensorTmul F A V x' θ))
        (formsComparisonTwo_formsWedge A V y' ω).symm).trans ?_
      refine (tensorTransitionTwo_tmul g V x' (formsWedge y' ω)).trans ?_
      refine congrArg (secondOrderTensorTmul F B (g.hom.targetHom.hom ⁻¹ᵁ V)
        (crystalRestrict F rV x')) ?_
      exact (congrArg ((formsComparisonTwo B).toFun (g.hom.targetHom.hom ⁻¹ᵁ V))
        (formsWedge_map rV y' ω)).trans (formsComparisonTwo_formsWedge B _ _ _)
    have hR : wedgeTransR hF g V ω (firstOrderTensorTmul F A V x' (formsCompOne A V ω')) =
        secondOrderTensorTmul F B (g.hom.targetHom.hom ⁻¹ᵁ V)
          (crystalRestrict F rV x')
          ((dpWedge B.obj.thickening.target S.S.scheme B.obj.toBase.hom).app
            (op (g.hom.targetHom.hom ⁻¹ᵁ V))
            (((restrictedToSheaf B.obj).app (op (g.hom.targetHom.hom ⁻¹ᵁ V))).hom
              ((crysDifferentials S).map rV.op y'))
            (((restrictedToSheaf B.obj).app (op (g.hom.targetHom.hom ⁻¹ᵁ V))).hom
              ((crysDifferentials S).map rV.op ω))) := by
      refine (wedgeTransR_apply hF g V ω _).trans ?_
      have h3 := crystalTensorTransition_tmul g hF V x' (formsCompOne A V ω')
      rw [h3]
      have hd : (dpDifferentialsMapSheaf g.hom).app V (formsCompOne A V ω') =
          ((restrictedToSheaf B.obj).app (op (g.hom.targetHom.hom ⁻¹ᵁ V))).hom
            ((crysDifferentials S).map rV.op y') :=
        (formsCompOne_map g V ω').symm.trans (congrArg
          ((restrictedToSheaf B.obj).app (op (g.hom.targetHom.hom ⁻¹ᵁ V))).hom
          (formsOneEquiv_map rV ω'))
      rw [hd]
      exact crystalWedge_tmul F B _ _ _ _
    exact hL.trans hR.symm

/-- **`τ²_g` on `x ⊗ d ω`**: `τ²(x ⊗ d ω) = g^* x ⊗ d (g^* ω)`. -/
theorem tensorTransitionTwo_tmul_dpDeRham (V : A.obj.thickening.target.scheme.Opens)
    (x : (crysAmbientSchemeModules F A).val.obj (op V))
    (ω : (crysDifferentialForms S 1).obj (op (A.restrictOpen V))) :
    tensorTransitionTwo F g V (secondOrderTensorTmul F A V x
        (dpDeRham A.obj.thickening.target S.S.scheme A.obj.toBase.hom (op V)
          (formsCompOne A V ω))) =
      secondOrderTensorTmul F B (g.hom.targetHom.hom ⁻¹ᵁ V)
        (crystalRestrict F (CrystallineThickening.restrictOpenMap g V) x)
        (dpDeRham B.obj.thickening.target S.S.scheme B.obj.toBase.hom
          (op (g.hom.targetHom.hom ⁻¹ᵁ V)) (formsCompOne B (g.hom.targetHom.hom ⁻¹ᵁ V)
            ((crysDifferentialForms S 1).map
              (CrystallineThickening.restrictOpenMap g V).op ω))) := by
  rw [← formsComparisonTwo_formsDeRham, tensorTransitionTwo_tmul]
  refine congrArg (secondOrderTensorTmul F B (g.hom.targetHom.hom ⁻¹ᵁ V)
    (crystalRestrict F (CrystallineThickening.restrictOpenMap g V) x)) ?_
  refine Eq.trans ?_ (formsComparisonTwo_formsDeRham B _ _)
  exact congrArg ((formsComparisonTwo B).toFun (g.hom.targetHom.hom ⁻¹ᵁ V))
    (crysDeRhamDifferential_naturality S 1 (CrystallineThickening.restrictOpenMap g V) ω)

/-- `tensorTransitionTwo_crystalWedge` with the one-form a section of `Ω^1_{X/S}`. -/
theorem tensorTransitionTwo_crystalWedge_forms (W : A.obj.thickening.target.scheme.Opens)
    (ω : (crysDifferentialForms S 1).obj (op (A.restrictOpen W)))
    (y : (tensorOne (F := F) A).val.obj (op W)) :
    tensorTransitionTwo F g W (crystalWedge F A W y (formsCompOne A W ω)) =
      crystalWedge F B (g.hom.targetHom.hom ⁻¹ᵁ W) (crystalTensorTransition g hF W y)
        (formsCompOne B (g.hom.targetHom.hom ⁻¹ᵁ W)
          ((crysDifferentialForms S 1).map (CrystallineThickening.restrictOpenMap g W).op ω)) := by
  have h := tensorTransitionTwo_crystalWedge hF g W (formsOneEquiv (A.restrictOpen W) ω) y
  have e : formsCompOne B (g.hom.targetHom.hom ⁻¹ᵁ W)
      ((crysDifferentialForms S 1).map (CrystallineThickening.restrictOpenMap g W).op ω) =
      ((restrictedToSheaf B.obj).app (op (g.hom.targetHom.hom ⁻¹ᵁ W))).hom
        ((crysDifferentials S).map (CrystallineThickening.restrictOpenMap g W).op
          (formsOneEquiv (A.restrictOpen W) ω)) :=
    congrArg ((restrictedToSheaf B.obj).app (op (g.hom.targetHom.hom ⁻¹ᵁ W))).hom
      (formsOneEquiv_map (CrystallineThickening.restrictOpenMap g W) ω)
  rw [e]
  exact h

/-- The left side of `tensorTransitionTwo_crystalConnectionExtensionApp` as an additive map. -/
def extTransL (V : A.obj.thickening.target.scheme.Opens) :
    ((SheafOfModules.toSheaf _).obj (ambientTensor F (dpDifferentialsSheaf
        A.obj.thickening.target S.S.scheme A.obj.toBase.hom))).obj.obj (op V) →+
      ((SheafOfModules.toSheaf _).obj (pushforwardTensorTwo F g)).obj.obj (op V) :=
  (tensorTransitionTwo F g V).comp (crystalConnectionExtensionApp A hF V)

/-- `extTransL hF g V` sends `z` to `τ²_g (∇ z)`. -/
theorem extTransL_apply (V : A.obj.thickening.target.scheme.Opens)
    (z : (tensorOne (F := F) A).val.obj (op V)) :
    extTransL hF g V z = tensorTransitionTwo F g V (crystalConnectionExtensionApp A hF V z) := rfl

/-- The right side of `tensorTransitionTwo_crystalConnectionExtensionApp` as an additive map. -/
def extTransR (V : A.obj.thickening.target.scheme.Opens) :
    ((SheafOfModules.toSheaf _).obj (ambientTensor F (dpDifferentialsSheaf
        A.obj.thickening.target S.S.scheme A.obj.toBase.hom))).obj.obj (op V) →+
      ((SheafOfModules.toSheaf _).obj (pushforwardTensorTwo F g)).obj.obj (op V) :=
  (crystalConnectionExtensionApp B hF (g.hom.targetHom.hom ⁻¹ᵁ V)).comp
    (crystalTensorTransition g hF V)

/-- `extTransR hF g V` sends `z` to `∇ (τ_g z)`. -/
theorem extTransR_apply (V : A.obj.thickening.target.scheme.Opens)
    (z : (tensorOne (F := F) A).val.obj (op V)) :
    extTransR hF g V z = crystalConnectionExtensionApp B hF (g.hom.targetHom.hom ⁻¹ᵁ V)
      (crystalTensorTransition g hF V z) := rfl

/-- **The degree-one extension of the canonical connection commutes with the transition maps**:
`τ²_g ∘ ∇ = ∇ ∘ τ_g` on `F_T ⊗ Ω_{T/S,δ}`. -/
theorem tensorTransitionTwo_crystalConnectionExtensionApp (W : A.obj.thickening.target.scheme.Opens)
    (z : (tensorOne (F := F) A).val.obj (op W)) :
    tensorTransitionTwo F g W (crystalConnectionExtensionApp A hF W z) =
      crystalConnectionExtensionApp B hF (g.hom.targetHom.hom ⁻¹ᵁ W)
        (crystalTensorTransition g hF W z) := by
  refine zariski_eq_of_tmul F (formsComparisonOne A)
    ((SheafOfModules.toSheaf _).obj (pushforwardTensorTwo F g)).property
    (Ω := fun _ ↦ PUnit.{1}) (fun _ _ ↦ PUnit.unit)
    (fun V _ ↦ extTransL hF g V) (fun V _ ↦ extTransR hF g V) ?_ ?_ ?_ W PUnit.unit z
  · intro V V' h _ z
    refine (congrArg _ (extTransL_apply hF g V z)).trans ?_
    refine Eq.trans ?_ (extTransL_apply hF g V' _).symm
    refine (tensorTransitionTwo_naturality g h _).trans ?_
    exact congrArg (tensorTransitionTwo F g V')
      (crystalConnectionExtensionApp_naturality A hF h z)
  · intro V V' h _ z
    refine (congrArg _ (extTransR_apply hF g V z)).trans ?_
    refine Eq.trans ?_ (extTransR_apply hF g V' _).symm
    refine (crystalConnectionExtensionApp_naturality B hF
      (g.hom.targetHom.hom.preimage_mono h) _).trans ?_
    exact congrArg (crystalConnectionExtensionApp B hF (g.hom.targetHom.hom ⁻¹ᵁ V'))
      (crystalTensorTransition_naturality g hF h z)
  · intro V _ x ω'
    let y' := formsOneEquiv (A.restrictOpen V) ω'
    let rV := CrystallineThickening.restrictOpenMap g V
    let x' : (crysAmbientSchemeModules F A).val.obj (op V) := x
    have hx : tensorFormsAmbientUnitApp F (formsComparisonOne A) V (restrTmul V x ω') =
        firstOrderTensorTmul F A V x' (formsCompOne A V ω') :=
      tensorFormsAmbientUnitApp_tmul F (formsComparisonOne A) V x ω'
    rw [hx]
    have hL : extTransL hF g V (firstOrderTensorTmul F A V x' (formsCompOne A V ω')) =
        crystalWedge F B (g.hom.targetHom.hom ⁻¹ᵁ V)
          (crystalConnectionApp B hF (g.hom.targetHom.hom ⁻¹ᵁ V) (crystalRestrict F rV x'))
          (formsCompOne B (g.hom.targetHom.hom ⁻¹ᵁ V)
              ((crysDifferentialForms S 1).map rV.op ω')) +
        secondOrderTensorTmul F B (g.hom.targetHom.hom ⁻¹ᵁ V) (crystalRestrict F rV x')
          (dpDeRham B.obj.thickening.target S.S.scheme B.obj.toBase.hom
            (op (g.hom.targetHom.hom ⁻¹ᵁ V)) (formsCompOne B (g.hom.targetHom.hom ⁻¹ᵁ V)
              ((crysDifferentialForms S 1).map rV.op ω'))) := by
      rw [extTransL_apply, crystalConnectionExtensionApp_tmul, map_add,
        tensorTransitionTwo_crystalWedge_forms hF g V ω', tensorTransitionTwo_tmul_dpDeRham,
        crystalTensorTransition_crystalConnectionApp]
    have hR : extTransR hF g V (firstOrderTensorTmul F A V x' (formsCompOne A V ω')) =
        crystalWedge F B (g.hom.targetHom.hom ⁻¹ᵁ V)
          (crystalConnectionApp B hF (g.hom.targetHom.hom ⁻¹ᵁ V) (crystalRestrict F rV x'))
          (formsCompOne B (g.hom.targetHom.hom ⁻¹ᵁ V)
              ((crysDifferentialForms S 1).map rV.op ω')) +
        secondOrderTensorTmul F B (g.hom.targetHom.hom ⁻¹ᵁ V) (crystalRestrict F rV x')
          (dpDeRham B.obj.thickening.target S.S.scheme B.obj.toBase.hom
            (op (g.hom.targetHom.hom ⁻¹ᵁ V)) (formsCompOne B (g.hom.targetHom.hom ⁻¹ᵁ V)
              ((crysDifferentialForms S 1).map rV.op ω'))) := by
      rw [extTransR_apply, crystalTensorTransition_tmul, ← formsCompOne_map]
      set_option maxRecDepth 10000 in
      exact crystalConnectionExtensionApp_tmul B hF (g.hom.targetHom.hom ⁻¹ᵁ V)
        (crystalRestrict F rV x') (formsCompOne B (g.hom.targetHom.hom ⁻¹ᵁ V)
          ((crysDifferentialForms S 1).map rV.op ω'))
    exact hL.trans hR.symm

end Transition

end Crystalline.GlobalCrystallineSituation.SmallSite

end

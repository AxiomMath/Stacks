module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageRestrictScalars
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModuleNatIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPoint
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesCompIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModuleRestrictScalarsNatIso

/-!
# Transport of sheaves of modules across a square of restriction functors

Let `u_X : C_X ⥤ C_X'` and `u_Y : C_Y ⥤ C_Y'` be continuous functors of sites, with restriction
functors `ρ_X`, `ρ_Y` on sheaves of sets, and let `Φ`, `Φ'` be finite-product-preserving
functors of sheaves of sets from `C_X` to `C_Y` and from `C_X'` to `C_Y'`, with
`θ : Φ' ⋙ ρ_Y ≅ ρ_X ⋙ Φ`. Given structure maps `σ' : R' ⟶ Φ'_* O'` and
`σ : u_Y^* R' ⟶ Φ_* (u_X^* O')` compatible through `θ`, the transport of modules along `Φ'`
followed by restriction along `u_Y` is restriction along `u_X` followed by transport along `Φ`.

## Main definitions

* `Stacks.Sheaves.ToposPullback.restrictionModulesIso`: restriction of modules is the transport
  along the restriction functor of sheaves of sets.
* `Stacks.Sheaves.ToposPullback.pullbackModuleRestrictionSquareIso`: the comparison of the two
  composites around the square.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Functor Opposite CategoryTheory.Sheaf

namespace Stacks.Sheaves.ToposPullback

open Stacks.Sheaves.RingedPoint Stacks.Sheaves.RingedToposModules

universe w vX uX vY uY vX' uX' vY' uY'

section Restriction

variable {C : Type uY} [Category.{vY} C] {D : Type uX} [Category.{vX} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})] [K.HasSheafCompose (forget AddCommGrpCat.{w})]
  (G : C ⥤ D) [G.IsContinuous J K] (O : Sheaf K RingCat.{w})

/-- Restriction of modules along a continuous functor is the transport along the restriction
functor of sheaves of sets, read through `restrictionRingIso`. -/
noncomputable def restrictionModulesIso :
    restrictionModules J K G O ≅
      pullbackModuleFunctor J (G.sheafPushforwardContinuous (Type w) J K) O ⋙
        SheafOfModules.restrictScalars (restrictionRingIso J K G O).inv :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ (sheafRestrictScalarsCompIsoId (restrictionRingIso J K G O).hom
      (restrictionRingIso J K G O).inv (restrictionRingIso J K G O).inv_hom_id).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (restrictionModuleIso J K G O).symm _

omit [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})] [K.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- Restriction of scalars before restriction of modules is restriction of scalars along the
restricted ring map after it: both only reindex sections. -/
theorem restrictScalars_comp_restrictionModules {O₁ : Sheaf K RingCat.{w}} (a : O₁ ⟶ O) :
    SheafOfModules.restrictScalars a ⋙ restrictionModules J K G O₁ =
      restrictionModules J K G O ⋙
        SheafOfModules.restrictScalars ((G.sheafPushforwardContinuous RingCat.{w} J K).map a) :=
  rfl

end Restriction

section Square

variable {CX : Type uX} [Category.{vX} CX] {CY : Type uY} [Category.{vY} CY]
  {CX' : Type uX'} [Category.{vX'} CX'] {CY' : Type uY'} [Category.{vY'} CY']
  (JX : GrothendieckTopology CX) (JY : GrothendieckTopology CY)
  (JX' : GrothendieckTopology CX') (JY' : GrothendieckTopology CY')
  [JX.HasSheafCompose (forget RingCat.{w})] [JY.HasSheafCompose (forget RingCat.{w})]
  [JX'.HasSheafCompose (forget RingCat.{w})] [JY'.HasSheafCompose (forget RingCat.{w})]
  [JX.HasSheafCompose (forget AddCommGrpCat.{w})] [JY.HasSheafCompose (forget AddCommGrpCat.{w})]
  [JX'.HasSheafCompose (forget AddCommGrpCat.{w})]
  [JY'.HasSheafCompose (forget AddCommGrpCat.{w})]
  (uX : CX ⥤ CX') [uX.IsContinuous JX JX'] (uY : CY ⥤ CY') [uY.IsContinuous JY JY']
  (Φ : Sheaf JX (Type w) ⥤ Sheaf JY (Type w)) [PreservesFiniteProducts Φ]
  (Φ' : Sheaf JX' (Type w) ⥤ Sheaf JY' (Type w)) [PreservesFiniteProducts Φ']
  (O' : Sheaf JX' RingCat.{w}) {R' : Sheaf JY' RingCat.{w}}

/-- The structure map of the left composite around the square: `σ'` restricted along `u_Y`,
read on the transport along `Φ' ⋙ ρ_Y`. -/
noncomputable def squareRingMapLeft (σ' : R' ⟶ pullbackRingSheaf JY' Φ' O') :
    (uY.sheafPushforwardContinuous RingCat.{w} JY JY').obj R' ⟶
      pullbackRingSheaf JY (Φ' ⋙ uY.sheafPushforwardContinuous (Type w) JY JY') O' :=
  ((uY.sheafPushforwardContinuous RingCat.{w} JY JY').map σ' ≫
    (restrictionRingIso JY JY' uY (pullbackRingSheaf JY' Φ' O')).inv) ≫
    (pullbackRingSheafCompIso JY JY' (uY.sheafPushforwardContinuous (Type w) JY JY') Φ' O').hom

/-- The structure map of the right composite around the square: `σ`, read on the transport
along `ρ_X ⋙ Φ`. -/
noncomputable def squareRingMapRight
    (σ : (uY.sheafPushforwardContinuous RingCat.{w} JY JY').obj R' ⟶
      pullbackRingSheaf JY Φ ((uX.sheafPushforwardContinuous RingCat.{w} JX JX').obj O')) :
    (uY.sheafPushforwardContinuous RingCat.{w} JY JY').obj R' ⟶
      pullbackRingSheaf JY (uX.sheafPushforwardContinuous (Type w) JX JX' ⋙ Φ) O' :=
  (σ ≫ pullbackRingSheafMap JY Φ (restrictionRingIso JX JX' uX O').inv) ≫
    (pullbackRingSheafCompIso JY JX Φ (uX.sheafPushforwardContinuous (Type w) JX JX') O').hom

omit [JX.HasSheafCompose (forget RingCat.{w})] [JX.HasSheafCompose (forget AddCommGrpCat.{w})]
  [JY.HasSheafCompose (forget AddCommGrpCat.{w})] [JX'.HasSheafCompose (forget AddCommGrpCat.{w})]
  [JY'.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The structure map of the left composite is, on underlying sheaves of sets, the restriction
of `σ'`. -/
theorem ringSheafMap_squareRingMapLeft (σ' : R' ⟶ pullbackRingSheaf JY' Φ' O') :
    (sheafCompose JY (forget RingCat.{w})).map (squareRingMapLeft JY JX' JY' uY Φ' O' σ') =
      (uY.sheafPushforwardContinuous (Type w) JY JY').map
        ((sheafCompose JY' (forget RingCat.{w})).map σ') :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

omit [JX.HasSheafCompose (forget AddCommGrpCat.{w})]
  [JY.HasSheafCompose (forget AddCommGrpCat.{w})] [JX'.HasSheafCompose (forget AddCommGrpCat.{w})]
  [JY'.HasSheafCompose (forget AddCommGrpCat.{w})] [JY'.HasSheafCompose (forget RingCat.{w})] in
/-- The structure map of the right composite is, on underlying sheaves of sets, `σ`. -/
theorem ringSheafMap_squareRingMapRight
    (σ : (uY.sheafPushforwardContinuous RingCat.{w} JY JY').obj R' ⟶
      pullbackRingSheaf JY Φ ((uX.sheafPushforwardContinuous RingCat.{w} JX JX').obj O')) :
    (sheafCompose JY (forget RingCat.{w})).map (squareRingMapRight JX JY JX' JY' uX uY Φ O' σ) =
      (sheafCompose JY (forget RingCat.{w})).map σ := by
  rw [squareRingMapRight, Functor.map_comp, Functor.map_comp, ringSheafMap_pullbackRingSheafMap,
    restrictionRingIso_inv_ringSheafMap]
  exact (congrArg (· ≫ _) ((congrArg (_ ≫ ·)
    (Φ.map_id ((uX.sheafPushforwardContinuous (Type w) JX JX').obj (Sheaf.ringSheaf O')))).trans
      (Category.comp_id _))).trans (Category.comp_id _)

/-- The left composite around the square, transport along `Φ'` followed by restriction along
`u_Y`, is the transport along `Φ' ⋙ ρ_Y`. -/
noncomputable def squareLeftIso (σ' : R' ⟶ pullbackRingSheaf JY' Φ' O') :
    (pullbackModuleFunctor JY' Φ' O' ⋙ SheafOfModules.restrictScalars σ') ⋙
        restrictionModules JY JY' uY R' ≅
      pullbackModuleFunctor JY (Φ' ⋙ uY.sheafPushforwardContinuous (Type w) JY JY') O' ⋙
        SheafOfModules.restrictScalars (squareRingMapLeft JY JX' JY' uY Φ' O' σ') :=
  have e₁ : (pullbackModuleFunctor JY' Φ' O' ⋙ SheafOfModules.restrictScalars σ') ⋙
        restrictionModules JY JY' uY R' =
      pullbackModuleFunctor JY' Φ' O' ⋙ (restrictionModules JY JY' uY
        (pullbackRingSheaf JY' Φ' O') ⋙ SheafOfModules.restrictScalars
          ((uY.sheafPushforwardContinuous RingCat.{w} JY JY').map σ')) :=
    (Functor.assoc _ _ _).trans (congrArg (pullbackModuleFunctor JY' Φ' O' ⋙ ·)
      (restrictScalars_comp_restrictionModules JY JY' uY (pullbackRingSheaf JY' Φ' O') σ'))
  have e₂ : pullbackModuleFunctor JY' Φ' O' ⋙
        ((pullbackModuleFunctor JY (uY.sheafPushforwardContinuous (Type w) JY JY')
          (pullbackRingSheaf JY' Φ' O') ⋙ SheafOfModules.restrictScalars
            (restrictionRingIso JY JY' uY (pullbackRingSheaf JY' Φ' O')).inv) ⋙
          SheafOfModules.restrictScalars
            ((uY.sheafPushforwardContinuous RingCat.{w} JY JY').map σ')) =
      (pullbackModuleFunctor JY' Φ' O' ⋙
          pullbackModuleFunctor JY (uY.sheafPushforwardContinuous (Type w) JY JY')
            (pullbackRingSheaf JY' Φ' O')) ⋙
        SheafOfModules.restrictScalars
          ((uY.sheafPushforwardContinuous RingCat.{w} JY JY').map σ' ≫
            (restrictionRingIso JY JY' uY (pullbackRingSheaf JY' Φ' O')).inv) :=
    (congrArg (pullbackModuleFunctor JY' Φ' O' ⋙ ·)
      ((Functor.assoc _ _ _).trans (congrArg (pullbackModuleFunctor JY
            (uY.sheafPushforwardContinuous (Type w) JY JY') (pullbackRingSheaf JY' Φ' O') ⋙ ·)
        (RingedToposModules.restrictScalars_comp _ _)))).trans (Functor.assoc _ _ _).symm
  have e₃ : (pullbackModuleFunctor JY (Φ' ⋙ uY.sheafPushforwardContinuous (Type w) JY JY') O' ⋙
          SheafOfModules.restrictScalars (pullbackRingSheafCompIso JY JY'
            (uY.sheafPushforwardContinuous (Type w) JY JY') Φ' O').hom) ⋙
        SheafOfModules.restrictScalars
          ((uY.sheafPushforwardContinuous RingCat.{w} JY JY').map σ' ≫
            (restrictionRingIso JY JY' uY (pullbackRingSheaf JY' Φ' O')).inv) =
      pullbackModuleFunctor JY (Φ' ⋙ uY.sheafPushforwardContinuous (Type w) JY JY') O' ⋙
        SheafOfModules.restrictScalars (squareRingMapLeft JY JX' JY' uY Φ' O' σ') :=
    (Functor.assoc _ _ _).trans (congrArg (pullbackModuleFunctor JY
      (Φ' ⋙ uY.sheafPushforwardContinuous (Type w) JY JY') O' ⋙ ·)
        (RingedToposModules.restrictScalars_comp _ _))
  eqToIso e₁ ≪≫
    Functor.isoWhiskerLeft (pullbackModuleFunctor JY' Φ' O')
      (Functor.isoWhiskerRight (restrictionModulesIso JY JY' uY (pullbackRingSheaf JY' Φ' O'))
        (SheafOfModules.restrictScalars
          ((uY.sheafPushforwardContinuous RingCat.{w} JY JY').map σ'))) ≪≫
    eqToIso e₂ ≪≫
    Functor.isoWhiskerRight (pullbackModuleCompIso JY JY'
        (uY.sheafPushforwardContinuous (Type w) JY JY') Φ' O')
      (SheafOfModules.restrictScalars
        ((uY.sheafPushforwardContinuous RingCat.{w} JY JY').map σ' ≫
          (restrictionRingIso JY JY' uY (pullbackRingSheaf JY' Φ' O')).inv)) ≪≫
    eqToIso e₃

/-- The right composite around the square, restriction along `u_X` followed by transport along
`Φ`, is the transport along `ρ_X ⋙ Φ`. -/
noncomputable def squareRightIso
    (σ : (uY.sheafPushforwardContinuous RingCat.{w} JY JY').obj R' ⟶
      pullbackRingSheaf JY Φ ((uX.sheafPushforwardContinuous RingCat.{w} JX JX').obj O')) :
    restrictionModules JX JX' uX O' ⋙
        (pullbackModuleFunctor JY Φ ((uX.sheafPushforwardContinuous RingCat.{w} JX JX').obj O') ⋙
          SheafOfModules.restrictScalars σ) ≅
      pullbackModuleFunctor JY (uX.sheafPushforwardContinuous (Type w) JX JX' ⋙ Φ) O' ⋙
        SheafOfModules.restrictScalars (squareRingMapRight JX JY JX' JY' uX uY Φ O' σ) :=
  have e₁ : (pullbackModuleFunctor JX (uX.sheafPushforwardContinuous (Type w) JX JX') O' ⋙
          SheafOfModules.restrictScalars (restrictionRingIso JX JX' uX O').inv) ⋙
        (pullbackModuleFunctor JY Φ ((uX.sheafPushforwardContinuous RingCat.{w} JX JX').obj O') ⋙
          SheafOfModules.restrictScalars σ) =
      pullbackModuleFunctor JX (uX.sheafPushforwardContinuous (Type w) JX JX') O' ⋙
        ((SheafOfModules.restrictScalars (restrictionRingIso JX JX' uX O').inv ⋙
          pullbackModuleFunctor JY Φ
            ((uX.sheafPushforwardContinuous RingCat.{w} JX JX').obj O')) ⋙
          SheafOfModules.restrictScalars σ) := rfl
  have e₂ : pullbackModuleFunctor JX (uX.sheafPushforwardContinuous (Type w) JX JX') O' ⋙
        ((pullbackModuleFunctor JY Φ
            (pullbackRingSheaf JX (uX.sheafPushforwardContinuous (Type w) JX JX') O') ⋙
          SheafOfModules.restrictScalars
            (pullbackRingSheafMap JY Φ (restrictionRingIso JX JX' uX O').inv)) ⋙
          SheafOfModules.restrictScalars σ) =
      (pullbackModuleFunctor JX (uX.sheafPushforwardContinuous (Type w) JX JX') O' ⋙
          pullbackModuleFunctor JY Φ
            (pullbackRingSheaf JX (uX.sheafPushforwardContinuous (Type w) JX JX') O')) ⋙
        SheafOfModules.restrictScalars
          (σ ≫ pullbackRingSheafMap JY Φ (restrictionRingIso JX JX' uX O').inv) :=
    (congrArg (pullbackModuleFunctor JX (uX.sheafPushforwardContinuous (Type w) JX JX') O' ⋙ ·)
      ((Functor.assoc _ _ _).trans (congrArg (pullbackModuleFunctor JY Φ
            (pullbackRingSheaf JX (uX.sheafPushforwardContinuous (Type w) JX JX') O') ⋙ ·)
        (RingedToposModules.restrictScalars_comp _ _)))).trans (Functor.assoc _ _ _).symm
  have e₃ : (pullbackModuleFunctor JY (uX.sheafPushforwardContinuous (Type w) JX JX' ⋙ Φ) O' ⋙
          SheafOfModules.restrictScalars (pullbackRingSheafCompIso JY JX Φ
            (uX.sheafPushforwardContinuous (Type w) JX JX') O').hom) ⋙
        SheafOfModules.restrictScalars
          (σ ≫ pullbackRingSheafMap JY Φ (restrictionRingIso JX JX' uX O').inv) =
      pullbackModuleFunctor JY (uX.sheafPushforwardContinuous (Type w) JX JX' ⋙ Φ) O' ⋙
        SheafOfModules.restrictScalars (squareRingMapRight JX JY JX' JY' uX uY Φ O' σ) :=
    (Functor.assoc _ _ _).trans (congrArg (pullbackModuleFunctor JY
      (uX.sheafPushforwardContinuous (Type w) JX JX' ⋙ Φ) O' ⋙ ·)
        (RingedToposModules.restrictScalars_comp _ _))
  Functor.isoWhiskerRight (restrictionModulesIso JX JX' uX O') _ ≪≫
    eqToIso e₁ ≪≫
    Functor.isoWhiskerLeft
      (pullbackModuleFunctor JX (uX.sheafPushforwardContinuous (Type w) JX JX') O')
      (Functor.isoWhiskerRight (pullbackModuleFunctorRestrictScalarsIso JY Φ
        (restrictionRingIso JX JX' uX O').inv).symm (SheafOfModules.restrictScalars σ)) ≪≫
    eqToIso e₂ ≪≫
    Functor.isoWhiskerRight (pullbackModuleCompIso JY JX Φ
        (uX.sheafPushforwardContinuous (Type w) JX JX') O')
      (SheafOfModules.restrictScalars
        (σ ≫ pullbackRingSheafMap JY Φ (restrictionRingIso JX JX' uX O').inv)) ≪≫
    eqToIso e₃

/-- **Transport of modules across a square of restriction functors.** If
`θ : Φ' ⋙ ρ_Y ≅ ρ_X ⋙ Φ` carries the structure map `σ'` restricted along `u_Y` to `σ`, then
transport along `Φ'` followed by restriction along `u_Y` is restriction along `u_X` followed by
transport along `Φ`. -/
noncomputable def pullbackModuleRestrictionSquareIso
    (θ : Φ' ⋙ uY.sheafPushforwardContinuous (Type w) JY JY' ≅
      uX.sheafPushforwardContinuous (Type w) JX JX' ⋙ Φ)
    (β : pullbackRingSheaf JY (Φ' ⋙ uY.sheafPushforwardContinuous (Type w) JY JY') O' ⟶
      pullbackRingSheaf JY (uX.sheafPushforwardContinuous (Type w) JX JX' ⋙ Φ) O')
    (hβ : (sheafCompose JY (forget RingCat.{w})).map β = θ.hom.app (Sheaf.ringSheaf O'))
    (σ' : R' ⟶ pullbackRingSheaf JY' Φ' O')
    (σ : (uY.sheafPushforwardContinuous RingCat.{w} JY JY').obj R' ⟶
      pullbackRingSheaf JY Φ ((uX.sheafPushforwardContinuous RingCat.{w} JX JX').obj O'))
    (h : squareRingMapLeft JY JX' JY' uY Φ' O' σ' ≫ β =
      squareRingMapRight JX JY JX' JY' uX uY Φ O' σ) :
    (pullbackModuleFunctor JY' Φ' O' ⋙ SheafOfModules.restrictScalars σ') ⋙
        restrictionModules JY JY' uY R' ≅
      restrictionModules JX JX' uX O' ⋙
        (pullbackModuleFunctor JY Φ ((uX.sheafPushforwardContinuous RingCat.{w} JX JX').obj O') ⋙
          SheafOfModules.restrictScalars σ) :=
  squareLeftIso JY JX' JY' uY Φ' O' σ' ≪≫
    pullbackModuleRestrictScalarsIsoOfNatIso JY O' θ β hβ _ _ h ≪≫
    (squareRightIso JX JY JX' JY' uX uY Φ O' σ).symm

end Square

end Stacks.Sheaves.ToposPullback

end

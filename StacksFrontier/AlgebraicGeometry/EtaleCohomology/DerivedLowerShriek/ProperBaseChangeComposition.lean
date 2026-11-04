module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.RestrictBaseBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionIsoIndependence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.BaseChangeCubeTorsion
import StacksCore.Tactic.StacksAttribute

/-!
# The base change isomorphisms of `Rf_!` are compatible with composition

[Stacks, Tag 0F7L], second part: the isomorphisms `g⁻¹ ∘ Rf_! ≅ Rf'_! ∘ (g')⁻¹` are compatible
with the isomorphisms `R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` of [Stacks, Tag 0F7J].

## Main results

* `Stacks.EtaleCohomology.derivedLowerShriekBaseChange_compIso`: for cartesian squares of
  quasi-compact and quasi-separated schemes, the base change isomorphisms of `Rf_!`, `Rg_!` and
  `R(g ∘ f)_!` are compatible with `R(g ∘ f)_! ≅ Rg_! ∘ Rf_!`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.CompactificationOf

variable {X Y Z X' Y' Z' : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z' ⟶ Z} {hY : Y' ⟶ Y}
  {g' : Y' ⟶ Z'} {hX : X' ⟶ X} {f' : X' ⟶ Y'}
  (sqg : IsPullback hY g' g h) (sqf : IsPullback hX f' f hY)
  (jg : CompactificationOf (Over.mk g)) (jX : CompactificationOf (Over.mk (f ≫ jg.immersion)))

/-- The cube of the compactifications `compOver` over the square `X' ⟶ X`. -/
theorem isPullback_compOver_baseChange :
    IsPullback hX (compOver (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX)).immersion
      (compOver jg jX).immersion (compImmersionBaseChangeι sqg sqf jg jX) :=
  isPullback_overBar_baseChange sqg sqf jg jX

/-- The structure morphisms to the bases of the compactifications `compOver` commute with the base
change morphisms `Z' ⟶ Z` and `compImmersionBaseChangeι`. -/
theorem compOver_baseChange_toBase_comm :
    (compOver (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX)).toBase ≫ h =
      compImmersionBaseChangeι sqg sqf jg jX ≫ (compOver jg jX).toBase := by
  have h1 := overBar_baseChange_toBase_comm sqg sqf jg jX
  have h2 : (jg.baseChange sqg).toBase ≫ h = pullback.fst jg.toBase h ≫ jg.toBase :=
    pullback.condition.symm
  show ((compImmersionBaseChange sqg sqf jg jX).toBase ≫ (jg.baseChange sqg).toBase) ≫ h =
    compImmersionBaseChangeι sqg sqf jg jX ≫ (jX.toBase ≫ jg.toBase)
  rw [Category.assoc, h2, ← Category.assoc]
  exact (congrArg (fun z => z ≫ jg.toBase) h1).trans (Category.assoc _ _ _)

end AlgebraicGeometry.CompactificationOf

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

attribute [local instance high] CompactificationOf.etale_restrictBaseι
  CompactificationOf.etale_overBar_immersion

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type) [Ring Λ] {X Y Z X' Y' Z' : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z' ⟶ Z}
  {hY : Y' ⟶ Y} {g' : Y' ⟶ Z'} {hX : X' ⟶ X} {f' : X' ⟶ Y'}
  (sqg : IsPullback hY g' g h) (sqf : IsPullback hX f' f hY)
  (jg : CompactificationOf (Over.mk g)) (jX : CompactificationOf (Over.mk (f ≫ jg.immersion)))


section Abstract

variable {CX CX' CXb CXb' CYb CYb' CY CY' CZ CZ' : Type*} [Category* CX] [Category* CX']
  [Category* CXb] [Category* CXb'] [Category* CYb] [Category* CYb'] [Category* CY] [Category* CY']
  [Category* CZ] [Category* CZ']

/-- For functors `Rfg ≅ Rf ⋙ Rg` and `Rfg' ≅ Rf' ⋙ Rg'` with base change transformations
compatible with these isomorphisms, the composite of `e2` with the base changes of `Rg` and `Rf`
agrees with the base change of `Rfg` followed by `e2'`. -/
theorem compOver_baseChange_abstract
    {Eab : CX ⥤ CXb} {Eab' : CX' ⥤ CXb'} {Rf : CXb ⥤ CYb} {Rf' : CXb' ⥤ CYb'}
    {Rg : CYb ⥤ CZ} {Rg' : CYb' ⥤ CZ'} {Rfg : CXb ⥤ CZ} {Rfg' : CXb' ⥤ CZ'}
    {G : CX ⥤ CY} {Gs : CX' ⥤ CY'} {Ei : CY ⥤ CYb} {Ei' : CY' ⥤ CYb'} {Dh : CZ ⥤ CZ'}
    {DhYb : CYb ⥤ CYb'} {DφX : CXb ⥤ CXb'} {DhX : CX ⥤ CX'} {DhY : CY ⥤ CY'}
    (e2 : Rfg ≅ Rf ⋙ Rg) (e2' : Rfg' ≅ Rf' ⋙ Rg')
    (BCpushg : Rg ⋙ Dh ⟶ DhYb ⋙ Rg') (BCpushf : Rf ⋙ DhYb ⟶ DφX ⋙ Rf')
    (BCpushfg : Rfg ⋙ Dh ⟶ DφX ⋙ Rfg') (cubeY : DhY ⋙ Ei' ≅ Ei ⋙ DhYb)
    (cubeX : DhX ⋙ Eab' ≅ Eab ⋙ DφX)
    (BCg : (Ei ⋙ Rg) ⋙ Dh ⟶ DhY ⋙ (Ei' ⋙ Rg'))
    (BCfg : (Eab ⋙ Rfg) ⋙ Dh ⟶ DhX ⋙ (Eab' ⋙ Rfg'))
    (BCoB : (Eab ⋙ Rf) ⋙ DhYb ⟶ DhX ⋙ (Eab' ⋙ Rf'))
    (BCf : G ⋙ DhY ⟶ DhX ⋙ Gs)
    (hBCg : BCg = Functor.whiskerLeft Ei BCpushg ≫ Functor.whiskerRight cubeY.inv Rg')
    (hBCfg : BCfg = Functor.whiskerLeft Eab BCpushfg ≫ Functor.whiskerRight cubeX.inv Rfg')
    (hBCoB : BCoB = Functor.whiskerLeft Eab BCpushf ≫ Functor.whiskerRight cubeX.inv Rf')
    (hV : BCpushfg ≫ Functor.whiskerLeft DφX e2'.hom =
      Functor.whiskerRight e2.hom Dh ≫ (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft Rf BCpushg ≫ (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight BCpushf Rg' ≫ (Functor.associator _ _ _).hom)
    (K₀ : CX) (ψ : Rf.obj (Eab.obj K₀) ⟶ Ei.obj (G.obj K₀))
    (ψ' : Rf'.obj (Eab'.obj (DhX.obj K₀)) ⟶ Ei'.obj (Gs.obj (DhX.obj K₀)))
    (hB : DhYb.map ψ ≫ cubeY.inv.app (G.obj K₀) ≫ Ei'.map (BCf.app K₀) = BCoB.app K₀ ≫ ψ') :
    Dh.map (e2.hom.app (Eab.obj K₀) ≫ Rg.map ψ) ≫ BCg.app (G.obj K₀) ≫
        Rg'.map (Ei'.map (BCf.app K₀)) =
      BCfg.app K₀ ≫ e2'.hom.app (Eab'.obj (DhX.obj K₀)) ≫ Rg'.map ψ' := by
  have hV' := NatTrans.congr_app hV (Eab.obj K₀)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Functor.comp_obj] at hV'
  have nψ := BCpushg.naturality ψ
  simp only [Functor.comp_map] at nψ
  have ne := e2'.hom.naturality (cubeX.inv.app K₀)
  simp only [Functor.comp_map] at ne
  subst hBCg hBCfg
  rw [hBCoB] at hB
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc] at hB ⊢
  rw [Functor.map_comp, Category.assoc, reassoc_of% nψ, ← Functor.map_comp, ← Functor.map_comp,
    hB, Functor.map_comp, Functor.map_comp, reassoc_of% ne, reassoc_of% hV']

/-- Given the commutation relations `hb` to `hh` between morphisms in `C`, `C'` and `D`, the
composites `Dh.map Φ ≫ bcg2 ≫ Rg'.map bcfjf` and `bcfgj ≫ Φ'` agree. -/
theorem compIso_baseChange_chain {C C' D : Type*} [Category* C] [Category* C'] [Category* D]
    (Dh : C ⥤ C') (Rg' : D ⥤ C')
    {A₀ A₁ A₂ A₃ : C} {B₁ B₂ B₃ : C'} {E₀ E₁ E₂ E₃ E₄ : D}
    (Φ : A₀ ⟶ A₃) (ci1 : A₀ ⟶ A₁) (co : A₁ ⟶ A₂) (rci2 : A₂ ⟶ A₃)
    (bcg2 : Dh.obj A₃ ⟶ Rg'.obj E₀) (bcfjf : E₀ ⟶ E₁) (bcg1 : Dh.obj A₂ ⟶ Rg'.obj E₂)
    (dci2 : E₂ ⟶ E₀) (bcfrb : E₂ ⟶ E₃) (ci3 : E₃ ⟶ E₁) (bc'f : E₂ ⟶ E₄) (ci4 : E₄ ⟶ E₃)
    (ci5 : E₄ ⟶ E₁) (bcfg' : Dh.obj A₁ ⟶ B₁) (co' : B₁ ⟶ Rg'.obj E₄)
    (bcfgcO : Dh.obj A₁ ⟶ B₂) (ci6 : B₂ ⟶ B₁) (bcfgj : Dh.obj A₀ ⟶ B₃) (ci7 : B₃ ⟶ B₂)
    (ci8 : B₃ ⟶ B₁) (Φ' : B₃ ⟶ Rg'.obj E₁)
    (hΦ : Φ = ci1 ≫ co ≫ rci2)
    (hb : Dh.map rci2 ≫ bcg2 = bcg1 ≫ Rg'.map dci2)
    (hc : dci2 ≫ bcfjf = bcfrb ≫ ci3) (hd : bcfrb = bc'f ≫ ci4) (hci : ci4 ≫ ci3 = ci5)
    (he : Dh.map co ≫ bcg1 ≫ Rg'.map bc'f = bcfg' ≫ co')
    (hg : bcfg' = bcfgcO ≫ ci6) (hf : Dh.map ci1 ≫ bcfgcO = bcfgj ≫ ci7)
    (hh : ci7 ≫ ci6 = ci8) (hΦ' : Φ' = ci8 ≫ co' ≫ Rg'.map ci5) :
    Dh.map Φ ≫ bcg2 ≫ Rg'.map bcfjf = bcfgj ≫ Φ' := by
  rw [hΦ, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, reassoc_of% hb,
    ← Functor.map_comp, hc, hd, Category.assoc, hci, Functor.map_comp, reassoc_of% he, hg,
    Category.assoc, reassoc_of% hf, hΦ', reassoc_of% hh]

end Abstract

open CompactificationOf in
/-- **The isomorphism `R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` through the auxiliary compactification is
compatible with base change** along `Z' ⟶ Z`. -/
theorem derivedLowerShriekCompOverIso_baseChange
    (K : (isTorsionPlus.{u, 0} Λ X).FullSubcategory) :
    (etaleModuleDerivedInverseImagePlus.{u, 0} Λ h).map
        ((derivedLowerShriekCompOverIso Λ f g jg jX).hom.app K) ≫
      (derivedLowerShriekBaseChange.{u, 0} Λ sqg jg).app
        ((derivedLowerShriek.{u, 0} f (restrictBase jg jX) Λ).obj K.obj) ≫
      (derivedLowerShriek.{u, 0} g' (jg.baseChange sqg) Λ).map
        ((derivedLowerShriekBaseChangeCube Λ (restrictBase jg jX)
          (restrictBase (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX))
          (restrictBaseBaseChangeι sqg sqf jg jX) (isPullback_restrictBase_baseChange sqg sqf jg jX)
          (restrictBase_baseChange_toBase_comm sqg sqf jg jX)).app K.obj) =
    (derivedLowerShriekBaseChangeCube Λ (compOver jg jX)
        (compOver (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX))
        (compImmersionBaseChangeι sqg sqf jg jX) (isPullback_compOver_baseChange sqg sqf jg jX)
        (compOver_baseChange_toBase_comm sqg sqf jg jX)).app K.obj ≫
      (derivedLowerShriekCompOverIso Λ f' g' (jg.baseChange sqg)
        (compImmersionBaseChange sqg sqf jg jX)).hom.app
          ⟨(etaleModuleDerivedInverseImagePlus.{u, 0} Λ hX).obj K.obj,
            isTorsionPlus_etaleModuleDerivedInverseImagePlus_obj Λ hX K.obj K.property⟩ := by
  rw [derivedLowerShriekCompOverIso_hom_app, derivedLowerShriekCompOverIso_hom_app]
  have := CompactificationOf.etale_overBar_immersion jg jX
  have := CompactificationOf.etale_overBar_immersion (jg.baseChange sqg)
    (compImmersionBaseChange sqg sqf jg jX)
  let cX := etaleModuleDerivedExtensionByZeroCubeIso Λ (isPullback_overBar_baseChange sqg sqf jg jX)
  exact compOver_baseChange_abstract
    (etaleModuleDerivedDirectImageComp.{u, 0} Λ jX.toBase jg.toBase (jX.toBase ≫ jg.toBase) rfl)
    (etaleModuleDerivedDirectImageComp.{u, 0} Λ (compImmersionBaseChange sqg sqf jg jX).toBase
      (jg.baseChange sqg).toBase
      ((compImmersionBaseChange sqg sqf jg jX).toBase ≫ (jg.baseChange sqg).toBase) rfl)
    (etaleModuleDerivedBaseChange.{u, 0} Λ jg.toBase (pullback.snd jg.toBase h) h
      (pullback.fst jg.toBase h) pullback.condition.symm)
    (etaleModuleDerivedBaseChange.{u, 0} Λ jX.toBase (compImmersionBaseChange sqg sqf jg jX).toBase
      (pullback.fst jg.toBase h) (compImmersionBaseChangeι sqg sqf jg jX)
      (overBar_baseChange_toBase_comm sqg sqf jg jX))
    (etaleModuleDerivedBaseChange.{u, 0} Λ (jX.toBase ≫ jg.toBase)
      ((compImmersionBaseChange sqg sqf jg jX).toBase ≫ (jg.baseChange sqg).toBase) h
      (compImmersionBaseChangeι sqg sqf jg jX) (compOver_baseChange_toBase_comm sqg sqf jg jX))
    (etaleModuleDerivedExtensionByZeroCubeIso Λ (isPullback_baseChange sqg jg))
    cX
    (derivedLowerShriekBaseChange.{u, 0} Λ sqg jg)
    (derivedLowerShriekBaseChangeCube Λ (compOver jg jX)
        (compOver (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX))
        (compImmersionBaseChangeι sqg sqf jg jX) (isPullback_compOver_baseChange sqg sqf jg jX)
        (compOver_baseChange_toBase_comm sqg sqf jg jX))
    (derivedLowerShriekBaseChangeCube Λ (overBar jg jX)
        (overBar (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX))
        (compImmersionBaseChangeι sqg sqf jg jX) (isPullback_overBar_baseChange sqg sqf jg jX)
        (overBar_baseChange_toBase_comm sqg sqf jg jX))
    (derivedLowerShriekBaseChangeCube Λ (restrictBase jg jX)
          (restrictBase (jg.baseChange sqg) (compImmersionBaseChange sqg sqf jg jX))
          (restrictBaseBaseChangeι sqg sqf jg jX) (isPullback_restrictBase_baseChange sqg sqf jg jX)
          (restrictBase_baseChange_toBase_comm sqg sqf jg jX))
    rfl rfl rfl
    (etaleModuleDerivedBaseChange_comp Λ jX.toBase jg.toBase (jX.toBase ≫ jg.toBase) rfl
      (compImmersionBaseChange sqg sqf jg jX).toBase (jg.baseChange sqg).toBase
      ((compImmersionBaseChange sqg sqf jg jX).toBase ≫ (jg.baseChange sqg).toBase) rfl
      (compImmersionBaseChangeι sqg sqf jg jX) (pullback.fst jg.toBase h) h
      (overBar_baseChange_toBase_comm sqg sqf jg jX) pullback.condition.symm
      (compOver_baseChange_toBase_comm sqg sqf jg jX))
    K.obj ((derivedLowerShriekRestrictBaseIso Λ jg jX).hom.app K)
    ((derivedLowerShriekRestrictBaseIso Λ (jg.baseChange sqg)
        (compImmersionBaseChange sqg sqf jg jX)).hom.app
          ⟨(etaleModuleDerivedInverseImagePlus.{u, 0} Λ hX).obj K.obj,
            isTorsionPlus_etaleModuleDerivedInverseImagePlus_obj Λ hX K.obj K.property⟩)
    (derivedLowerShriekRestrictBaseIso_baseChange Λ sqg sqf jg jX K)


section Composition

variable {X Y Z X' Y' Z' : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : Z' ⟶ Z} {hY : Y' ⟶ Y}
  {g' : Y' ⟶ Z'} {hX : X' ⟶ X} {f' : X' ⟶ Y'}
  [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z] [CompactSpace X'] [QuasiSeparatedSpace X']
  [CompactSpace Y'] [QuasiSeparatedSpace Y'] [CompactSpace Z'] [QuasiSeparatedSpace Z']
  [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]

open CompactificationOf in
/-- For cartesian squares of quasi-compact and quasi-separated schemes
```
X' --hX--> X
|f'        |f
Y' --hY--> Y
|g'        |g
Z' --h-->  Z
```
with `f` and `g` separated of finite type, the base change isomorphisms
`h⁻¹ ∘ R(g ∘ f)_! ≅ R(g' ∘ f')_! ∘ hX⁻¹`, `h⁻¹ ∘ Rg_! ≅ Rg'_! ∘ hY⁻¹` and
`hY⁻¹ ∘ Rf_! ≅ Rf'_! ∘ hX⁻¹` (`Stacks.EtaleCohomology.derivedLowerShriekBaseChange`) are
compatible with the isomorphisms `R(g ∘ f)_! ≅ Rg_! ∘ Rf_!`
(`Stacks.EtaleCohomology.derivedLowerShriekCompIso`) on `D⁺_tors(X_étale, Λ)`, for arbitrary
compactifications. -/
@[stacks 0F7L "compatibility of the base change isomorphisms with the isomorphisms of Lemma 0F7J"]
theorem derivedLowerShriekBaseChange_compIso (sqg : IsPullback hY g' g h)
    (sqf : IsPullback hX f' f hY) (jf : CompactificationOf (Over.mk f))
    (jg : CompactificationOf (Over.mk g)) (j : CompactificationOf (Over.mk (f ≫ g)))
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)) (hK : isTorsionPlus.{u, 0} Λ X K) :
    haveI : IsSeparated f' := MorphismProperty.of_isPullback sqf inferInstance
    haveI : LocallyOfFiniteType f' := MorphismProperty.of_isPullback sqf inferInstance
    haveI : IsSeparated g' := MorphismProperty.of_isPullback sqg inferInstance
    haveI : LocallyOfFiniteType g' := MorphismProperty.of_isPullback sqg inferInstance
    (etaleModuleDerivedInverseImagePlus.{u, 0} Λ h).map
        ((derivedLowerShriekCompIso Λ f g jf jg j).hom.app ⟨K, hK⟩) ≫
      (derivedLowerShriekBaseChange.{u, 0} Λ sqg jg).app
        ((derivedLowerShriek.{u, 0} f jf Λ).obj K) ≫
      (derivedLowerShriek.{u, 0} g' (jg.baseChange sqg) Λ).map
        ((derivedLowerShriekBaseChange.{u, 0} Λ sqf jf).app K) =
    (derivedLowerShriekBaseChange.{u, 0} Λ (sqf.paste_vert sqg) j).app K ≫
      (derivedLowerShriekCompIso Λ f' g' (jf.baseChange sqf) (jg.baseChange sqg)
        (j.baseChange (sqf.paste_vert sqg))).hom.app
          ⟨(etaleModuleDerivedInverseImagePlus.{u, 0} Λ hX).obj K,
            isTorsionPlus_etaleModuleDerivedInverseImagePlus_obj Λ hX K hK⟩ := by
  have : IsSeparated f' := MorphismProperty.of_isPullback sqf inferInstance
  have : LocallyOfFiniteType f' := MorphismProperty.of_isPullback sqf inferInstance
  have : IsSeparated g' := MorphismProperty.of_isPullback sqg inferInstance
  have : LocallyOfFiniteType g' := MorphismProperty.of_isPullback sqg inferInstance
  have : QuasiCompact f := quasiCompact_of_compactSpace f
  have : QuasiCompact (f ≫ g) := quasiCompact_of_compactSpace _
  have : QuasiCompact f' := quasiCompact_of_compactSpace f'
  have : QuasiCompact (f' ≫ g') := quasiCompact_of_compactSpace _
  have : QuasiCompact (f ≫ jg.immersion) := quasiCompact_of_compactSpace _
  let jX := (nonempty_compactificationOf_comp_immersion f g jg).some
  let jXs := compImmersionBaseChange sqg sqf jg jX
  have hΦ := congrArg (fun e => e.hom.app (⟨K, hK⟩ : (isTorsionPlus.{u, 0} Λ X).FullSubcategory))
    (derivedLowerShriekCompIso_eq_compOver Λ f g jf jg j jX)
  simp only [derivedLowerShriekCompIsoThrough, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app] at hΦ
  have hΦ' := congrArg (fun e => e.hom.app (⟨(etaleModuleDerivedInverseImagePlus.{u, 0} Λ hX).obj K,
      isTorsionPlus_etaleModuleDerivedInverseImagePlus_obj Λ hX K hK⟩ :
        (isTorsionPlus.{u, 0} Λ X').FullSubcategory))
    (derivedLowerShriekCompIso_eq_compOver Λ f' g' (jf.baseChange sqf) (jg.baseChange sqg)
      (j.baseChange (sqf.paste_vert sqg)) jXs)
  simp only [derivedLowerShriekCompIsoThrough, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app] at hΦ'
  have hb := (derivedLowerShriekBaseChange.{u, 0} Λ sqg jg).naturality
    ((derivedLowerShriekCompactificationIso f (restrictBase jg jX) jf Λ).hom.app ⟨K, hK⟩)
  simp only [Functor.comp_map] at hb
  have hc := derivedLowerShriekBaseChange_compactificationIso Λ sqf (restrictBase jg jX) jf K hK
  have hd0 := derivedLowerShriekBaseChangeCube_app_eq Λ sqf (restrictBase jg jX)
    (restrictBase (jg.baseChange sqg) jXs) (restrictBaseBaseChangeι sqg sqf jg jX)
    (isPullback_restrictBase_baseChange sqg sqf jg jX)
    (restrictBase_baseChange_toBase_comm sqg sqf jg jX) K hK
  have hd : (derivedLowerShriekBaseChange.{u, 0} Λ sqf (restrictBase jg jX)).app K =
      (derivedLowerShriekBaseChangeCube Λ (restrictBase jg jX)
          (restrictBase (jg.baseChange sqg) jXs) (restrictBaseBaseChangeι sqg sqf jg jX)
          (isPullback_restrictBase_baseChange sqg sqf jg jX)
          (restrictBase_baseChange_toBase_comm sqg sqf jg jX)).app K ≫
        (derivedLowerShriekCompactificationIso f' (restrictBase (jg.baseChange sqg) jXs)
          ((restrictBase jg jX).baseChange sqf) Λ).hom.app
            ⟨(etaleModuleDerivedInverseImagePlus.{u, 0} Λ hX).obj K,
              isTorsionPlus_etaleModuleDerivedInverseImagePlus_obj Λ hX K hK⟩ := by
    rw [hd0, Category.assoc, ← derivedLowerShriekCompactificationIso_symm, Iso.symm_hom,
      Iso.inv_hom_id_app]
    exact (Category.comp_id _).symm
  have hci := congrArg (fun e => e.hom.app (⟨(etaleModuleDerivedInverseImagePlus.{u, 0} Λ hX).obj K,
      isTorsionPlus_etaleModuleDerivedInverseImagePlus_obj Λ hX K hK⟩ :
        (isTorsionPlus.{u, 0} Λ X').FullSubcategory))
    (derivedLowerShriekCompactificationIso_trans f' Λ (restrictBase (jg.baseChange sqg) jXs)
      ((restrictBase jg jX).baseChange sqf) (jf.baseChange sqf))
  simp only [Iso.trans_hom, NatTrans.comp_app] at hci
  have he := derivedLowerShriekCompOverIso_baseChange Λ sqg sqf jg jX ⟨K, hK⟩
  have hg := derivedLowerShriekBaseChangeCube_app_eq Λ (sqf.paste_vert sqg) (compOver jg jX)
    (compOver (jg.baseChange sqg) jXs) (compImmersionBaseChangeι sqg sqf jg jX)
    (isPullback_compOver_baseChange sqg sqf jg jX)
    (compOver_baseChange_toBase_comm sqg sqf jg jX) K hK
  have hf := derivedLowerShriekBaseChange_compactificationIso Λ (sqf.paste_vert sqg) j
    (compOver jg jX) K hK
  have hh := congrArg (fun e => e.hom.app (⟨(etaleModuleDerivedInverseImagePlus.{u, 0} Λ hX).obj K,
      isTorsionPlus_etaleModuleDerivedInverseImagePlus_obj Λ hX K hK⟩ :
        (isTorsionPlus.{u, 0} Λ X').FullSubcategory))
    (derivedLowerShriekCompactificationIso_trans (f' ≫ g') Λ (j.baseChange (sqf.paste_vert sqg))
      ((compOver jg jX).baseChange (sqf.paste_vert sqg)) (compOver (jg.baseChange sqg) jXs))
  simp only [Iso.trans_hom, NatTrans.comp_app] at hh
  exact compIso_baseChange_chain (etaleModuleDerivedInverseImagePlus.{u, 0} Λ h)
    (derivedLowerShriek.{u, 0} g' (jg.baseChange sqg) Λ) (hΦ := hΦ) (hb := hb) (hc := hc)
    (hd := hd) (hci := hci) (he := he) (hg := hg) (hf := hf) (hh := hh) (hΦ' := hΦ')

end Composition

end Stacks.EtaleCohomology

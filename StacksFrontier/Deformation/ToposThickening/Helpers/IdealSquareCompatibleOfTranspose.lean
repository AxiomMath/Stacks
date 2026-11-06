module

public import StacksFrontier.Deformation.ToposThickening.Helpers.ObstructionDescentBasePullback
public import StacksFrontier.Deformation.ToposThickening.FlatThickeningComplexBaseIdealMaps

/-!
# The ideal-square compatibility from the transposed comparison of pulled-back ideals

In the setting of
`Deformation.ToposThickening.ThickeningTargetMorphism.IdealSquareCompatible` (two first order
thickenings `iₖ : X ⟶ Yₖ`, each in a strict square of Situation 08VV over `tₖ : Sₖ ⟶ S'ₖ` with
flat `f'ₖ`, a morphism `j : Y₂ ⟶ Y₁` of the targets and `E : Ψ₀ ∘ i₂_* ≅ i₁_*`), this file
reduces the compatibility of a map `λ : f₁^*𝒥₁ ⟶ f₂^*𝒥₂` with the map of square-zero ideals
`I₁ ⟶ j_*I₂` to two statements about a map `ν : f'₁^*𝒥₁ ⟶ j_*f'₂^*𝒥₂` of `O_{Y₁}`-modules:

* the canonical maps of ideals `ψₖ : f'ₖ^*𝒥ₖ ⟶ Iₖ` of Stacks 08M7 carry `ν` to `j^♯` on
  `I₁ ⊂ O_{Y₁}`;
* the reductions `f'ₖ^*𝒥ₖ ⟶ iₖ_*fₖ^*𝒥ₖ` carry `ν` to `i₁_*λ`, read through `E`.

The identifications `fₖ^*𝒥ₖ = Iₖ` disappear from the statement: they are the reductions
followed by the maps of ideals (`Deformation.ToposThickening.`
`basePullbackIdealReduction_comp_basePullbackIdealIsoIdeal`).

This module is a helper and carries no `@[stacks]` attribute.

## References

* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
* [Stacks Project, Tag 0CYF](https://stacks.math.columbia.edu/tag/0CYF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

universe v u v₁ u₁ v₂ u₂ w e e' vS uS wS vS' uS' wS' vT uT wT vT' uT' wT'

namespace Deformation.ToposThickening.ThickeningTargetMorphism

attribute [local instance 5000] SheafOfModules.instAbelian

section Ideal

variable {X : RingedTopos.{v, u, w}} {Y₁ : RingedTopos.{v₁, u₁, w}} {Y₂ : RingedTopos.{v₂, u₂, w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y₁.J.HasSheafCompose (forget RingCat.{w})]
  [Y₂.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y₁.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y₂.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y₁.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y₂.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y₁.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y₁.J AddCommGrpCat.{w}]
  [Y₂.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y₂.J AddCommGrpCat.{w}]
  {i₁ : RingedToposHom X Y₁} {i₂ : RingedToposHom X Y₂} (D : ThickeningTargetMorphism i₁ i₂)
  (hi₁ : FirstOrderThickening i₁) (hi₂ : FirstOrderThickening i₂)

omit [Y₁.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y₁.J AddCommGrpCat.{w}]
  [Y₂.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y₂.J AddCommGrpCat.{w}] in
/-- **The map `I₁ ⟶ j_*I₂` of square-zero ideals is `j^♯` on `I₁ ⊂ O_{Y₁}`.** -/
theorem idealMapOver_comp_map_incl :
    D.idealMapOver hi₁ hi₂ ≫ D.j.pushforwardModules.map hi₂.incl = hi₁.incl ≫ D.jSharpUnit :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦
    ModuleCat.hom_ext (LinearMap.ext fun a ↦
      D.pushforwardModules_map_incl_idealSection hi₁ hi₂ U a))

omit [Y₁.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y₁.J AddCommGrpCat.{w}]
  [Y₂.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y₂.J AddCommGrpCat.{w}] in
/-- `j_*M ≅ Ψ₀M` over `O_{Y₁}` is natural in `M`. -/
theorem map_comp_restrictIso_hom {M M' : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₂))} (m : M ⟶ M') :
    D.j.pushforwardModules.map ((structureRestrict i₂).map m) ≫ (D.restrictIso M').hom =
      (D.restrictIso M).hom ≫ (structureRestrict i₁).map (D.basePushforward.map m) :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun _ ↦
    ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl))

omit [Y₁.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y₂.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y₁.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y₁.J AddCommGrpCat.{w}]
  [Y₂.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y₂.J AddCommGrpCat.{w}] in
/-- `j^♯ : O_{Y₁} ⟶ j_*O_{Y₂}` as a map of unit modules is the unit-module structure map of `j`. -/
theorem jSharpUnit_eq_unitStructureMap : D.jSharpUnit = RingedToposHom.unitStructureMap D.j :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦ ModuleCat.hom_ext (LinearMap.ext fun a ↦
    (RingedToposHom.unitStructureMap_val_app D.j U a).symm))

omit [Y₁.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y₁.J AddCommGrpCat.{w}] in
/-- Two maps into `j_*I₂` agreeing after `j_*` of the inclusion `I₂ ⊂ O_{Y₂}` agree. -/
theorem eq_of_comp_map_incl {N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y₁.O)}
    {l₁ l₂ : N ⟶ D.j.pushforwardModules.obj ((structureRestrict i₂).obj hi₂.I)}
    (h : l₁ ≫ D.j.pushforwardModules.map hi₂.incl = l₂ ≫ D.j.pushforwardModules.map hi₂.incl) :
    l₁ = l₂ := by
  have : Mono hi₂.incl := ⟨fun {_} a b hab => ((Stacks.SheafOfModules.existsUnique_factorThrough
    hi₂.incl hi₂.injective (a ≫ hi₂.incl) fun _ _ => ⟨_, rfl⟩).unique rfl hab.symm)⟩
  have := (RingedToposHom.pullbackAdjPushforwardModules D.j).isRightAdjoint
  exact (cancel_mono (D.j.pushforwardModules.map hi₂.incl)).1 h

end Ideal

/-- A composite through a factorisation `ψ ≫ a = ν ≫ J ψ₂`, a naturality square
`r ≫ m' = J m ≫ r'` and `ψ₂ ≫ m = red`. -/
theorem _root_.CategoryTheory.comp_comp_comp_eq_of_comp_eq_map {𝒞 𝒟 : Type*} [Category* 𝒞]
    [Category* 𝒟] (J : 𝒞 ⥤ 𝒟) {P I R R' Z : 𝒟} {Q I₂ M₂ : 𝒞}
    (ψ : P ⟶ I) (a : I ⟶ J.obj I₂) (r : J.obj I₂ ⟶ R) (m' : R ⟶ R') (x : R' ⟶ Z)
    (ν : P ⟶ J.obj Q) (ψ₂ : Q ⟶ I₂) (m : I₂ ⟶ M₂) (r' : J.obj M₂ ⟶ R') (red : Q ⟶ M₂)
    (hc : ψ ≫ a = ν ≫ J.map ψ₂) (hn : J.map m ≫ r' = r ≫ m') (h₂ : ψ₂ ≫ m = red) :
    ψ ≫ (a ≫ r) ≫ m' ≫ x = ν ≫ J.map red ≫ r' ≫ x := by
  rw [← h₂, J.map_comp, Category.assoc, Category.assoc, ← Category.assoc ψ a, hc,
    Category.assoc, reassoc_of% hn]


variable {X : RingedTopos.{v, u, w}} {Y₁ : RingedTopos.{v₁, u₁, w}} {Y₂ : RingedTopos.{v₂, u₂, w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y₁.J.HasSheafCompose (forget RingCat.{w})]
  [Y₂.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y₁.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y₂.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y₁.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y₂.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [Y₁.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y₁.J AddCommGrpCat.{w}]
  [Y₂.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y₂.J AddCommGrpCat.{w}]
  [HasSheafify Y₁.J AddCommGrpCat.{w}] [HasSheafify Y₂.J AddCommGrpCat.{w}]
  {S₁ : RingedTopos.{vS, uS, wS}} {S'₁ : RingedTopos.{vS', uS', wS'}}
  [S₁.J.HasSheafCompose (forget RingCat.{wS})] [S'₁.J.HasSheafCompose (forget RingCat.{wS'})]
  [S₁.J.HasSheafCompose (forget₂ CommRingCat.{wS} RingCat.{wS})]
  [S'₁.J.HasSheafCompose (forget₂ CommRingCat.{wS'} RingCat.{wS'})]
  [S₁.J.HasSheafCompose (forget AddCommGrpCat.{wS})]
  [S'₁.J.HasSheafCompose (forget AddCommGrpCat.{wS'})]
  [HasWeakSheafify S₁.J AddCommGrpCat.{wS}] [S₁.J.WEqualsLocallyBijective AddCommGrpCat.{wS}]
  {S₂ : RingedTopos.{vT, uT, wT}} {S'₂ : RingedTopos.{vT', uT', wT'}}
  [S₂.J.HasSheafCompose (forget RingCat.{wT})] [S'₂.J.HasSheafCompose (forget RingCat.{wT'})]
  [S₂.J.HasSheafCompose (forget₂ CommRingCat.{wT} RingCat.{wT})]
  [S'₂.J.HasSheafCompose (forget₂ CommRingCat.{wT'} RingCat.{wT'})]
  [S₂.J.HasSheafCompose (forget AddCommGrpCat.{wT})]
  [S'₂.J.HasSheafCompose (forget AddCommGrpCat.{wT'})]
  [HasWeakSheafify S₂.J AddCommGrpCat.{wT}] [S₂.J.WEqualsLocallyBijective AddCommGrpCat.{wT}]
  {i₁ : RingedToposHom X Y₁} {i₂ : RingedToposHom X Y₂} (D : ThickeningTargetMorphism i₁ i₂)
  (hi₁ : FirstOrderThickening i₁) (hi₂ : FirstOrderThickening i₂)
  (hj : FirstOrderThickening D.j)
  (t₁ : RingedToposHom S₁ S'₁) (f₁ : RingedToposHom X S₁) (f'₁ : RingedToposHom Y₁ S'₁)
  (ht₁ : FirstOrderThickening t₁) (comm₁ : f'₁.comp i₁ = t₁.comp f₁) (hf'₁ : f'₁.IsFlat)
  (hstrict₁ : (MorphismOfThickenings.ofFirstOrderThickenings i₁ t₁ f₁ f'₁ hi₁ ht₁
    comm₁).IsStrict)
  (t₂ : RingedToposHom S₂ S'₂) (f₂ : RingedToposHom X S₂) (f'₂ : RingedToposHom Y₂ S'₂)
  (ht₂ : FirstOrderThickening t₂) (comm₂ : f'₂.comp i₂ = t₂.comp f₂) (hf'₂ : f'₂.IsFlat)
  (hstrict₂ : (MorphismOfThickenings.ofFirstOrderThickenings i₂ t₂ f₂ f'₂ hi₂ ht₂
    comm₂).IsStrict)
  (E : thickenedModulesFunctor i₂ ⋙ D.basePushforward ≅ thickenedModulesFunctor i₁)

include hf'₂ hstrict₂ in
/-- **The ideal-square compatibility from a transposed comparison `ν : f'₁^*𝒥₁ ⟶ j_*f'₂^*𝒥₂`.**
If the canonical maps of ideals carry `ν` to `j^♯` on `I₁` (`H₁`) and the reductions
`f'ₖ^*𝒥ₖ ⟶ iₖ_*fₖ^*𝒥ₖ` carry `ν` to `i₁_*λ` read through `E` (`H₂`), then `λ` is compatible with
the map of square-zero ideals. -/
theorem idealSquareCompatible_of_transpose
    (lam : basePullbackIdeal t₁ f₁ ht₁ ⟶ basePullbackIdeal t₂ f₂ ht₂)
    (ν : (pullbackModules f'₁.toModulesHom).obj ht₁.idealOfThickening.I ⟶
      D.j.pushforwardModules.obj ((pullbackModules f'₂.toModulesHom).obj ht₂.idealOfThickening.I))
    (H₁ : ν ≫ D.j.pushforwardModules.map
        ((MorphismOfThickenings.ofFirstOrderThickenings i₂ t₂ f₂ f'₂ hi₂ ht₂ comm₂).idealMap ≫
          hi₂.idealOfThickening.incl) =
      (MorphismOfThickenings.ofFirstOrderThickenings i₁ t₁ f₁ f'₁ hi₁ ht₁ comm₁).idealMap ≫
        hi₁.idealOfThickening.incl ≫ D.jSharpUnit)
    (H₂ : (RingedToposHom.pullbackAdjPushforwardModules i₁).homEquiv _ _
        (eqToHom (congrArg (fun g => (pullbackModules g).obj
          ((pullbackModules f'₁.toModulesHom).obj ht₁.idealOfThickening.I))
          i₁.toModulesHom_eq_toRingedToposModulesHom.symm).symm ≫
            (basePullbackIdealIsoPullback i₁ t₁ f₁ f'₁ hi₁ ht₁ comm₁).inv) ≫
        (structureRestrict i₁).map ((thickenedModulesFunctor i₁).map lam) =
      ν ≫ D.j.pushforwardModules.map ((RingedToposHom.pullbackAdjPushforwardModules i₂).homEquiv _ _
        (eqToHom (congrArg (fun g => (pullbackModules g).obj
          ((pullbackModules f'₂.toModulesHom).obj ht₂.idealOfThickening.I))
          i₂.toModulesHom_eq_toRingedToposModulesHom.symm).symm ≫
            (basePullbackIdealIsoPullback i₂ t₂ f₂ f'₂ hi₂ ht₂ comm₂).inv)) ≫
        (D.restrictIso ((thickenedModulesFunctor i₂).obj (basePullbackIdeal t₂ f₂ ht₂))).hom ≫
        (structureRestrict i₁).map (E.hom.app (basePullbackIdeal t₂ f₂ ht₂))) :
    D.IdealSquareCompatible hi₁ hi₂ t₁ f₁ f'₁ ht₁ comm₁ hf'₁ hstrict₁ t₂ f₂ f'₂ ht₂ comm₂
      hf'₂ hstrict₂ E lam := by
  have L₁ := basePullbackIdealReduction_comp_basePullbackIdealIsoIdeal i₁ t₁ f₁ f'₁ hi₁ ht₁ comm₁
    hf'₁ hstrict₁
  have L₂ := basePullbackIdealReduction_comp_basePullbackIdealIsoIdeal i₂ t₂ f₂ f'₂ hi₂ ht₂ comm₂
    hf'₂ hstrict₂
  have hiso := (MorphismOfThickenings.ofFirstOrderThickenings i₁ t₁ f₁ f'₁ hi₁ ht₁
    comm₁).isIso_idealMap hf'₁ hstrict₁
  have hepi := @IsIso.epi_of_iso _ _ _ _ _ hiso
  have h₁ := ((Iso.eq_comp_inv ((SheafOfModules.restrictScalars (structureRingMap i₁)).mapIso _)).2
    L₁).symm
  have h₂ := ((Iso.eq_comp_inv ((SheafOfModules.restrictScalars (structureRingMap i₂)).mapIso _)).2
    L₂).symm
  have hc : (MorphismOfThickenings.ofFirstOrderThickenings i₁ t₁ f₁ f'₁ hi₁ ht₁ comm₁).idealMap ≫
      D.idealMapOver hi₁ hi₂ = ν ≫ D.j.pushforwardModules.map
        (MorphismOfThickenings.ofFirstOrderThickenings i₂ t₂ f₂ f'₂ hi₂ ht₂ comm₂).idealMap := by
    refine D.eq_of_comp_map_incl hi₂ ?_
    exact (Category.assoc _ _ _).trans ((congrArg (CategoryStruct.comp _)
      (D.idealMapOver_comp_map_incl hi₁ hi₂)).trans (H₁.symm.trans
        ((congrArg (CategoryStruct.comp ν) (Functor.map_comp _ _ _)).trans
          (Category.assoc _ _ _).symm)))
  have eR : (structureRestrict i₁).map (D.idealMap hi₁ hi₂ ≫
      D.basePushforward.map (basePullbackIdealIsoIdeal i₂ t₂ f₂ f'₂ hi₂ ht₂ comm₂ hf'₂
        hstrict₂).inv ≫ E.hom.app (basePullbackIdeal t₂ f₂ ht₂)) =
      (D.idealMapOver hi₁ hi₂ ≫ (D.restrictIso hi₂.I).hom) ≫
        (structureRestrict i₁).map (D.basePushforward.map (basePullbackIdealIsoIdeal i₂ t₂ f₂ f'₂
          hi₂ ht₂ comm₂ hf'₂ hstrict₂).inv) ≫
        (structureRestrict i₁).map (E.hom.app (basePullbackIdeal t₂ f₂ ht₂)) := by
    rw [Functor.map_comp, Functor.map_comp, D.restrictScalars_map_idealMap hi₁ hi₂]
  refine ⟨hi₁.restrictScalarsFullyFaithful.map_injective ?_⟩
  refine (cancel_epi (MorphismOfThickenings.ofFirstOrderThickenings i₁ t₁ f₁ f'₁ hi₁ ht₁
    comm₁).idealMap).1 ?_
  refine (congrArg (CategoryStruct.comp (MorphismOfThickenings.ofFirstOrderThickenings i₁ t₁ f₁
    f'₁ hi₁ ht₁ comm₁).idealMap) (Functor.map_comp _ _ _)).trans ?_
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h₁)).trans ?_
  refine H₂.trans ?_
  refine Eq.symm ((congrArg (CategoryStruct.comp (MorphismOfThickenings.ofFirstOrderThickenings i₁
    t₁ f₁ f'₁ hi₁ ht₁ comm₁).idealMap) eR).trans ?_)
  exact comp_comp_comp_eq_of_comp_eq_map _ _ _ _ _ _ _ _ _ _ _ hc
    (D.map_comp_restrictIso_hom (basePullbackIdealIsoIdeal i₂ t₂ f₂ f'₂ hi₂ ht₂ comm₂ hf'₂
      hstrict₂).inv) h₂

end Deformation.ToposThickening.ThickeningTargetMorphism

end

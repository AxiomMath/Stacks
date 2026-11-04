module

public import StacksFrontier.Deformation.ToposThickening.Helpers.IdealSquareCompatibleOfTranspose

/-!
# Reduction hypothesis of transposed ideal-square compatibility from an equation of transposes

The second hypothesis of
`Deformation.ToposThickening.ThickeningTargetMorphism.idealSquareCompatible_of_transpose`, on the
reductions `f'ₖ^*𝒥ₖ ⟶ iₖ_*fₖ^*𝒥ₖ`, is an equation
`a₁(w₁) ≫ i₁_*(m) = ν ≫ j_*(a₂(w₂)) ≫ c` of transposes under adjunctions `iₖ^* ⊣ iₖ_*`.
`Deformation.ToposThickening.ThickeningTargetMorphism.homEquiv_comp_map_eq_of_eq` derives it from
such an equation with every piece a variable, each identified with its value in the hypothesis by
a separate equation, so that the equation is matched by the term that proves it (for instance the
cube comparison `Deformation.ToposThickening.homEquiv_comp_map_eq_cubeTopTranspose_comp_of_eq`)
and each identification is checked on its own;
`CategoryTheory.Adjunction.homEquiv_eq_comp_map_unit_comp_of_heq` transports a mate equation in the
same way. Used in the functoriality of the obstruction classes of `Coh_{X/B}` (second proof of
Stacks 08WA).

## References

* [Stacks Project, Tag 08WA](https://stacks.math.columbia.edu/tag/08WA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

universe v u v₁ u₁ v₂ u₂ w e e' vS uS wS vS' uS' wS' vT uT wT vT' uT' wT'

namespace Deformation.ToposThickening

/-- The hypothesis `P` of an implication `P → Q`. A statement `premise h` is elaborated from the
already elaborated type of `h`, so that a hypothesis of a lemma instantiated at concrete arguments
can be proved on its own without stating it again. -/
abbrev premise {P Q : Prop} (_ : P → Q) : Prop := P

end Deformation.ToposThickening

namespace CategoryTheory.Adjunction

universe v₀ u₀ v₁' u₁' v₂' u₂'

/-- **A mate equation `t₁^♭(q) = κ ≫ γ_*(η₂) ≫ c` transported along identifications of all its
pieces**: categories, their category structures, the functors and adjunctions, the comparison
`c : t₂_* ⋙ γ_* ≅ t₁_*`, the objects and the maps. The equation `H` comes first, so that its
variables are determined by the term proving it; each identification is then a separate
hypothesis, checked on its own. -/
theorem homEquiv_eq_comp_map_unit_comp_of_heq
    {𝒯 𝒯' : Type u₀} {𝒯₁ 𝒯₁' : Type u₁'} {𝒯₂ 𝒯₂' : Type u₂'}
    {c : Category.{v₀} 𝒯} {c' : Category.{v₀} 𝒯'} {c₁ : Category.{v₁'} 𝒯₁}
    {c₁' : Category.{v₁'} 𝒯₁'} {c₂ : Category.{v₂'} 𝒯₂} {c₂' : Category.{v₂'} 𝒯₂'}
    {Lt₁ : 𝒯₁ ⥤ 𝒯} {Rt₁ : 𝒯 ⥤ 𝒯₁} {at₁ : Lt₁ ⊣ Rt₁} {Lt₂ : 𝒯₂ ⥤ 𝒯} {Rt₂ : 𝒯 ⥤ 𝒯₂}
    {at₂ : Lt₂ ⊣ Rt₂} {Rγ : 𝒯₂ ⥤ 𝒯₁} {ct : Rt₂ ⋙ Rγ ≅ Rt₁} {N₁ : 𝒯₁} {N₂ : 𝒯₂}
    {q : Lt₁.obj N₁ ⟶ Lt₂.obj N₂} {κ : N₁ ⟶ Rγ.obj N₂}
    {Lt₁' : 𝒯₁' ⥤ 𝒯'} {Rt₁' : 𝒯' ⥤ 𝒯₁'} {at₁' : Lt₁' ⊣ Rt₁'} {Lt₂' : 𝒯₂' ⥤ 𝒯'}
    {Rt₂' : 𝒯' ⥤ 𝒯₂'} {at₂' : Lt₂' ⊣ Rt₂'} {Rγ' : 𝒯₂' ⥤ 𝒯₁'} {ct' : Rt₂' ⋙ Rγ' ≅ Rt₁'}
    {N₁' : 𝒯₁'} {N₂' : 𝒯₂'} {q' : Lt₁'.obj N₁' ⟶ Lt₂'.obj N₂'} {κ' : N₁' ⟶ Rγ'.obj N₂'}
    (H : at₁.homEquiv _ _ q = κ ≫ Rγ.map (at₂.unit.app N₂) ≫ ct.hom.app (Lt₂.obj N₂))
    (e : 𝒯 = 𝒯') (e₁ : 𝒯₁ = 𝒯₁') (e₂ : 𝒯₂ = 𝒯₂') (ec : HEq c c') (ec₁ : HEq c₁ c₁')
    (ec₂ : HEq c₂ c₂') (eLt₁ : HEq Lt₁ Lt₁') (eRt₁ : HEq Rt₁ Rt₁') (eat₁ : HEq at₁ at₁')
    (eLt₂ : HEq Lt₂ Lt₂') (eRt₂ : HEq Rt₂ Rt₂') (eat₂ : HEq at₂ at₂') (eRγ : HEq Rγ Rγ')
    (ect : HEq ct ct') (eN₁ : HEq N₁ N₁') (eN₂ : HEq N₂ N₂') (eq : HEq q q') (eκ : HEq κ κ') :
    at₁'.homEquiv _ _ q' = κ' ≫ Rγ'.map (at₂'.unit.app N₂') ≫ ct'.hom.app (Lt₂'.obj N₂') := by
  subst e e₁ e₂
  obtain rfl := eq_of_heq ec
  obtain rfl := eq_of_heq ec₁
  obtain rfl := eq_of_heq ec₂
  obtain rfl := eq_of_heq eLt₁
  obtain rfl := eq_of_heq eRt₁
  obtain rfl := eq_of_heq eLt₂
  obtain rfl := eq_of_heq eRt₂
  obtain rfl := eq_of_heq eRγ
  obtain rfl := eq_of_heq eat₁
  obtain rfl := eq_of_heq eat₂
  obtain rfl := eq_of_heq ect
  obtain rfl := eq_of_heq eN₁
  obtain rfl := eq_of_heq eN₂
  obtain rfl := eq_of_heq eq
  obtain rfl := eq_of_heq eκ
  exact H

end CategoryTheory.Adjunction

namespace Deformation.ToposThickening.ThickeningTargetMorphism

attribute [local instance 5000] SheafOfModules.instAbelian

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

/-- **The reduction hypothesis of `idealSquareCompatible_of_transpose` from an equation of
transposes with variable pieces.** If `a₁(w₁) ≫ i₁_*(m) = ν' ≫ j_*(a₂(w₂)) ≫ c` for adjunctions
`aₖ`, maps `wₖ`, `m`, `ν'`, `c` which are the adjunctions `iₖ^* ⊣ iₖ_*`, the identifications
`f'ₖ^*𝒥ₖ ⟶ iₖ^*f'ₖ^*𝒥ₖ ≅ fₖ^*𝒥ₖ`, `λ`, `ν` and the comparison `j_*iₖ_* ≅ i₁_*` read through `E`,
then the reductions carry `ν` to `i₁_*λ`. -/
theorem homEquiv_comp_map_eq_of_eq
    (lam : basePullbackIdeal t₁ f₁ ht₁ ⟶ basePullbackIdeal t₂ f₂ ht₂)
    (ν : (pullbackModules f'₁.toModulesHom).obj ht₁.idealOfThickening.I ⟶
      D.j.pushforwardModules.obj ((pullbackModules f'₂.toModulesHom).obj ht₂.idealOfThickening.I))
    {a₁ : pullbackModules i₁.toModulesHom ⊣ i₁.pushforwardModules}
    {a₂ : pullbackModules i₂.toModulesHom ⊣ i₂.pushforwardModules}
    {w₁ : (pullbackModules i₁.toModulesHom).obj
        ((pullbackModules f'₁.toModulesHom).obj ht₁.idealOfThickening.I) ⟶
      basePullbackIdeal t₁ f₁ ht₁}
    {w₂ : (pullbackModules i₂.toModulesHom).obj
        ((pullbackModules f'₂.toModulesHom).obj ht₂.idealOfThickening.I) ⟶
      basePullbackIdeal t₂ f₂ ht₂}
    {m : basePullbackIdeal t₁ f₁ ht₁ ⟶ basePullbackIdeal t₂ f₂ ht₂}
    {ν' : (pullbackModules f'₁.toModulesHom).obj ht₁.idealOfThickening.I ⟶
      D.j.pushforwardModules.obj ((pullbackModules f'₂.toModulesHom).obj ht₂.idealOfThickening.I)}
    {c : D.j.pushforwardModules.obj (i₂.pushforwardModules.obj (basePullbackIdeal t₂ f₂ ht₂)) ⟶
      i₁.pushforwardModules.obj (basePullbackIdeal t₂ f₂ ht₂)}
    (hcube : a₁.homEquiv _ _ w₁ ≫ i₁.pushforwardModules.map m =
      ν' ≫ D.j.pushforwardModules.map (a₂.homEquiv _ _ w₂) ≫ c)
    (ha₁ : a₁ = RingedToposHom.pullbackAdjPushforwardModules i₁)
    (ha₂ : a₂ = RingedToposHom.pullbackAdjPushforwardModules i₂)
    (hw₁ : w₁ = eqToHom (congrArg (fun g => (pullbackModules g).obj
          ((pullbackModules f'₁.toModulesHom).obj ht₁.idealOfThickening.I))
          i₁.toModulesHom_eq_toRingedToposModulesHom.symm).symm ≫
            (basePullbackIdealIsoPullback i₁ t₁ f₁ f'₁ hi₁ ht₁ comm₁).inv)
    (hw₂ : w₂ = eqToHom (congrArg (fun g => (pullbackModules g).obj
          ((pullbackModules f'₂.toModulesHom).obj ht₂.idealOfThickening.I))
          i₂.toModulesHom_eq_toRingedToposModulesHom.symm).symm ≫
            (basePullbackIdealIsoPullback i₂ t₂ f₂ f'₂ hi₂ ht₂ comm₂).inv)
    (hm : m = lam) (hν : ν' = ν)
    (hc : c = (D.restrictIso ((thickenedModulesFunctor i₂).obj (basePullbackIdeal t₂ f₂ ht₂))).hom ≫
        (structureRestrict i₁).map (E.hom.app (basePullbackIdeal t₂ f₂ ht₂))) :
    (RingedToposHom.pullbackAdjPushforwardModules i₁).homEquiv _ _
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
        (structureRestrict i₁).map (E.hom.app (basePullbackIdeal t₂ f₂ ht₂)) := by
  subst ha₁ ha₂ hw₁ hw₂ hm hν hc
  exact hcube

/-- **The reduction hypothesis along `j = φ` from an equation of transposes with variable
pieces**: the form of
`Deformation.ToposThickening.ThickeningTargetMorphism.homEquiv_comp_map_eq_of_eq` with `j`
replaced by a morphism `φ` and the comparison of the reductions by a map `c` out of
`φ_*i₂_*f₂^*𝒥₂`, the hypothesis on the reductions of
`Deformation.ToposThickening.ThickeningTargetMorphism.idealSquareCompatible_of_transpose_of_j_eq`.
-/
theorem homEquiv_comp_map_eq_comp_of_eq (φ : RingedToposHom Y₂ Y₁)
    (lam : basePullbackIdeal t₁ f₁ ht₁ ⟶ basePullbackIdeal t₂ f₂ ht₂)
    (ν : (pullbackModules f'₁.toModulesHom).obj ht₁.idealOfThickening.I ⟶
      φ.pushforwardModules.obj ((pullbackModules f'₂.toModulesHom).obj ht₂.idealOfThickening.I))
    (c : φ.pushforwardModules.obj ((structureRestrict i₂).obj
        ((thickenedModulesFunctor i₂).obj (basePullbackIdeal t₂ f₂ ht₂))) ⟶
      (structureRestrict i₁).obj ((thickenedModulesFunctor i₁).obj (basePullbackIdeal t₂ f₂ ht₂)))
    {a₁ : pullbackModules i₁.toModulesHom ⊣ i₁.pushforwardModules}
    {a₂ : pullbackModules i₂.toModulesHom ⊣ i₂.pushforwardModules}
    {w₁ : (pullbackModules i₁.toModulesHom).obj
        ((pullbackModules f'₁.toModulesHom).obj ht₁.idealOfThickening.I) ⟶
      basePullbackIdeal t₁ f₁ ht₁}
    {w₂ : (pullbackModules i₂.toModulesHom).obj
        ((pullbackModules f'₂.toModulesHom).obj ht₂.idealOfThickening.I) ⟶
      basePullbackIdeal t₂ f₂ ht₂}
    {m : basePullbackIdeal t₁ f₁ ht₁ ⟶ basePullbackIdeal t₂ f₂ ht₂}
    {ν' : (pullbackModules f'₁.toModulesHom).obj ht₁.idealOfThickening.I ⟶
      φ.pushforwardModules.obj ((pullbackModules f'₂.toModulesHom).obj ht₂.idealOfThickening.I)}
    (hcube : a₁.homEquiv _ _ w₁ ≫ i₁.pushforwardModules.map m =
      ν' ≫ φ.pushforwardModules.map (a₂.homEquiv _ _ w₂) ≫ c)
    (ha₁ : a₁ = RingedToposHom.pullbackAdjPushforwardModules i₁)
    (ha₂ : a₂ = RingedToposHom.pullbackAdjPushforwardModules i₂)
    (hw₁ : w₁ = eqToHom (congrArg (fun g => (pullbackModules g).obj
          ((pullbackModules f'₁.toModulesHom).obj ht₁.idealOfThickening.I))
          i₁.toModulesHom_eq_toRingedToposModulesHom.symm).symm ≫
            (basePullbackIdealIsoPullback i₁ t₁ f₁ f'₁ hi₁ ht₁ comm₁).inv)
    (hw₂ : w₂ = eqToHom (congrArg (fun g => (pullbackModules g).obj
          ((pullbackModules f'₂.toModulesHom).obj ht₂.idealOfThickening.I))
          i₂.toModulesHom_eq_toRingedToposModulesHom.symm).symm ≫
            (basePullbackIdealIsoPullback i₂ t₂ f₂ f'₂ hi₂ ht₂ comm₂).inv)
    (hm : m = lam) (hν : ν' = ν) :
    (RingedToposHom.pullbackAdjPushforwardModules i₁).homEquiv _ _
        (eqToHom (congrArg (fun g => (pullbackModules g).obj
          ((pullbackModules f'₁.toModulesHom).obj ht₁.idealOfThickening.I))
          i₁.toModulesHom_eq_toRingedToposModulesHom.symm).symm ≫
            (basePullbackIdealIsoPullback i₁ t₁ f₁ f'₁ hi₁ ht₁ comm₁).inv) ≫
        (structureRestrict i₁).map ((thickenedModulesFunctor i₁).map lam) =
      ν ≫ φ.pushforwardModules.map ((RingedToposHom.pullbackAdjPushforwardModules i₂).homEquiv _ _
        (eqToHom (congrArg (fun g => (pullbackModules g).obj
          ((pullbackModules f'₂.toModulesHom).obj ht₂.idealOfThickening.I))
          i₂.toModulesHom_eq_toRingedToposModulesHom.symm).symm ≫
            (basePullbackIdealIsoPullback i₂ t₂ f₂ f'₂ hi₂ ht₂ comm₂).inv)) ≫ c := by
  subst ha₁ ha₂ hw₁ hw₂ hm hν
  exact hcube

end Deformation.ToposThickening.ThickeningTargetMorphism

end

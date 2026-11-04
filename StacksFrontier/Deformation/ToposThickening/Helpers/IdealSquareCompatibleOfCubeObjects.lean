module

public import StacksFrontier.Deformation.ToposThickening.Helpers.IdealSquareCompatibleOfCube

/-!
# The reduction hypothesis along `j = φ`, with variable objects in the equation of transposes

`Deformation.ToposThickening.ThickeningTargetMorphism.homEquiv_comp_map_eq_comp_of_eq` matches the
equation of transposes `a₁(w₁) ≫ i₁_*(m) = ν' ≫ φ_*(a₂(w₂)) ≫ c` against its proof with the objects
of the equation fixed (`f'ₖ^*𝒥ₖ`, `fₖ^*𝒥ₖ`), and the comparison `c` read between the restricted
modules. At the relative squares of `Coh_{X/B}` the proof is the cube comparison, whose objects are
spelled differently and whose comparison is out of `φ_*i₂_*`, and the match unfolds them.
`Deformation.ToposThickening.ThickeningTargetMorphism.homEquiv_comp_map_eq_comp_of_heq` takes the
objects, the pieces and the comparison as variables and identifies each with its value by a
separate hypothesis. Used in the functoriality of the obstruction classes of `Coh_{X/B}` (second
proof of Stacks 08WA).

This module is a helper and carries no `@[stacks]` attribute.

## References

* [Stacks Project, Tag 08WA](https://stacks.math.columbia.edu/tag/08WA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

universe v u v₁ u₁ v₂ u₂ w vS uS wS vS' uS' wS' vT uT wT vT' uT' wT'

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

/-- **The reduction hypothesis along `j = φ` from an equation of transposes with variable objects**:
`Deformation.ToposThickening.ThickeningTargetMorphism.homEquiv_comp_map_eq_comp_of_eq` with the
objects `A₁ = f'₁^*𝒥₁`, `B₁ = f₁^*𝒥₁`, `B₂ = B'₂ = f₂^*𝒥₂`, `A₂ = f'₂^*𝒥₂` of the equation of
transposes, its comparison `c'` out of `φ_*i₂_*B'₂` (equal to `c` through a map `c₀` out of
`φ_*i₂_*f₂^*𝒥₂`) and its pieces given as variables, each identified with its value by a separate
hypothesis (heterogeneously for the maps), so that the equation is matched by the term proving it
and each identification is checked on its own. -/
theorem homEquiv_comp_map_eq_comp_of_heq (φ : RingedToposHom Y₂ Y₁)
    (lam : basePullbackIdeal t₁ f₁ ht₁ ⟶ basePullbackIdeal t₂ f₂ ht₂)
    (ν : (pullbackModules f'₁.toModulesHom).obj ht₁.idealOfThickening.I ⟶
      φ.pushforwardModules.obj ((pullbackModules f'₂.toModulesHom).obj ht₂.idealOfThickening.I))
    (c : φ.pushforwardModules.obj ((structureRestrict i₂).obj
        ((thickenedModulesFunctor i₂).obj (basePullbackIdeal t₂ f₂ ht₂))) ⟶
      (structureRestrict i₁).obj ((thickenedModulesFunctor i₁).obj (basePullbackIdeal t₂ f₂ ht₂)))
    {A₁ : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y₁.O)}
    {A₂ : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y₂.O)}
    {B₁ B₂ B'₂ : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    {a₁ : pullbackModules i₁.toModulesHom ⊣ i₁.pushforwardModules}
    {a₂ : pullbackModules i₂.toModulesHom ⊣ i₂.pushforwardModules}
    {w₁ : (pullbackModules i₁.toModulesHom).obj A₁ ⟶ B₁} {m : B₁ ⟶ B₂}
    {ν' : A₁ ⟶ φ.pushforwardModules.obj A₂} {w₂ : (pullbackModules i₂.toModulesHom).obj A₂ ⟶ B'₂}
    {c' : φ.pushforwardModules.obj (i₂.pushforwardModules.obj B'₂) ⟶ i₁.pushforwardModules.obj B₂}
    (hcube : a₁.homEquiv A₁ B₁ w₁ ≫ i₁.pushforwardModules.map m =
      ν' ≫ φ.pushforwardModules.map (a₂.homEquiv A₂ B'₂ w₂) ≫ c')
    (eA₁ : A₁ = (pullbackModules f'₁.toModulesHom).obj ht₁.idealOfThickening.I)
    (eA₂ : A₂ = (pullbackModules f'₂.toModulesHom).obj ht₂.idealOfThickening.I)
    (eB₁ : B₁ = basePullbackIdeal t₁ f₁ ht₁) (eB₂ : B₂ = basePullbackIdeal t₂ f₂ ht₂)
    (eB'₂ : B'₂ = basePullbackIdeal t₂ f₂ ht₂)
    (ha₁ : a₁ = RingedToposHom.pullbackAdjPushforwardModules i₁)
    (ha₂ : a₂ = RingedToposHom.pullbackAdjPushforwardModules i₂)
    (hw₁ : w₁ ≍ (eqToHom (congrArg (fun g => (pullbackModules g).obj
          ((pullbackModules f'₁.toModulesHom).obj ht₁.idealOfThickening.I))
          i₁.toModulesHom_eq_toRingedToposModulesHom.symm).symm ≫
            (basePullbackIdealIsoPullback i₁ t₁ f₁ f'₁ hi₁ ht₁ comm₁).inv :
          (pullbackModules i₁.toModulesHom).obj
              ((pullbackModules f'₁.toModulesHom).obj ht₁.idealOfThickening.I) ⟶
            basePullbackIdeal t₁ f₁ ht₁))
    (hw₂ : w₂ ≍ (eqToHom (congrArg (fun g => (pullbackModules g).obj
          ((pullbackModules f'₂.toModulesHom).obj ht₂.idealOfThickening.I))
          i₂.toModulesHom_eq_toRingedToposModulesHom.symm).symm ≫
            (basePullbackIdealIsoPullback i₂ t₂ f₂ f'₂ hi₂ ht₂ comm₂).inv :
          (pullbackModules i₂.toModulesHom).obj
              ((pullbackModules f'₂.toModulesHom).obj ht₂.idealOfThickening.I) ⟶
            basePullbackIdeal t₂ f₂ ht₂))
    (hm : m ≍ lam) (hν : ν' ≍ ν)
    (c₀ : φ.pushforwardModules.obj (i₂.pushforwardModules.obj (basePullbackIdeal t₂ f₂ ht₂)) ⟶
      i₁.pushforwardModules.obj (basePullbackIdeal t₂ f₂ ht₂))
    (hc : c' ≍ c₀) (hc₀ : c₀ = c) :
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
  subst eA₁ eA₂ eB₁ eB₂ eB'₂ ha₁ ha₂ hw₁ hw₂ hm hν hc hc₀
  exact hcube

end Deformation.ToposThickening.ThickeningTargetMorphism

end

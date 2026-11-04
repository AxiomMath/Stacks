module

public import StacksFrontier.Deformation.ToposThickening.Helpers.ObstructionDescentKey

/-!
# The descended obstruction classes of Situation 08VV along a morphism of thickenings

Let `i₁ : X ⟶ Y₁` and `i₂ : X ⟶ Y₂` be first order thickenings of one ringed topos and
`j : Y₂ ⟶ Y₁` a morphism of their targets, and let each `iₖ` sit in a strict square of
Situation 08VV over a first order thickening `tₖ : Sₖ ⟶ S'ₖ`, with `f'ₖ` flat. The class of
Stacks 08VW, part (1), of an `O_X`-module `F` across `iₖ` is the class `o(iₖ_*F, ...)` of
Stacks 08MF for the action `I ⊗ iₖ_*F ⟶ fₖ^*𝒥ₖ ⊗ iₖ_*F` which is the identity under the
identification `fₖ^*𝒥ₖ = Iₖ` (`Deformation.ToposThickening.basePullbackIdealTensorIso`); it
descends to `Ext²_X(F, fₖ^*𝒥ₖ ⊗ F)` along the equivalence `iₖ_*`.

This file shows that the descended class of the second thickening is the descended class of the
first pushed forward along `λ ⊗ F`, for any map `λ : f₁^*𝒥₁ ⟶ f₂^*𝒥₂` compatible with the map
`I₁ ⟶ j_*I₂` of square-zero ideals under the identifications `fₖ^*𝒥ₖ = Iₖ`
(`ThickeningTargetMorphism.extDescentAddEquiv_symm_existenceObstructionClass_basePullbackIdeal`).
This is the functoriality of the obstruction classes along a morphism of thickenings used in the
proof of Stacks 0CYF, read on `X`.

This module is a helper and carries no `@[stacks]` attribute.

## References

* [Stacks Project, Tag 08VW](https://stacks.math.columbia.edu/tag/08VW)
* [Stacks Project, Tag 0CYF](https://stacks.math.columbia.edu/tag/0CYF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)

universe v u v₁ u₁ v₂ u₂ w e e' vS uS wS vS' uS' wS' vT uT wT vT' uT' wT'

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

/-- **The compatibility of the identifications of Situation 08VV with the map of square-zero
ideals** for `λ : f₁^*𝒥₁ ⟶ f₂^*𝒥₂`: under `eₖ : iₖ_*fₖ^*𝒥ₖ ≅ Iₖ`, `i₁_*λ` is the map
`I₁ ⟶ j_*I₂` of square-zero ideals followed by an isomorphism `E : Ψ₀ ∘ i₂_* ≅ i₁_*`. -/
structure IdealSquareCompatible
    (lam : basePullbackIdeal t₁ f₁ ht₁ ⟶ basePullbackIdeal t₂ f₂ ht₂) : Prop where
  /-- The compatibility. -/
  eq : (basePullbackIdealIsoIdeal i₁ t₁ f₁ f'₁ hi₁ ht₁ comm₁ hf'₁ hstrict₁).inv ≫
        (thickenedModulesFunctor i₁).map lam =
      D.idealMap hi₁ hi₂ ≫
        D.basePushforward.map (basePullbackIdealIsoIdeal i₂ t₂ f₂ f'₂ hi₂ ht₂ comm₂ hf'₂
          hstrict₂).inv ≫
        E.hom.app (basePullbackIdeal t₂ f₂ ht₂)

variable
  [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₁)))]
  [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₂)))]
  [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y₁.O))]
  [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y₂.O))]
  [HasExt.{e'} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

include hj in
/-- **The descended classes of Stacks 08VW, part (1), along a morphism of thickenings.** For a map
`λ : f₁^*𝒥₁ ⟶ f₂^*𝒥₂` which, under the identifications `eₖ : iₖ_*fₖ^*𝒥ₖ ≅ Iₖ` of
Situation 08VV, is the map `I₁ ⟶ j_*I₂` of square-zero ideals followed by
`E : Ψ₀ ∘ i₂_* ≅ i₁_*` (`H`), for any `E` which is an isomorphism `θ : j_*i₂_* ≅ i₁_*` on
underlying sheaves of sets (`hE`), the class of `F` across `i₂`, descended to
`Ext²_X(F, f₂^*𝒥₂ ⊗ F)`, is the descended class across `i₁` pushed forward along `λ ⊗ F`. -/
theorem extDescentAddEquiv_symm_existenceObstructionClass_basePullbackIdeal
    (θ : (D.baseHom.comp (pushforwardRingToposHom i₂ X.O)).toToposHom.pushforward ≅
      (pushforwardRingToposHom i₁ X.O).toToposHom.pushforward)
    (hE : ∀ M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O),
      (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₁))).map
          (E.hom.app M) =
        θ.hom.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M))
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (lam : basePullbackIdeal t₁ f₁ ht₁ ⟶ basePullbackIdeal t₂ f₂ ht₂)
    (H : D.IdealSquareCompatible hi₁ hi₂ t₁ f₁ f'₁ ht₁ comm₁ hf'₁ hstrict₁ t₂ f₂ f'₂ ht₂ comm₂
      hf'₂ hstrict₂ E lam) :
    (extDescentAddEquiv hi₂ F (basePullbackIdeal t₂ f₂ ht₂) 2).symm
        (existenceObstructionClass hi₂ ((thickenedModulesFunctor i₂).obj F) _
          (basePullbackIdealTensorIso i₂ t₂ f₂ f'₂ hi₂ ht₂ comm₂ hf'₂ hstrict₂
            ((thickenedModulesFunctor i₂).obj F)).inv) =
      ((extDescentAddEquiv hi₁ F (basePullbackIdeal t₁ f₁ ht₁) 2).symm
        (existenceObstructionClass hi₁ ((thickenedModulesFunctor i₁).obj F) _
          (basePullbackIdealTensorIso i₁ t₁ f₁ f'₁ hi₁ ht₁ comm₁ hf'₁ hstrict₁
            ((thickenedModulesFunctor i₁).obj F)).inv)).comp
        (Abelian.Ext.mk₀ (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj F).map lam))
        (add_zero 2) :=
  D.extDescentAddEquiv_symm_existenceObstructionClass_eq_comp hi₁ hi₂ hj E F _ _ lam
    (basePullbackIdealIsoIdeal i₁ t₁ f₁ f'₁ hi₁ ht₁ comm₁ hf'₁ hstrict₁)
    (basePullbackIdealIsoIdeal i₂ t₂ f₂ f'₂ hi₂ ht₂ comm₂ hf'₂ hstrict₂)
    (D.hkey_of_idealMap hi₁ hi₂ E θ hE F _ _ lam _ _ H.eq)

end Deformation.ToposThickening.ThickeningTargetMorphism

end

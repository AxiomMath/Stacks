module

public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.CoherentStackRelativeIdealTransposeIdeals

/-!
# The ideal-square compatibility from a transposed comparison, along `j = φ`

`Deformation.ToposThickening.ThickeningTargetMorphism.idealSquareCompatible_of_transpose` reduces
the ideal-square compatibility of a map `λ : f₁^*𝒥₁ ⟶ f₂^*𝒥₂` for a morphism `D` of the targets
of two thickenings to two statements about a map `ν : f'₁^*𝒥₁ ⟶ j_*f'₂^*𝒥₂`, where `j = D.j`.
When `D.j` is equal to a morphism `φ` given in another form, the same holds with `ν`, the two
statements and the comparison `j_*i₂_* ≅ i₁_*` of the reductions written with `φ`
(`Deformation.ToposThickening.ThickeningTargetMorphism.idealSquareCompatible_of_transpose_of_j_eq`).
For the relative squares of morphisms `h₁ : T ⟶ T'₁`, `h₂ : T ⟶ T'₂`, `g : T'₂ ⟶ T'₁` of affine
first order thickenings with `h₂ ≫ g = h₁`, `φ` is the morphism of small étale ringed topoi of
`X_g : X_{T'₂} ⟶ X_{T'₁}` and the comparison of the reductions is Stacks 03LU
(`AlgebraicGeometry.Space.modulePushforwardCompIsoOfEq`), a comparison of direct images of modules
`i_*`. The condition on the reductions, written with these direct images, gives the hypothesis of
the theorem, written with `i_*` over `i_*O_X` restricted along `i^♯`
(`Deformation.ToposThickening.comp_structureRestrict_map_eq_of_comp_pushforwardModules_map_eq`).

This is used in the functoriality of the obstruction classes of `Coh_{X/B}` (second proof of
Stacks 08WA). This module is a helper and carries no `@[stacks]` attribute.

## Main results

* `Deformation.ToposThickening.ThickeningTargetMorphism.idealSquareCompatible_of_transpose_of_j_eq`.
* `Deformation.ToposThickening.comp_structureRestrict_map_eq_of_comp_pushforwardModules_map_eq`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 08WA](https://stacks.math.columbia.edu/tag/08WA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
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
  (t₁ : RingedToposHom S₁ S'₁) (f₁ : RingedToposHom X S₁) (f'₁ : RingedToposHom Y₁ S'₁)
  (ht₁ : FirstOrderThickening t₁) (comm₁ : f'₁.comp i₁ = t₁.comp f₁) (hf'₁ : f'₁.IsFlat)
  (hstrict₁ : (MorphismOfThickenings.ofFirstOrderThickenings i₁ t₁ f₁ f'₁ hi₁ ht₁
    comm₁).IsStrict)
  (t₂ : RingedToposHom S₂ S'₂) (f₂ : RingedToposHom X S₂) (f'₂ : RingedToposHom Y₂ S'₂)
  (ht₂ : FirstOrderThickening t₂) (comm₂ : f'₂.comp i₂ = t₂.comp f₂) (hf'₂ : f'₂.IsFlat)
  (hstrict₂ : (MorphismOfThickenings.ofFirstOrderThickenings i₂ t₂ f₂ f'₂ hi₂ ht₂
    comm₂).IsStrict)
  (E : thickenedModulesFunctor i₂ ⋙ D.basePushforward ≅ thickenedModulesFunctor i₁)

/-- **The ideal-square compatibility from a transposed comparison, along `j = φ`.**
`Deformation.ToposThickening.ThickeningTargetMorphism.idealSquareCompatible_of_transpose` with
`j` replaced by a morphism `φ` equal to it: the comparison `ν : f'₁^*𝒥₁ ⟶ φ_*f'₂^*𝒥₂`, the
condition on the maps of ideals (`H₁`, with the unit-module structure map of `φ` for `j^♯`) and
the condition on the reductions (`H₂`, with a map `c` out of `φ_*i₂_*f₂^*𝒥₂` which is
`j_*i₂_* ≅ Ψ₀i₂_*` followed by `E`, by `hc`) are written with `φ`. -/
theorem idealSquareCompatible_of_transpose_of_j_eq (φ : RingedToposHom Y₂ Y₁) (hj : D.j = φ)
    (lam : basePullbackIdeal t₁ f₁ ht₁ ⟶ basePullbackIdeal t₂ f₂ ht₂)
    (ν : (pullbackModules f'₁.toModulesHom).obj ht₁.idealOfThickening.I ⟶
      φ.pushforwardModules.obj ((pullbackModules f'₂.toModulesHom).obj ht₂.idealOfThickening.I))
    (c : φ.pushforwardModules.obj ((structureRestrict i₂).obj
        ((thickenedModulesFunctor i₂).obj (basePullbackIdeal t₂ f₂ ht₂))) ⟶
      (structureRestrict i₁).obj ((thickenedModulesFunctor i₁).obj (basePullbackIdeal t₂ f₂ ht₂)))
    (hc : (D.restrictIso ((thickenedModulesFunctor i₂).obj (basePullbackIdeal t₂ f₂ ht₂))).hom ≫
        (structureRestrict i₁).map (E.hom.app (basePullbackIdeal t₂ f₂ ht₂)) =
      eqToHom (congrArg (fun ψ : RingedToposHom Y₂ Y₁ => ψ.pushforwardModules.obj
        ((structureRestrict i₂).obj ((thickenedModulesFunctor i₂).obj
          (basePullbackIdeal t₂ f₂ ht₂)))) hj) ≫ c)
    (H₁ : ν ≫ φ.pushforwardModules.map
        ((MorphismOfThickenings.ofFirstOrderThickenings i₂ t₂ f₂ f'₂ hi₂ ht₂ comm₂).idealMap ≫
          hi₂.idealOfThickening.incl) =
      (MorphismOfThickenings.ofFirstOrderThickenings i₁ t₁ f₁ f'₁ hi₁ ht₁ comm₁).idealMap ≫
        hi₁.idealOfThickening.incl ≫ RingedToposHom.unitStructureMap φ)
    (H₂ : (RingedToposHom.pullbackAdjPushforwardModules i₁).homEquiv _ _
        (eqToHom (congrArg (fun g => (pullbackModules g).obj
          ((pullbackModules f'₁.toModulesHom).obj ht₁.idealOfThickening.I))
          i₁.toModulesHom_eq_toRingedToposModulesHom.symm).symm ≫
            (basePullbackIdealIsoPullback i₁ t₁ f₁ f'₁ hi₁ ht₁ comm₁).inv) ≫
        (structureRestrict i₁).map ((thickenedModulesFunctor i₁).map lam) =
      ν ≫ φ.pushforwardModules.map ((RingedToposHom.pullbackAdjPushforwardModules i₂).homEquiv _ _
        (eqToHom (congrArg (fun g => (pullbackModules g).obj
          ((pullbackModules f'₂.toModulesHom).obj ht₂.idealOfThickening.I))
          i₂.toModulesHom_eq_toRingedToposModulesHom.symm).symm ≫
            (basePullbackIdealIsoPullback i₂ t₂ f₂ f'₂ hi₂ ht₂ comm₂).inv)) ≫ c) :
    D.IdealSquareCompatible hi₁ hi₂ t₁ f₁ f'₁ ht₁ comm₁ hf'₁ hstrict₁ t₂ f₂ f'₂ ht₂ comm₂
      hf'₂ hstrict₂ E lam := by
  subst hj
  rw [eqToHom_refl, Category.id_comp] at hc
  subst hc
  exact D.idealSquareCompatible_of_transpose hi₁ hi₂ t₁ f₁ f'₁ ht₁ comm₁ hf'₁ hstrict₁ t₂ f₂ f'₂
    ht₂ comm₂ hf'₂ hstrict₂ E lam ν (by rwa [jSharpUnit_eq_unitStructureMap]) H₂

end Deformation.ToposThickening.ThickeningTargetMorphism

namespace Deformation.ToposThickening

section PushforwardSpelling

variable {X : RingedTopos.{v, u, w}} {Y₁ : RingedTopos.{v₁, u₁, w}} {Y₂ : RingedTopos.{v₂, u₂, w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y₁.J.HasSheafCompose (forget RingCat.{w})]
  [Y₂.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y₁.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y₂.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y₁.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y₂.J.HasSheafCompose (forget AddCommGrpCat.{w})]

omit [Y₁.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y₂.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- **The condition on the reductions, from its spelling with direct images of modules.** For
`i₁ : X ⟶ Y₁`, `i₂ : X ⟶ Y₂`, `φ : Y₂ ⟶ Y₁`, maps `x₁ : P ⟶ i₁_*N₁`, `λ : N₁ ⟶ N₂`,
`ν : P ⟶ φ_*Q`, `x₂ : Q ⟶ i₂_*N₂` and `c : φ_*i₂_*N₂ ⟶ i₁_*N₂`, the equation
`x₁ ≫ i₁_*λ = ν ≫ φ_*x₂ ≫ c`, with `i₁_*λ` and the objects of the composites written with the
direct images `i_*` of modules, is the same equation with `i₁_*λ` written as `i₁_*λ` over
`i₁_*O_X` with the scalars restricted along `i₁^♯` and `c` read between these modules: the
shape of the hypothesis `H₂` of
`ThickeningTargetMorphism.idealSquareCompatible_of_transpose_of_j_eq`. -/
theorem comp_structureRestrict_map_eq_of_comp_pushforwardModules_map_eq
    {i₁ : RingedToposHom X Y₁} {i₂ : RingedToposHom X Y₂} {φ : RingedToposHom Y₂ Y₁}
    {P : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y₁.O)}
    {Q : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y₂.O)}
    {N₁ N₂ : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (x₁ : P ⟶ i₁.pushforwardModules.obj N₁) (lam : N₁ ⟶ N₂)
    (ν : P ⟶ φ.pushforwardModules.obj Q) (x₂ : Q ⟶ i₂.pushforwardModules.obj N₂)
    (c : φ.pushforwardModules.obj ((structureRestrict i₂).obj
        ((thickenedModulesFunctor i₂).obj N₂)) ⟶
      (structureRestrict i₁).obj ((thickenedModulesFunctor i₁).obj N₂))
    (h : x₁ ≫ i₁.pushforwardModules.map lam =
      ν ≫ @CategoryStruct.comp _ _ (φ.pushforwardModules.obj Q)
        (φ.pushforwardModules.obj (i₂.pushforwardModules.obj N₂))
        (i₁.pushforwardModules.obj N₂) (φ.pushforwardModules.map x₂) c) :
    x₁ ≫ (structureRestrict i₁).map ((thickenedModulesFunctor i₁).map lam) =
      ν ≫ φ.pushforwardModules.map x₂ ≫ c :=
  h

end PushforwardSpelling

end Deformation.ToposThickening

end

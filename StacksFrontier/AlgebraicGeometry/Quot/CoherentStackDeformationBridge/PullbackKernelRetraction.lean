module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.PullbackQuotientRetraction

/-!
# The kernel square of the pullback unit along a general retraction

For `a ≫ b = k` of small étale ringed topoi with retractions `c` of `k` and `c₂` of `a`,
`b ≫ c = c₂`, the kernel square of a morphism of extensions read through the retractions
(`AlgebraicGeometry.Space.retraction_map_idealTensorMap_comp_eq`), from the case `c₂ = b ≫ c`
(`AlgebraicGeometry.Space.retraction_map_idealTensorMap_comp_eq_comp`). The comparison
`c_*b_* ≅ (b ≫ c)_* ≅ c₂_*` contains an `eqToIso`; after `subst` it is identified with
`c_*b_* ≅ (b ≫ c)_*` as an isomorphism (`CategoryTheory.map_comp_hom_app_eq_of_eq`), never
componentwise at two spellings of an object.

This module is a helper and carries no `@[stacks]` attribute.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)
open Deformation.ToposThickening
open AlgebraicGeometry (RingedTopos RingedToposHom)

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels

universe u vS uS wS vS' uS' wS' vT uT wT vT' uT' wT'

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance 10000] smallEtaleRingedTopos_hasSheafCompose_forget_ringCat
  smallEtaleRingedTopos_hasSheafCompose_forget₂_commRingCat
  smallEtaleRingedTopos_hasSheafCompose_forget_addCommGrpCat
  smallEtaleRingedTopos_hasSheafCompose_forget_commRingCat
  smallEtaleRingedTopos_hasWeakSheafify_addCommGrpCat
  smallEtaleRingedTopos_hasSheafify_addCommGrpCat
  smallEtaleRingedTopos_wEqualsLocallyBijective_addCommGrpCat

variable {X₀ X₁ X₂ : AlgebraicSpaces B S hS} (a : X₀ ⟶ X₂) (b : X₂ ⟶ X₁) (c : X₁ ⟶ X₀)
  {k : X₀ ⟶ X₁} {c₂ : X₂ ⟶ X₀} (e₁ : a ≫ b = k) (e₂ : b ≫ c = c₂) (h₁ : k ≫ c = 𝟙 X₀)
  (h₂ : a ≫ c₂ = 𝟙 X₀)
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
  (hi₁ : FirstOrderThickening.{u, u + 1, u, u, u + 1, u} (smallEtaleRingedToposHom B S hS k))
  (hi₂ : FirstOrderThickening.{u, u + 1, u, u, u + 1, u} (smallEtaleRingedToposHom B S hS a))
  (t₁ : RingedToposHom S₁ S'₁) (f₁ : RingedToposHom (smallEtaleRingedTopos B S hS X₀) S₁)
  (f'₁ : RingedToposHom (smallEtaleRingedTopos B S hS X₁) S'₁)
  (ht₁ : FirstOrderThickening t₁)
  (comm₁ : f'₁.comp (smallEtaleRingedToposHom B S hS k) = t₁.comp f₁) (hf'₁ : f'₁.IsFlat)
  (hstrict₁ : (MorphismOfThickenings.ofFirstOrderThickenings (smallEtaleRingedToposHom B S hS k)
    t₁ f₁ f'₁ hi₁ ht₁ comm₁).IsStrict)
  (t₂ : RingedToposHom S₂ S'₂) (f₂ : RingedToposHom (smallEtaleRingedTopos B S hS X₀) S₂)
  (f'₂ : RingedToposHom (smallEtaleRingedTopos B S hS X₂) S'₂)
  (ht₂ : FirstOrderThickening t₂)
  (comm₂ : f'₂.comp (smallEtaleRingedToposHom B S hS a) = t₂.comp f₂) (hf'₂ : f'₂.IsFlat)
  (hstrict₂ : (MorphismOfThickenings.ofFirstOrderThickenings (smallEtaleRingedToposHom B S hS a)
    t₂ f₂ f'₂ hi₂ ht₂ comm₂).IsStrict)
  (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos B S hS X₀).O))

/-- `c_*b_* ≅ (b ≫ c)_*` followed by `eqToIso` of a self-equality is `c_*b_* ≅ (b ≫ c)_*`. -/
theorem pushforwardModulesCompAt_trans_eqToIso_rfl :
    pushforwardModulesCompAt B S hS b c ≪≫
        eqToIso (congrArg (fun x : X₂ ⟶ X₀ =>
          (smallEtaleRingedToposHom B S hS x).pushforwardModules) (rfl : b ≫ c = b ≫ c)) =
      pushforwardModulesCompAt B S hS b c :=
  Iso.ext <| NatTrans.ext <| funext fun X =>
    CoherentSituation.trans_eqToIso_hom_app_of_eq_self (pushforwardModulesCompAt B S hS b c)
      (congrArg (fun x : X₂ ⟶ X₀ => (smallEtaleRingedToposHom B S hS x).pushforwardModules)
        (rfl : b ≫ c = b ≫ c)) X

include h₁ h₂ in
/-- The kernel square of a morphism of extensions along `a ≫ b = k`, read through the retractions
`c` of `k` and `c₂` of `a` with `b ≫ c = c₂`: the instance of
`ThickeningTargetMorphism.retraction_map_idealTensorMap_comp_eq_of_idealSquareCompatible` for
`Ψ₀ ∘ a_* ≅ k_*` and `c_*b_* ≅ (b ≫ c)_* ≅ c₂_*`, from the case `c₂ = b ≫ c`
(`AlgebraicGeometry.Space.retraction_map_idealTensorMap_comp_eq_comp`) by `subst`, the two
comparisons being identified as isomorphisms (`CategoryTheory.map_comp_hom_app_eq_of_eq`). -/
theorem retraction_map_idealTensorMap_comp_eq
    (lam : basePullbackIdeal t₁ f₁ ht₁ ⟶ basePullbackIdeal t₂ f₂ ht₂)
    (H : (smallEtaleThickeningTargetOfEq a b k e₁).IdealSquareCompatible hi₁ hi₂ t₁ f₁ f'₁ ht₁
      comm₁ hf'₁ hstrict₁ t₂ f₂ f'₂ ht₂ comm₂ hf'₂ hstrict₂
      (smallEtaleThickenedModulesCompIso a b k e₁) lam)
    {N₁' N₂' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X₀).O)}
    (l₁ : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedTopos B S hS X₀).O).flip.obj F).obj (basePullbackIdeal t₁ f₁ ht₁) ⟶ N₁')
    (l₂ : N₁' ⟶ N₂')
    (l₃ : N₂' ⟶ ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedTopos B S hS X₀).O).flip.obj F).obj (basePullbackIdeal t₂ f₂ ht₂))
    (hlam : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedTopos B S hS X₀).O).flip.obj F).map lam = l₁ ≫ l₂ ≫ l₃) :
    type_of% ((smallEtaleThickeningTargetOfEq a b k
      e₁).retraction_map_idealTensorMap_comp_eq_of_idealSquareCompatible
      hi₁ hi₂ (smallEtaleThickenedModulesCompIso a b k e₁)
      (smallEtaleThickeningTargetPushforwardIso a b k e₁)
      (moduleSheafFunctor_map_smallEtaleThickenedModulesCompIso_hom_app a b k e₁)
      t₁ f₁ f'₁ ht₁ comm₁ hf'₁ hstrict₁ t₂ f₂ f'₂ ht₂ comm₂ hf'₂ hstrict₂
      (smallEtaleRingedToposHom B S hS c).pushforwardModules
      (smallEtaleRingedToposHom B S hS c₂).pushforwardModules
      (pushforwardModulesCompAt B S hS b c ≪≫
        eqToIso (congrArg (fun x : X₂ ⟶ X₀ =>
          (smallEtaleRingedToposHom B S hS x).pushforwardModules) e₂))
      (thickenedPushforwardRetractionIso k c h₁) (thickenedPushforwardRetractionIso a c₂ h₂)
      (thickenedPushforwardRetractionIso_hom_app_thickenedModulesCompIso a b c e₁ e₂ h₁ h₂)
      F lam H l₁ l₂ l₃ hlam) := by
  subst e₂
  exact CategoryTheory.map_comp_hom_app_eq_of_eq rfl
    (pushforwardModulesCompAt_trans_eqToIso_rfl b c)
    (retraction_map_idealTensorMap_comp_eq_comp a b c e₁ h₁ hi₁ hi₂ t₁ f₁ f'₁ ht₁ comm₁ hf'₁
      hstrict₁ t₂ f₂ f'₂ ht₂ comm₂ hf'₂ hstrict₂ F h₂ lam H l₁ l₂ l₃ hlam)

end AlgebraicGeometry.Space

end

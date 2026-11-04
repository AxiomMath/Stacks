module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackChartTangentNaturalityR2
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackChartTangentNaturalityR3
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.PullbackQuotientRetraction

/-!
# Two ingredients of the class of a pulled back lift along a morphism of split thickenings

Let `ξ = (T, 𝒢)` be an object of `Coh_{X/Y}` (Stacks 08KB) and `h : T ⟶ T'`, `h₂ : T ⟶ T'₂`
first order thickenings with `g : T'₂ ⟶ T'` under `T`. To compare the classes on `X_T` of a lift
and of its pullback along `g`, the kernel map of the unit `𝒢' ⟶ (X_g)_*(X_g)^*𝒢'` is read as
the map of coefficient modules `λ_g : 𝒢 ⊗ f_T^*𝒥 ⟶ 𝒢 ⊗ f_T^*𝒥₂`. This file records two
ingredients: `λ ⊗ 𝒢` is `λ_g` through `𝒢 ⊗ f^*𝒥 ≅ 𝒢 ⊗ f_T^*𝒥`
(`AlgebraicGeometry.Space.CoherentSituation.sheafTensor_map_relativeSquareIdealMap`), and the
compatibility of the actions along `f ≫ g = k` of small étale ringed topoi
(`AlgebraicGeometry.Space.smallEtale_hkey_of_idealMap`), and the kernel square of the unit in the
form taken by `CoherentSituation.thickeningLiftDifference_pullback_eq_comp_of_extensionMaps`
(`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftExtension_f_comp_pullbackUnit_eq_comp`).

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.sheafTensor_map_relativeSquareIdealMap`.
* `AlgebraicGeometry.Space.smallEtale_hkey_of_idealMap`.
* `AlgebraicGeometry.Space.CoherentSituation.thickeningLiftExtension_f_comp_pullbackUnit_eq_comp`.

## References

* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
* [Stacks Project, Tag 08VW](https://stacks.math.columbia.edu/tag/08VW)
* [Stacks Project, Tag 08WA](https://stacks.math.columbia.edu/tag/08WA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Deformation.ToposThickening
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels

-- Typeclass search for `(smallEtaleRingedTopos X).J.HasSheafCompose (forget RingCat)` exceeds
-- 1000 heartbeats below priority 10000.
attribute [local instance 10000]
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafCompose_forget_ringCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafCompose_forget_addCommGrpCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasWeakSheafify_addCommGrpCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafify_addCommGrpCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_wEqualsLocallyBijective_addCommGrpCat

universe e u

namespace Stacks.Homology

universe v₁ v₂ u₁ u₂

/-- **`F(λ)` through isomorphisms `F(eₖ)`**: if `λ = e₁ ≫ m ≫ e₂⁻¹`, then `F(λ)` is `F(m)` read
through `F(e₁)`, `F(e₂)`, for any isomorphisms `γₖ` equal to `F(eₖ)` and any `κ` equal to
`F(m)`. -/
theorem map_eq_hom_comp_comp_inv_of_eq {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] (F : C ⥤ D) {A₁ A₂ B₁ B₂ : C} (lam : A₁ ⟶ A₂) (e₁ : A₁ ≅ B₁)
    (e₂ : A₂ ≅ B₂) (m : B₁ ⟶ B₂) (hlam : lam = e₁.hom ≫ m ≫ e₂.inv)
    (γ₁ : F.obj A₁ ≅ F.obj B₁) (γ₂ : F.obj A₂ ≅ F.obj B₂)
    (hγ₁ : γ₁ = F.mapIso e₁) (hγ₂ : γ₂ = F.mapIso e₂)
    (κ : F.obj B₁ ⟶ F.obj B₂) (hκ : κ = F.map m) :
    F.map lam = γ₁.hom ≫ κ ≫ γ₂.inv := by
  subst hlam hγ₁ hγ₂ hκ
  simp

/-- Reassociation of the right side of `f ≫ u = a ≫ b ≫ p`, with the intermediate objects those
of the given composite. -/
theorem comp_eq_comp_comp_of_eq {C : Type u₁} [Category.{v₁} C] {X Y W Z V : C} (f : X ⟶ Y)
    (u : Y ⟶ W) (a : X ⟶ Z) (b : Z ⟶ V) (p : V ⟶ W) (h : f ≫ u = a ≫ b ≫ p) :
    f ≫ u = (a ≫ b) ≫ p :=
  h.trans (Category.assoc a b p).symm

end Stacks.Homology

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- `Deformation.ToposThickening.ThickeningTargetMorphism.hkey_of_idealMap` for `f ≫ g = k` of
small étale ringed topoi, with `Ψ₀ ∘ f_* ≅ k_*` and its value on sheaves of sets. -/
theorem smallEtale_hkey_of_idealMap {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (k : X ⟶ Z) (hk : f ≫ g = k)
    (hi₁ : FirstOrderThickening.{u, u + 1, u, u, u + 1, u} (smallEtaleRingedToposHom B S hS k))
    (hi₂ : FirstOrderThickening.{u, u + 1, u, u, u + 1, u} (smallEtaleRingedToposHom B S hS f))
    (F J₁ J₂ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X).O)) (lam : J₁ ⟶ J₂)
    (e₁ : (thickenedModulesFunctor (smallEtaleRingedToposHom B S hS k)).obj J₁ ≅ hi₁.I)
    (e₂ : (thickenedModulesFunctor (smallEtaleRingedToposHom B S hS f)).obj J₂ ≅ hi₂.I)
    (H : e₁.inv ≫ (thickenedModulesFunctor (smallEtaleRingedToposHom B S hS k)).map lam =
      (smallEtaleThickeningTargetOfEq f g k hk).idealMap hi₁ hi₂ ≫
        (smallEtaleThickeningTargetOfEq f g k hk).basePushforward.map e₂.inv ≫
        (smallEtaleThickenedModulesCompIso f g k hk).hom.app J₂) :
    type_of% ((smallEtaleThickeningTargetOfEq f g k hk).hkey_of_idealMap hi₁ hi₂
      (smallEtaleThickenedModulesCompIso f g k hk)
      (smallEtaleThickeningTargetPushforwardIso f g k hk)
      (moduleSheafFunctor_map_smallEtaleThickenedModulesCompIso_hom_app f g k hk) F J₁ J₂ lam e₁ e₂
      H) :=
  (smallEtaleThickeningTargetOfEq f g k hk).hkey_of_idealMap hi₁ hi₂
    (smallEtaleThickenedModulesCompIso f g k hk) (smallEtaleThickeningTargetPushforwardIso f g k hk)
    (moduleSheafFunctor_map_smallEtaleThickenedModulesCompIso_hom_app f g k hk) F J₁ J₂ lam e₁ e₂ H

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {D : CoherentSituation B S hS} {ξ : CoherentObject D} {T' T'₂ : SchemesOver D.Y}
  {h : ξ.T ⟶ T'} {h₂ : ξ.T ⟶ T'₂}
  (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))
  (hh₂ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₂.left))
  (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h)
  {r : T' ⟶ ξ.T} {r₂ : T'₂ ⟶ ξ.T} (hr : h ≫ r = 𝟙 ξ.T) (hr₂ : h₂ ≫ r₂ = 𝟙 ξ.T)
  (hgr : r₂ = g ≫ r)
  (hfl : IsFlat B S hS (D.projection T').hom) (hfl₂ : IsFlat B S hS (D.projection T'₂).hom)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj ξ.T.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₂.left)]


/-- **`λ ⊗ 𝒢` is the map of coefficient modules `λ_g`**, read through `𝒢 ⊗ f^*𝒥 ≅ 𝒢 ⊗ f_T^*𝒥`
(`AlgebraicGeometry.Space.CoherentSituation.thickeningCoefficientIso`). -/
theorem sheafTensor_map_relativeSquareIdealMap :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O).flip.obj
        (objectToposModule ξ)).map (relativeSquareIdealMap h h₂ g hg hh hh₂) =
      (thickeningCoefficientIso h hh).hom ≫ thickeningCoefficientMap g hg hh hh₂ ≫
        (thickeningCoefficientIso h₂ hh₂).inv := by
  have e₁ := relativeSquareIdealMap_eq_thickeningTestIdeal hh hh₂ g hg
  have e₂ := thickeningCoefficientMap_eq_map hh hh₂ g hg
  exact Stacks.Homology.map_eq_hom_comp_comp_inv_of_eq
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O).flip.obj
        (objectToposModule ξ)) _ _ _ _ e₁ (thickeningCoefficientIso h hh)
    (thickeningCoefficientIso h₂ hh₂) rfl rfl _ e₂

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj ξ.T.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'.left)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T'₂.left)] in
/-- **The kernel square of the unit `𝒢' ⟶ (X_g)_*(X_g)^*𝒢'`**
(`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftExtension_f_comp_pullbackUnit`), with
the kernel map `I ⊗ (i_*𝒢 ≅ Ψ₀ i₂_*𝒢)` followed by the comparison of the map of square-zero
ideals as one map: the form of the hypothesis `hK` of
`thickeningLiftDifference_pullback_eq_comp_of_extensionMaps`. -/
theorem thickeningLiftExtension_f_comp_pullbackUnit_eq_comp (L : D.ThickeningLift ξ h) :
    type_of% (Stacks.Homology.comp_eq_comp_comp_of_eq _ _ _ _ _
      (thickeningLiftExtension_f_comp_pullbackUnit hh hh₂ g hg L)) :=
  Stacks.Homology.comp_eq_comp_comp_of_eq _ _ _ _ _
    (thickeningLiftExtension_f_comp_pullbackUnit hh hh₂ g hg L)

end AlgebraicGeometry.Space.CoherentSituation

end

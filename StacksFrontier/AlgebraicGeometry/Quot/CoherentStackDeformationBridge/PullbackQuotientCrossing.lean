module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.PullbackDifference

/-!
# The quotient square of the pullback unit, in the spelling of the extensions

Let `ξ = (T, 𝒢)` be an object of `Coh_{X/Y}` (Stacks 08KB), `L` a lift of `ξ` across a first
order thickening `h : T ⟶ T'` and `g : T'₂ ⟶ T'` a morphism under `T` from a first order
thickening `h₂ : T ⟶ T'₂`. The quotient square of the unit `𝒢' ⟶ (X_g)_*(X_g)^*𝒢'`
(`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftExtension_g_comp_pullbackQuotientMap`)
is stated there with the quotients `i_*𝒢`, `i₂_*𝒢` written as `Ψ_* 𝒢` for the thickened direct
image functor. This file states it with the quotients written as in the extensions attached to the
lifts, `AlgebraicGeometry.Space.CoherentSituation.thickenedModule`, and with the quotient map
`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftPullbackQuotientMap`: the form in which
the square enters the naturality of the class of an extension.

## Main results

* `AlgebraicGeometry.Space.g_comp_eq_comp_map_g_of_heq_restrictIso_inv`: the quotient square
  of a map of extensions along `a ≫ b = k`, with the quotients and the quotient map as variables.
* `CoherentSituation.thickeningLiftExtension_g_comp_pullbackQuotientMap_eq`: the quotient square
  of the unit `𝒢' ⟶ (X_g)_*(X_g)^*𝒢'` in the spelling of the extensions.
* `CoherentSituation.thickeningLiftExtension_g_comp_pullbackQuotientMap_eq_j`: the same square
  with the direct image along the morphism of thickened targets.

## Implementation notes

Two spellings of one quotient object in the type of an extension make the kernel compare the
direct images `(X_g)_*(E.g)` of the two spellings by unfolding the direct image (about 145000
heartbeats). The quotients are therefore variables of the generic lemma, unified with the
quotients of the given extensions, and its hypotheses fix them by `rfl`; the quotient map and the
comparison of Stacks 03LU enter through `HEq`, so that the given terms keep their own spellings.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Deformation.ToposThickening

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels

-- Below priority 10000, instance search for `(smallEtaleRingedTopos X).J.HasSheafCompose
-- (forget RingCat)` exceeds 1000 heartbeats.
attribute [local instance 10000]
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafCompose_forget_ringCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafCompose_forget₂_commRingCat

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The quotient square of a map of extensions along `a ≫ b = k`, with the quotients as
variables**: for extensions `E₁`, `E₂` of objects `Q₁`, `Q₂` equal to `k_*M`, `a_*M`, a map
`u : E₁ ⟶ b_*E₂` lying over a map `c` which is the comparison `b_*a_* ≅ k_*` of Stacks 03LU, and a
map `τ` which is `k_*M ≅ Ψ₀ a_*M ≅ b_* a_*M`, the quotient map of `E₁` followed by `τ` is `u`
followed by `b_*` of the quotient map of `E₂`
(`AlgebraicGeometry.Space.g_comp_restrictIso_inv_eq_of_comp_map_g_eq`). -/
theorem g_comp_eq_comp_map_g_of_heq_restrictIso_inv {X₀ X₂ X₁ : AlgebraicSpaces B S hS}
    (a : X₀ ⟶ X₂) (b : X₂ ⟶ X₁) {k : X₀ ⟶ X₁} (e : a ≫ b = k)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X₀).O))
    {K₁ Q₁ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X₁).O)}
    {K₂ Q₂ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X₂).O)}
    (E₁ : Abelian.YonedaExtension Q₁ K₁ 0) (E₂ : Abelian.YonedaExtension Q₂ K₂ 0)
    (hQ₁ : (structureRestrict (smallEtaleRingedToposHom B S hS k)).obj
        ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS k)).obj M) = Q₁)
    (hQ₂ : (structureRestrict (smallEtaleRingedToposHom B S hS a)).obj
        ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS a)).obj M) = Q₂)
    (u : E₁.Z.left ⟶ (smallEtaleRingedToposHom B S hS b).pushforwardModules.obj E₂.Z.left)
    (τ : Q₁ ⟶ (smallEtaleRingedToposHom B S hS b).pushforwardModules.obj Q₂)
    (hτ : HEq τ ((structureRestrict (smallEtaleRingedToposHom B S hS k)).map
        ((smallEtaleThickenedModulesCompIso a b k e).inv.app M) ≫
      ((smallEtaleThickeningTargetOfEq a b k e).restrictIso
        ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS a)).obj M)).inv))
    (c : (smallEtaleRingedToposHom B S hS b).pushforwardModules.obj Q₂ ⟶ Q₁)
    (hQ : u ≫ (smallEtaleRingedToposHom B S hS b).pushforwardModules.map E₂.g ≫ c = E₁.g)
    (hc : HEq c ((pushforwardModulesCompAt B S hS a b).hom.app M ≫
        eqToHom (congrArg (fun x : X₀ ⟶ X₁ =>
          (smallEtaleRingedToposHom B S hS x).pushforwardModules.obj M) e))) :
    E₁.g ≫ τ = u ≫ (smallEtaleRingedToposHom B S hS b).pushforwardModules.map E₂.g := by
  subst hQ₁ hQ₂
  have hτ' := eq_of_heq hτ
  subst hτ'
  have hc' := eq_of_heq hc
  subst hc'
  exact g_comp_restrictIso_inv_eq_of_comp_map_g_eq a b e M E₁ E₂ u hQ

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {D : CoherentSituation B S hS} {ξ : CoherentObject D} {T' T'₂ : SchemesOver D.Y}
  {h : ξ.T ⟶ T'} {h₂ : ξ.T ⟶ T'₂}
  (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))
  (hh₂ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₂.left))
  (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h)

/-- **The quotient square of the unit `𝒢' ⟶ (X_g)_*(X_g)^*𝒢'`, in the spelling of the
extensions**: the reduction of `L` followed by the quotient map
`AlgebraicGeometry.Space.CoherentSituation.thickeningLiftPullbackQuotientMap` is the unit followed
by the direct image along `X_g` of the reduction of the pulled back lift. -/
theorem thickeningLiftExtension_g_comp_pullbackQuotientMap_eq (L : D.ThickeningLift ξ h) :
    (thickeningLiftExtension h hh L).g ≫ thickeningLiftPullbackQuotientMap g hg =
      thickeningLiftPullbackUnit hh hh₂ g hg L ≫
        (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap g)).pushforwardModules.map
          (thickeningLiftExtension h₂ hh₂ (L.pullback g hg)).g :=
  g_comp_eq_comp_map_g_of_heq_restrictIso_inv (D.relativeSquareSituation.relativeMap h₂)
    (D.relativeSquareSituation.relativeMap g) (relativeMap_comp_of_comp_eq g hg) ξ.F
    (thickeningLiftExtension h hh L) (thickeningLiftExtension h₂ hh₂ (L.pullback g hg)) rfl rfl
    (thickeningLiftPullbackUnit hh hh₂ g hg L) (thickeningLiftPullbackQuotientMap g hg) HEq.rfl
    _ (thickeningLiftPullbackUnit_comp_map_thickeningLiftExtension_g hh hh₂ g hg L) HEq.rfl

/-- `thickeningLiftExtension_g_comp_pullbackQuotientMap_eq` with the direct image along the
morphism of thickened targets
`AlgebraicGeometry.Space.smallEtaleThickeningTargetOfEq`. -/
theorem thickeningLiftExtension_g_comp_pullbackQuotientMap_eq_j (L : D.ThickeningLift ξ h) :
    (thickeningLiftExtension h hh L).g ≫ thickeningLiftPullbackQuotientMap g hg =
      thickeningLiftPullbackUnit hh hh₂ g hg L ≫
        (smallEtaleThickeningTargetOfEq (D.relativeSquareSituation.relativeMap h₂)
          (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h)
          (relativeMap_comp_of_comp_eq g hg)).j.pushforwardModules.map
          (thickeningLiftExtension h₂ hh₂ (L.pullback g hg)).g :=
  thickeningLiftExtension_g_comp_pullbackQuotientMap_eq hh hh₂ g hg L

end AlgebraicGeometry.Space.CoherentSituation

end

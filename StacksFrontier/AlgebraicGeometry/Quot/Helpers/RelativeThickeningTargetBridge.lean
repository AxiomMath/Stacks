module

public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.SmallEtaleThickeningTargetJBridge

/-!
# The morphism of thickened small étale topoi of a factorization, read through `g`

For morphisms of algebraic spaces `f : X ⟶ Y`, `g : Y ⟶ Z`, `k : X ⟶ Z` with `f ≫ g = k`, the
morphism `j` of `AlgebraicGeometry.Space.smallEtaleThickeningTargetOfEq` is the morphism of small
étale ringed topoi of `g` (`AlgebraicGeometry.Space.smallEtaleThickeningTargetOfEq_j`), its
structure map `j^♯` is the unit-module structure map of `g`
(`AlgebraicGeometry.Space.smallEtaleThickeningTargetOfEq_jSharpUnit`,
`AlgebraicGeometry.Space.comp_map_eq_comp_unitStructureMap_of_smallEtaleThickeningTargetOfEq`),
and the comparison `j_*f_* ≅ Ψ₀f_* ≅ k_*` of the reductions built from
`AlgebraicGeometry.Space.smallEtaleThickenedModulesCompIso` is Stacks 03LU
(`AlgebraicGeometry.Space.modulePushforwardCompIsoOfEq`) read along that equality
(`restrictIso_hom_comp_map_smallEtaleThickenedModulesCompIso_hom_app_eq_eqToHom_comp`),
in the shape of the hypotheses `hj` and `hc` of
`Deformation.ToposThickening.ThickeningTargetMorphism.idealSquareCompatible_of_transpose_of_j_eq`.
All of this is proved once, for variable algebraic spaces. For the relative squares of
`h₁ : T ⟶ T'₁`, `h₂ : T ⟶ T'₂`, `g : T'₂ ⟶ T'₁` with `h₂ ≫ g = h₁`, the equality `hj` is
`AlgebraicGeometry.Space.CoherentSituation.relativeThickeningTarget_j`.

This is used in the functoriality of the obstruction classes of `Coh_{X/B}` (second proof of
Stacks 08WA). This module is a helper and carries no `@[stacks]` attribute.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 08WA](https://stacks.math.columbia.edu/tag/08WA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Deformation.ToposThickening
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify

universe u vS uS wS vS' uS' wS' vT uT wT vT' uT' wT'

namespace AlgebraicGeometry.Space

section Generic

-- Local priority 10000: as in `SmallEtaleObstructionDescentNaturality`, these searches through
-- `smallEtaleRingedTopos` are slow otherwise.
attribute [local instance 10000] smallEtaleRingedTopos_hasSheafCompose_forget_ringCat
  smallEtaleRingedTopos_hasSheafCompose_forget₂_commRingCat
  smallEtaleRingedTopos_hasSheafCompose_forget_addCommGrpCat
  smallEtaleRingedTopos_hasSheafCompose_forget_commRingCat
  smallEtaleRingedTopos_hasWeakSheafify_addCommGrpCat
  smallEtaleRingedTopos_hasSheafify_addCommGrpCat
  smallEtaleRingedTopos_wEqualsLocallyBijective_addCommGrpCat

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (hk : f ≫ g = k)

/-- **The morphism `j` of `smallEtaleThickeningTargetOfEq f g k hk` is that of `g`.** -/
theorem smallEtaleThickeningTargetOfEq_j :
    (smallEtaleThickeningTargetOfEq f g k hk).j = smallEtaleRingedToposHom B S hS g :=
  rfl

/-- **`j^♯` of `smallEtaleThickeningTargetOfEq f g k hk` is the unit-module structure map of
`g`.** -/
theorem smallEtaleThickeningTargetOfEq_jSharpUnit :
    (smallEtaleThickeningTargetOfEq f g k hk).jSharpUnit =
      RingedToposHom.unitStructureMap (smallEtaleRingedToposHom B S hS g) :=
  ThickeningTargetMorphism.jSharpUnit_eq_unitStructureMap (smallEtaleThickeningTargetOfEq f g k hk)

/-- **A square through `j^♯` for `smallEtaleThickeningTargetOfEq f g k hk`, read through `g`**:
`ν ≫ j_*a = b ≫ j^♯` gives the same square for the morphism of small étale ringed topoi of `g` and
its unit-module structure map. -/
theorem comp_map_eq_comp_unitStructureMap_of_smallEtaleThickeningTargetOfEq
    {P : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS Z).O)}
    {Q : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS Y).O)}
    (ν : P ⟶ (smallEtaleRingedToposHom B S hS g).pushforwardModules.obj Q)
    (a : Q ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS Y).O))
    (b : P ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS Z).O))
    (h : ν ≫ (smallEtaleThickeningTargetOfEq f g k hk).j.pushforwardModules.map a =
      b ≫ (smallEtaleThickeningTargetOfEq f g k hk).jSharpUnit) :
    ν ≫ (smallEtaleRingedToposHom B S hS g).pushforwardModules.map a =
      b ≫ RingedToposHom.unitStructureMap (smallEtaleRingedToposHom B S hS g) :=
  h.trans (congrArg (b ≫ ·) (smallEtaleThickeningTargetOfEq_jSharpUnit f g k hk))

/-- **`j_*f_* ≅ Ψ₀f_* ≅ k_*` is Stacks 03LU along `j = g`**: the comparison of the reductions
built from `AlgebraicGeometry.Space.smallEtaleThickenedModulesCompIso` is
`AlgebraicGeometry.Space.modulePushforwardCompIsoOfEq` read along
`AlgebraicGeometry.Space.smallEtaleThickeningTargetOfEq_j`. -/
theorem restrictIso_hom_comp_map_smallEtaleThickenedModulesCompIso_hom_app_eq_eqToHom_comp
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X).O)) :
    ((smallEtaleThickeningTargetOfEq f g k hk).restrictIso
        ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS f)).obj M)).hom ≫
      (structureRestrict (smallEtaleRingedToposHom B S hS k)).map
        ((smallEtaleThickenedModulesCompIso f g k hk).hom.app M) =
    eqToHom (congrArg (fun ψ : RingedToposHom (smallEtaleRingedTopos B S hS Y)
        (smallEtaleRingedTopos B S hS Z) => ψ.pushforwardModules.obj
          ((structureRestrict (smallEtaleRingedToposHom B S hS f)).obj
            ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS f)).obj M)))
        (smallEtaleThickeningTargetOfEq_j f g k hk)) ≫
      (modulePushforwardCompIsoOfEq f g k hk).hom.app M :=
  (restrictIso_hom_comp_map_smallEtaleThickenedModulesCompIso_hom_app_of_eq f g k hk M).trans
    ((congrArg (· ≫ (modulePushforwardCompIsoOfEq f g k hk).hom.app M) (eqToHom_refl _ _)).trans
      (Category.id_comp _)).symm

end Generic

namespace CoherentSituation

/-! The instance context of
`AlgebraicGeometry.Space.CoherentSituation.RelativeIdealSquareCompatible`
(`CoherentStackObstructionNaturality`), so that the statements below are elaborated with the same
instances as that definition. -/

attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels
attribute [local instance] pointTopology

-- Local priority 10000: as observed in `CoherentStackObstructionNaturality`, these searches through
-- `relBaseTop`/`relBaseBottom` take 1-3 s each.
attribute [local instance 10000] relBaseTop_hasSheafCompose_forget_ringCat
  relBaseTop_hasSheafCompose_forget₂_commRingCat relBaseTop_hasSheafCompose_forget_addCommGrpCat
  relBaseBottom_hasSheafCompose_forget_ringCat relBaseBottom_hasSheafCompose_forget₂_commRingCat

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}
  {ξ : CoherentObject D} {T'₁ T'₂ : SchemesOver D.Y} (h₁ : ξ.T ⟶ T'₁) (h₂ : ξ.T ⟶ T'₂)
  (g : T'₂ ⟶ T'₁) (hg : h₂ ≫ g = h₁)
  (hh₁ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₁.left))
  (hh₂ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₂.left))
  (hfl₁ : IsFlat B S hS (D.projection T'₁).hom) (hfl₂ : IsFlat B S hS (D.projection T'₂).hom)

/-- **The morphism `j` of `relativeThickeningTarget h₁ h₂ g hg` is that of `X_g`.** -/
theorem relativeThickeningTarget_j :
    (relativeThickeningTarget h₁ h₂ g hg).j =
      smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap g) :=
  smallEtaleThickeningTargetOfEq_j _ _ _ _

end CoherentSituation


end AlgebraicGeometry.Space

end

module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineDerivedBaseChangeCompExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackLocallyFree
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackUnitComp

/-!
# The derived pullback of the structure sheaf along a composite of algebraic spaces

For morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of algebraic spaces, the identifications
`Lφ^*(𝒪[0]) ≅ 𝒪[0]` (`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackUnitIso`) are
compatible with the composition law `Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*` of Stacks 0D6D
(`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso`): the two identifications of
`Lf^* Lg^* 𝒪_Z[0]` with `𝒪_X[0]` agree.

## Main results

* `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso_hom_app_unit_comp`.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y Z : AlgebraicSpaces B S hS}

/-- **The identifications `L(-)^*(𝒪[0]) ≅ 𝒪[0]` are compatible with composition**: for
`f : X ⟶ Y` and `g : Y ⟶ Z`, the composition law `Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*` of Stacks 0D6D at
`𝒪_Z[0]`, followed by `L(f ≫ g)^*(𝒪_Z[0]) ≅ 𝒪_X[0]`, is `Lf^*` of `Lg^*(𝒪_Z[0]) ≅ 𝒪_Y[0]`
followed by `Lf^*(𝒪_Y[0]) ≅ 𝒪_X[0]`. -/
theorem smallEtaleDerivedModulePullbackCompIso_hom_app_unit_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    (smallEtaleDerivedModulePullbackCompIso B S hS f g).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj
          (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Z))) ≫
      (smallEtaleDerivedModulePullbackUnitIso (f ≫ g)).hom =
    (smallEtaleDerivedModulePullback B S hS f).map (smallEtaleDerivedModulePullbackUnitIso g).hom ≫
      (smallEtaleDerivedModulePullbackUnitIso f).hom := by
  have key :=
    Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackCompIso_hom_app_unit_comp
      (smallEtaleRingedToposHom B S hS f) (smallEtaleRingedToposHom B S hS g)
      (smallEtaleRingedToposHom B S hS (f ≫ g)) (pullbackModulesCompTransport B S hS f g)
  have he := RingedToposHom.pullbackModulesObjUnitIso_hom_comp_of_eq
    (smallEtaleRingedToposHom B S hS f) (smallEtaleRingedToposHom B S hS g)
    (smallEtaleRingedToposHom B S hS (f ≫ g)) (pushforwardModulesCompAt B S hS f g)
    (smallToposMorphismTypeU_comp B S hS f g).hom
    (fun N => moduleSheafFunctor_map_pushforwardModulesCompAt_hom_app B S hS f g N)
    ((RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B S hS f)
      (smallEtaleRingedToposHom B S hS g)).symm ≪≫ pullbackModulesCompTransport B S hS f g)
    (smallEtaleModulePullbackCompIso_eq_leftAdjointCompIso B S hS f g)
  exact (Category.assoc _ _ _).trans (key he)

/-- **The automorphism of `𝒪_X[0]` comparing the two identifications is the identity**:
`L(f ≫ g)^*(𝒪_Z[0]) ≅ 𝒪_X[0]`, inverted, followed by the inverse of the composition law of
Stacks 0D6D, by `Lf^*` of `Lg^*(𝒪_Z[0]) ≅ 𝒪_Y[0]` and by `Lf^*(𝒪_Y[0]) ≅ 𝒪_X[0]`, is `𝟙`. -/
theorem smallEtaleDerivedModulePullbackUnitIso_inv_comp_compIso_inv_app (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    (smallEtaleDerivedModulePullbackUnitIso (f ≫ g)).inv ≫
        (smallEtaleDerivedModulePullbackCompIso B S hS f g).inv.app
          ((DerivedCategory.singleFunctor _ 0).obj
            (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Z))) ≫
        (smallEtaleDerivedModulePullback B S hS f).map
          (smallEtaleDerivedModulePullbackUnitIso g).hom ≫
        (smallEtaleDerivedModulePullbackUnitIso f).hom = 𝟙 _ := by
  rw [← smallEtaleDerivedModulePullbackCompIso_hom_app_unit_comp, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id]

end AlgebraicGeometry.Space

end

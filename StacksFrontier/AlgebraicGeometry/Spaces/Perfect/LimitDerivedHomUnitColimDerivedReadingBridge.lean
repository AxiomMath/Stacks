module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomUnitColimCocycleCrossComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomUnitColimTransportedCompCross
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.DerivedPullComparisonCompHomotopy

/-!
# The composition law of 09RI's crossing isomorphism, from the underived cocycle

The composition law `AlgebraicGeometry.Space.smallEtaleDerivedPullbackDataModelIso_comp` of the
crossing isomorphism of the pullback datum of Stacks 09RI has a hypothesis `h₂`: the factorisation
of the composition comparison of `AlgebraicGeometry.Space.smallEtaleDerivedPullbackData` through
the transported comparison `AlgebraicGeometry.Space.spacesEtaleModelTransportedPullbackComparison`.
Here `h₂` is deduced from the **underived** cocycle of
`AlgebraicGeometry.Space.spacesEtaleModelPullbackHomotopyIso`, which gives the composition law with
that cocycle as its only hypothesis.

## Main definitions

* `AlgebraicGeometry.Space.SpacesEtaleModelPullbackHomotopyIsoCocycle`: the underived cocycle, as
  an equation of isomorphisms of functors on homotopy categories.

## Main results

* `AlgebraicGeometry.Space.spacesEtaleModelTransportedPullbackComparison_comp`: **the hypothesis
  `h₂` of `AlgebraicGeometry.Space.smallEtaleDerivedPullbackDataModelIso_comp`**, from the
  underived cocycle.
* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackDataModelIso_comp_of_underivedCocycle`: **the
  composition law of the crossing isomorphism**, with the underived cocycle as its only
  hypothesis.

## Implementation notes

Two readings of the derived category of `𝒪`-modules on the small étale site of an algebraic space
meet in `h₂`: `AlgebraicGeometry.Space.derivedModules`, through
`AlgebraicGeometry.Space.smallEtaleRingedSite`, carries
`((smallEtaleDerivedPullbackData B S hS).pull f).map`, while
`(spacesEtaleModelModulesDerivedFunctor B S hS X).map` is typed through
`AlgebraicGeometry.Space.smallEtaleRingedTopos`.  The two agree only at default transparency, and
a generic statement has a single category instance for the two, so nothing in the generic layer is
stated at both.  Two things make the passage affordable, and neither is optional:

* the underived cocycle is taken as an **equation of isomorphisms**, and
  `Stacks.CategoryTheory.ModelComparison.underived_comp_app_of_iso` turns it into the pointwise
  shape the generic lemma consumes.  Written out pointwise at the geometric data instead, the
  hypothesis is accepted by the elaborator and then exceeds `maxRecDepth` when it is matched
  against the shape the generic lemma asks for: re-elaborating the components resolves the
  category instances the other way round.  Nothing about the spelling of the binder changes this.
* the conclusion is supplied with `convert ... using 1`, not with `exact`: a single `isDefEq`
  between the whole of the stated equation and the whole of the generic one exceeds `maxRecDepth`,
  while congruence lets each `isDefEq` see one factor.

## References

* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace Stacks.CategoryTheory.ModelComparison

variable {HX HY HZ H'X H'Y H'Z : Type*} [Category HX] [Category HY] [Category HZ]
  [Category H'X] [Category H'Y] [Category H'Z]
  {JX : HX ⥤ H'X} {JY : HY ⥤ H'Y} {JZ : HZ ⥤ H'Z}
  {pf : HY ⥤ HX} {pg : HZ ⥤ HY} {pc : HZ ⥤ HX}
  {p'f : H'Y ⥤ H'X} {p'g : H'Z ⥤ H'Y} {p'c : H'Z ⥤ H'X}

/-- **The compatibility `hχ` of the identifications of the underived pullbacks with the two
underived composition isomorphisms, from the same statement as an equation of isomorphisms.**

This is the hypothesis `hχ` of `Stacks.CategoryTheory.ModelComparison.comp_comm_transported_app`
and of `Stacks.CategoryTheory.ModelComparison.comp_comm_transported_factors`. -/
theorem underived_comp_app_of_iso {e : pg ⋙ pf ≅ pc} {e' : p'g ⋙ p'f ≅ p'c}
    {χf : pf ⋙ JX ≅ JY ⋙ p'f} {χg : pg ⋙ JY ≅ JZ ⋙ p'g} {χc : pc ⋙ JX ≅ JZ ⋙ p'c}
    (h : Functor.isoWhiskerLeft pg χf ≪≫ (Functor.associator pg JY p'f).symm ≪≫
          Functor.isoWhiskerRight χg p'f ≪≫ Functor.associator JZ p'g p'f ≪≫
          Functor.isoWhiskerLeft JZ e' =
        (Functor.associator pg pf JX).symm ≪≫ Functor.isoWhiskerRight e JX ≪≫ χc)
    (M : HZ) :
    χf.hom.app (pg.obj M) ≫ p'f.map (χg.hom.app M) ≫ e'.hom.app (JZ.obj M) =
      JX.map (e.hom.app M) ≫ χc.hom.app M := by
  have h' := congrArg (fun i : pg ⋙ pf ⋙ JX ≅ JZ ⋙ p'c => i.hom.app M) h
  simpa using h'

end Stacks.CategoryTheory.ModelComparison

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] RingedSite.hasSheafCompose_forget₂_ringCat

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Z : AlgebraicSpaces B S hS}

/-- `AlgebraicGeometry.Space.smallEtaleDerivedPullbackData_compIso_inv_app_comp_α` with the
composition isomorphism of degreewise pullbacks written as the one of the datum
`AlgebraicGeometry.Space.modulePullbackDataTopos` on homotopy categories. -/
theorem smallEtaleDerivedPullbackData_compIso_inv_app_comp_α_mapHomotopyCategory (f : X ⟶ Y)
    (g : Y ⟶ Z) (N : HomotopyCategory (Modules.{u, u} B S hS Z.1 Z.2) (ComplexShape.up ℤ)) :
    ((smallEtaleDerivedPullbackData B S hS).compIso f g).inv.app (DerivedCategory.Qh.obj N) ≫
        ((derivedModulePullbackLeftDerived B S hS).α (f ≫ g)).app N =
      ((smallEtaleDerivedPullbackData B S hS).pull f).map
          (((derivedModulePullbackLeftDerived B S hS).α g).app N) ≫
        ((derivedModulePullbackLeftDerived B S hS).α f).app
            (((modulePullbackDataTopos B S hS).mapHomotopyCategory.pull g).obj N) ≫
          ((derivedModulePullbackLeftDerived B S hS).Q X).map
            (((modulePullbackDataTopos B S hS).mapHomotopyCategory.compIso f g).symm.hom.app
              N) := by
  rw [modulePullbackDataTopos_mapHomotopyCategory_compIso_symm_eq]
  exact smallEtaleDerivedPullbackData_compIso_inv_app_comp_α B S hS f g N

/-- **The underived cocycle of the identification of the two degreewise inverse images of
`𝒪`-modules**, as an equation of isomorphisms of functors on homotopy categories: for composable
`f : X ⟶ Y` and `g : Y ⟶ Z`, the identification
`AlgebraicGeometry.Space.spacesEtaleModelPullbackHomotopyIso` at `g`, then the one at `f`, then
the composition isomorphism of the degreewise inverse images on the small étale sites, agree with
the composition isomorphism `AlgebraicGeometry.Space.spacesEtaleModelPullbackComp` of the
degreewise inverse images on the spaces-étale models followed by the identification at `f ≫ g`.

This is the homotopy-category form of the composition law
`AlgebraicGeometry.Space.spacesEtaleModelModulesPullbackHom_comp` of the comparison of the
underived inverse images. -/
abbrev SpacesEtaleModelPullbackHomotopyIsoCocycle (f : X ⟶ Y) (g : Y ⟶ Z) : Prop :=
  Functor.isoWhiskerLeft ((spacesEtaleModelHom B S hS g).pullbackTopos.mapHomotopyCategory
            (ComplexShape.up ℤ)) (spacesEtaleModelPullbackHomotopyIso B S hS f) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (spacesEtaleModelPullbackHomotopyIso B S hS g)
          ((modulePullbackDataTopos B S hS).mapHomotopyCategory.pull f) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (spacesEtaleModelModulesHomotopyFunctor B S hS Z)
          ((modulePullbackDataTopos B S hS).mapHomotopyCategory.compIso f g).symm =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso
            (spacesEtaleModelPullbackComp B S hS f g) (ComplexShape.up ℤ))
          (spacesEtaleModelModulesHomotopyFunctor B S hS X) ≪≫
        spacesEtaleModelPullbackHomotopyIso B S hS (f ≫ g)

/-- **The hypothesis `h₂` of
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackDataModelIso_comp`**: at a complex of
`𝒪`-modules on the model of `Z`, the composition comparison of
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData` followed by the transported comparison
for `f ≫ g` is the transported comparison for `g`, then the one for `f`, then the image of the
composition comparison of the degreewise inverse images on the models. -/
theorem spacesEtaleModelTransportedPullbackComparison_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hχ : SpacesEtaleModelPullbackHomotopyIsoCocycle B S hS f g)
    (M : HomotopyCategory (spacesEtaleModelRingedTopos B S hS Z).Modules
      (ComplexShape.up ℤ)) :
    ((smallEtaleDerivedPullbackData B S hS).compIso f g).inv.app
          ((spacesEtaleModelModulesDerivedFunctor B S hS Z).obj (DerivedCategory.Qh.obj M)) ≫
        (spacesEtaleModelTransportedPullbackComparison B S hS (f ≫ g)).app M =
      ((smallEtaleDerivedPullbackData B S hS).pull f).map
          ((spacesEtaleModelTransportedPullbackComparison B S hS g).app M) ≫
        (spacesEtaleModelTransportedPullbackComparison B S hS f).app
            (((spacesEtaleModelHom B S hS g).pullbackTopos.mapHomotopyCategory
              (ComplexShape.up ℤ)).obj M) ≫
          (spacesEtaleModelModulesDerivedFunctor B S hS X).map (DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryCompIso (spacesEtaleModelPullbackComp B S hS f g)
              (ComplexShape.up ℤ)).hom.app M)) := by
  have := hasDerivedModulePullbacks B S hS f
  have := hasDerivedModulePullbacks B S hS g
  have := hasDerivedModulePullbacks B S hS (f ≫ g)
  have key := Stacks.CategoryTheory.ModelComparison.comp_comm_transported_app
    (e := Functor.mapHomotopyCategoryCompIso (spacesEtaleModelPullbackComp B S hS f g)
      (ComplexShape.up ℤ))
    (htf := spacesEtaleModelTransportedPullbackComparison_app B S hS f)
    (htg := spacesEtaleModelTransportedPullbackComparison_app B S hS g)
    (htc := spacesEtaleModelTransportedPullbackComparison_app B S hS (f ≫ g))
    (h' := smallEtaleDerivedPullbackData_compIso_inv_app_comp_α_mapHomotopyCategory B S hS f g)
    (Stacks.CategoryTheory.ModelComparison.underived_comp_app_of_iso hχ) M
  convert key using 1

/-- **The crossing isomorphisms of 09RI's pullback datum are compatible with composition**, with
the underived cocycle of the degreewise inverse images as the only hypothesis.

This is `AlgebraicGeometry.Space.smallEtaleDerivedPullbackDataModelIso_comp` with its hypothesis
`h₂` discharged by
`AlgebraicGeometry.Space.spacesEtaleModelTransportedPullbackComparison_comp`. -/
theorem smallEtaleDerivedPullbackDataModelIso_comp_of_underivedCocycle (f : X ⟶ Y) (g : Y ⟶ Z)
    (hχ : SpacesEtaleModelPullbackHomotopyIsoCocycle B S hS f g)
    (K : DerivedCategory (spacesEtaleModelRingedTopos B S hS Z).Modules) :
    ((smallEtaleDerivedPullbackData B S hS).compIso f g).inv.app
          ((spacesEtaleModelModulesDerivedFunctor B S hS Z).obj K) ≫
        (smallEtaleDerivedPullbackDataModelIso B S hS (f ≫ g)).inv.app K =
      ((smallEtaleDerivedPullbackData B S hS).pull f).map
          ((smallEtaleDerivedPullbackDataModelIso B S hS g).inv.app K) ≫
        (smallEtaleDerivedPullbackDataModelIso B S hS f).inv.app
            ((derivedPullback (X := spacesEtaleModelRingedTopos B S hS Y)
              (Y := spacesEtaleModelRingedTopos B S hS Z)
              (spacesEtaleModelHom B S hS g)).obj K) ≫
          (spacesEtaleModelModulesDerivedFunctor B S hS X).map
            ((spacesEtaleModelDerivedPullbackCompIso B S hS f g).hom.app K) := by
  refine smallEtaleDerivedPullbackDataModelIso_comp B S hS f g (fun M => ?_) K
  convert spacesEtaleModelTransportedPullbackComparison_comp B S hS f g hχ M using 1

end AlgebraicGeometry.Space

end

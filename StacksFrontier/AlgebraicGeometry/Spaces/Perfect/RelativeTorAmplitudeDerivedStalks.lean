module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Relative
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedDerivedPullbackQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackFlatExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkStructureMap
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkPullbackEtaleLocalRing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkBaseChangeMate
public import StacksFrontier.CategoryTheory.Sites.Point.ModuleStalkDerived

/-!
# Derived stalks of relative objects on the small étale site of an algebraic space

This file computes two derived stalks at a geometric point, as they occur in Stacks 0DL2.

* For a morphism `f : X ⟶ Y` of algebraic spaces and an object `E` of `D(𝒪_X)` represented by a
  complex `K`, the derived stalk at `x̄` of `E` read in `D(f⁻¹𝒪_Y)` is the stalk complex `K_x̄`
  with scalars restricted along the fibre `(f⁻¹𝒪_Y)_x̄ ⟶ 𝒪_{X,x̄}` of the structure map.
* For a *flat* morphism `g : X' ⟶ X`, the derived pullback `Lg^*` of Stacks 06YY is computed
  degreewise, and the stalk of the degreewise pullback at a geometric point `x̄'` of `X'` is the
  extension of scalars of the stalk at `g(x̄')` (Stacks 05V5).

## Main definitions

* `AlgebraicGeometry.Space.scalarRestrictionStalkIso`: the stalk of restriction of scalars along
  `f⁻¹𝒪_Y ⟶ 𝒪_X` is restriction of scalars of the stalk.
* `AlgebraicGeometry.Space.derivedStalkScalarRestrictionIso`: its derived form, at a complex.
* `AlgebraicGeometry.Space.derivedPullbackObjIsoOfIsFlat`: `Lg^*` of a complex along a flat
  morphism is the degreewise pullback.
* `AlgebraicGeometry.Space.pullbackModulesStalkIso` and
  `AlgebraicGeometry.Space.stalkComplexPullbackIso`: Stacks 05V5 for the pullback the derived
  pullback derives, for modules and for complexes.

## Implementation notes

Two spellings of the categories of `𝒪`-modules occur: `AlgebraicGeometry.Space.Modules`, over the
small étale ringed site, and modules over the structure sheaf of the small étale ringed topos,
over which the derived pullback is stated. The restriction-of-scalars side is stated in the first
and the pullback side in the second. The instance
`Stacks.Cohomology.SiteModules.moduleSheavesAbelian` is switched off where the derived category of
modules over the ringed topos is formed, and the derived categories use the model
`HasDerivedCategory.standard`.

## References

* [Stacks Project, Tag 0DL2](https://stacks.math.columbia.edu/tag/0DL2)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
* [Stacks Project, Tag 04EQ](https://stacks.math.columbia.edu/tag/04EQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section ScalarRestriction

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (x : GeometricPoint B S hS X.1)

/-- The stalk of restriction of scalars along `f⁻¹𝒪_Y ⟶ 𝒪_X` at a geometric point `x̄` of
`X` is restriction of scalars of the stalk along the fibre `(f⁻¹𝒪_Y)_x̄ ⟶ 𝒪_{X,x̄}` of the
structure map, naturally in the `𝒪_X`-module. -/
def scalarRestrictionStalkIso :
    scalarRestriction B S hS f ⋙
        Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
          (inverseImageRingedSite B S hS f).O ≅
      Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
          (smallEtaleRingedTopos B S hS X).O ⋙
        ModuleCat.restrictScalars (Stacks.SitePointBaseChange.stalkRingHom
          (smallEtaleRingedToposHom B S hS f).fSharpInverseImage.hom
          (etaleSitePoint B S hS X.1 x X.2)) :=
  Stacks.Sheaves.StalkPullback.restrictScalarsSheafStalkNatIso (etaleSitePoint B S hS X.1 x X.2)
    (smallEtaleRingedToposHom B S hS f).fSharpInverseImage.hom
    (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageRingedSite B S hS f).O).property
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property

/-- The naturality square of `AlgebraicGeometry.Space.scalarRestrictionStalkIso`, stated with the
two composites unfolded. -/
theorem scalarRestrictionStalkIso_naturality {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N) :
    (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
        (inverseImageRingedSite B S hS f).O).map ((scalarRestriction B S hS f).map φ) ≫
      ((scalarRestrictionStalkIso B S hS f x).app N).hom =
    ((scalarRestrictionStalkIso B S hS f x).app M).hom ≫
      (ModuleCat.restrictScalars (Stacks.SitePointBaseChange.stalkRingHom
          (smallEtaleRingedToposHom B S hS f).fSharpInverseImage.hom
          (etaleSitePoint B S hS X.1 x X.2))).map
        ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
          (smallEtaleRingedTopos B S hS X).O).map φ) :=
  (scalarRestrictionStalkIso B S hS f x).hom.naturality φ

/-- The stalk complex at `x̄` of a complex of `𝒪_X`-modules read over `f⁻¹𝒪_Y` is its stalk
complex with scalars restricted along `(f⁻¹𝒪_Y)_x̄ ⟶ 𝒪_{X,x̄}`. -/
def stalkComplexScalarRestrictionIso (K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) :
    ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
        (inverseImageRingedSite B S hS f).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((scalarRestriction B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
    (CochainComplex.restrictScalars (Stacks.SitePointBaseChange.stalkRingHom
          (smallEtaleRingedToposHom B S hS f).fSharpInverseImage.hom
          (etaleSitePoint B S hS X.1 x X.2))).obj
        (((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
          (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (scalarRestrictionStalkIso B S hS f x).app (K.X n))
    (fun i j _ => (scalarRestrictionStalkIso_naturality B S hS f x (K.d i j)).symm)

attribute [local instance 10000] HasDerivedCategory.standard

/-- The derived stalk of an object of `D(𝒪_X)` read in `D(f⁻¹𝒪_Y)`: for a complex `K` of
`𝒪_X`-modules, the derived stalk at a geometric point `x̄` of `K` read over `f⁻¹𝒪_Y` is the stalk
complex `K_x̄` with scalars restricted along `(f⁻¹𝒪_Y)_x̄ ⟶ 𝒪_{X,x̄}`. -/
def derivedStalkScalarRestrictionIso
    (K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) :
    (Stacks.derivedModuleFiber (etaleSitePoint B S hS X.1 x X.2)
        (inverseImageRingedSite B S hS f).O).obj
      ((derivedScalarRestriction B S hS f).obj (DerivedCategory.Q.obj K)) ≅
    DerivedCategory.Q.obj ((CochainComplex.restrictScalars (Stacks.SitePointBaseChange.stalkRingHom
          (smallEtaleRingedToposHom B S hS f).fSharpInverseImage.hom
          (etaleSitePoint B S hS X.1 x X.2))).obj
        (((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
          (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K)) :=
  (Stacks.derivedModuleFiber (etaleSitePoint B S hS X.1 x X.2)
      (inverseImageRingedSite B S hS f).O).mapIso
      ((derivedScalarRestrictionFactors B S hS f).app K) ≪≫
    (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
      (inverseImageRingedSite B S hS f).O).mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso (stalkComplexScalarRestrictionIso B S hS f x K)

end ScalarRestriction

section Pullback

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

/-- The pullback of modules along a flat morphism of algebraic spaces, in the spelling of the
morphism of ringed topoi that the derived pullback derives, is left exact. -/
theorem preservesFiniteLimits_toModulesHom_pullbackModules {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsFlat B S hS f.hom) :
    PreservesFiniteLimits (smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules := by
  rw [pullbackModules_eq_modulePullback]
  exact preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS f hf

attribute [local instance 10000] HasDerivedCategory.standard

/-- For a flat morphism `f` of algebraic spaces, the derived pullback `Lf^*` of a complex is its
degreewise pullback, through the canonical comparison `Lf^* ⟶ f^*` of Stacks 06YY. -/
def derivedPullbackObjIsoOfIsFlat {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsFlat B S hS f.hom)
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS Y).O)) ℤ) :
    (smallEtaleDerivedModulePullback B S hS f).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj
        (((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) :=
  haveI := preservesFiniteLimits_toModulesHom_pullbackModules B S hS f hf
  haveI := Stacks.Cohomology.DerivedPullbackOfToposHom.isIso_derivedPullbackComparison_app
    (smallEtaleRingedToposHom B S hS f) _
    (Stacks.Cohomology.DerivedPullbackOfToposHom.hasResolutions_top
      (Y := smallEtaleRingedTopos B S hS Y))
    (Stacks.Cohomology.DerivedPullbackOfToposHom.pullbackInvertsQuasiIso_top
      (smallEtaleRingedToposHom B S hS f)) ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)
    trivial
  (smallEtaleDerivedModulePullback B S hS f).mapIso
      ((DerivedCategory.quotientCompQhIso _).app P).symm ≪≫
    asIso ((smallEtaleDerivedModulePullbackComparison B S hS f).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) ≪≫
    DerivedCategory.Qh.mapIso
      ((((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules.mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).app P).symm) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _

/-- Stacks 05V5 at a geometric point, for the pullback of modules that the derived pullback
derives: the stalk at `x̄` of the pullback of an `𝒪_Y`-module is the extension of scalars of its
stalk at `f(x̄)`. -/
def pullbackModulesStalkIso {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (x : GeometricPoint B S hS X.1) :=
  Stacks.Sheaves.StalkPullback.stalkFunctorIso (smallEtaleRingedToposHom B S hS f).toModulesHom
      (etaleSitePoint B S hS X.1 x X.2)
      (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
      (smallEtaleInverseImageFiberIso B S hS f x)

/-- The naturality square of `AlgebraicGeometry.Space.pullbackModulesStalkIso`, stated with the
two composites unfolded. -/
theorem pullbackModulesStalkIso_naturality {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (x : GeometricPoint B S hS X.1)
    {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS Y).O)} (φ : M ⟶ N) :
    (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O).map
        ((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules.map φ) ≫
      ((pullbackModulesStalkIso B S hS f x).app N).hom =
    ((pullbackModulesStalkIso B S hS f x).app M).hom ≫
      (ModuleCat.extendScalars (Stacks.Sheaves.StalkPullback.stalkRingMap
        (smallEtaleRingedToposHom B S hS f).toModulesHom
        (etaleSitePoint B S hS X.1 x X.2)
        (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
        (smallEtaleInverseImageFiberIso B S hS f x))).map
        ((Stacks.sheafModuleFiberOfCommRing
          (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
          (smallEtaleRingedTopos B S hS Y).O).map φ) :=
  (pullbackModulesStalkIso B S hS f x).hom.naturality φ

/-- Stacks 05V5 for complexes: the stalk complex at `x̄` of the degreewise pullback of a
complex of `𝒪_Y`-modules is the degreewise extension of scalars of its stalk complex at `f(x̄)`. -/
def stalkComplexPullbackIso {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (x : GeometricPoint B S hS X.1)
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS Y).O)) ℤ) :
    ((Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
        (smallEtaleRingedTopos B S hS X).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ≅
    (CochainComplex.extendScalars (Stacks.Sheaves.StalkPullback.stalkRingMap
        (smallEtaleRingedToposHom B S hS f).toModulesHom
        (etaleSitePoint B S hS X.1 x X.2)
        (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
        (smallEtaleInverseImageFiberIso B S hS f x))).obj
      (((Stacks.sheafModuleFiberOfCommRing
          (etaleSitePoint B S hS Y.1 (geometricPointMap f.hom x) Y.2)
          (smallEtaleRingedTopos B S hS Y).O).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (pullbackModulesStalkIso B S hS f x).app (P.X n))
    (fun i j _ => (pullbackModulesStalkIso_naturality B S hS f x (P.d i j)).symm)

end Pullback

end AlgebraicGeometry.Space

end

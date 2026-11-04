module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.TorIndependentDerivedPullback
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposFlatModule
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesComparisonPullback
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0DKD (2) for modules flat as `f⁻¹𝒪_Y`-modules

Let `S` be a scheme and let

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

be a cartesian square of algebraic spaces over `S` with `X` and `Y'` Tor independent over `Y`.
Stacks 0DKD (2) says: if `𝒢` is an `𝒪_X`-module flat over `Y`, then `L(g')^*𝒢 = (g')^*𝒢`.

Flatness over `Y` of an arbitrary `𝒪_X`-module is flatness as an `f⁻¹𝒪_Y`-module (Stacks 08M5),
whose stalks are then flat over the stalks of `f⁻¹𝒪_Y` (Stacks 05VB); no quasi-coherence is
needed. The argument is the one of
`isIso_smallEtaleDerivedModulePullbackComparison_of_forall_isFlatOverAtGeometricPoint`, run from
flatness of the stalks over the stalks of `f⁻¹𝒪_Y`.

## Main results

* `isIso_smallEtaleDerivedModulePullbackComparison_of_forall_flat_relativeStalk`: the comparison
  is an isomorphism for a module whose stalks are flat over the stalks of `f⁻¹𝒪_Y`.
* `isIso_smallEtaleDerivedModulePullbackComparison_of_ringedToposHom_isFlatOver`: the
  comparison is an isomorphism for an `𝒪_X`-module flat over `Y` (Stacks 0DKD (2)).

## References

* [Stacks Project, Tag 0DKD](https://stacks.math.columbia.edu/tag/0DKD)
* [Stacks Project, Tag 05VB](https://stacks.math.columbia.edu/tag/05VB)
* [Stacks Project, Tag 08M5](https://stacks.math.columbia.edu/tag/08M5)
-/

/- Instances that come into scope here only through the base versions of imported modules,
and that would change the elaboration below (universe joins, the small model of `D(R)`). -/
attribute [-instance] Stacks.SheafOfModules.coefficientSheafification
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
  CategoryTheory.sheafCompose

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Bounded

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- **The stalk of a module flat over `Y` is flat over the stalk of `f⁻¹𝒪_Y`.** An `𝒪_X`-module
flat over `Y` in the sense of Stacks 08M5 — flat as an `f⁻¹𝒪_Y`-module — has, at every point `x̄`
of the small étale site of `X`, a stalk flat over `(f⁻¹𝒪_Y)_{x̄}` (Stacks 05VB). -/
theorem flat_relativeStalk_of_ringedToposHom_isFlatOver (x : GeometricPoint B S hS X.1)
    (G : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (hG : RingedToposHom.IsFlatOver (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f) G) :
    Module.Flat (relativeStalkRing f x)
      ((ModuleCat.restrictScalars (relativeStalkMap f x)).obj
        (Stacks.moduleStalk (etaleSitePoint B S hS X.1 x X.2)
          (smallEtaleRingedTopos B S hS X).O G)) := by
  have h : Stacks.IsFlatModuleStalk (etaleSitePoint B S hS X.1 x X.2)
      (inverseImageRingedSite B S hS f).O ((scalarRestriction B S hS f).obj G) :=
    Stacks.isFlatModuleStalk_of_isFlat_freeUniverse (inverseImageRingedSite B S hS f).O
      ((scalarRestriction B S hS f).obj G) (etaleSitePoint B S hS X.1 x X.2) hG
  have : Module.Flat (relativeStalkRing f x)
      ((scalarRestriction B S hS f ⋙ Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS X.1 x X.2) (inverseImageRingedSite B S hS f).O).obj G) := h
  exact Module.Flat.of_linearEquiv
    ((scalarRestrictionStalkIso _ _ _ f x).app G).symm.toLinearEquiv

end Bounded

section Main

variable {X' X Y' Y : AlgebraicSpaces B S hS} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
  (g : Y' ⟶ Y) (hpb : IsPullback g' f' f g)

include hpb in
/-- For a cartesian square of algebraic spaces with `X` and `Y'` Tor independent over `Y`, and an
`𝒪_X`-module `𝒢` whose stalk at every point `x̄` of the small étale site of `X` is flat over the
stalk of `f⁻¹𝒪_Y`, the canonical comparison `L(g')^*𝒢 ⟶ (g')^*𝒢` is an isomorphism. -/
theorem isIso_smallEtaleDerivedModulePullbackComparison_of_forall_flat_relativeStalk
    (htor : TorIndependent X.2 Y'.2 Y.2 f.hom g.hom)
    (G : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (hG : ∀ x, Module.Flat (relativeStalkRing f x)
      ((ModuleCat.restrictScalars (relativeStalkMap f x)).obj
        (Stacks.moduleStalk (etaleSitePoint B S hS X.1 x X.2)
          (smallEtaleRingedTopos B S hS X).O G))) :
    IsIso ((smallEtaleDerivedModulePullbackComparison B S hS g').app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) 0).obj G))) := by
  obtain ⟨P, q, hq, hPLE, hPflat⟩ := exists_flat_resolution ((CochainComplex.singleFunctor
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) 0).obj G) 0 inferInstance
  have hPK := @smallEtaleModuleKFlat_of_isStrictlyLE B S hS X P 0 hPLE hPflat
  refine isIso_smallEtaleDerivedModulePullbackComparison_of_quasiIso g' q hq ?_
    (isIso_smallEtaleDerivedModulePullbackComparison_app B S hS g' _ hPK)
  refine quasiIso_of_forall_stalkComplex _ (fun x' => ?_)
  refine (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoOfNatIso (pullbackStalkComplexNatIso g' x')
    (Arrow.mk q))).2 ?_
  let x := geometricPointMap g'.hom x'
  let F := Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
    (smallEtaleRingedTopos B S hS X).O
  have : F.Additive := Stacks.instAdditiveSheafModuleFiberOfCommRing
    (etaleSitePoint B S hS X.1 x X.2) (smallEtaleRingedTopos B S hS X).O
  have : PreservesFiniteLimits F := Stacks.preservesFiniteLimits_sheafModuleFiberOfCommRing
    (etaleSitePoint B S hS X.1 x X.2) (smallEtaleRingedTopos B S hS X).O
  have : PreservesFiniteColimits F := Stacks.instPreservesFiniteColimitsSheafModuleFiberOfCommRing
    (etaleSitePoint B S hS X.1 x X.2) (smallEtaleRingedTopos B S hS X).O
  let E := ModuleCat.extendScalars.{u, u, u} (smallEtaleStalkPullbackRingMap B S hS g' x')
  let s := (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app G
  let qL := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map q ≫ s.hom
  have : QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map q) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology q F
  have : QuasiIso qL := inferInstanceAs (QuasiIso (_ ≫ _))
  have hring : QuasiIso ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map qL) :=
    quasiIso_extendScalars_relativeStalk g' f' f g hpb htor x' P
      (kFlat_stalkComplex x P 0 hPLE hPflat) (F.obj G) (hG x) qL
  have : QuasiIso ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map s.hom) := inferInstance
  have hc : QuasiIso ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map q) ≫
      (E.mapHomologicalComplex (ComplexShape.up ℤ)).map s.hom) := by
    rwa [← Functor.map_comp]
  exact (quasiIso_iff_comp_right _ _).1 hc

include hpb in
/-- For a cartesian square of algebraic spaces with `X` and `Y'` Tor independent over `Y`, and an
`𝒪_X`-module `𝒢` flat over `Y` — flat as an `f⁻¹𝒪_Y`-module, Stacks 08M5 — the canonical
comparison `L(g')^*𝒢 ⟶ (g')^*𝒢` is an isomorphism. -/
@[stacks 0DKD "part (2)"]
theorem isIso_smallEtaleDerivedModulePullbackComparison_of_ringedToposHom_isFlatOver
    (htor : TorIndependent X.2 Y'.2 Y.2 f.hom g.hom)
    (G : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (hG : RingedToposHom.IsFlatOver (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f) G) :
    IsIso ((smallEtaleDerivedModulePullbackComparison B S hS g').app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) 0).obj G))) :=
  isIso_smallEtaleDerivedModulePullbackComparison_of_forall_flat_relativeStalk g' f' f g hpb htor
    G (fun x => flat_relativeStalk_of_ringedToposHom_isFlatOver f x G hG)

end Main

end AlgebraicGeometry.Space

end

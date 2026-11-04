module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.DualityPullbackComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedHigherDirectImageComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedRightAdjointDuality
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped

/-!
# Reading the right adjoint of a represented morphism on the Zariski site

Let `g : T' ⟶ T` be a morphism of the big fppf site over `S` between quasi-compact and
quasi-separated objects, with underlying morphism of schemes `g_0 : X'_0 ⟶ X_0`. By Stacks 0E6E
the right adjoint `a` of `Rf_*` for the represented morphism of algebraic spaces `f` and the
right adjoint `a_0` of `Rg_{0,*}` correspond under the equivalences `Φ` of Stacks 071Q. This file
reads that correspondence on cohomology sheaves: for `M ∈ D_QCoh(𝒪_{X_0})`, the restriction to
the Zariski site of `X'_0` of `H^n(a(Φ M))` is `H^n(a_0 M)`.

## Main results

* `AlgebraicGeometry.Space.representedZariskiPullbackRestrictIso`: for a quasi-coherent
  `𝒪_{X_0}`-module `F`, the restriction of `ε^* F` to the Zariski site of `X_0` is `F`.
* `AlgebraicGeometry.Space.representedEquivalenceHomologyRestrictIso`: for
  `E ∈ D_QCoh(𝒪_{X_0})`, the restriction of `H^n(Φ E)` to the Zariski site of `X_0` is `H^n(E)`.
* `AlgebraicGeometry.Space.representedRightAdjointHomologyRestrictIso`: the restriction of
  `H^n(a(Φ M))` is `H^n(a_0 M)`.

## Implementation notes

Unregistered helpers (towards the relative dualizing sheaf of a family of curves, Stacks 0E6Q,
whose fibres are read through Section 0E6N: "for any base change of `X` which is a scheme, the
relative dualizing complex agrees with the relative dualizing complex of Duality for Schemes").

## References

* [Stacks Project, Tag 0E6E](https://stacks.math.columbia.edu/tag/0E6E)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 0E6N](https://stacks.math.columbia.edu/tag/0E6N)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

-- No global `HasDerivedCategory` instance applies to modules on small étale sites, which are not
-- `SmallCategory`; at low priority the standard model chooses nothing where a global one exists.
attribute [local instance low] HasDerivedCategory.standard

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- **`ε^*` followed by the restriction to the Zariski site is the identity on quasi-coherent
modules**: for a quasi-coherent `𝒪_{X_0}`-module `F`, the restriction of `ε^* F` to the Zariski
site of `X_0` along the identity chart is `F`. This is the unit `F ≅ ε_* ε^* F` of
Stacks 03DX (2), with `ε_*` read as the restriction to the identity chart. -/
def representedZariskiPullbackRestrictIso
    (F : (representedSchemeRepresentedZariskiRingedToposHom B S hS U).Modules)
    (hF : F.IsQuasicoherent) :
    restrictToChartScheme B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
        ((representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U).obj F)
        (idEtaleChart B S hS U) ≅ F :=
  haveI := isIso_representedZariskiModuleAdjunction_unit_app_representedZariskiModuleAdjunction
    B S hS U F hF
  restrictToChartSchemeIdEtaleChartIso B S hS U _ ≪≫
    (AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).mapIso
        ((representedSmallEtaleModuleEquivalenceInverseIso B S hS U).app _) ≪≫
    ((representedZariskiModulePushforwardIsoRepresentedZariskiModuleAdjunction B S hS U).app
      _).symm ≪≫
    (asIso ((representedZariskiModuleAdjunctionRepresentedZariskiModuleAdjunction B S hS U).unit.app
      F)).symm

/-- **The equivalence `Φ` of Stacks 071Q, read on cohomology sheaves and restricted to the
Zariski site**: for `E ∈ D_QCoh(𝒪_{X_0})` (at the locally small model), the restriction of
`H^n(Φ E)` to the Zariski site of `X_0` along the identity chart is `H^n(E)`. Here `Φ` is the
comparison of the two models of `D(𝒪_{X_0})` followed by `Lε^*`, so `H^n(Φ E) = ε^* H^n(E)`,
and `ε^*` followed by the restriction is the identity on quasi-coherent modules. -/
def representedEquivalenceHomologyRestrictIso
    (E : Stacks.Duality.quasiCoherentDerivedCategory
      (representedSchemeRepresentedZariskiRingedToposHom B S hS U)) (n : ℤ) :
    restrictToChartScheme B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
        ((DerivedCategory.homologyFunctor _ n).obj
          ((representedDualityQuasicoherentDerivedEquivalence B S hS U).functor.obj E).obj)
        (idEtaleChart B S hS U) ≅
      (DerivedCategory.homologyFunctor
        (representedSchemeRepresentedZariskiRingedToposHom B S hS U).Modules n).obj E.obj :=
  let e := Stacks.Injectives.grothendieckModelEquiv.{u}
    (representedSchemeRepresentedZariskiRingedToposHom B S hS U).Modules
  let E' := e.inverse.obj E.obj
  let h₁ := (representedZariskiDerivedPullbackHomologyIso B S hS U n).app E'
  let h₂ : (@DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) n).obj E' ≅
      (DerivedCategory.homologyFunctor
        (representedSchemeRepresentedZariskiRingedToposHom B S hS U).Modules n).obj E.obj :=
    ((StacksDraft.DerivedModel.grothendieckModelEquivHomologyIso _ n).app E').symm ≪≫
      (DerivedCategory.homologyFunctor
        (representedSchemeRepresentedZariskiRingedToposHom B S hS U).Modules n).mapIso
        (e.counitIso.app E.obj)
  (restrictToChartSchemeFunctor B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
      (idEtaleChart B S hS U)).mapIso
      (h₁ ≪≫
        (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U).mapIso h₂) ≪≫
    representedZariskiPullbackRestrictIso B S hS U _ (E.property n)

/-- **The comparison of models carries `𝒪_{X_0}` in degree zero to `𝒪_{X_0}` in degree zero.**
The inverse of the comparison of the standard and the locally small model of `D(𝒪_{X_0})`
takes the structure sheaf placed in degree zero to the structure sheaf placed in degree zero:
both models localize the same category of complexes, and the comparison matches the two
localization functors on the nose. -/
def grothendieckModelEquivInverseStructureSheafIso (X : Scheme.{u}) :
    (Stacks.Injectives.grothendieckModelEquiv.{u} X.Modules).inverse.obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf)) ≅
      (@DerivedCategory.singleFunctor X.Modules _ _ (HasDerivedCategory.standard _) 0).obj
        (SheafOfModules.unit X.ringCatSheaf) :=
  let e := Stacks.Injectives.grothendieckModelEquiv.{u} X.Modules
  let K := (HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj
    (SheafOfModules.unit X.ringCatSheaf)
  e.inverse.mapIso ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app _) ≪≫
    eqToIso (congrArg e.inverse.obj
      (Functor.congr_obj (Stacks.Injectives.grothendieckModelEquiv_comp_Q.{u} X.Modules).symm
        K)) ≪≫
    (e.unitIso.app _).symm ≪≫
    (@DerivedCategory.singleFunctorIsoCompQ X.Modules _ _
      (HasDerivedCategory.standard _) 0).symm.app _

/-- `ε^* 𝒪_{X_0} = 𝒪_X` (Stacks 03LU for the comparison morphism `ε`). -/
def representedZariskiPullbackUnitIso :
    (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U).obj
        (SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf :
          (representedSchemeRepresentedZariskiRingedToposHom B S hS U).Modules) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).O) :=
  (Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso
    (X := smallEtaleRingedTopos B S hS (representedSpace U))
    (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
    (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U).toModulesHom).symm

open scoped Stacks.StandardDerivedModel in
/-- **The equivalence `Φ` of Stacks 071Q carries the structure sheaf to the structure sheaf**:
`Φ(𝒪_{X_0}) = Lε^* 𝒪_{X_0} = ε^* 𝒪_{X_0} = 𝒪_X`, all placed in degree zero. The functor `Lε^*`
is stated at the standard model of `D(𝒪_{X_0})`, which the scope opened here selects. -/
def representedEquivalenceStructureSheafIso :
    (representedDualityQuasicoherentDerivedEquivalence B S hS U).functor.obj
        (Stacks.Duality.DerivedPushforward.derivedStructureSheaf
          ((BigFppfOver.toScheme B S hS).obj U)) ≅
      derivedStructureSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) :=
  ObjectProperty.isoMk _
    ((representedZariskiDerivedPullback B S hS U).mapIso
        (grothendieckModelEquivInverseStructureSheafIso ((BigFppfOver.toScheme B S hS).obj U)) ≪≫
      (representedZariskiDerivedPullbackIso B S hS U).app _ ≪≫
      ((representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U
        ).mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso (representedZariskiPullbackUnitIso B S hS U))

section RightAdjoint

variable {B S hS} (hZ : B.Contains (⊤_ Scheme.{u})) {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
  (hXqc : IsQuasiCompactSpace B S hS (yoneda.obj T'))
  (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj T'))
  (hYqc : IsQuasiCompactSpace B S hS (yoneda.obj T))
  (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj T))

/-- **Stacks 0E6E read on cohomology sheaves.** Let `g : T' ⟶ T` be a morphism of quasi-compact
and quasi-separated objects of the big fppf site, `a` the right adjoint of `Rf_*` for the
represented morphism of algebraic spaces and `a_0` the right adjoint of `Rg_{0,*}` for the
underlying morphism of schemes. For `M ∈ D_QCoh(𝒪_{X_0})`, the restriction of `H^n(a(Φ M))` to
the Zariski site of `X'_0` is `H^n(a_0 M)`. -/
def representedRightAdjointHomologyRestrictIso
    (M : Stacks.Duality.quasiCoherentDerivedCategory (BigFppfOver.toScheme B S hS |>.obj T))
    (n : ℤ) :
    haveI : CompactSpace (B.inclusion.obj T'.left) :=
      compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS hXqc
    haveI : QuasiSeparatedSpace (B.inclusion.obj T'.left) :=
      (isAbsolutelyQuasiSeparated_yoneda_iff_quasiSeparatedSpace B S hS hZ T').1 hXqs
    haveI : CompactSpace (B.inclusion.obj T.left) :=
      compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS hYqc
    haveI : QuasiSeparatedSpace (B.inclusion.obj T.left) :=
      (isAbsolutelyQuasiSeparated_yoneda_iff_quasiSeparatedSpace B S hS hZ T).1 hYqs
    haveI :=
      Stacks.Duality.DerivedPushforward.isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_qcqs
        (B.inclusion.map g.left)
    haveI := isLeftAdjoint_quasicoherentDerivedPushforward hZ (representedSpaceMap B S hS g)
      hXqc hXqs hYqs
    restrictToChartScheme B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')
        ((DerivedCategory.homologyFunctor _ n).obj
          ((quasicoherentDerivedPushforward B S hS (representedSpaceMap B S hS g)
            (representedSpaceMap_isQuasiCompact hZ g hXqc hYqs)
            (representedSpaceMap_isQuasiSeparated hZ g hXqs)).rightAdjoint.obj
              ((representedDualityQuasicoherentDerivedEquivalence B S hS T).functor.obj
                M)).obj)
        (idEtaleChart B S hS T') ≅
      (DerivedCategory.homologyFunctor (BigFppfOver.toScheme B S hS |>.obj T').Modules n).obj
        ((Stacks.Duality.DerivedPushforward.qcqsRestrictedDerivedPushforward
          (B.inclusion.map g.left)).rightAdjoint.obj M).obj :=
  (restrictToChartSchemeFunctor B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')
      (idEtaleChart B S hS T')).mapIso
      ((DerivedCategory.homologyFunctor _ n).mapIso
        ((ObjectProperty.ι _).mapIso
          ((representedRightAdjointIso hZ g hXqc hXqs hYqc hYqs).app M).symm)) ≪≫
    representedEquivalenceHomologyRestrictIso B S hS T' _ n

end RightAdjoint

end AlgebraicGeometry.Space

end

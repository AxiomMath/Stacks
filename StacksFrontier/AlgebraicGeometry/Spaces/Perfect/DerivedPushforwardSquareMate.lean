module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedAdjunctionOfExactUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedCoheratorComparisonConservative
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedCoheratorCounitMate
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PushforwardOfSupportedPerfectCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RestrictExtensionByZero
public import StacksFrontier.CategoryTheory.Adjunction.Mates
public import StacksFrontier.Homology.Injectives.DerivedCategory.ArbitraryModelCounit

/-!
# The square of adjunctions behind the hypothesis of Stacks 09TG

For an étale morphism `j : V ⟶ W` of algebraic spaces the inverse images `j^*` of all modules
and of quasi-coherent modules are exact, so they induce functors of derived categories which,
by Stacks 09T5, are left adjoint to the derived direct image `Rj_*` and to the functor `Φ` of
Stacks 08GZ; together with the comparison functors `i_V`, `i_W` of Stacks 08F1 this is a square
of four adjunctions with an invertible 2-cell.  The file also records that `Rg_* ⋙ Rf_*` is a
total right derived functor of the direct image along `g ≫ f` when `g` is étale, and that a
total right derived functor of `k_*((-)|_k)` splits as a restriction followed by `Rk_*`.

## Main definitions

* `AlgebraicGeometry.Space.etaleDerivedModulePullbackPushforwardAdjunction` and
  `AlgebraicGeometry.Space.quasicoherentDerivedPullbackPushforwardAdjunction`: the two vertical
  adjunctions of the square, `j^* ⊣ Rj_*` on all modules and `j^* ⊣ Φ` on quasi-coherent
  modules.
* `AlgebraicGeometry.Space.derivedComparisonCompιEtalePullbackIso` and
  `AlgebraicGeometry.Space.derivedComparisonCompιEtalePullbackSquare`: the 2-cell of the square,
  the commutation of the comparison functors of Stacks 08F1 with the derived inverse images. The
  2-cell is invertible, being the `hom` of the isomorphism (`CategoryTheory.Iso.isIso_hom`).

## Main results

* `AlgebraicGeometry.Space.etaleDerivedModulePullbackPushforwardAdjunction_counit_fac` and
  `AlgebraicGeometry.Space.quasicoherentDerivedPullbackPushforwardAdjunction_counit_fac`: each of
  the two vertical adjunctions has, on a cochain complex, the class of the degreewise counit as
  its counit — after the derivation unit of the corresponding derived direct image.  These are
  what make the counit square of the mates correspondence computable on the image of
  `DerivedCategory.Q`, which is where
  `Stacks.CategoryTheory.mateEquiv_eq_of_counit_rightDerived` asks for it.
* `AlgebraicGeometry.Space.isRightDerivedFunctor_derivedModulePushforwardComp`: for an étale
  `g : U ⟶ V` and any `f : V ⟶ W`, the composite `Rg_* ⋙ Rf_*` is a total right derived functor
  of the direct image along `g ≫ f`, because `g_*` preserves K-injectivity.
* `AlgebraicGeometry.Space.nonempty_rightDerivedRestrictPushObjIso`: a total right derived
  functor of `k_*((-)|_k)` along an étale `k` is `Rk_*` of the derived restriction, at every
  object.

## What is not here

No Stacks tag is registered.  The identification of the canonical comparison
`AlgebraicGeometry.Space.derivedPushforwardSquareComparison` of the hypothesis of Stacks 09TG
with the mate of the 2-cell under the two vertical adjunctions is **not** proved, and without it
nothing here is connected to that hypothesis; see
`AlgebraicGeometry.Space.derivedComparisonCompιEtalePullbackSquare`.

## Implementation notes

Exactness of the inverse image on quasi-coherent modules holds because an étale morphism is
flat, `AlgebraicGeometry.Space.preservesFiniteLimits_quasicoherentPullbackFunctor_of_isFlat` and
`AlgebraicGeometry.Space.preservesFiniteColimits_quasicoherentPullbackFunctor`; it is carried as
two instance binders in the section on quasi-coherent modules because the functor of derived
categories it induces cannot be written down without it, and a consumer discharges them from
`AlgebraicGeometry.Space.isFlat_of_isEtale`.

## References

* [Stacks Project, Tag 09TG](https://stacks.math.columbia.edu/tag/09TG)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
* [Stacks Project, Tag 08F1](https://stacks.math.columbia.edu/tag/08F1)
* [Stacks Project, Tag 08GZ](https://stacks.math.columbia.edu/tag/08GZ)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback
  isClosedUnderKernels_quasicoherentSheaves_schemeUniverse
  isClosedUnderCokernels_quasicoherentSheaves quasicoherentSheaves_abelian_of_closure

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {V W : AlgebraicSpaces B S hS} (j : V ⟶ W) (hj : IsEtale B S hS j.hom)

/-- **The derived adjunction `j^* ⊣ Rj_*` on all modules**, Stacks 09T5 for the étale
restriction adjunction of Stacks 03LU: the étale inverse image is exact, so the functor it
induces on derived categories is left adjoint to the total right derived functor of the
direct image. -/
def etaleDerivedModulePullbackPushforwardAdjunction :
    (etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory ⊣
      derivedModulePushforward B S hS j :=
  let := isGrothendieckAbelian_modules B S hS V.1 V.2
  (Stacks.DerivedModel.adjunctionOfExact (etaleModulePullback.{u, u} B S hS j hj)
      (DerivedCategory.Q (C := Modules.{u, u} B S hS V.1 V.2))
      (DerivedCategory.Q (C := Modules.{u, u} B S hS W.1 W.2))
      (etaleModulePullbackAdjunction B S hS j hj) (derivedModulePushforward B S hS j)
      (derivedModulePushforwardComplexUnit B S hS j)).ofNatIsoLeft
    (Stacks.DerivedQCoh.derivedFunctorOfExactIsoMapDerivedCategory
      (etaleModulePullback.{u, u} B S hS j hj))

/-- **The counit of `j^* ⊣ Rj_*` on a cochain complex of modules.**  The derivation unit of
`Rj_*` followed by the counit is the class of the degreewise counit of the étale restriction
adjunction of Stacks 03LU.  This is
`Stacks.DerivedModel.adjunctionOfExactMapDerivedCategory_counit_fac` for the adjunction
`AlgebraicGeometry.Space.etaleDerivedModulePullbackPushforwardAdjunction`; the Grothendieck
abelian instance is the one its construction uses. -/
theorem etaleDerivedModulePullbackPushforwardAdjunction_counit_fac
    (K : CochainComplex (Modules.{u, u} B S hS V.1 V.2) ℤ) :
    (etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory.map
          ((derivedModulePushforwardComplexUnit B S hS j).app K) ≫
        (etaleDerivedModulePullbackPushforwardAdjunction B S hS j hj).counit.app
          (DerivedCategory.Q.obj K) =
      (etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategoryFactors.hom.app
          (((modulePushforward B S hS j).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((Adjunction.mapHomologicalComplexAdjunction
          (etaleModulePullbackAdjunction B S hS j hj) (ComplexShape.up ℤ)).counit.app K) :=
  let := isGrothendieckAbelian_modules B S hS V.1 V.2
  Stacks.DerivedModel.adjunctionOfExactMapDerivedCategory_counit_fac
    (etaleModulePullback.{u, u} B S hS j hj) (etaleModulePullbackAdjunction B S hS j hj)
    (derivedModulePushforward B S hS j) (derivedModulePushforwardComplexUnit B S hS j) K

section Quasicoherent

variable [PreservesFiniteLimits (quasicoherentPullbackFunctor B S hS j)]
  [PreservesFiniteColimits (quasicoherentPullbackFunctor B S hS j)]

/-- **The derived adjunction `j^* ⊣ Φ` on quasi-coherent modules**, Stacks 09T5 for the
restriction to `QCoh` of the adjunction of Stacks 03LU: along a flat morphism the inverse image
of quasi-coherent modules is exact, so the functor it induces on derived categories is left
adjoint to the total right derived functor `Φ` of the direct image. -/
def quasicoherentDerivedPullbackPushforwardAdjunction
    (hjqc : IsQuasiCompact B S hS j.hom) (hjqs : IsQuasiSeparated B S hS j.hom) :
    (quasicoherentPullbackFunctor B S hS j).mapDerivedCategory ⊣
      derivedQuasicoherentPushforward B S hS j
        (pushforwardPreservesQuasicoherence_of_qcqs B S hS j hjqc hjqs) :=
  let : IsGrothendieckAbelian.{u} (QuasicoherentSheaves.{u, u} B S hS V.1 V.2) :=
    quasicoherentSheaves_isGrothendieckAbelian B S hS V.1 V.2
  (Stacks.DerivedModel.adjunctionOfExact (quasicoherentPullbackFunctor B S hS j)
      (DerivedCategory.Q (C := QuasicoherentSheaves.{u, u} B S hS V.1 V.2))
      (DerivedCategory.Q (C := QuasicoherentSheaves.{u, u} B S hS W.1 W.2))
      (quasicoherentPullbackFunctorAdjunction B S hS j hjqc hjqs)
      (derivedQuasicoherentPushforward B S hS j
        (pushforwardPreservesQuasicoherence_of_qcqs B S hS j hjqc hjqs))
      (derivedQuasicoherentPushforwardUnit B S hS j
        (pushforwardPreservesQuasicoherence_of_qcqs B S hS j hjqc hjqs))).ofNatIsoLeft
    (Stacks.DerivedQCoh.derivedFunctorOfExactIsoMapDerivedCategory
      (quasicoherentPullbackFunctor B S hS j))

/-- **The counit of `j^* ⊣ Φ` on a cochain complex of quasi-coherent modules.**  The derivation
unit of `Φ` followed by the counit is the class of the degreewise counit of the adjunction of
Stacks 03LU on the quasi-coherent modules.  This is
`Stacks.DerivedModel.adjunctionOfExactMapDerivedCategory_counit_fac` for the adjunction
`AlgebraicGeometry.Space.quasicoherentDerivedPullbackPushforwardAdjunction`. -/
theorem quasicoherentDerivedPullbackPushforwardAdjunction_counit_fac
    (hjqc : IsQuasiCompact B S hS j.hom) (hjqs : IsQuasiSeparated B S hS j.hom)
    (K : CochainComplex (QuasicoherentSheaves.{u, u} B S hS V.1 V.2) ℤ) :
    (quasicoherentPullbackFunctor B S hS j).mapDerivedCategory.map
          ((derivedQuasicoherentPushforwardUnit B S hS j
            (pushforwardPreservesQuasicoherence_of_qcqs B S hS j hjqc hjqs)).app K) ≫
        (quasicoherentDerivedPullbackPushforwardAdjunction B S hS j hjqc hjqs).counit.app
          (DerivedCategory.Q.obj K) =
      (quasicoherentPullbackFunctor B S hS j).mapDerivedCategoryFactors.hom.app
          (((quasicoherentPushforward B S hS j
            (pushforwardPreservesQuasicoherence_of_qcqs B S hS j hjqc hjqs)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((Adjunction.mapHomologicalComplexAdjunction
          (quasicoherentPullbackFunctorAdjunction B S hS j hjqc hjqs)
          (ComplexShape.up ℤ)).counit.app K) :=
  let : IsGrothendieckAbelian.{u} (QuasicoherentSheaves.{u, u} B S hS V.1 V.2) :=
    quasicoherentSheaves_isGrothendieckAbelian B S hS V.1 V.2
  Stacks.DerivedModel.adjunctionOfExactMapDerivedCategory_counit_fac
    (quasicoherentPullbackFunctor B S hS j)
    (quasicoherentPullbackFunctorAdjunction B S hS j hjqc hjqs)
    (derivedQuasicoherentPushforward B S hS j
      (pushforwardPreservesQuasicoherence_of_qcqs B S hS j hjqc hjqs))
    (derivedQuasicoherentPushforwardUnit B S hS j
      (pushforwardPreservesQuasicoherence_of_qcqs B S hS j hjqc hjqs)) K

/-- The underived square `ι_W ∘ j^* = j^*_{QCoh} ∘ ι_V` of inverse images along an étale
morphism: the étale inverse image of a quasi-coherent module, read as a module, is the inverse
image of the module. -/
def quasicoherentSheavesιCompEtaleModulePullbackIso :
    quasicoherentSheavesι B S hS W ⋙ etaleModulePullback.{u, u} B S hS j hj ≅
      quasicoherentPullbackFunctor B S hS j ⋙ quasicoherentSheavesι B S hS V :=
  (Functor.isoWhiskerLeft (quasicoherentSheavesι B S hS W)
      (modulePullbackIsoEtaleModulePullback B S hS j hj)).symm ≪≫
    (ObjectProperty.liftCompιIso _ _ _).symm

/-- **The square of Stacks 09TG at the level of inverse images**, as a 2-cell of the square of
adjunctions: the comparison functors of Stacks 08F1, followed by the inclusions into the
unbounded derived categories, commute with the derived inverse images along `j`.  Both
composites induce, on derived categories, the two sides of
`AlgebraicGeometry.Space.quasicoherentSheavesιCompEtaleModulePullbackIso`. -/
def derivedComparisonCompιEtalePullbackIso :
    (quasicoherentDerivedComparison B S hS W.1 W.2 ⋙
          (DerivedCategoryB.derivedCategoryB
            (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedSite B S hS W.1 W.2).O)))).ι) ⋙
        (etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory ≅
      (quasicoherentPullbackFunctor B S hS j).mapDerivedCategory ⋙
        (quasicoherentDerivedComparison B S hS V.1 V.2 ⋙
          (DerivedCategoryB.derivedCategoryB
            (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
              ((Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedSite B S hS V.1 V.2).O)))).ι) :=
  Functor.isoWhiskerRight (quasicoherentDerivedComparisonCompιIso B S hS W.1 W.2)
      (etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory ≪≫
    (Functor.mapDerivedCategoryComp (quasicoherentSheavesι B S hS W)
      (etaleModulePullback.{u, u} B S hS j hj)).symm ≪≫
    asIso (NatTrans.mapDerivedCategory
      (quasicoherentSheavesιCompEtaleModulePullbackIso B S hS j hj).hom) ≪≫
    Functor.mapDerivedCategoryComp (quasicoherentPullbackFunctor B S hS j)
      (quasicoherentSheavesι B S hS V) ≪≫
    Functor.isoWhiskerLeft (quasicoherentPullbackFunctor B S hS j).mapDerivedCategory
      (quasicoherentDerivedComparisonCompιIso B S hS V.1 V.2).symm

/-- **The square of Stacks 09TG at the level of inverse images, as a 2-cell.**  The 2-cell of the
square of adjunctions whose horizontal legs are the comparison functors of Stacks 08F1 followed
by the inclusions into the unbounded derived categories, and whose vertical legs are the derived
inverse images along `j`. -/
def derivedComparisonCompιEtalePullbackSquare :
    TwoSquare (quasicoherentDerivedComparison B S hS W.1 W.2 ⋙
        (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS W.1 W.2).O)))).ι)
      (quasicoherentPullbackFunctor B S hS j).mapDerivedCategory
      (etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory
      (quasicoherentDerivedComparison B S hS V.1 V.2 ⋙
        (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS V.1 V.2).O)))).ι) :=
  TwoSquare.mk _ _ _ _ (derivedComparisonCompιEtalePullbackIso B S hS j hj).hom

end Quasicoherent

section Composition

variable {U : AlgebraicSpaces B S hS} (g : U ⟶ V) (hg : IsEtale B S hS g.hom) (f : V ⟶ W)

/-- The derivation unit of `Rk_*` is invertible on a K-injective complex of modules. -/
private theorem isIso_derivedModulePushforwardComplexUnit_app {X Y : AlgebraicSpaces B S hS}
    (k : X ⟶ Y) (I : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (hI : I.IsKInjective) :
    IsIso ((derivedModulePushforwardComplexUnit B S hS k).app I) :=
  let := isGrothendieckAbelian_modules B S hS X.1 X.2
  Stacks.Injectives.KInjectiveResolution.isIso_app_of_isKInjective DerivedCategory.Q
    (derivedModulePushforward B S hS k) (derivedModulePushforwardComplexUnit B S hS k)
    (Stacks.Injectives.KInjectiveResolution.invertsQuasiIso_mapHomologicalComplex_comp_Q
      (modulePushforward B S hS k)) I hI

/-- The derivation unit of the composite `Rg_* ⋙ Rf_*` relative to the direct image along
`g ≫ f`: the degreewise comparison `(g ≫ f)_* = f_* ∘ g_*` followed by the derivation units of
`Rf_*` and of `Rg_*`. -/
def derivedModulePushforwardCompUnit :
    (modulePushforward B S hS (g ≫ f)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q (C := Modules.{u, u} B S hS W.1 W.2) ⟶
      DerivedCategory.Q (C := Modules.{u, u} B S hS U.1 U.2) ⋙
        (derivedModulePushforward B S hS g ⋙ derivedModulePushforward B S hS f) :=
  Functor.whiskerRight
      (Functor.mapHomologicalComplexCompIso (modulePushforwardCompIso B S hS g f)
        (ComplexShape.up ℤ)).inv DerivedCategory.Q ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft
      ((modulePushforward B S hS g).mapHomologicalComplex (ComplexShape.up ℤ))
      (derivedModulePushforwardComplexUnit B S hS f) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (derivedModulePushforwardComplexUnit B S hS g)
      (derivedModulePushforward B S hS f) ≫
    (Functor.associator _ _ _).hom

include hg in
open Stacks.Injectives.KInjectiveResolution in
/-- **K-injective complexes compute the composite `Rg_* ⋙ Rf_*`.**  For `g` étale the direct
image `g_*` carries a K-injective complex to a K-injective complex, its left adjoint being the
exact étale inverse image (Stacks 08BJ), so both derivation units entering
`AlgebraicGeometry.Space.derivedModulePushforwardCompUnit` are invertible there. -/
theorem isIso_derivedModulePushforwardCompUnit_app_of_isKInjective
    (I : CochainComplex (Modules.{u, u} B S hS U.1 U.2) ℤ) (hI : I.IsKInjective) :
    IsIso ((derivedModulePushforwardCompUnit B S hS g f).app I) := by
  let := isGrothendieckAbelian_modules B S hS U.1 U.2
  let := isGrothendieckAbelian_modules B S hS V.1 V.2
  let := hI
  have hg' : CochainComplex.IsKInjective
      (((modulePushforward B S hS g).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    CochainComplex.isKInjective_mapHomologicalComplex_of_exact (modulePushforward B S hS g)
      (etaleModulePullback.{u, u} B S hS g hg) (etaleModulePullbackAdjunction B S hS g hg) I
  have h₁ := isIso_derivedModulePushforwardComplexUnit_app B S hS g I hI
  have h₂ := isIso_derivedModulePushforwardComplexUnit_app B S hS f _ hg'
  dsimp only [derivedModulePushforwardCompUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app]
  infer_instance

include hg in
open Stacks.Injectives.KInjectiveResolution in
/-- The composite `Rg_* ⋙ Rf_*` is a total right derived functor of the direct image along
`g ≫ f`. -/
theorem isRightDerivedFunctor_derivedModulePushforwardComp :
    (derivedModulePushforward B S hS g ⋙
      derivedModulePushforward B S hS f).IsRightDerivedFunctor
      (derivedModulePushforwardCompUnit B S hS g f)
      (HomologicalComplex.quasiIso (Modules.{u, u} B S hS U.1 U.2) (ComplexShape.up ℤ)) := by
  let := isGrothendieckAbelian_modules B S hS U.1 U.2
  refine (isRightDerivedFunctor_iff_isIso_app_of_isKInjective DerivedCategory.Q _
    (derivedModulePushforwardCompUnit B S hS g f)
    (invertsQuasiIso_mapHomologicalComplex_comp_Q
      (modulePushforward B S hS (g ≫ f)))).2 fun K hK => ?_
  exact isIso_derivedModulePushforwardCompUnit_app_of_isKInjective B S hS g hg f K hK

end Composition

section RestrictPush

open CategoryTheory.PushforwardMayerVietoris

/-- **A total right derived functor of `k_*((-)|_k)` is `Rk_*` of the restriction.**  For an
étale `k : Y ⟶ W` of algebraic spaces both are computed on a K-injective representative `I` of
the object by `k_*(I|_Y)`, the restriction `I|_Y` being K-injective again (Stacks 070K, 079P).

This is the splitting of a vertex of the Mayer–Vietoris triangle of Stacks 08GW into a
restriction followed by a derived direct image, for each of the three vertices at once: the
restriction is `CategoryTheory.Functor.mapDerivedCategory` of the exact étale inverse image and
the direct image is `AlgebraicGeometry.Space.derivedModulePushforward`. -/
theorem nonempty_rightDerivedRestrictPushObjIso {Y Z : AlgebraicSpaces B S hS} (k : Y ⟶ Z)
    (hk : IsEtale B S hS k.hom)
    (R : DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2))
    (η : (etaleModulePullback.{u, u} B S hS k hk ⋙
          modulePushforward B S hS k).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ R)
    (hR : R.IsRightDerivedFunctor η
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Z.1 Z.2) (ComplexShape.up ℤ)))
    (L : DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)) :
    Nonempty (R.obj L ≅ (derivedModulePushforward B S hS k).obj
      ((etaleModulePullback.{u, u} B S hS k hk).mapDerivedCategory.obj L)) := by
  have hres := exists_quasiIso_isKInjective_modules B S hS Z.1 Z.2
  obtain ⟨I, hI, ⟨e⟩⟩ := exists_isKInjective_representative_of_universe hres L
  have hI' : CochainComplex.IsKInjective
      (((etaleModulePullback.{u, u} B S hS k hk).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) :=
    isKInjective_etaleModulePullback_of_isEtale B S hS k hk I hI
  have : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS Y.1 Y.2) :=
    isGrothendieckAbelian_modules B S hS _ _
  have hunit := isIso_derivedModulePushforwardComplexUnit_app B S hS k _ hI'
  exact ⟨R.mapIso e.symm ≪≫
    (rightDerivedObjIsoOfKInjective hres
      (etaleModulePullback.{u, u} B S hS k hk ⋙ modulePushforward B S hS k) inferInstance R η hR
      I hI).symm ≪≫
    DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (etaleModulePullback.{u, u} B S hS k hk ⋙ modulePushforward B S hS k))
      (ComplexShape.up ℤ)).app I).symm ≪≫
    @asIso _ _ _ _ ((derivedModulePushforwardComplexUnit B S hS k).app _) hunit ≪≫
    (derivedModulePushforward B S hS k).mapIso
      (((etaleModulePullback.{u, u} B S hS k hk).mapDerivedCategoryFactors.app I).symm ≪≫
        (etaleModulePullback.{u, u} B S hS k hk).mapDerivedCategory.mapIso e)⟩

end RestrictPush

end AlgebraicGeometry.Space

end

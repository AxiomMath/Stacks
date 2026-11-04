module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareMapResolution
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FrobeniusFactorization07N5

/-!
# The derived comparison along a change of divided power base, on acyclic resolutions

The comparison of derived global sections on the big crystalline sites along a change of divided
power base `(f, g)` from `S` to `S'`,

`derivedChangeBaseBigGlobalSectionsMap f g h N : RΓ(CRIS(Y/S'), N) ⟶ res_* RΓ(CRIS(X/S), u^* N)`,

is an instance of the derived comparison of a square,
`CategoryTheory.Functor.derivedSquareMap`
(`...SmallSite.derivedChangeBaseBigGlobalSectionsMap_eq_derivedSquareMap`).  By
`CategoryTheory.Functor.derivedSquareMap_eq_of_resolutions` it is computed on acyclic resolutions:
given a resolution `N[0] ⟶ J` by `Γ(CRIS(Y/S'), -)`-acyclic sheaves, a resolution
`(u^* N)[0] ⟶ J'` by `Γ(CRIS(X/S), -)`-acyclic sheaves and a compatible map `u^* J ⟶ J'`, the
comparison is the class of the map of complexes `Γ(J) ⟶ res_* Γ(J')` restricting sections
degreewise; and it is an isomorphism when that map of complexes is a quasi-isomorphism.

## Main results

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `derivedChangeBaseBigGlobalSectionsMap_eq_of_resolutions`: the comparison on two compatible
  acyclic resolutions.
* `isIso_derivedChangeBaseBigGlobalSectionsMap_of_resolutions`: it is an isomorphism when the
  underived map of complexes is a quasi-isomorphism.
* `isIso_derivedChangeBaseBigGlobalSectionsMap_of_resolution`: the same for one resolution `J`
  of `N` whose pullback `u^* J` is a complex of acyclic sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u wB wA

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {S S' : GlobalCrystallineSituation.{u}}
  [HasDerivedCategory.{wB} (BigModuleSheaf S)] [HasDerivedCategory.{wB} (BigModuleSheaf S')]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤))]

/-- **The comparison along a change of divided power base on two compatible acyclic
resolutions.**  Let `ι : N[0] ⟶ J` be a quasi-isomorphism onto a bounded below complex of
`Γ(CRIS(Y/S'), -)`-acyclic sheaves of modules, `ι' : (u^* N)[0] ⟶ J'` one onto a bounded below
complex of `Γ(CRIS(X/S), -)`-acyclic sheaves of modules, and `τ : u^* J ⟶ J'` a map of complexes
with `u^*(ι) ≫ τ = ι'`.  Under `RΓ(CRIS(Y/S'), N) ≅ Γ(J)` and `RΓ(CRIS(X/S), u^* N) ≅ Γ(J')`, the
comparison is the class of the map of complexes `Γ(J) ⟶ res_* Γ(J')`: the restriction of
sections `changeBaseBigBaseGlobalSectionsTrans` degreewise, followed by `Γ(τ)`. -/
theorem derivedChangeBaseBigGlobalSectionsMap_eq_of_resolutions (f : S.S ⟶ S'.S)
    (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
    {N : BigModuleSheaf S'} {J : HomotopyCategory.Plus (BigModuleSheaf S')}
    (ι : (HomotopyCategory.Plus.singleFunctor (BigModuleSheaf S') 0).obj N ⟶ J)
    (hι : IsIso (DerivedCategory.Plus.Qh.map ι))
    (hJ : ∀ n : ℤ, (bigBaseModuleGlobalSections S').rightAcyclic (J.obj.as.X n))
    {J' : HomotopyCategory.Plus (BigModuleSheaf S)}
    (ι' : (HomotopyCategory.Plus.singleFunctor (BigModuleSheaf S) 0).obj
      ((changeBaseBigModulePullback S S' f g h).obj N) ⟶ J')
    (hι' : IsIso (DerivedCategory.Plus.Qh.map ι'))
    (hJ' : ∀ n : ℤ, (bigBaseModuleGlobalSections S).rightAcyclic (J'.obj.as.X n))
    (τ : (changeBaseBigModulePullback S S' f g h).mapHomotopyCategoryPlus.obj J ⟶ J')
    (hτ : (changeBaseBigModulePullback S S' f g h).mapHomotopyCategoryPlus.map ι ≫ τ =
      ((changeBaseBigModulePullback S S' f g h).mapHomotopyCategoryPlusObjSingleIso 0 N).hom ≫
        ι') :
    derivedChangeBaseBigGlobalSectionsMap f g h N =
      (Functor.rightDerivedFunctorPlusObjSingleIsoOfResolution
          (bigBaseModuleGlobalSections S') ι hι hJ).hom ≫
        DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatTrans
            (changeBaseBigBaseGlobalSectionsTrans f g h)).app J ≫
          (ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f)).mapHomotopyCategoryPlus.map
            ((bigBaseModuleGlobalSections S).mapHomotopyCategoryPlus.map τ)) ≫
        (ModuleCat.restrictScalars.{u + 1}
            (baseChangeRingHom f)).mapDerivedCategoryPlusFactorsh.inv.app
          ((bigBaseModuleGlobalSections S).mapHomotopyCategoryPlus.obj J') ≫
        (ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f)).mapDerivedCategoryPlus.map
          (Functor.rightDerivedFunctorPlusObjSingleIsoOfResolution
            (bigBaseModuleGlobalSections S) ι' hι' hJ').inv := by
  rw [derivedChangeBaseBigGlobalSectionsMap_eq_derivedSquareMap]
  exact Functor.derivedSquareMap_eq_of_resolutions _ ι hι hJ ι' hι' hJ' τ hτ

/-- **The comparison along a change of divided power base is an isomorphism when it is one on
acyclic resolutions**: in the situation of
`derivedChangeBaseBigGlobalSectionsMap_eq_of_resolutions`, with `ι` and `ι'` quasi-isomorphisms,
if the map of complexes `Γ(J) ⟶ res_* Γ(J')` (restriction of sections degreewise followed by
`Γ(τ)`) is a quasi-isomorphism, then `derivedChangeBaseBigGlobalSectionsMap f g h N` is an
isomorphism. -/
theorem isIso_derivedChangeBaseBigGlobalSectionsMap_of_resolutions (f : S.S ⟶ S'.S)
    (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
    {N : BigModuleSheaf S'} {J : HomotopyCategory.Plus (BigModuleSheaf S')}
    (ι : (HomotopyCategory.Plus.singleFunctor (BigModuleSheaf S') 0).obj N ⟶ J)
    (hι : HomotopyCategory.Plus.quasiIso _ ι)
    (hJ : ∀ n : ℤ, (bigBaseModuleGlobalSections S').rightAcyclic (J.obj.as.X n))
    {J' : HomotopyCategory.Plus (BigModuleSheaf S)}
    (ι' : (HomotopyCategory.Plus.singleFunctor (BigModuleSheaf S) 0).obj
      ((changeBaseBigModulePullback S S' f g h).obj N) ⟶ J')
    (hι' : HomotopyCategory.Plus.quasiIso _ ι')
    (hJ' : ∀ n : ℤ, (bigBaseModuleGlobalSections S).rightAcyclic (J'.obj.as.X n))
    (τ : (changeBaseBigModulePullback S S' f g h).mapHomotopyCategoryPlus.obj J ⟶ J')
    (hτ : (changeBaseBigModulePullback S S' f g h).mapHomotopyCategoryPlus.map ι ≫ τ =
      ((changeBaseBigModulePullback S S' f g h).mapHomotopyCategoryPlusObjSingleIso 0 N).hom ≫
        ι')
    (hα : HomotopyCategory.Plus.quasiIso _ ((Functor.mapHomotopyCategoryPlusNatTrans
        (changeBaseBigBaseGlobalSectionsTrans f g h)).app J ≫
      (ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f)).mapHomotopyCategoryPlus.map
        ((bigBaseModuleGlobalSections S).mapHomotopyCategoryPlus.map τ))) :
    IsIso (derivedChangeBaseBigGlobalSectionsMap f g h N) := by
  rw [derivedChangeBaseBigGlobalSectionsMap_eq_derivedSquareMap]
  exact Functor.isIso_derivedSquareMap_of_resolutions _ ι hι hJ ι' hι' hJ' τ hτ hα

/-- **The comparison along a change of divided power base is an isomorphism when it is one on an
acyclic resolution**: for a quasi-isomorphism `ι : N[0] ⟶ J` onto a bounded below complex of
`Γ(CRIS(Y/S'), -)`-acyclic sheaves whose pullback `u^* J` is a complex of
`Γ(CRIS(X/S), -)`-acyclic sheaves, if the restriction of sections `Γ(J) ⟶ res_* Γ(u^* J)`
degreewise is a quasi-isomorphism, then `derivedChangeBaseBigGlobalSectionsMap f g h N` is an
isomorphism. -/
theorem isIso_derivedChangeBaseBigGlobalSectionsMap_of_resolution (f : S.S ⟶ S'.S)
    (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
    {N : BigModuleSheaf S'} {J : HomotopyCategory.Plus (BigModuleSheaf S')}
    (ι : (HomotopyCategory.Plus.singleFunctor (BigModuleSheaf S') 0).obj N ⟶ J)
    (hι : HomotopyCategory.Plus.quasiIso _ ι)
    (hJ : ∀ n : ℤ, (bigBaseModuleGlobalSections S').rightAcyclic (J.obj.as.X n))
    (hPJ : ∀ n : ℤ, (bigBaseModuleGlobalSections S).rightAcyclic
      ((changeBaseBigModulePullback S S' f g h).obj (J.obj.as.X n)))
    (hα : HomotopyCategory.Plus.quasiIso _ ((Functor.mapHomotopyCategoryPlusNatTrans
        (changeBaseBigBaseGlobalSectionsTrans f g h)).app J)) :
    IsIso (derivedChangeBaseBigGlobalSectionsMap f g h N) := by
  rw [derivedChangeBaseBigGlobalSectionsMap_eq_derivedSquareMap]
  exact Functor.isIso_derivedSquareMap_of_resolution _ ι hι hJ hPJ hα

end Crystalline.GlobalCrystallineSituation.SmallSite

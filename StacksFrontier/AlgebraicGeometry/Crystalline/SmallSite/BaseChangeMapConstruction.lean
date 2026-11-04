module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.BaseChangeMap
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FrobeniusSemilinearAction
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleUniverseComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorSingleObject
public import StacksFrontier.Homology.DerivedIndexing.Composite

/-!
# The base change map (07MT) of [Stacks, Tag 07MS] for `g` an open immersion

Let `(S, I, γ) ⟶ (S', I', γ')` be a morphism of divided power schemes over `ℤ_{(p)}`, let
`g : X ⟶ X'` be a compatible morphism of the schemes over the closed fibres, and write
`A = Γ(S, 𝒪_S)` and `A' = Γ(S', 𝒪_{S'})`.  [Stacks, Tag 07MS] constructs from a sheaf `F'` of
`𝒪_{X'/S'}`-modules, with pullback `F`, a canonical map

`RΓ(Cris(X'/S'), F') ⊗^L_{A'} A ⟶ RΓ(Cris(X/S), F)`

of `D(A)`, the map labelled (07MT) and the subject of [Stacks, Tag 07MU].  This file builds it,
**for `g` an open immersion**, as a term of
`Crystalline.GlobalCrystallineSituation.SmallSite.BaseChangeMap07MT`.

## Main definitions

* `smallChangeBaseModulePullbackLow` — the pullback of [Stacks, Tag 07MS] at the module universe
  of the chapter's predicates.
* `derivedBaseChangeGlobalSectionsTrans` — the natural transformation
  `RΓ_{S'} ⟶ RP ⋙ RΓ_S ⋙ res_*` of functors `D⁺(Mod_{𝒪_{X'/S'}}) ⥤ D⁺(Mod_{A'})`, for `P` the
  pullback and `res_*` restriction of scalars along `A' ⟶ A`.
* `derivedBaseChangeGlobalSectionsMap` — **the comparison
  `RΓ(Cris(X'/S'), F') ⟶ res_* RΓ(Cris(X/S), F)` in `D⁺(A')`**, at a sheaf `F'`.
* `baseChangeMap07MT` — **the base change map (07MT)**, a term of
  `...SmallSite.BaseChangeMap07MT`.
* `baseChangeMap07MTOfPullback` — the same map read at
  `...SmallSite.BaseChangeMap07MTOfPullback`.

## Main results

* `moduleULift_comp_smallChangeBaseModulePullback` — raising the module universe commutes with
  the pullback, definitionally.

## References

* [Stacks Project, Tag 07MS](https://stacks.math.columbia.edu/tag/07MS)
* [Stacks Project, Tag 07MU](https://stacks.math.columbia.edu/tag/07MU)
* [Stacks Project, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u wS wS' wA wA'

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S S' : GlobalCrystallineSituation.{u}} {f : S.S ⟶ S'.S} {g : S.X ⟶ S'.X}
  {h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber}

/-! ### The pullback at the module universe of the chapter's predicates -/

/-- **The pullback `F` of [Stacks, Tag 07MS] at the module universe `u`**, the universe at which
the chapter's crystal and quasi-coherence predicates — and the coefficients of
`Crystalline.GlobalCrystallineSituation.SmallSite.BaseChangeMap07MT` — are stated. -/
def smallChangeBaseModulePullbackLow (S S' : GlobalCrystallineSituation.{u}) (f : S.S ⟶ S'.S)
    (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
    [IsOpenImmersion g] :
    SheafOfModules.{u} (structureSheaf S') ⥤ SheafOfModules.{u} (structureSheaf S) :=
  SheafOfModules.pushforward.{u} (smallChangeBaseStructureHom S S' f g h)

/-- **Raising the module universe commutes with the pullback, on the nose.**  Both composites
send `F'` to the sheaf whose sections over an object `(U, T, δ)` of `Cris(X/S)` are
`ULift (F'(U, T ⟶ S ⟶ S', δ))`, and the two sheaves of modules are definitionally equal, not
merely isomorphic. -/
theorem moduleULift_comp_smallChangeBaseModulePullback [IsOpenImmersion g] :
    smallChangeBaseModulePullbackLow S S' f g h ⋙ moduleULift S =
      moduleULift S' ⋙ smallChangeBaseModulePullback S S' f g h :=
  rfl

/-! ### The comparison on derived global sections -/

section Derived

variable [IsOpenImmersion g] [HasDerivedCategory.{wS} (ModuleSheaf S)]
  [HasDerivedCategory.{wS'} (ModuleSheaf S')]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
  [HasDerivedCategory.{wA'} (ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤))]

/-- **The comparison of derived global sections along the pullback**, as a natural transformation

`RΓ_{S'} ⟶ RP ⋙ RΓ_S ⋙ res_*`

of functors `D⁺(Mod_{𝒪_{X'/S'}}) ⥤ D⁺(Mod_{A'})`, where `P` is the pullback, `Γ` the
`A`-module-valued global sections and `res_*` restriction of scalars along
`Crystalline.GlobalCrystallineSituation.SmallSite.baseChangeRingHom`. -/
def derivedBaseChangeGlobalSectionsTrans (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
    [IsOpenImmersion g] :
    (baseModuleGlobalSections S').rightDerivedFunctorPlus ⟶
      (smallChangeBaseModulePullback S S' f g h).rightDerivedFunctorPlus ⋙
        (baseModuleGlobalSections S).rightDerivedFunctorPlus ⋙
          (ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f)).mapDerivedCategoryPlus :=
  Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans
      (baseChangeGlobalSectionsTrans S S' f g h) ≫
    Stacks.DerivedIndexing.rightDerivedPlusCompTrans (smallChangeBaseModulePullback S S' f g h)
      (baseModuleGlobalSections S ⋙ ModuleCat.restrictScalars (baseChangeRingHom f)) ≫
    Functor.whiskerLeft (smallChangeBaseModulePullback S S' f g h).rightDerivedFunctorPlus
      ((Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic (baseModuleGlobalSections S)
            (ModuleCat.restrictScalars (baseChangeRingHom f))
            (fun _ _ => Functor.rightAcyclic_of_exact _ _)).hom ≫
        Functor.whiskerLeft (baseModuleGlobalSections S).rightDerivedFunctorPlus
          (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
            (ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f))).hom)

/-- **The comparison on derived global sections**,

`RΓ(Cris(X'/S'), F') ⟶ res_* RΓ(Cris(X/S), F)`   in `D⁺(Mod_{A'})`,

for `F` the pullback of `F'`. -/
def derivedBaseChangeGlobalSectionsMap (F' : SheafOfModules.{u} (structureSheaf S')) :
    moduleULiftDerivedGlobalSections S' F' ⟶
      (ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f)).mapDerivedCategoryPlus.obj
        (moduleULiftDerivedGlobalSections S
          ((smallChangeBaseModulePullbackLow S S' f g h).obj F')) :=
  (derivedBaseChangeGlobalSectionsTrans f g h).app
      ((DerivedCategory.Plus.singleFunctor (ModuleSheaf S') 0).obj ((moduleULift S').obj F')) ≫
    ((baseModuleGlobalSections S).rightDerivedFunctorPlus ⋙
        (ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f)).mapDerivedCategoryPlus).map
      (Functor.rightDerivedFunctorPlusObjSingleIso (smallChangeBaseModulePullback S S' f g h)
        ((moduleULift S').obj F')).hom

/-! ### The base change map (07MT) -/

/-- **The base change map (07MT) of [Stacks, Tag 07MS] for `g : X ⟶ X'` an open immersion**

`RΓ(Cris(X'/S'), F') ⊗^L_{A'} A ⟶ RΓ(Cris(X/S), F)`

of `D(A)`, with `F` the pullback of `F'` along change of divided power base. -/
def baseChangeMap07MT (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
    [IsOpenImmersion g] (F' : SheafOfModules.{u} (structureSheaf S')) :
    BaseChangeMap07MT f F' ((smallChangeBaseModulePullbackLow S S' f g h).obj F') :=
  ((derivedBaseChangeTensorAdjunction f).homEquiv _ _).symm
    (DerivedCategory.Plus.ι.map (derivedBaseChangeGlobalSectionsMap F'))

/-- **The base change map at the type that pins `F` to the pullback**,
`Crystalline.GlobalCrystallineSituation.SmallSite.BaseChangeMap07MTOfPullback`. -/
def baseChangeMap07MTOfPullback (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
    [IsOpenImmersion g] (F' : SheafOfModules.{u} (structureSheaf S')) :
    BaseChangeMap07MTOfPullback f g h F' :=
  baseChangeMap07MT f g h F'

end Derived

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end

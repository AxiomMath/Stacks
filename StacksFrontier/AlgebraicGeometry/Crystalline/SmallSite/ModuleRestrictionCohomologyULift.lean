module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleRestrictionAcyclicity
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleUniverseComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SheafCrystal

/-!
# `RΓ(CRIS(X/S), N) ≅ RΓ(Cris(X/S), i^{-1}N)` at the module universe `u`

Fix a global crystalline situation `(p, (S, I, γ), X)` at level `u`, and let
`i : Cris(X/S) ⥤ CRIS(X/S)` be the inclusion of the small crystalline site into the big one. For a
sheaf of `𝒪_{X/S}`-modules `N` on `CRIS(X/S)` with sections in `Type u`, the derived global
sections over `CRIS(X/S)` of the universe lift of `N` are the derived global sections over
`Cris(X/S)` of the universe lift of `i^{-1}N`.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `bigModuleULift` — the universe-lifting functor for sheaves of `𝒪_{X/S}`-modules on
  `CRIS(X/S)`, from the module universe `u` to the module universe `u + 1`.

## Main results

* `moduleULift_obj_restrictSheafOfModules` — restricting to `Cris(X/S)` and lifting the module
  universe commute, on the nose.
* `derivedRestrictModuleGlobalSectionsULiftIso` — `RΓ(CRIS(X/S), N) ≅ RΓ(Cris(X/S), i^{-1}N)` for
  a sheaf of `𝒪_{X/S}`-modules `N` on `CRIS(X/S)` at the module universe `u`.

## Implementation notes

The derived global sections are formed at the module universe `u + 1`, and `bigModuleULift` and
`moduleULift` lift a module with sections in `Type u` there.

## References

* [Stacks Project, Tag 07N5](https://stacks.math.columbia.edu/tag/07N5)
* [Stacks Project, Tag 07IM](https://stacks.math.columbia.edu/tag/07IM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})

/-- **The universe-lifting functor for sheaves of `𝒪_{X/S}`-modules on the big crystalline
site**, from sheaves with sections in `Type u` to sheaves with sections in `Type (u + 1)`. The
site, the structure sheaf `𝒪_{X/S}` and the base ring `A = Γ(S, 𝒪_S)` are unchanged, and the
sections of the value over an object of `CRIS(X/S)` are the universe lift of the sections there. -/
def bigModuleULift : SheafOfModules.{u} (crystallineStructureSheaf S) ⥤ BigModuleSheaf S :=
  SheafOfModules.uliftForPresentationFunctor.{u + 1, u, u, u, u + 1}

/-- The sections of the lift of `N` over an object of `CRIS(X/S)` are the universe lift of the
sections of `N` there. -/
theorem bigModuleULift_obj_val_obj_carrier (N : SheafOfModules.{u} (crystallineStructureSheaf S))
    (A : (Thickening S)ᵒᵖ) :
    (((bigModuleULift S).obj N).val.obj A : Type (u + 1)) = ULift.{u + 1} (N.val.obj A) := rfl

/-- **Restricting to `Cris(X/S)` and lifting the module universe commute**, on the nose. -/
theorem moduleULift_obj_restrictSheafOfModules
    (N : SheafOfModules.{u} (crystallineStructureSheaf S)) :
    (moduleULift S).obj (restrictSheafOfModules N) =
      (moduleRestrictι S).obj ((bigModuleULift S).obj N) :=
  rfl

section Derived

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

universe v₁ v₂ v₃

variable [HasDerivedCategory.{v₁} (ModuleSheaf S)] [HasDerivedCategory.{v₂} (BigModuleSheaf S)]
  [HasDerivedCategory.{v₃} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]

/-- **`RΓ(CRIS(X/S), N) ≅ RΓ(Cris(X/S), i^{-1}N)` for a sheaf of `𝒪_{X/S}`-modules `N` on the big
crystalline site at the module universe `u`**: the derived global sections over `CRIS(X/S)` of the
universe lift of `N` are `moduleULiftDerivedGlobalSections` of the restriction of `N` to
`Cris(X/S)`. -/
def derivedRestrictModuleGlobalSectionsULiftIso
    (N : SheafOfModules.{u} (crystallineStructureSheaf S)) :
    (derivedBigModuleGlobalSections S).obj ((bigModuleULift S).obj N) ≅
      moduleULiftDerivedGlobalSections S (restrictSheafOfModules N) :=
  derivedRestrictModuleGlobalSectionsObjIso S ((bigModuleULift S).obj N)

end Derived

end Crystalline.GlobalCrystallineSituation.SmallSite

end

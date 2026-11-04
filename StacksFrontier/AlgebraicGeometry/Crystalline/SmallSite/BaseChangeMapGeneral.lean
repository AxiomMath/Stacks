module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FrobeniusDerivedGlobalSections
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LowerShriekModules
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleRestrictionAcyclicity

/-!
# The base change map of [Stacks, Tag 07MS] for an arbitrary morphism

Let `(S, I, γ) ⟶ (S', I', γ')` be a morphism of divided power schemes over `ℤ_{(p)}`, with
`S = Spec(A)` and `S' = Spec(A')`, and let `g : X ⟶ X'` be a morphism of schemes over
`S₀ ⟶ S'₀`, with `p` locally nilpotent on `X` and `X'`: the situation of [Stacks, Tag 07MJ],
with no further hypothesis on `g`.  For a sheaf `F'` of `𝒪_{X'/S'}`-modules on `Cris(X'/S')` with
pullback `F = f_cris^*F'`, [Stacks, Tag 07MS] constructs the base change map (07MT)

`RΓ(Cris(X'/S'), F') ⊗^L_{A'} A ⟶ RΓ(Cris(X/S), F)`   in `D(A)`.

This file builds a map of that shape for an arbitrary `g` directly on the big crystalline sites,
through `i_!` and change of base.

## The pullback

The pullback `F = f_cris^*F'` is `...SmallSite.crisModuleInverseImage`, the module pullback along
`f_cris = π_{X'} ∘ f_CRIS ∘ i_X` of [Stacks, Tag 07IK]: the module-level lower shriek
`i_{X', !}` of [Stacks, Tag 07IJ] followed by restriction along
`Cris(X/S) ⥤ CRIS(X/S) ⥤ CRIS(X'/S')`.

## Main definitions

* `crisDerivedBaseChangeGlobalSectionsMap` — the comparison
  `RΓ(Cris(X'/S'), F') ⟶ res_* RΓ(Cris(X/S), f_cris^*F')` in `D⁺(Mod_{A'})`.
* `crisBaseChangeMap` — **the base change map (07MT)**
  `RΓ(Cris(X'/S'), F') ⊗^L_{A'} A ⟶ RΓ(Cris(X/S), f_cris^*F')` in `D(A)`.

## Main results

* `homEquiv_crisBaseChangeMap` — the base change map is the transpose of
  `crisDerivedBaseChangeGlobalSectionsMap` across `- ⊗^L_{A'} A ⊣ res_*`.

## References

* [Stacks Project, Tag 07MS](https://stacks.math.columbia.edu/tag/07MS)
* [Stacks Project, Tag 07MJ](https://stacks.math.columbia.edu/tag/07MJ)
* [Stacks Project, Tag 07IK](https://stacks.math.columbia.edu/tag/07IK)
* [Stacks Project, Tag 07IJ](https://stacks.math.columbia.edu/tag/07IJ)
* [Stacks Project, Tag 07IM](https://stacks.math.columbia.edu/tag/07IM)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u wS wB wA

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {S S' : GlobalCrystallineSituation.{u}}
  [HasDerivedCategory.{wS} (ModuleSheaf S)] [HasDerivedCategory.{wS} (ModuleSheaf S')]
  [HasDerivedCategory.{wB} (BigModuleSheaf S)] [HasDerivedCategory.{wB} (BigModuleSheaf S')]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S'.S.scheme, ⊤))]

/-- **The comparison on derived global sections along `f_cris`, for an arbitrary `g`**:

`RΓ(Cris(X'/S'), F') ⟶ res_* RΓ(Cris(X/S), f_cris^*F')`   in `D⁺(Mod_{A'})`,

with `f_cris^*` the module pullback `...SmallSite.crisModuleInverseImage` and `res_*` restriction
of scalars along `...SmallSite.baseChangeRingHom f : A' ⟶ A`. -/
def crisDerivedBaseChangeGlobalSectionsMap (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
    (F' : ModuleSheaf S') :
    (derivedModuleGlobalSections S').obj F' ⟶
      (ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f)).mapDerivedCategoryPlus.obj
        ((derivedModuleGlobalSections S).obj ((crisModuleInverseImage f g h).obj F')) :=
  (derivedModuleGlobalSections S').map
      ((moduleLowerShriekUnitIso S').hom.app F' ≫
        (crisRestrictModulesIsoModuleRestrictι S').hom.app ((moduleLowerShriek S').obj F')) ≫
    (derivedRestrictModuleGlobalSectionsObjIso S' ((moduleLowerShriek S').obj F')).inv ≫
      derivedChangeBaseBigGlobalSectionsMap f g h ((moduleLowerShriek S').obj F') ≫
        (ModuleCat.restrictScalars.{u + 1} (baseChangeRingHom f)).mapDerivedCategoryPlus.map
          ((derivedRestrictModuleGlobalSectionsObjIso S
              ((changeBaseBigModulePullback S S' f g h).obj
                ((moduleLowerShriek S').obj F'))).hom ≫
            (derivedModuleGlobalSections S).map
              ((crisRestrictModulesIsoModuleRestrictι S).inv.app
                ((changeBaseBigModulePullback S S' f g h).obj
                  ((moduleLowerShriek S').obj F'))))

/-- **A base change map of the shape (07MT) of [Stacks, Tag 07MS], built on the big sites**

`RΓ(Cris(X'/S'), F') ⊗^L_{A'} A ⟶ RΓ(Cris(X/S), F)`   in `D(A)`,

for an arbitrary morphism `g : X ⟶ X'` over a morphism of divided power bases
`f : (S, I, γ) ⟶ (S', I', γ')` with `A = Γ(S, 𝒪_S)` and `A' = Γ(S', 𝒪_{S'})` (the situation of
[Stacks, Tag 07MJ] with `S` and `S'` affine), for every sheaf `F'` of `𝒪_{X'/S'}`-modules on
`Cris(X'/S')`, where `F = f_cris^*F'` is the pullback `...SmallSite.crisModuleInverseImage`. -/
def crisBaseChangeMap (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
    (F' : ModuleSheaf S') :
    (derivedBaseChangeTensor f).obj
        (DerivedCategory.Plus.ι.obj ((derivedModuleGlobalSections S').obj F')) ⟶
      DerivedCategory.Plus.ι.obj
        ((derivedModuleGlobalSections S).obj ((crisModuleInverseImage f g h).obj F')) :=
  ((derivedBaseChangeTensorAdjunction f).homEquiv _ _).symm
    (DerivedCategory.Plus.ι.map (crisDerivedBaseChangeGlobalSectionsMap f g h F'))

/-- **The base change map is the transpose of the semilinear comparison.**  Across the
adjunction `- ⊗^L_{A'} A ⊣ res_*` of [Stacks, Tag 0GMT], `crisBaseChangeMap` corresponds to the
comparison `crisDerivedBaseChangeGlobalSectionsMap` on derived global sections. -/
theorem homEquiv_crisBaseChangeMap (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
    (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
    (F' : ModuleSheaf S') :
    (derivedBaseChangeTensorAdjunction f).homEquiv _ _ (crisBaseChangeMap f g h F') =
      DerivedCategory.Plus.ι.map (crisDerivedBaseChangeGlobalSectionsMap f g h F') :=
  Equiv.apply_symm_apply _ _

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end

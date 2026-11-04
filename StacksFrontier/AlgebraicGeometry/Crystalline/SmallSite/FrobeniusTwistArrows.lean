module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactIdentityComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.FrobeniusRelativeTwist
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FrobeniusDerivedGlobalSections
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FrobeniusIsogenyReduction

/-!
# The first two arrows of the proof of [Stacks, Tag 07N5], separately

The proof of [Stacks, Tag 07N5] writes its map as a composition of three arrows through
`X^{(1)} = X ×_{S₀, F_{S₀}} S₀`:

1. the base change map (07QC)
   `RΓ(Cris(X/S), E) ⊗^L_{A, σ} A ⟶ RΓ(Cris(X^{(1)}/S), E^{(1)})`;
2. the pullback (07N6) along the relative Frobenius
   `F_{X/S₀}^* : RΓ(Cris(X^{(1)}/S), E^{(1)}) ⟶ RΓ(Cris(X/S), (F_X)^*_cris E)`;
3. the map (07QD) induced by the Frobenius structure `F_E`.

The third is `...SmallSite.frobeniusCohomologyMap`, and its isogeny is proved.  This file
builds the **first two**, which the library had only in their composite form
`...SmallSite.frobeniusBaseChangeArrows07N5`.

Keeping them apart is what makes the source's two citations citable one at a time: (07QC) is an
isomorphism by [Stacks, Tag 07MU] together with the perfectness [Stacks, Tag 07MY], while (07N6)
is only an isogeny, by [Stacks, Tag 07QB].  A statement about the composite cannot distinguish
the two, and would be a statement about the whole of what the library is missing rather than
about the source's two inputs.

## How they are built

Both are instances of one construction, `...SmallSite.derivedChangeBaseBigGlobalSectionsMap`: the
comparison on derived global sections along a change of divided power base, on the big
crystalline site, where change of base carries no hypothesis on the morphism of schemes.  The two
squares are the two halves of the Frobenius square, exactly as
`Crystalline/FrobeniusRelativeTwist.lean` sets them up:

* arrow 1 is taken along `Spec(σ) : S ⟶ S` and the projection `X^{(1)} ⟶ X`, whose module
  pullback is `E ↦ E^{(1)}` (`Crystalline.FCrystalSituation.sigmaModulePullback`).  It is
  therefore `σ`-semilinear, and the source's (07QC) is its transpose across
  `...SmallSite.frobeniusDerivedBaseChangeAdjunction`, the chapter's instance of
  [Stacks, Tag 0GMT].
* arrow 2 is taken along `𝟙 : S ⟶ S` and the relative Frobenius `F_{X/S₀} : X ⟶ X^{(1)}`, whose
  module pullback is `F_{X/S₀}^*` (`Crystalline.FCrystalSituation.twistModulePullback`).  The
  base does not change, so the arrow is `A`-linear: the restriction of scalars in the target of
  the general construction is along `...SmallSite.baseChangeRingHom (𝟙 S)`, which is the identity
  ring map by `...SmallSite.baseChangeRingHom_id`, and `restrictScalarsIdDerivedPlusIso` removes
  it.  Its target is read at `(F_X)^*_cris E` through `frobeniusBigModulePullbackIso`, the
  source's `F_{X/S₀}^* E^{(1)} = (F_X)^*_cris E` at the module universe of the cohomology (the
  twin of `Crystalline.FCrystalSituation.frobeniusModulePullbackIso`).

In both cases the passage from the big crystalline site to the small one is
`...SmallSite.derivedRestrictModuleGlobalSectionsULiftIso`, as for the composite arrow.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `restrictScalarsIdDerivedPlusIso` — restriction of scalars along `baseChangeRingHom (𝟙 S)` is
  the identity of `D⁺(Mod_A)`.
* `twistDerivedGlobalSections` — `RΓ(Cris(X^{(1)}/S), E^{(1)})` as an object of `D(Mod_A)`.
* `derivedSigmaTwistRestrictGlobalSectionsMap` — the `σ`-semilinear comparison
  `RΓ(Cris(X/S), E) ⟶ σ_* RΓ(Cris(X^{(1)}/S), E^{(1)})`.
* `baseChangeArrow07QC` — **arrow 1, the source's (60.26.4.1)**:
  `RΓ(Cris(X/S), E) ⊗^L_{A, σ} A ⟶ RΓ(Cris(X^{(1)}/S), E^{(1)})`.
* `relativeFrobeniusArrow07N6` — **arrow 2, the source's (60.26.4.2)**:
  `RΓ(Cris(X^{(1)}/S), E^{(1)}) ⟶ RΓ(Cris(X/S), (F_X)^*_cris E)`.

Their composite `baseChangeArrow07QC T E ≫ relativeFrobeniusArrow07N6 T E` is the one-step
comparison `...SmallSite.frobeniusBaseChangeArrows07N5` for the Frobenius square:
`...SmallSite.frobeniusBaseChangeArrows07N5_eq_comp` of
`SmallSite/FrobeniusFactorization07N5.lean`.

## What is and is not proved

Nothing here asserts that either arrow is invertible, in any sense; the two are constructions.
No `@[stacks 07N5]` attribute is placed in this file.

## References

* [Stacks Project, Tag 07N5](https://stacks.math.columbia.edu/tag/07N5)
* [Stacks Project, Tag 07N2](https://stacks.math.columbia.edu/tag/07N2)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u wS wB wA

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section RestrictScalarsId

variable (S : GlobalCrystallineSituation.{u})
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]

/-- **Restriction of scalars along `baseChangeRingHom (𝟙 S)` is the identity of `D⁺(Mod_A)`.**

When the divided power base does not change, the ring map `A ⟶ A` of
`...SmallSite.baseChangeRingHom` is the identity (`...SmallSite.baseChangeRingHom_id`), so the
restriction of scalars appearing in the target of
`...SmallSite.derivedChangeBaseBigGlobalSectionsMap` is the identity functor and the comparison
is an honest `A`-linear map.  Mathlib's `ModuleCat.restrictScalarsId'` supplies the underived
isomorphism and `CategoryTheory.Functor.rightDerivedFunctorPlusIdIsoOf` carries it to the
bounded below derived category, through the identification of the right derived functor of an
exact functor with the degreewise one. -/
def restrictScalarsIdDerivedPlusIso :
    (ModuleCat.restrictScalars.{u + 1}
        (baseChangeRingHom (S := S) (S' := S) (𝟙 S.S))).mapDerivedCategoryPlus ≅
      𝟭 (DerivedCategory.Plus (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))) :=
  (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
      (ModuleCat.restrictScalars.{u + 1}
        (baseChangeRingHom (S := S) (S' := S) (𝟙 S.S)))).symm ≪≫
    Functor.rightDerivedFunctorPlusIdIsoOf _
      (ModuleCat.restrictScalarsId'.{u + 1} _ (baseChangeRingHom_id S))

end RestrictScalarsId

section Twist

variable (T : Crystalline.FCrystalSituation.{u})
  [HasDerivedCategory.{wS} (ModuleSheaf T.global)]
  [HasDerivedCategory.{wS} (ModuleSheaf T.frobeniusTwistSituation)]
  [HasDerivedCategory.{wB} (BigModuleSheaf T.global)]
  [HasDerivedCategory.{wB} (BigModuleSheaf T.frobeniusTwistSituation)]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤))]

/-- The base of `X^{(1)}/S` is the base of `X/S`, so the derived category of its modules of
global sections is the one already assumed.  Instance search does not see through the definition
of `Crystalline.FCrystalSituation.frobeniusTwistSituation`, so the instance is restated. -/
instance hasDerivedCategory_twistBaseModules :
    HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ((T.frobeniusTwistSituation).S.scheme, ⊤)) :=
  inferInstanceAs (HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤)))

/-- **The base change `E ↦ E^{(1)}` by `Spec(σ)` at the module universe of the cohomology**: the
pullback of sheaves of modules along the square with `X^{(1)} ⟶ X` on top and `Spec(σ) : S ⟶ S`
on the bottom, on `...SmallSite.BigModuleSheaf`. -/
abbrev sigmaBigModulePullback :
    BigModuleSheaf T.global ⥤ BigModuleSheaf T.frobeniusTwistSituation :=
  changeBaseBigModulePullback T.frobeniusTwistSituation T.global T.specSigma T.twistProjection
    T.twistToClosedFiber_comp_closedFiberMap_specSigma

/-- The pullback `E ↦ E^{(1)}` is additive; stated at the spelling of its base change, which
instance search does not unfold to the general instance. -/
instance additive_sigmaPullback :
    (changeBaseBigModulePullback T.frobeniusTwistSituation T.global T.specSigma
      T.twistProjection T.twistToClosedFiber_comp_closedFiberMap_specSigma).Additive :=
  changeBaseBigModulePullback_additive _ _ _ _ _

/-- The pullback `E ↦ E^{(1)}` preserves finite limits. -/
instance preservesFiniteLimits_sigmaPullback :
    PreservesFiniteLimits (changeBaseBigModulePullback T.frobeniusTwistSituation T.global
      T.specSigma T.twistProjection T.twistToClosedFiber_comp_closedFiberMap_specSigma) :=
  changeBaseBigModulePullback_preservesFiniteLimits _ _ _ _ _

/-- The pullback `E ↦ E^{(1)}` preserves finite colimits. -/
instance preservesFiniteColimits_sigmaPullback :
    PreservesFiniteColimits (changeBaseBigModulePullback T.frobeniusTwistSituation T.global
      T.specSigma T.twistProjection T.twistToClosedFiber_comp_closedFiberMap_specSigma) :=
  changeBaseBigModulePullback_preservesFiniteColimits _ _ _ _ _

/-- **The pullback `F_{X/S₀}^*` at the module universe of the cohomology**, on
`...SmallSite.BigModuleSheaf`. -/
abbrev twistBigModulePullback :
    BigModuleSheaf T.frobeniusTwistSituation ⥤ BigModuleSheaf T.global :=
  changeBaseBigModulePullback T.global T.frobeniusTwistSituation (𝟙 T.global.S)
    T.relativeFrobeniusToTwist T.toClosedFiber_comp_closedFiberMap_id

/-- **`F_{X/S₀}^* E^{(1)} = (F_X)^*_cris E` at the module universe of the cohomology**: the
module-universe-`u + 1` twin of `Crystalline.FCrystalSituation.frobeniusModulePullbackIso`, built
the same way, from the composite of the two changes of base
(`Crystalline.FCrystalSituation.twistChangeBaseCompIso`). -/
def frobeniusBigModulePullbackIso :
    sigmaBigModulePullback T ⋙ twistBigModulePullback T ≅ frobeniusBigModulePullback T :=
  SheafOfModules.pushforwardComp (F := T.twistChangeBase) (G := T.sigmaChangeBase)
      (changeBaseStructureHom T.global T.frobeniusTwistSituation
        (𝟙 T.global.S) T.relativeFrobeniusToTwist T.toClosedFiber_comp_closedFiberMap_id)
      (changeBaseStructureHom T.frobeniusTwistSituation T.global
        T.specSigma T.twistProjection T.twistToClosedFiber_comp_closedFiberMap_specSigma) ≪≫
    SheafOfModules.pushforwardCongr₂ (e := T.twistChangeBaseCompIso.symm)
      (ψ := changeBaseStructureHom T.global T.global T.specSigma
        T.frobenius T.toClosedFiber_comp_closedFiberMap_specSigma) (he := by ext; rfl)

/-- **`RΓ(Cris(X^{(1)}/S), N^{(1)})` in `D⁺(Mod_A)`**, for `N` a sheaf of `𝒪_{X/S}`-modules: the
derived global sections over the small crystalline site of `X^{(1)}/S` of the base change of `N`
by `Spec(σ)`.

The base of `X^{(1)}/S` is the base of `X/S`, so the coefficients are the same ring `A`. -/
abbrev twistDerivedGlobalSectionsPlus
    (N : SheafOfModules.{u} (crystallineStructureSheaf T.global)) :
    DerivedCategory.Plus (ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤)) :=
  moduleULiftDerivedGlobalSections T.frobeniusTwistSituation
    (restrictSheafOfModules (T.sigmaModulePullback.obj N))

/-- **The `σ`-semilinear comparison of arrow 1**, read on the small crystalline sites:

`RΓ(Cris(X/S), N) ⟶ σ_* RΓ(Cris(X^{(1)}/S), N^{(1)})`   in `D⁺(Mod_A)`.

It is `...SmallSite.derivedChangeBaseBigGlobalSectionsMap` for the square with `Spec(σ)` on the
bottom and the projection `X^{(1)} ⟶ X` on top, conjugated by
`...SmallSite.derivedRestrictModuleGlobalSectionsULiftIso` at each end — the same recipe as
`...SmallSite.derivedFrobeniusRestrictGlobalSectionsMap`, which is the composite of the two
arrows. -/
def derivedSigmaTwistRestrictGlobalSectionsMap
    (N : SheafOfModules.{u} (crystallineStructureSheaf T.global)) :
    moduleULiftDerivedGlobalSections T.global (restrictSheafOfModules N) ⟶
      (frobeniusSigmaRestrictScalarsPlus T).obj (twistDerivedGlobalSectionsPlus T N) :=
  (derivedRestrictModuleGlobalSectionsULiftIso T.global N).inv ≫
    derivedChangeBaseBigGlobalSectionsMap (S := T.frobeniusTwistSituation) (S' := T.global)
        T.specSigma T.twistProjection
        T.twistToClosedFiber_comp_closedFiberMap_specSigma ((bigModuleULift T.global).obj N) ≫
      (frobeniusSigmaRestrictScalarsPlus T).map
        (derivedRestrictModuleGlobalSectionsULiftIso T.frobeniusTwistSituation
          (T.sigmaModulePullback.obj N)).hom

/-- **The comparison of arrow 2**, read on the small crystalline sites:

`RΓ(Cris(X^{(1)}/S), N^{(1)}) ⟶ RΓ(Cris(X/S), (F_X)^*_cris N)`   in `D⁺(Mod_A)`.

It is `...SmallSite.derivedChangeBaseBigGlobalSectionsMap` for the square with the identity of
`S` on the bottom and the relative Frobenius `F_{X/S₀} : X ⟶ X^{(1)}` on top.  Three
identifications read it in the shape above: `restrictScalarsIdDerivedPlusIso` removes the
restriction of scalars along `baseChangeRingHom (𝟙 S)`, which is the identity ring map;
`frobeniusBigModulePullbackIso`, the module-universe twin of
`Crystalline.FCrystalSituation.frobeniusModulePullbackIso`, is the source's
`F_{X/S₀}^* N^{(1)} = (F_X)^*_cris N`; and
`...SmallSite.derivedRestrictModuleGlobalSectionsULiftIso` crosses from the big crystalline site
to the small one at each end. -/
def derivedRelativeFrobeniusRestrictGlobalSectionsMap
    (N : SheafOfModules.{u} (crystallineStructureSheaf T.global)) :
    twistDerivedGlobalSectionsPlus T N ⟶
      moduleULiftDerivedGlobalSections T.global
        (restrictSheafOfModules (T.frobeniusModulePullback.obj N)) :=
  (derivedRestrictModuleGlobalSectionsULiftIso T.frobeniusTwistSituation
        (T.sigmaModulePullback.obj N)).inv ≫
    derivedChangeBaseBigGlobalSectionsMap (S := T.global) (S' := T.frobeniusTwistSituation)
        (𝟙 T.global.S) T.relativeFrobeniusToTwist T.toClosedFiber_comp_closedFiberMap_id
        ((bigModuleULift T.frobeniusTwistSituation).obj (T.sigmaModulePullback.obj N)) ≫
      (restrictScalarsIdDerivedPlusIso T.global).hom.app _ ≫
        (derivedBigModuleGlobalSections T.global).map
            ((frobeniusBigModulePullbackIso T).hom.app ((bigModuleULift T.global).obj N)) ≫
          (derivedRestrictModuleGlobalSectionsULiftIso T.global
            (T.frobeniusModulePullback.obj N)).hom

/-! ### The two arrows of the source's proof -/

/-- **The `σ`-semilinear form of arrow 1, in the unbounded derived category**,

`RΓ(Cris(X/S), E) ⟶ σ_* RΓ(Cris(X^{(1)}/S), E^{(1)})`,

at the module of an `F`-crystal.  The tag's objects live in `D(Mod_A)` rather than `D⁺(Mod_A)`
because the derived tensor product `- ⊗^L_{A, σ} A` is only right t-exact. -/
def sigmaTwistSemilinearArrow (E : Crystalline.FCrystal T) :
    DerivedCategory.Plus.ι.obj (moduleULiftDerivedGlobalSections T.global (toSmallFCrystal E)) ⟶
      (frobeniusSigmaRestrictScalars T).obj
        (DerivedCategory.Plus.ι.obj (twistDerivedGlobalSectionsPlus T E.crystal)) :=
  DerivedCategory.Plus.ι.map (derivedSigmaTwistRestrictGlobalSectionsMap T E.crystal)

/-- **Arrow 1 of the proof of [Stacks, Tag 07N5], the source's base change map (60.26.4.1)**:

`RΓ(Cris(X/S), E) ⊗^L_{A, σ} A ⟶ RΓ(Cris(X^{(1)}/S), E^{(1)})`.

It is `sigmaTwistSemilinearArrow` transposed across
`...SmallSite.frobeniusDerivedBaseChangeAdjunction`, the chapter's instance of
[Stacks, Tag 0GMT], exactly as `...SmallSite.frobeniusBaseChangeArrows07N5` is the transpose of
the composite semilinear arrow. -/
def baseChangeArrow07QC (E : Crystalline.FCrystal T) :
    frobeniusDerivedBaseChangeTensorGlobalSections T (toSmallFCrystal E) ⟶
      DerivedCategory.Plus.ι.obj (twistDerivedGlobalSectionsPlus T E.crystal) :=
  ((frobeniusDerivedBaseChangeAdjunction T).homEquiv _ _).symm (sigmaTwistSemilinearArrow T E)

/-- **Arrow 2 of the proof of [Stacks, Tag 07N5], the source's (60.26.4.2)**:

`F_{X/S₀}^* : RΓ(Cris(X^{(1)}/S), E^{(1)}) ⟶ RΓ(Cris(X/S), (F_X)^*_cris E)`.

It is `derivedRelativeFrobeniusRestrictGlobalSectionsMap` at the module of an `F`-crystal, read
in the unbounded derived category. -/
def relativeFrobeniusArrow07N6 (E : Crystalline.FCrystal T) :
    DerivedCategory.Plus.ι.obj (twistDerivedGlobalSectionsPlus T E.crystal) ⟶
      frobeniusPullbackDerivedGlobalSections T E :=
  DerivedCategory.Plus.ι.map (derivedRelativeFrobeniusRestrictGlobalSectionsMap T E.crystal)

end Twist

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end

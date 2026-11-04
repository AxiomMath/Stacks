module

public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreOverField
public import StacksFrontier.AlgebraicGeometry.LerayAffineBase.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatRankOpen
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.CechAffineCover
public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections

/-!
# A direct image which is a module placed in degree zero

Let `π : Y ⟶ T` be a morphism of schemes and `ℱ` an `𝒪_Y`-module whose derived direct image
`Rπ_*ℱ` is isomorphic to a module `𝒫` placed in degree zero. Then:

* the higher direct images `Rᵠπ_*ℱ`, `q > 0`, vanish, and `π_*ℱ ≅ 𝒫`;
* if `T` is affine and `π` quasi-compact and quasi-separated, then for `ℱ` quasi-coherent the
  cohomology `Hᵖ(Y, ℱ)` vanishes for `p > 0`.

For `π` proper and `ℱ` of finite presentation and flat over the base, the hypothesis passes to an
open of the base, by [Stacks, Tag 08FE].

## Main results

* `AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.hdiIsoHomologyDerivedPushforwardModule`:
  `Rᵠπ_*ℱ` is the `q`-th cohomology sheaf of `Rπ_*ℱ`.
* `AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.isZero_hdi_of_iso_single` and
  `AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.pushforwardIsoOfIsoSingle`: if `Rπ_*ℱ` is
  a module `𝒫` placed in degree zero, then `Rᵠπ_*ℱ = 0` for `q > 0` and `π_*ℱ ≅ 𝒫`.
* `AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.subsingleton_rightDerived_of_iso_single`:
  no higher cohomology over an affine base.
* `AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.nonempty_iso_single_of_isOpenImmersion`:
  restriction of the hypothesis to an open of the base.

## Implementation notes

`Rπ_*ℱ` is computed on Mathlib's chosen injective resolution `J` of `ℱ`, as in
`AlgebraicGeometry.DerivedFibreOverField.derivedPushforwardModuleIsoResolution` (which is the
case of a base `Spec K`): `J` is K-injective, so `Rπ_*ℱ ≅ π_*J`, and Mathlib's `ℕ`-indexed
`Rᵠπ_*` is the homology of `π_*J` too (`Stacks.DerivedIndexing.rightDerivedIsoRes`). The
vanishing of cohomology over an affine base is the Leray degeneration
`Stacks.AlgebraicGeometry.LerayAffineBase.isZero_hgroup_of_isZero_hdi`.

## References

* [Stacks Project, Tag 0B9X](https://stacks.math.columbia.edu/tag/0B9X)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

attribute [local instance] _root_.Stacks.SchemeCohomology.sheafOfModules_abelian
  _root_.Stacks.Cohomology.enoughInjectives_sheafOfModules_ringCatSheaf

/-- **`Rg_*ℱ` is computed on the chosen injective resolution**, for an arbitrary morphism of
schemes `g`. -/
def derivedPushforwardModuleIsoInjectiveResolution {Y T : Scheme.{u}} (g : Y ⟶ T)
    (F : Y.Modules) :
    derivedPushforwardModule g F ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj
        (((modulePushforward g.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ)).obj
          (injectiveResolution F).cochainComplex)) :=
  have hQ : IsIso (DerivedCategory.Q.map (injectiveResolution F).ι') :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  have hK : (injectiveResolution F).cochainComplex.IsKInjective :=
    CochainComplex.isKInjective_of_injective _ 0
  have : IsIso ((derivedPushforwardUnit g.toLRSHom.toShHom).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj (injectiveResolution F).cochainComplex)) :=
    isIso_derivedPushforwardUnit_app_of_isKInjective g.toLRSHom.toShHom _ hK
  (derivedPushforward g.toLRSHom.toShHom).mapIso
      (@asIso _ _ _ _ (DerivedCategory.Q.map (injectiveResolution F).ι') hQ ≪≫
        (DerivedCategory.quotientCompQhIso _).symm.app _) ≪≫
    (asIso ((derivedPushforwardUnit g.toLRSHom.toShHom).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj (injectiveResolution F).cochainComplex))).symm

/-- **The higher direct images are the cohomology sheaves of `Rg_*ℱ`.** -/
def hdiIsoHomologyDerivedPushforwardModule {Y T : Scheme.{u}} (g : Y ⟶ T) (F : Y.Modules)
    (q : ℕ) :
    Stacks.AlgebraicGeometry.LerayAffineBase.hdi g q F ≅
      (DerivedCategory.homologyFunctor T.Modules q).obj (derivedPushforwardModule g F) :=
  (Stacks.DerivedIndexing.rightDerivedIsoRes (Scheme.Modules.pushforward g) q).app F ≪≫
    (HomotopyCategory.homologyFunctorFactors _ _ (q : ℤ)).app _ ≪≫
    ((DerivedCategory.homologyFunctor T.Modules (q : ℤ)).mapIso
      (derivedPushforwardModuleIsoInjectiveResolution g F) ≪≫
    (DerivedCategory.homologyFunctorFactorsh T.Modules (q : ℤ)).app _ ≪≫
    (HomotopyCategory.homologyFunctorFactors _ _ (q : ℤ)).app _).symm

/-- If `Rg_*ℱ` is a module placed in degree zero, the higher direct images of `ℱ` vanish. -/
theorem isZero_hdi_of_iso_single {Y T : Scheme.{u}} {g : Y ⟶ T} {F : Y.Modules} {P : T.Modules}
    (e : derivedPushforwardModule g F ≅ (DerivedCategory.singleFunctor T.Modules 0).obj P)
    {q : ℕ} (hq : 0 < q) : IsZero (Stacks.AlgebraicGeometry.LerayAffineBase.hdi g q F) :=
  (Scheme.Modules.isZero_homologyFunctor_singleFunctor_obj P (by omega)).of_iso
    (hdiIsoHomologyDerivedPushforwardModule g F q ≪≫
      (DerivedCategory.homologyFunctor T.Modules q).mapIso e)

/-- If `Rg_*ℱ` is a module `P` placed in degree zero, then `g_*ℱ ≅ P`. -/
def pushforwardIsoOfIsoSingle {Y T : Scheme.{u}} {g : Y ⟶ T} {F : Y.Modules} {P : T.Modules}
    (e : derivedPushforwardModule g F ≅ (DerivedCategory.singleFunctor T.Modules 0).obj P) :
    (Scheme.Modules.pushforward g).obj F ≅ P :=
  have := Stacks.SchemeCohomology.pushforward_preservesFiniteLimits g
  ((Scheme.Modules.pushforward g).rightDerivedZeroIsoSelf.app F).symm ≪≫
    hdiIsoHomologyDerivedPushforwardModule g F 0 ≪≫
    (DerivedCategory.homologyFunctor T.Modules 0).mapIso e ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso T.Modules 0).app P

/-- **No higher cohomology over an affine base.** If `T` is affine, `g` quasi-compact and
quasi-separated, `ℱ` quasi-coherent and `Rg_*ℱ` a module placed in degree zero, then
`Hᵖ(Y, ℱ) = 0` for `p > 0`. -/
theorem subsingleton_rightDerived_of_iso_single {Y T : Scheme.{u}} [IsAffine T] {g : Y ⟶ T}
    [QuasiCompact g] [QuasiSeparated g] {F : Y.Modules} [F.IsQuasicoherent] {P : T.Modules}
    (e : derivedPushforwardModule g F ≅ (DerivedCategory.singleFunctor T.Modules 0).obj P)
    (p : ℕ) (hp : 0 < p) :
    Subsingleton (((AlgebraicGeometry.moduleGlobalSections Y).rightDerived p).obj F) := by
  have h := Stacks.AlgebraicGeometry.LerayAffineBase.isZero_hgroup_of_isZero_hdi g 1 F
    (Stacks.AlgebraicGeometry.LerayAffineBase.hasAcyclicDirectImages_of_isAffine g F)
    (fun q hq _ => isZero_hdi_of_iso_single e hq) p hp hp
  exact ModuleCat.subsingleton_of_isZero
    (Stacks.Cohomology.Affine.isZero_rightDerived_evaluation_of_isZero_Hgroup
      (X := Y) (R := Y.ringCatSheaf) ⊤ p F h)

end AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

namespace AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

/-- **A module placed in degree zero restricts to an open immersion of the base.** Let `f` be
proper and of finite presentation and `ℱ` of finite presentation and flat over `S`. If `Rf_*ℱ` is
a module `P` placed in degree zero, then for an open immersion `g : T ⟶ S` with base change
`f' : X' ⟶ T`, the derived direct image along `f'` of the pullback of `ℱ` is the restriction of
`P` to `T` placed in degree zero. -/
theorem nonempty_iso_single_of_isOpenImmersion {X S X' T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [IsOpenImmersion g] (f' : X' ⟶ T) (g' : X' ⟶ X) (hsq : IsPullback g' f' f g)
    (hfp : FinitePresentation f) [IsProper f] (F : X.Modules) (hF : F.IsFinitePresentation)
    (hflat : IsFlatOver f.toLRSHom.toShHom F) {P : S.Modules}
    (e : derivedPushforwardModule f F ≅ (DerivedCategory.singleFunctor S.Modules 0).obj P) :
    Nonempty (derivedPushforwardModule f' ((Scheme.Modules.pullback g').obj F) ≅
      (DerivedCategory.singleFunctor T.Modules 0).obj
        ((Scheme.Modules.restrictFunctor g).obj P)) := by
  obtain ⟨e'⟩ := ProperFlatRankOpen.openImmersionBaseChangeDerivedPushforward f g f' g' hsq hfp
    inferInstance F hF hflat
  exact ⟨e'.symm ≪≫ (Scheme.Modules.restrictFunctor g).mapDerivedCategory.mapIso e ≪≫
    ((Scheme.Modules.restrictFunctor g).mapDerivedCategorySingleFunctor 0).app P⟩

end AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

end

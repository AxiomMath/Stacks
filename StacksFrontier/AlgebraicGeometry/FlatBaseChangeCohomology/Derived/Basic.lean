module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.FlatBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianDerivedBaseChangeCriteria
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.RestrictionCoverTriangle
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineDegreeZero.Modules
public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.Vanishing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived base change map of a square of schemes

Let
```
X' --g'--> X
|f'        |f
S' --g-->  S
```
be a commutative square of schemes with `g` and `g'` flat. The base change map of
[Stacks, Tag 02N7] is the morphism

`g^* Rf_* ⟶ Rf'_* (g')^*`

of functors `D⁺(𝒪_X) ⥤ D⁺(𝒪_{S'})`, `Stacks.Cohomology.FlatBaseChange.baseChangeMap` of the
underlying square of ringed spaces. This file records its basic properties and proves that it is
an isomorphism at a quasi-coherent module when `f` is affine and the square is cartesian.

## Main definitions

* `Stacks.AlgebraicGeometry.FlatBaseChangeDerived.schemeBaseChange`: the base change map of
  [Stacks, Tag 02N7] for a commutative square of schemes.

## Main results

* `Stacks.AlgebraicGeometry.FlatBaseChangeDerived.moduleBaseChange_eq`: the underived base change
  map of the square of ringed spaces is the base change morphism
  `Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans` of the square of schemes.
* `Stacks.AlgebraicGeometry.FlatBaseChangeDerived.natTransCommShift_schemeBaseChange`: the base
  change map is compatible with the shift.
* `Stacks.AlgebraicGeometry.FlatBaseChangeDerived.isIso_schemeBaseChange_of_isAffineHom`: for a
  cartesian square with `g` flat and `f` affine, the base change map is an isomorphism at every
  quasi-coherent module.

## References

* [Stacks Project, Tag 02N7](https://stacks.math.columbia.edu/tag/02N7)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingedSpaceModuleAdjunction

universe u

namespace Stacks.AlgebraicGeometry.FlatBaseChangeDerived

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
  Stacks.DerivedIndexing.isTriangulated_rightDerivedFunctorPlus

/-- Sheaves of modules on a ringed space form an abelian category. -/
@[instance_reducible] local instance abelianModules (Z : RingedSpace.{u, u}) :
    Abelian (_root_.SheafOfModules.{u} (structureSheafRing Z)) :=
  _root_.SheafOfModules.instAbelian _

/-- Sheaves of modules on a ringed space have enough injectives. -/
@[sga "4½ Etat_0 6.2" "special case"]
local instance enoughInjectivesModules (Z : RingedSpace.{u, u}) :
    EnoughInjectives (_root_.SheafOfModules.{u} (structureSheafRing Z)) :=
  Stacks.Cohomology.FlatBaseChange.enoughInjectives_ringSheaf Z

/-- A flat morphism of schemes is a flat morphism of ringed spaces. -/
theorem isFlat_toShHom {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    AlgebraicGeometry.IsFlat f.toLRSHom.toShHom :=
  fun x => Flat.stalkMap f x

/-- Pullback along a flat morphism of schemes is exact. -/
theorem preservesFiniteLimits_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    PreservesFiniteLimits (modulePullback f.toLRSHom.toShHom) :=
  preservesFiniteLimits_modulePullback_of_isFlat _ (isFlat_toShHom f)

/-- The unit of the derived pullback along a flat morphism of schemes is invertible. -/
private theorem isIso_rightDerivedFunctorPlusUnit_modulePullback {A B : Scheme.{u}} (h : A ⟶ B)
    [Flat h] : IsIso (modulePullback h.toLRSHom.toShHom).rightDerivedFunctorPlusUnit :=
  (Stacks.Cohomology.FlatBaseChange.flatPullbackComparison h.toLRSHom.toShHom
    (isFlat_toShHom h)).isIso_hom

section Square

variable {X X' S S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (w : g' ≫ f = f' ≫ g)

/-- **The base change map of [Stacks, Tag 02N7] for a commutative square of schemes** with flat
horizontal morphisms: `g^* Rf_* ⟶ Rf'_* (g')^*` on bounded below derived categories of sheaves of
modules. -/
abbrev schemeBaseChange [Flat g] [Flat g'] :
    (modulePushforward f.toLRSHom.toShHom).rightDerivedFunctorPlus ⋙
        (modulePullback g.toLRSHom.toShHom).rightDerivedFunctorPlus ⟶
      (modulePullback g'.toLRSHom.toShHom).rightDerivedFunctorPlus ⋙
        (modulePushforward f'.toLRSHom.toShHom).rightDerivedFunctorPlus :=
  Stacks.Cohomology.FlatBaseChange.baseChangeMap f.toLRSHom.toShHom f'.toLRSHom.toShHom
    g.toLRSHom.toShHom g'.toLRSHom.toShHom (congrArg (fun h => h.toLRSHom.toShHom) w)
    (isFlat_toShHom g) (isFlat_toShHom g')

/-- The underived base change map of the square of schemes, read on ringed spaces. -/
abbrev schemeModuleBaseChange :
    modulePushforward f.toLRSHom.toShHom ⋙ modulePullback g.toLRSHom.toShHom ⟶
      modulePullback g'.toLRSHom.toShHom ⋙ modulePushforward f'.toLRSHom.toShHom :=
  Stacks.Cohomology.FlatBaseChange.moduleBaseChange f.toLRSHom.toShHom f'.toLRSHom.toShHom
    g.toLRSHom.toShHom g'.toLRSHom.toShHom (congrArg (fun h => h.toLRSHom.toShHom) w)

/-- Pushforwards along equal morphisms of schemes: the transport along the equality is
`AlgebraicGeometry.Scheme.Modules.pushforwardCongr`. -/
theorem eqToIso_eq_pushforwardCongr {A B : Scheme.{u}} {φ ψ : A ⟶ B} (h : φ = ψ) :
    eqToIso (congrArg (fun k : A ⟶ B => modulePushforward k.toLRSHom.toShHom) h) =
      Scheme.Modules.pushforwardCongr h := by
  subst h
  ext M U x
  let M' : A.Modules := M
  have h₁ : ((Scheme.Modules.pushforwardCongr (rfl : φ = φ)).hom.app M').app U.unop =
      𝟙 _ :=
    (Scheme.Modules.pushforwardCongr_hom_app_app (M := M') rfl U.unop).trans
      ((congrArg (fun t => M'.presheaf.map t) (Subsingleton.elim _ (𝟙 _))).trans
        (CategoryTheory.Functor.map_id _ _))
  exact (congrArg (fun t => t.hom x) h₁).symm

/-- The identification of the two composite direct images around the square of ringed spaces is
the one of the square of schemes. -/
theorem squarePushforwardIso_eq :
    Stacks.Cohomology.FlatBaseChange.squarePushforwardIso f.toLRSHom.toShHom
      f'.toLRSHom.toShHom g.toLRSHom.toShHom g'.toLRSHom.toShHom
      (congrArg (fun h => h.toLRSHom.toShHom) w) =
    Stacks.AlgebraicGeometry.AffinePushforward.pushforwardSquareIso w := by
  unfold Stacks.Cohomology.FlatBaseChange.squarePushforwardIso
    Stacks.AlgebraicGeometry.AffinePushforward.pushforwardSquareIso
  rw [← eqToIso_eq_pushforwardCongr w]
  rfl

/-- **The underived base change map of the square of ringed spaces is the base change morphism
of the square of schemes.** -/
theorem moduleBaseChange_eq :
    schemeModuleBaseChange f f' g g' w =
      Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans w := by
  unfold schemeModuleBaseChange Stacks.Cohomology.FlatBaseChange.moduleBaseChange
  rw [Stacks.Cohomology.BaseChange.mate_eq_mateEquiv_symm, squarePushforwardIso_eq,
    Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans_eq]
  rfl

variable [Flat g] [Flat g']

/-- **The base change map is compatible with the shift.** -/
theorem natTransCommShift_schemeBaseChange :
    NatTrans.CommShift (schemeBaseChange f f' g g' w) ℤ := by
  have := isIso_rightDerivedFunctorPlusUnit_modulePullback g
  exact Stacks.Cohomology.BaseChange.natTransCommShift_derived _ _ _ _ _ _
    (Stacks.Cohomology.BaseChange.natTransCommShift_onHomotopy _ _ _ _ _ _
      (Stacks.DerivedIndexing.natTransCommShiftRightDerivedFunctorPlusUnit _)
      (Stacks.Cohomology.BaseChange.natTransCommShift_mapPlus _)
      (Stacks.Cohomology.BaseChange.natTransCommShift_mapHomotopyCategoryPlusCompIso _)
      (Stacks.Cohomology.BaseChange.natTransCommShift_mapHomotopyCategoryPlusCompIso _))

end Square

/-- The unit of the derived pullback along a flat morphism is invertible. -/
theorem isIso_pullbackUnit {A B : Scheme.{u}} (h : A ⟶ B) [Flat h] :
    IsIso (modulePullback h.toLRSHom.toShHom).rightDerivedFunctorPlusUnit :=
  isIso_rightDerivedFunctorPlusUnit_modulePullback h

/-- A complex concentrated in degree zero has a zero term in every nonzero degree. -/
theorem isZero_single_X {C : Type*} [Category* C] [Abelian C] (M : C) {n : ℤ} (hn : n ≠ 0) :
    IsZero (((HomotopyCategory.Plus.singleFunctor C 0).obj M).obj.as.X n) :=
  HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M n hn

/-- **The affine case.** For a cartesian square of schemes with `g` flat and `f` affine, the base
change map of [Stacks, Tag 02N7] is an isomorphism at every quasi-coherent `𝒪_X`-module: both
direct images are computed by the underived ones ([Stacks, Tag 01XC]), and the underived base
change map is an isomorphism ([Stacks, Tag 02KG]). -/
theorem isIso_schemeBaseChange_of_isAffineHom {X X' S S' : Scheme.{u}} {f : X ⟶ S}
    {f' : X' ⟶ S'} {g : S' ⟶ S} {g' : X' ⟶ X} (H : IsPullback g' f' f g) [Flat g] [Flat g']
    [IsAffineHom f] (F : X.Modules) [F.IsQuasicoherent] :
    IsIso ((schemeBaseChange f f' g g' H.w).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) := by
  have : IsAffineHom f' := MorphismProperty.of_isPullback H inferInstance
  let K := (HomotopyCategory.Plus.singleFunctor
    (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj F
  refine Stacks.Cohomology.RestrictionCover.isIso_app_of_iso _
    ((Functor.singleFunctorPlusIsoCompQh 0).app F) ?_
  have := isIso_pullbackUnit g'
  have hF : IsIso ((modulePushforward f.toLRSHom.toShHom).rightDerivedFunctorPlusUnit.app K) :=
    Stacks.AffineHigherDirectImage.rightAcyclic_pushforward f F
  have hF'₀ : IsIso ((modulePushforward f'.toLRSHom.toShHom).rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.singleFunctor _ 0).obj
        ((modulePullback g'.toLRSHom.toShHom).obj F))) := by
    have : ((Scheme.Modules.pullback g').obj F).IsQuasicoherent :=
      Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback g' F
    exact Stacks.AffineHigherDirectImage.rightAcyclic_pushforward f'
      ((Scheme.Modules.pullback g').obj F)
  have hF' : IsIso ((modulePushforward f'.toLRSHom.toShHom).rightDerivedFunctorPlusUnit.app
      ((modulePullback g'.toLRSHom.toShHom).mapHomotopyCategoryPlus.obj K)) :=
    Stacks.Cohomology.RestrictionCover.isIso_app_of_iso _
      ((Functor.mapHomotopyCategoryPlusSingleFunctor (modulePullback g'.toLRSHom.toShHom) 0).app F)
      hF'₀
  refine Stacks.Cohomology.BaseChange.isIso_derived_app_Qh_of_acyclic _ _ _ _ _ _ K hF
    (NatIso.isIso_app_of_isIso _ K) hF' (fun n => ?_)
  rcases eq_or_ne n 0 with rfl | hn
  · have hτ : IsIso ((schemeModuleBaseChange f f' g g' H.w).app F) := by
      rw [moduleBaseChange_eq]
      exact Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat H F
    exact Stacks.Cohomology.RestrictionCover.isIso_app_of_iso _
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F) hτ
  · exact isIso_of_source_target_iso_zero _
      (((modulePullback g.toLRSHom.toShHom).map_isZero
        ((modulePushforward f.toLRSHom.toShHom).map_isZero (isZero_single_X F hn))).isoZero)
      (((modulePushforward f'.toLRSHom.toShHom).map_isZero
        ((modulePullback g'.toLRSHom.toShHom).map_isZero (isZero_single_X F hn))).isoZero)

end Stacks.AlgebraicGeometry.FlatBaseChangeDerived

end

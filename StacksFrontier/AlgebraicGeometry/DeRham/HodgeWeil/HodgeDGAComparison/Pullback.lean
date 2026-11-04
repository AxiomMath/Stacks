module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.HodgeDGAComparison.Multiplicative

/-!
# The identification of the Hodge complex cohomology with Hodge cohomology and pullback

The pullback along a morphism of ringed spaces commutes with the shift of complexes, and the
identification `hodgeDgaEquiv : H^n(X, ℋ) ≅ H^n_{Hodge}(X/S)` is compatible with pullback along
a commutative square of schemes.

## References

* [Stacks Project, Remark 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
* [Stacks Project, Remark 0FU7](https://stacks.math.columbia.edu/tag/0FU7)
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf StacksDraft.KFlat.modulePullback
  StacksDraft.KFlat.modulePushforward CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf
  AlgebraicGeometry.SheafOfModules.baseRingedSpace

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry ComplexShape
open AlgebraicGeometry.SheafOfModules
open Stacks.Cohomology.GlobalKunneth Stacks.Cohomology.DerivedGlobalCupProduct
open Stacks.SheafOfModules.Tensor (sheafTensor)
open scoped TensorProduct DirectSum Stacks.Topology.SheafTensorAdditiveOnOpens

universe u

namespace Stacks.HodgeWeil

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] abelianModules hasSheafifyOpens wEqualsLocallyBijectiveOpens

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))

attribute [local instance] AlgebraicGeometry.SheafOfModules.preservesZeroMorphisms_sheafTensor
  AlgebraicGeometry.SheafOfModules.preservesZeroMorphisms_sheafTensor_obj

/-! ### The pullback commutes with the shift -/

section PullbackShift

open Stacks.Cohomology.NaiveCupProductOnRingedSpaces (pushforwardComplex)
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces (pushforwardComparisonQ)
open Stacks.Cohomology.LerayCupPairing (lerayCohomologyIso restrictGlobal)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
  (isIso_derivedPushforwardUnit_app_of_isKInjective)

variable {Z Z' : RingedSpace.{u, u}} (h : Z' ⟶ Z)

/-- A cocycle of `Γ(Z, h_*K')`, read as a cocycle of `Γ(Z', K')`. -/
abbrev pushforwardCycle (K' : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing Z')) ℤ)
    (n : ℤ) (c : (sectionsComplex Z ((pushforwardComplex h).obj K')).cycles n) :
    (sectionsComplex Z' K').cycles n :=
  (((sectionsComplex Z' K').sc n).mapCyclesIso (restrictGlobal h)).hom.hom c

/-- A cocycle of `Γ(Z, h_*K')` and the same cocycle of `Γ(Z', K')` have the same underlying
section. -/
theorem iCycles_pushforwardCycle
    (K' : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing Z')) ℤ) (n : ℤ)
    (c : (sectionsComplex Z ((pushforwardComplex h).obj K')).cycles n) :
    ((sectionsComplex Z' K').iCycles n).hom (pushforwardCycle h K' n c) =
      ((sectionsComplex Z ((pushforwardComplex h).obj K')).iCycles n).hom c :=
  ConcreteCategory.congr_hom
    (((sectionsComplex Z' K').sc n).mapCyclesIso_hom_iCycles (restrictGlobal h)) c

/-- **The pullback of the class of a global cocycle of `h_*K'`**, along the identity of `h_*K'`,
is the class of the same cocycle on `Z'`. -/
theorem cohomologyPullback_id_globalClass
    (K' : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing Z')) ℤ) (n : ℤ)
    (c : (sectionsComplex Z ((pushforwardComplex h).obj K')).cycles n) :
    (cohomologyPullback h (𝟙 ((pushforwardComplex h).obj K')) n).hom
        (globalClass ((pushforwardComplex h).obj K') n c) =
      globalClass K' n (pushforwardCycle h K' n c) := by
  refine cohomologyPullback_globalClass h _ n c _ ?_
  refine Eq.trans ?_ (iCycles_pushforwardCycle h K' n c).symm
  rw [CategoryTheory.Functor.map_id, HomologicalComplex.cyclesMap_id]
  rfl

/-- On the direct image of a K-injective complex the pullback along the identity is injective:
the comparison `h_*J ⟶ Rh_*J` and the Leray identification are isomorphisms. -/
theorem injective_cohomologyPullback_id
    (J : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing Z')) ℤ) (hJ : J.IsKInjective)
    (n : ℤ) :
    Function.Injective (cohomologyPullback h (𝟙 ((pushforwardComplex h).obj J)) n).hom := by
  have hu := isIso_derivedPushforwardUnit_app_of_isKInjective h J hJ
  have ha : IsIso ((DerivedCategory.quotientCompQhIso
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)).inv.app
        ((pushforwardComplex h).obj J)) :=
    inferInstanceAs (IsIso ((DerivedCategory.quotientCompQhIso
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z)).app _).inv)
  have hb : IsIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward h).map
      ((DerivedCategory.quotientCompQhIso
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z')).hom.app J)) :=
    Functor.map_isIso _ _
  have hc : IsIso (pushforwardComparisonQ h J) := by
    unfold pushforwardComparisonQ
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ ha (@IsIso.comp_isIso _ _ _ _ _ _ _ hu hb)
  have : IsIso (cohomologyPullback h (𝟙 ((pushforwardComplex h).obj J)) n) := by
    unfold cohomologyPullback
    rw [DerivedCategory.Q.map_id, Category.id_comp]
    infer_instance
  exact (ConcreteCategory.bijective_of_isIso _).1

/-- **On the direct image of a K-injective complex every class is the class of a global
cocycle.** -/
theorem exists_globalClass_pushforward_of_isKInjective
    (J : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing Z')) ℤ) (hJ : J.IsKInjective)
    (n : ℤ) (y : cohomologyModule (DerivedCategory.Q.obj ((pushforwardComplex h).obj J)) n) :
    ∃ c, globalClass ((pushforwardComplex h).obj J) n c = y := by
  obtain ⟨c, hc⟩ := exists_globalClass_of_isKInjective J hJ n
    ((cohomologyPullback h (𝟙 ((pushforwardComplex h).obj J)) n).hom y)
  let cY := (((sectionsComplex Z' J).sc n).mapCyclesIso (restrictGlobal h)).inv.hom c
  refine ⟨cY, injective_cohomologyPullback_id h J hJ n ?_⟩
  refine (cohomologyPullback_id_globalClass h J n cY).trans (Eq.trans ?_ hc)
  exact congrArg (globalClass J n)
    (ModuleCat.hom_inv_apply (((sectionsComplex Z' J).sc n).mapCyclesIso (restrictGlobal h)) c)

/-- The identification `h_*(K')[t] ≅ h_*(K'[t])`, degreewise the identity. -/
abbrev pushforwardShiftHom
    (K' : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing Z')) ℤ)
    (t : ℤ) : ((pushforwardComplex h).obj K')⟦t⟧ ⟶ (pushforwardComplex h).obj (K'⟦t⟧) :=
  ((pushforwardComplex h).commShiftIso t).inv.app K'

/-- The identification `Hᵃ(S, 𝒦^•[t]) ≅ Hᵃ⁺ᵗ(S, 𝒦^•)` on the class of a global cocycle, on
elements. -/
theorem shiftCohomologyIso_globalClass {S : RingedSpace.{u, u}}
    (N : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing S)) ℤ) (t a a' : ℤ)
    (ha : t + a = a') (s : (sectionsComplex S (N⟦t⟧)).cycles a) :
    (shiftCohomologyIso N t a a' ha).hom.hom (globalClass (N⟦t⟧) a s) =
      globalClass N a' ((shiftCycles (sectionsComplex S N) a' ha
        (ModuleCat.ofHom (LinearMap.toSpanSingleton (baseRing S) _ s) ≫
          HomologicalComplex.cyclesMap ((((globalSections S).mapHomologicalComplex
            (ComplexShape.up ℤ)).commShiftIso t).hom.app N) a)).hom 1) := by
  have e := congrArg (fun f => f.hom (1 : baseRing S)) (globalCycleClass_shiftCohomologyIso N t a a'
    ha (ModuleCat.ofHom (LinearMap.toSpanSingleton (baseRing S) _ s)))
  refine Eq.trans ?_ e
  exact congrArg (fun x => (shiftCohomologyIso N t a a' ha).hom.hom (globalClass (N⟦t⟧) a x))
    (one_smul _ _).symm

/-- **The pullback commutes with the shift on the classes of global cocycles of a direct
image.** -/
theorem shiftCohomologyIso_cohomologyPullback_globalClass
    (J : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing Z')) ℤ) (t a a' : ℤ)
    (ha : t + a = a') (s : (sectionsComplex Z (((pushforwardComplex h).obj J)⟦t⟧)).cycles a) :
    (shiftCohomologyIso J t a a' ha).hom.hom ((cohomologyPullback h (pushforwardShiftHom h J t)
        a).hom (globalClass _ a s)) =
      (cohomologyPullback h (𝟙 ((pushforwardComplex h).obj J)) a').hom
        ((shiftCohomologyIso ((pushforwardComplex h).obj J) t a a' ha).hom.hom
          (globalClass _ a s)) := by
  let Γc := (globalSections Z).mapHomologicalComplex (ComplexShape.up ℤ)
  let s' := pushforwardCycle h (J⟦t⟧) a
    ((HomologicalComplex.cyclesMap (Γc.map (pushforwardShiftHom h J t)) a).hom s)
  have e1 := cohomologyPullback_globalClass h (pushforwardShiftHom h J t) a s s'
    (iCycles_pushforwardCycle h (J⟦t⟧) a _).symm
  refine (congrArg (fun x => (shiftCohomologyIso J t a a' ha).hom.hom x) e1).trans ?_
  refine (shiftCohomologyIso_globalClass J t a a' ha s').trans ?_
  refine Eq.trans ?_ (congrArg (fun x => (cohomologyPullback h
    (𝟙 ((pushforwardComplex h).obj J)) a').hom x)
      (shiftCohomologyIso_globalClass ((pushforwardComplex h).obj J) t a a' ha s)).symm
  refine Eq.trans ?_ (cohomologyPullback_id_globalClass h J a' _).symm
  refine congrArg (globalClass J a') ?_
  apply (ModuleCat.mono_iff_injective ((sectionsComplex Z' J).iCycles a')).1 inferInstance
  let z' := ModuleCat.ofHom (LinearMap.toSpanSingleton (baseRing Z') _ s')
  let C' := HomologicalComplex.cyclesMap ((((globalSections Z').mapHomologicalComplex
    (ComplexShape.up ℤ)).commShiftIso t).hom.app J) a
  let z := ModuleCat.ofHom (LinearMap.toSpanSingleton (baseRing Z) _ s)
  let C := HomologicalComplex.cyclesMap ((((globalSections Z).mapHomologicalComplex
    (ComplexShape.up ℤ)).commShiftIso t).hom.app ((pushforwardComplex h).obj J)) a
  have L1 := ConcreteCategory.congr_hom (shiftCycles_iCycles (sectionsComplex Z' J) a' ha
    (z' ≫ C')) 1
  have R1 := iCycles_pushforwardCycle h J a'
    ((shiftCycles (sectionsComplex Z ((pushforwardComplex h).obj J)) a' ha (z ≫ C)).hom 1)
  have R2 := ConcreteCategory.congr_hom (shiftCycles_iCycles
    (sectionsComplex Z ((pushforwardComplex h).obj J)) a' ha (z ≫ C)) 1
  refine L1.trans (Eq.trans ?_ (R1.trans R2).symm)
  have c1 := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
    ((((globalSections Z').mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso t).hom.app J)
      a) (z'.hom 1)
  have c2 := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
    ((((globalSections Z).mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso t).hom.app
      ((pushforwardComplex h).obj J)) a) (z.hom 1)
  have c3 := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i
    (Γc.map (pushforwardShiftHom h J t)) a) s
  have hz' : z'.hom 1 = s' := one_smul _ _
  have hz : z.hom 1 = s := one_smul _ _
  have i3 := iCycles_pushforwardCycle h (J⟦t⟧) a
    ((HomologicalComplex.cyclesMap (Γc.map (pushforwardShiftHom h J t)) a).hom s)
  have hψ : (Γc.map (pushforwardShiftHom h J t)).f a = 𝟙 _ := rfl
  let I' := HomologicalComplex.iCycles ((CategoryTheory.shiftFunctor
    (CochainComplex (ModuleCat.{u} (baseRing Z')) ℤ) t).obj (sectionsComplex Z' J)) a
  let S' := ((sectionsComplex Z' J).shiftFunctorObjXIso t a a' (by omega)).hom
  let I := HomologicalComplex.iCycles ((CategoryTheory.shiftFunctor
    (CochainComplex (ModuleCat.{u} (baseRing Z)) ℤ) t).obj
      (sectionsComplex Z ((pushforwardComplex h).obj J))) a
  let S := ((sectionsComplex Z ((pushforwardComplex h).obj J)).shiftFunctorObjXIso t a a'
    (by omega)).hom
  change S'.hom (I'.hom (C'.hom (z'.hom 1))) = S.hom (I.hom (C.hom (z.hom 1)))
  refine eq_of_heq ((moduleCat_eqToHom_hom_heq (congrArg (sectionsComplex Z' J).X
    (show a + t = a' by omega)) _).trans (HEq.trans ?_ (moduleCat_eqToHom_hom_heq
      (congrArg (sectionsComplex Z ((pushforwardComplex h).obj J)).X
        (show a + t = a' by omega)) _).symm))
  refine heq_of_eq (c1.trans (Eq.trans ?_ c2.symm))
  refine (congrArg _ hz').trans (Eq.trans ?_ (congrArg _ hz).symm)
  refine i3.trans (c3.trans ?_)
  exact congrArg (fun f => ((sectionsComplex Z (((pushforwardComplex h).obj J)⟦t⟧)).iCycles a ≫
    f).hom s) hψ

/-- `H^n(X, -)` of a map of complexes, as a function. -/
abbrev cohomologyFun {S : RingedSpace.{u, u}}
    {K L : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing S)) ℤ} (f : K ⟶ L)
    (n : ℤ) :
    cohomologyModule (DerivedCategory.Q.obj K) n → cohomologyModule (DerivedCategory.Q.obj L) n :=
  ((DerivedCategory.homologyFunctor _ n).map ((baseSections S).map (DerivedCategory.Q.map f))).hom

/-- `cohomologyFun` of a composite. -/
theorem cohomologyFun_comp {S : RingedSpace.{u, u}}
    {K L M : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing S)) ℤ} (f : K ⟶ L)
    (g : L ⟶ M) (n : ℤ) (x : cohomologyModule (DerivedCategory.Q.obj K) n) :
    cohomologyFun (f ≫ g) n x = cohomologyFun g n (cohomologyFun f n x) := by
  unfold cohomologyFun
  rw [DerivedCategory.Q.map_comp, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp]
  rfl

/-- `cohomologyFun` of an identity. -/
theorem cohomologyFun_id {S : RingedSpace.{u, u}}
    (K : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing S)) ℤ) (n : ℤ)
    (x : cohomologyModule (DerivedCategory.Q.obj K) n) : cohomologyFun (𝟙 K) n x = x := by
  unfold cohomologyFun
  rw [DerivedCategory.Q.map_id, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rfl

/-- **On the shift of the direct image of a K-injective complex every class is the class of a
global cocycle.** -/
theorem exists_globalClass_pushforward_shift
    (J : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing Z')) ℤ) (hJ : J.IsKInjective)
    (t a : ℤ) (w : cohomologyModule (DerivedCategory.Q.obj (((pushforwardComplex h).obj J)⟦t⟧)) a) :
    ∃ c, globalClass (((pushforwardComplex h).obj J)⟦t⟧) a c = w := by
  have hJt : (J⟦t⟧).IsKInjective := (CochainComplex.isKInjective_shift_iff J t).2 hJ
  obtain ⟨c, hc⟩ := exists_globalClass_pushforward_of_isKInjective h (J⟦t⟧) hJt a
    (cohomologyFun (pushforwardShiftHom h J t) a w)
  let ε := ((pushforwardComplex h).commShiftIso t).hom.app J
  refine ⟨(HomologicalComplex.cyclesMap (((globalSections Z).mapHomologicalComplex
    (ComplexShape.up ℤ)).map ε) a).hom c, ?_⟩
  refine (globalClass_map (X := Z) ε a c).symm.trans ?_
  refine (congrArg (cohomologyFun ε a) hc).trans ?_
  refine (cohomologyFun_comp _ _ a w).symm.trans ?_
  refine Eq.trans ?_ (cohomologyFun_id _ a w)
  exact congrArg (fun f => cohomologyFun f a w)
    (((pushforwardComplex h).commShiftIso t).inv_hom_id_app J)

/-- The shift `K[t] ⟶ h_*(K'[t])` of a map of complexes `K ⟶ h_*K'`. -/
abbrev pushforwardShiftMap {K : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing Z)) ℤ}
    {K' : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing Z')) ℤ}
    (φ : K ⟶ (pushforwardComplex h).obj K') (t : ℤ) :
    K⟦t⟧ ⟶ (pushforwardComplex h).obj (K'⟦t⟧) :=
  φ⟦t⟧' ≫ pushforwardShiftHom h K' t

/-- The pullback commutes with the shift for a map into the direct image of a K-injective
complex. -/
theorem cohomologyPullback_shift_of_isKInjective
    {K : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing Z)) ℤ}
    (J : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing Z')) ℤ) (hJ : J.IsKInjective)
    (φ : K ⟶ (pushforwardComplex h).obj J) (t a a' : ℤ) (ha : t + a = a')
    (y : cohomologyModule (DerivedCategory.Q.obj (K⟦t⟧)) a) :
    (shiftCohomologyIso J t a a' ha).hom.hom
        ((cohomologyPullback h (pushforwardShiftMap h φ t) a).hom y) =
      (cohomologyPullback h φ a').hom ((shiftCohomologyIso K t a a' ha).hom.hom y) := by
  have n1 := (cohomologyPullback_naturality h φ (𝟙 ((pushforwardComplex h).obj J)) φ (𝟙 J)
    ((congrArg (φ ≫ ·) (CategoryTheory.Functor.map_id _ _)).trans
      (Category.comp_id _)) a' ((shiftCohomologyIso K t a a' ha).hom.hom y)).trans
        (cohomologyFun_id _ _ _)
  have n2 := ConcreteCategory.congr_hom (shiftCohomologyIso_naturality φ t a a' ha) y
  have n3 := (cohomologyPullback_naturality h (pushforwardShiftMap h φ t)
    (pushforwardShiftHom h J t) (φ⟦t⟧') (𝟙 (J⟦t⟧))
    ((congrArg (pushforwardShiftMap h φ t ≫ ·) (CategoryTheory.Functor.map_id _ _)).trans
      (Category.comp_id _)) a y).trans (cohomologyFun_id _ _ _)
  obtain ⟨c, hc⟩ := exists_globalClass_pushforward_shift h J hJ t a (cohomologyFun (φ⟦t⟧') a y)
  have key := shiftCohomologyIso_cohomologyPullback_globalClass h J t a a' ha c
  refine (congrArg (fun z => (shiftCohomologyIso J t a a' ha).hom.hom z) n3.symm).trans ?_
  refine (congrArg (fun z => (shiftCohomologyIso J t a a' ha).hom.hom
    ((cohomologyPullback h (pushforwardShiftHom h J t) a).hom z)) hc.symm).trans ?_
  refine key.trans ?_
  refine (congrArg (fun z => (cohomologyPullback h (𝟙 ((pushforwardComplex h).obj J)) a').hom
    ((shiftCohomologyIso ((pushforwardComplex h).obj J) t a a' ha).hom.hom z)) hc).trans ?_
  refine (congrArg (fun z => (cohomologyPullback h (𝟙 ((pushforwardComplex h).obj J)) a').hom z)
    n2).trans ?_
  exact n1

/-- **The pullback commutes with the shift**: for a morphism of ringed spaces `h : Z' ⟶ Z` and a
map of complexes `φ : K ⟶ h_*K'`, the pullback along the shift `K[t] ⟶ h_*(K'[t])` of `φ`,
read through the identifications `Hᵃ(-[t]) ≅ Hᵃ⁺ᵗ(-)`, is the pullback along `φ`. -/
theorem cohomologyPullback_shift
    {K : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing Z)) ℤ}
    {K' : CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing Z')) ℤ}
    (φ : K ⟶ (pushforwardComplex h).obj K') (t a a' : ℤ) (ha : t + a = a')
    (x : cohomologyModule (DerivedCategory.Q.obj (K⟦t⟧)) a) :
    (shiftCohomologyIso K' t a a' ha).hom.hom
        ((cohomologyPullback h (pushforwardShiftMap h φ t) a).hom x) =
      (cohomologyPullback h φ a').hom ((shiftCohomologyIso K t a a' ha).hom.hom x) := by
  obtain ⟨J, b, hJ, hb⟩ :=
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective Z' K'
  have : IsIso (DerivedCategory.Q.map b) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ b).2 hb
  have hinj : Function.Injective (cohomologyFun b a') :=
    (ConcreteCategory.bijective_of_isIso ((DerivedCategory.homologyFunctor _ a').map
      ((baseSections Z').map (DerivedCategory.Q.map b)))).1
  apply hinj
  have m1 := ConcreteCategory.congr_hom (shiftCohomologyIso_naturality b t a a' ha)
    ((cohomologyPullback h (pushforwardShiftMap h φ t) a).hom x)
  have m2 := cohomologyPullback_naturality h (pushforwardShiftMap h φ t)
    (pushforwardShiftMap h (φ ≫ (pushforwardComplex h).map b) t) (𝟙 (K⟦t⟧)) (b⟦t⟧')
    ((Category.assoc _ _ _).trans ((congrArg (φ⟦t⟧' ≫ ·)
      (((pushforwardComplex h).commShiftIso t).inv.naturality b).symm).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pushforwardShiftHom h J t)
          ((CategoryTheory.shiftFunctor _ t).map_comp _ _).symm).trans
            (Category.id_comp _).symm)))) a x
  have m3 := cohomologyPullback_naturality h φ (φ ≫ (pushforwardComplex h).map b) (𝟙 K) b
    (Category.id_comp _).symm a' ((shiftCohomologyIso K t a a' ha).hom.hom x)
  have m2' := (congrArg (cohomologyPullback h
    (pushforwardShiftMap h (φ ≫ (pushforwardComplex h).map b) t) a).hom
      (cohomologyFun_id _ _ x)).symm.trans m2
  have m3' := (congrArg (cohomologyPullback h (φ ≫ (pushforwardComplex h).map b) a').hom
    (cohomologyFun_id _ _ ((shiftCohomologyIso K t a a' ha).hom.hom x))).symm.trans m3
  refine m1.symm.trans ?_
  refine (congrArg (fun z => (shiftCohomologyIso J t a a' ha).hom.hom z) m2'.symm).trans ?_
  exact (cohomologyPullback_shift_of_isKInjective h J hJ _ t a a' ha x).trans m3'

end PullbackShift

/-! ### Pullback -/

section HodgePullback

open Stacks.DeRhamBaseChange Stacks.DeRhamDirectImage
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces (pushforwardComplex)

variable {X X' S S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
  (w : g' ≫ f = f' ≫ g)

/-- The summand `Ω^p_{X/S}[-p]` of the Hodge complex of `f : X ⟶ S`, as a complex of modules over
the ringed space `(X, f⁻¹𝒪_S)`. -/
abbrev hodgeSummandOf {X S : Scheme.{u}} (f : X ⟶ S) (p : ℕ) :
    CochainComplex (_root_.SheafOfModules.{u} (structureSheafRing (inverseImageBase f))) ℤ :=
  hodgeSummand (X := X.toRingedSpace)
    (A := (TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)
    (formsAlgebras f) p

/-- The canonical map of Hodge complexes on the summand `Ω^p[-p]`:
`Ω^p_{X/S}[-p] ⟶ ℋ_{X/S} ⟶ (g₀)_*ℋ_{X'/S'} ⟶ (g₀)_*Ω^p_{X'/S'}[-p]`. -/
def hodgeSummandPushforward (p : ℕ) :
    hodgeSummandOf f p ⟶
      (pushforwardComplex (inverseImageBaseMap g' f' f g w)).obj (hodgeSummandOf f' p) :=
  hodgeSummandι (formsAlgebras f) p ≫ hodgeDgaPushforward g' f' f g w ≫
    (pushforwardComplex (inverseImageBaseMap g' f' f g w)).map (hodgeSummandπ (formsAlgebras f') p)

/-- The canonical map of Hodge complexes restricts to the summands. -/
theorem hodgeSummandPushforward_comp_ι (p : ℕ) :
    hodgeSummandPushforward g' f' f g w p ≫
        (pushforwardComplex (inverseImageBaseMap g' f' f g w)).map
          (hodgeSummandι (formsAlgebras f') p) =
      hodgeSummandι (formsAlgebras f) p ≫ hodgeDgaPushforward g' f' f g w := by
  refine HomologicalComplex.from_single_hom_ext ?_
  have e1 : (StacksDraft.KFlat.modulePushforward (inverseImageBaseMap g' f' f g w)).map
        ((hodgeSummandπ (formsAlgebras f') p).f (p : ℤ)) ≫
      (StacksDraft.KFlat.modulePushforward (inverseImageBaseMap g' f' f g w)).map
        ((hodgeSummandι (formsAlgebras f') p).f (p : ℤ)) = 𝟙 _ :=
    ((CategoryTheory.Functor.map_comp _ _ _).symm.trans
      (congrArg _ (hodgeSummandπ_ι_f_self (formsAlgebras f') p))).trans
        (CategoryTheory.Functor.map_id _ _)
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) e1).trans (Category.comp_id _))))

/-- `Ω^p_{X/S}[-p] ≅ Ω^p_{X/S}[0][-p]`, the shift taken in the complexes of modules over
`(X, f⁻¹𝒪_S)`. -/
def hodgeSummandFormsShiftIso {X S : Scheme.{u}} (f : X ⟶ S) (p : ℕ) :
    hodgeSummandOf f p ≅ (CategoryTheory.shiftFunctor (CochainComplex
      (_root_.SheafOfModules.{u} (structureSheafRing (inverseImageBase f))) ℤ) (-(p : ℤ))).obj
        (formsSingle f p) :=
  hodgeSummandShiftIso (formsAlgebras f) p ≪≫
    shiftBridge (S := baseRingedSpace ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf))
      (singleInt (A := (TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)
        (deRhamTerm (formsAlgebras f) p)) (-(p : ℤ))

/-- In degree `p` the identification `Ω^p[-p] ≅ Ω^p[0][-p]` is an identification of
objects. -/
theorem exists_eqToHom_hodgeSummandFormsShiftIso_hom_f {X S : Scheme.{u}} (f : X ⟶ S) (p : ℕ) :
    ∃ h, (hodgeSummandFormsShiftIso f p).hom.f (p : ℤ) = eqToHom h := by
  obtain ⟨e, he⟩ := exists_eqToHom_hodgeSummandShiftIso_hom_f (formsAlgebras f) p
  exact ⟨e, (congrArg (· ≫ 𝟙 _) he).trans (Category.comp_id _)⟩

/-- In degree `p` the projection `ℋ ⟶ Ω^p[-p]` is an identification of objects. -/
theorem exists_eqToHom_hodgeSummandπ_f {X : RingedSpace.{u, u}}
    {A : TopCat.Sheaf CommRingCat.{u} X.carrier}
    {φ : A ⟶ X.sheaf} (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ)) (p : ℕ) :
    ∃ h, (hodgeSummandπ B p).f (p : ℤ) = eqToHom h := by
  rw [hodgeSummandπ, HomologicalComplex.mkHomToSingle_f, Category.id_comp]
  exact exists_eqToHom_singleObjXSelf_inv _ _

/-- The degree-`k` component of the canonical map `Ω^p[0] ⟶ g₀_*Ω^p[0]`, for `k = 0`, on local
sections. -/
theorem formsSinglePushforward_f_val_app_heq_of_eq (p : ℕ) (k : ℤ) (hk : k = 0)
    (U : (Opens X.carrier)ᵒᵖ) (z : ((formsSingle f p).X k).val.obj U) :
    ∃ z' : Γ(Scheme.Hom.relativeDifferentialForms f (p : ℤ), U.unop), HEq z z' ∧
      HEq (((formsSinglePushforward g' f' f g w p).f k).val.app U z)
        (Scheme.Hom.relativeDifferentialFormsPullback g' f f' g w (p : ℤ) U.unop z') := by
  subst hk
  exact ⟨z, HEq.rfl, formsSinglePushforward_f_zero_val_app_heq g' f' f g w p U z⟩

/-- **The canonical map of the summands is the shift of the canonical map of forms in degree
`0`.** -/
theorem hodgeSummandPushforward_comp_shiftIso (p : ℕ) :
    hodgeSummandPushforward g' f' f g w p ≫
        (pushforwardComplex (inverseImageBaseMap g' f' f g w)).map
          (hodgeSummandFormsShiftIso f' p).hom =
      (hodgeSummandFormsShiftIso f p).hom ≫ pushforwardShiftMap (inverseImageBaseMap g' f' f g w)
        (formsSinglePushforward g' f' f g w p) (-(p : ℤ)) := by
  refine HomologicalComplex.from_single_hom_ext ?_
  refine _root_.SheafOfModules.Hom.ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun ω => ?_))
  obtain ⟨e₁, he₁⟩ := exists_eqToHom_hodgeSummandι_f (formsAlgebras f) p
  obtain ⟨e₂, he₂⟩ := exists_eqToHom_hodgeSummandπ_f (formsAlgebras f') p
  obtain ⟨e₃, he₃⟩ := exists_eqToHom_hodgeSummandFormsShiftIso_hom_f f' p
  obtain ⟨e₄, he₄⟩ := exists_eqToHom_hodgeSummandFormsShiftIso_hom_f f p
  let F := StacksDraft.KFlat.modulePushforward (inverseImageBaseMap g' f' f g w)
  have hι : HEq (((hodgeSummandι (formsAlgebras f) p).f (p : ℤ)).val.app U ω) ω := by
    rw [he₁]
    exact Stacks.DeRhamSmooth.eqToHom_val_app_heq_of_eq _ _ _
  have hB : HEq (((hodgeSummandFormsShiftIso f p).hom.f (p : ℤ)).val.app U ω) ω := by
    rw [he₄]
    exact Stacks.DeRhamSmooth.eqToHom_val_app_heq_of_eq _ _ _
  obtain ⟨z', hz, hR⟩ := formsSinglePushforward_f_val_app_heq_of_eq g' f' f g w p
    ((p : ℤ) + -(p : ℤ)) (by omega) U (((hodgeSummandFormsShiftIso f p).hom.f (p : ℤ)).val.app U ω)
  have hD := hodgeDgaPushforward_f_app_heq g' f' f g w (p : ℤ) p rfl U
    (((hodgeSummandι (formsAlgebras f) p).f (p : ℤ)).val.app U ω) z' (hι.trans (hB.symm.trans hz))
  have hA : ∀ y, HEq ((F.map ((hodgeSummandFormsShiftIso f' p).hom.f (p : ℤ))).val.app U
      ((F.map ((hodgeSummandπ (formsAlgebras f') p).f (p : ℤ))).val.app U y)) y := by
    intro y
    rw [he₂, he₃]
    exact (Stacks.DeRhamSmooth.map_eqToHom_val_app_heq F e₃ U _).trans
      (Stacks.DeRhamSmooth.map_eqToHom_val_app_heq F e₂ U y)
  exact eq_of_heq ((hA _).trans (hD.trans hR.symm))

/-- `hodgeSummandCohomologyIso` for a morphism of schemes, through the shift of `Ω^p[0]` in the
complexes of modules over `(X, f⁻¹𝒪_S)`. -/
theorem hodgeSummandCohomologyIso_hom_apply_formsShift {X S : Scheme.{u}} (f : X ⟶ S) (p : ℕ)
    (n q : ℤ) (h : -(p : ℤ) + n = q)
    (a : cohomologyModule (DerivedCategory.Q.obj (hodgeSummandOf f p)) n) :
    (hodgeSummandCohomologyIso (formsAlgebras f) p n q h).hom.hom a =
      (shiftCohomologyIso (S := baseRingedSpace ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
        S.sheaf)) (singleInt (A := (TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)
          (deRhamTerm (formsAlgebras f) p)) (-(p : ℤ)) n q h).hom.hom
        (cohomologyFun (S := baseRingedSpace ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
          S.sheaf)) (hodgeSummandFormsShiftIso f p).hom n a) :=
  congrArg (fun z => (shiftCohomologyIso (S := baseRingedSpace
    ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf))
      (singleInt (A := (TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)
        (deRhamTerm (formsAlgebras f) p)) (-(p : ℤ)) n q h).hom.hom z)
    (cohomologyFun_comp (S := baseRingedSpace ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
      S.sheaf)) (hodgeSummandShiftIso (formsAlgebras f) p).hom
      (shiftBridge (S := baseRingedSpace ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj
        S.sheaf)) (singleInt (A := (TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)
          (deRhamTerm (formsAlgebras f) p)) (-(p : ℤ))).hom n a).symm

/-- **The identification `H^n(X, Ω^p[-p]) ≅ H^q(X, Ω^p)` is compatible with pullback.** -/
theorem hodgeSummandCohomologyIso_cohomologyPullback (p : ℕ) (n q : ℤ) (h : -(p : ℤ) + n = q)
    (a : cohomologyModule (DerivedCategory.Q.obj (hodgeSummandOf f p)) n) :
    (hodgeSummandCohomologyIso (formsAlgebras f') p n q h).hom.hom
        ((cohomologyPullback (inverseImageBaseMap g' f' f g w)
          (hodgeSummandPushforward g' f' f g w p) n).hom a) =
      hodgePullback g' f' f g w p q
        ((hodgeSummandCohomologyIso (formsAlgebras f) p n q h).hom.hom a) := by
  have n1 := cohomologyPullback_naturality (inverseImageBaseMap g' f' f g w)
    (hodgeSummandPushforward g' f' f g w p)
    (hodgeSummandPushforward g' f' f g w p ≫
      (pushforwardComplex (inverseImageBaseMap g' f' f g w)).map
      (hodgeSummandFormsShiftIso f' p).hom) (𝟙 _) (hodgeSummandFormsShiftIso f' p).hom
    (Category.id_comp _).symm n a
  have n2 := cohomologyPullback_naturality (inverseImageBaseMap g' f' f g w)
    ((hodgeSummandFormsShiftIso f p).hom ≫ pushforwardShiftMap (inverseImageBaseMap g' f' f g w)
      (formsSinglePushforward g' f' f g w p) (-(p : ℤ)))
    (pushforwardShiftMap (inverseImageBaseMap g' f' f g w)
      (formsSinglePushforward g' f' f g w p) (-(p : ℤ)))
    (hodgeSummandFormsShiftIso f p).hom (𝟙 _)
    ((congrArg (_ ≫ ·) (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)) n a
  have e1 := cohomologyPullback_shift (inverseImageBaseMap g' f' f g w)
    (formsSinglePushforward g' f' f g w p) (-(p : ℤ)) n q h
    (cohomologyFun (hodgeSummandFormsShiftIso f p).hom n a)
  refine (hodgeSummandCohomologyIso_hom_apply_formsShift f' p n q h _).trans ?_
  refine (congrArg (fun z => (shiftCohomologyIso (formsSingle f' p) (-(p : ℤ)) n q h).hom.hom z)
    (((congrArg (cohomologyPullback (inverseImageBaseMap g' f' f g w) _ n).hom
      (cohomologyFun_id _ n a)).symm.trans n1).symm)).trans ?_
  refine (congrArg (fun z => (shiftCohomologyIso (formsSingle f' p) (-(p : ℤ)) n q h).hom.hom
    ((cohomologyPullback (inverseImageBaseMap g' f' f g w) z n).hom a))
      (hodgeSummandPushforward_comp_shiftIso g' f' f g w p)).trans ?_
  refine (congrArg (fun z => (shiftCohomologyIso (formsSingle f' p) (-(p : ℤ)) n q h).hom.hom z)
    (n2.trans (cohomologyFun_id _ n _)).symm).trans ?_
  refine e1.trans ?_
  exact congrArg (hodgePullback g' f' f g w p q)
    (hodgeSummandCohomologyIso_hom_apply_formsShift f p n q h a).symm

/-- The inclusion of a class of pure bidegree, written with the ringed space `(X, f⁻¹𝒪_S)`. -/
theorem hodgeIncl_eq_cohomologyFun {X S : Scheme.{u}} (f : X ⟶ S) {n : ℤ} (i : HodgeBidegreeInt n)
    (ξ : hodgeCohomologyComponent (formsAlgebras f) i.1.1 (i.1.2 : ℤ)) :
    hodgeIncl (formsAlgebras f) i ξ = cohomologyFun (S := inverseImageBase f)
      (hodgeSummandι (formsAlgebras f) i.1.1) n
        ((hodgeSummandCohomologyIso (formsAlgebras f) i.1.1 n i.1.2 i.neg_add_eq).inv.hom ξ) :=
  rfl

/-- `hodgeDgaEquiv` on the image of the cohomology of a summand. -/
theorem hodgeDgaEquiv_cohomologyFun_hodgeSummandι {X S : Scheme.{u}} (f : X ⟶ S) {n : ℤ}
    (i : HodgeBidegreeInt n)
    (z : cohomologyModule (DerivedCategory.Q.obj (hodgeSummandOf f i.1.1)) n) :
    hodgeDgaEquiv (formsAlgebras f) n (cohomologyFun (S := inverseImageBase f)
      (hodgeSummandι (formsAlgebras f) i.1.1) n z) =
      DirectSum.of _ i ((hodgeSummandCohomologyIso (formsAlgebras f) i.1.1 n i.1.2
        i.neg_add_eq).hom.hom z) :=
  (congrArg (hodgeDgaEquiv (formsAlgebras f) n) ((hodgeIncl_eq_cohomologyFun f i _).trans
    (congrArg (cohomologyFun (S := inverseImageBase f) (hodgeSummandι (formsAlgebras f) i.1.1) n)
      (ModuleCat.inv_hom_apply _ z))).symm).trans (hodgeDgaEquiv_hodgeIncl _ i _)

/-- **The identification `H^*(X, ℋ) ≅ H^*_{Hodge}(X/S)` is compatible with pullback.** For a
commutative square of schemes, the pullback on the cohomology of the Hodge complexes along the
canonical map `ℋ_{X/S} ⟶ (g₀)_*ℋ_{X'/S'}` is carried by `hodgeDgaEquiv` to the pullback
`hodgePiecePullback` on Hodge cohomology. -/
theorem hodgeDgaEquiv_pullback (n : ℤ) (x : dgaCohomology (hodgeDGA (formsAlgebras f)) n) :
    hodgeDgaEquiv (formsAlgebras f') n ((cohomologyPullback (inverseImageBaseMap g' f' f g w)
      (hodgeDgaPushforward g' f' f g w) n).hom x) =
      hodgePiecePullback g' f' f g w n (hodgeDgaEquiv (formsAlgebras f) n x) := by
  have key : ∀ (i : HodgeBidegreeInt n)
      (ξ : hodgeCohomologyComponent (formsAlgebras f) i.1.1 (i.1.2 : ℤ)),
      hodgeDgaEquiv (formsAlgebras f') n ((cohomologyPullback (inverseImageBaseMap g' f' f g w)
        (hodgeDgaPushforward g' f' f g w) n).hom (hodgeIncl (formsAlgebras f) i ξ)) =
        hodgePiecePullback g' f' f g w n (hodgeDgaEquiv (formsAlgebras f) n
          (hodgeIncl (formsAlgebras f) i ξ)) := by
    intro i ξ
    have n1 := cohomologyPullback_naturality (inverseImageBaseMap g' f' f g w)
      (hodgeSummandPushforward g' f' f g w i.1.1) (hodgeDgaPushforward g' f' f g w)
      (hodgeSummandι (formsAlgebras f) i.1.1) (hodgeSummandι (formsAlgebras f') i.1.1)
      (hodgeSummandPushforward_comp_ι g' f' f g w i.1.1) n
      ((hodgeSummandCohomologyIso (formsAlgebras f) i.1.1 n i.1.2 i.neg_add_eq).inv.hom ξ)
    refine (congrArg (fun y => hodgeDgaEquiv (formsAlgebras f') n
      ((cohomologyPullback (inverseImageBaseMap g' f' f g w)
        (hodgeDgaPushforward g' f' f g w) n).hom y)) (hodgeIncl_eq_cohomologyFun f i ξ)).trans ?_
    refine (congrArg (hodgeDgaEquiv (formsAlgebras f') n) n1).trans ?_
    refine (hodgeDgaEquiv_cohomologyFun_hodgeSummandι f' i _).trans ?_
    refine (congrArg (DirectSum.of _ i) ((hodgeSummandCohomologyIso_cohomologyPullback g' f' f g w
      i.1.1 n i.1.2 i.neg_add_eq _).trans (congrArg (hodgePullback g' f' f g w i.1.1 (i.1.2 : ℤ))
        (ModuleCat.hom_inv_apply _ ξ)))).trans ?_
    exact (hodgePiecePullback_of g' f' f g w n i ξ).symm.trans
      (congrArg (hodgePiecePullback g' f' f g w n) (hodgeDgaEquiv_hodgeIncl _ i ξ).symm)
  have hx := sum_hodgeIncl_hodgeProj (formsAlgebras f) n x
  refine (congrArg (fun y => hodgeDgaEquiv (formsAlgebras f') n
    ((cohomologyPullback (inverseImageBaseMap g' f' f g w)
      (hodgeDgaPushforward g' f' f g w) n).hom y)) hx.symm).trans (Eq.trans ?_
        (congrArg (fun y => hodgePiecePullback g' f' f g w n
          (hodgeDgaEquiv (formsAlgebras f) n y)) hx))
  let Φ₁ : dgaCohomology (hodgeDGA (formsAlgebras f)) n →+ hodgePiece (formsAlgebras f') n :=
    (hodgeDgaEquiv (formsAlgebras f') n).toLinearMap.toAddMonoidHom.comp
      (cohomologyPullback (inverseImageBaseMap g' f' f g w)
        (hodgeDgaPushforward g' f' f g w) n).hom.toAddMonoidHom
  let Φ₂ : dgaCohomology (hodgeDGA (formsAlgebras f)) n →+ hodgePiece (formsAlgebras f') n :=
    (hodgePiecePullback g' f' f g w n).comp
      (hodgeDgaEquiv (formsAlgebras f) n).toLinearMap.toAddMonoidHom
  exact (map_sum Φ₁ _ _).trans ((Finset.sum_congr rfl fun i _ => key i _).trans
    (map_sum Φ₂ _ _).symm)

end HodgePullback

end Stacks.HodgeWeil

end

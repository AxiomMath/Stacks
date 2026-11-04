module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.GlobalCupProductShift
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CupProductAndDerivedPushforward
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CupPairingNaturality
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomologyCompIso
public import StacksFrontier.Algebra.Homology.DerivedCategory.PostcomposedTotalRightDerived
public import StacksFrontier.Algebra.Homology.ShortComplex.MapHomologyPi
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedGlobalCupProduct.UnitEvaluation
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.NaiveCupProductSummand
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparisonBraiding
import all StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CupPairingNaturality
import all StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalCupProductOnSections

/-!
# The relative cup product on cohomology, through the Leray identification

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces.  This file sets up the
identification `Hⁿ(Y, Rf_*K) ≅ Hⁿ(X, K)` of Tag 0D5W (the Leray identification, from
`RΓ(Y, Rf_*-) = RΓ(X, -)`) as an isomorphism of `Γ(Y, 𝒪_Y)`-modules, shows that it is natural,
compatible with the units `Γ ⟶ RΓ` and with classes of global cocycles, and computes the naive
cup product of `f` on global sections and the total cup pairing on classes of global cocycles.

## Main definitions

* `Stacks.Cohomology.LerayCupPairing.restrictGlobal`: restriction of scalars along
  `f^♯ : Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)`.
* `Stacks.Cohomology.LerayCupPairing.lerayCohomologyIso`: the Leray identification
  `Hⁿ(Y, Rf_*K) ≅ res Hⁿ(X, K)`.

## Main results

* `Stacks.Cohomology.LerayCupPairing.lerayCohomologyIso_naturality`: it is natural in `K`.
* `Stacks.Cohomology.LerayCupPairing.sectionsUnitQ_comp_lerayRestrictIso`: it is compatible with
  the units `Γ ⟶ RΓ` on both sides.
* `Stacks.Cohomology.LerayCupPairing.lerayCohomologyIso_globalClass`: it sends the class of a
  global cocycle of `f_*N` to the class of the same section on `X`.
* `Stacks.Cohomology.LerayCupPairing.naiveCupProduct_unit_tmul`: the naive cup product of
  `f` on two global sections is the sheafified pure tensor.
* `Stacks.Cohomology.LerayCupPairing.totalCupPairing_globalClass`: the total cup pairing of two
  classes of global cocycles is the class of the naive cup product of the two sections.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.GlobalKunneth
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedGlobalCupProduct
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.SiteCohomologyPresheaf
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.LerayCupPairing

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- `f^♯ : Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)` on global sections. -/
abbrev globalRingHom : baseRing Y ⟶ baseRing X :=
  f.hom.c.app (op ⊤)

/-- Restriction of scalars along `f^♯ : Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)`. -/
abbrev restrictGlobal : ModuleCat.{u} (baseRing X) ⥤ ModuleCat.{u} (baseRing Y) :=
  ModuleCat.restrictScalars (globalRingHom f).hom

/-- Restriction of scalars along `f^♯` is additive. -/
instance restrictGlobal_additive : (restrictGlobal f).Additive where
  map_add := rfl

/-- Restriction of scalars along `f^♯` preserves finite limits. -/
instance restrictGlobal_preservesFiniteLimits : PreservesFiniteLimits (restrictGlobal f) :=
  inferInstanceAs (PreservesFiniteLimits (ModuleCat.restrictScalars.{u} (globalRingHom f).hom))

/-- Restriction of scalars along `f^♯` preserves finite colimits. -/
instance restrictGlobal_preservesFiniteColimits : PreservesFiniteColimits (restrictGlobal f) :=
  inferInstanceAs (PreservesFiniteColimits (ModuleCat.restrictScalars.{u} (globalRingHom f).hom))

/-- Derived sections over `f⁻¹ ⊤ = ⊤` are derived global sections on `X` with scalars restricted
along `f^♯`. -/
def preimageSectionsIso :
    baseSections X ⋙ (restrictGlobal f).mapDerivedCategory ≅ derivedPreimageSections f ⊤ :=
  totalRightDerivedMapDerivedCategoryIso (sectionsOverOpen X ⊤) (restrictGlobal f)

/-- **The Leray identification** `RΓ(Y, Rf_* -) ≅ RΓ(X, -)` (Tag 0D5W), with the right hand side
read over `Γ(Y, 𝒪_Y)` by restriction of scalars along `f^♯`. -/
def lerayRestrictIso :
    derivedPushforward f ⋙ baseSections Y ≅
      baseSections X ⋙ (restrictGlobal f).mapDerivedCategory :=
  lerayIso f ≪≫ (preimageSectionsIso f).symm

/-- **The Leray identification on cohomology** `Hⁿ(Y, Rf_*K) ≅ Hⁿ(X, K)`, as modules over
`Γ(Y, 𝒪_Y)`. -/
def lerayCohomologyIso (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (n : ℤ) :
    cohomologyModule ((derivedPushforward f).obj K) n ≅
      (restrictGlobal f).obj (cohomologyModule K n) :=
  (DerivedCategory.homologyFunctor _ n).mapIso ((lerayRestrictIso f).app K) ≪≫
    ((restrictGlobal f).mapDerivedCategoryHomologyFunctorIso n).app ((baseSections X).obj K)

/-- The Leray identification on cohomology is natural. -/
theorem lerayCohomologyIso_naturality
    {K K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))} (g : K ⟶ K') (n : ℤ) :
    (DerivedCategory.homologyFunctor _ n).map
          ((baseSections Y).map ((derivedPushforward f).map g)) ≫
        (lerayCohomologyIso f K' n).hom =
      (lerayCohomologyIso f K n).hom ≫
        (restrictGlobal f).map
          ((DerivedCategory.homologyFunctor _ n).map ((baseSections X).map g)) := by
  dsimp only [lerayCohomologyIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  rw [← Functor.map_comp_assoc]
  have h1 := (lerayRestrictIso f).hom.naturality g
  dsimp only [Functor.comp_map] at h1
  rw [h1, Functor.map_comp, Category.assoc]
  exact congrArg (_ ≫ ·) (((restrictGlobal f).mapDerivedCategoryHomologyFunctorIso n).hom.naturality
    ((baseSections X).map g))

/-- The Leray identification on cohomology, on elements. -/
theorem lerayCohomologyIso_naturality_apply
    {K K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))} (g : K ⟶ K') (n : ℤ)
    (x : cohomologyModule ((derivedPushforward f).obj K) n) :
    (lerayCohomologyIso f K' n).hom
        (((DerivedCategory.homologyFunctor _ n).map
          ((baseSections Y).map ((derivedPushforward f).map g))).hom x) =
      ((DerivedCategory.homologyFunctor _ n).map ((baseSections X).map g)).hom
        ((lerayCohomologyIso f K n).hom x) :=
  ConcreteCategory.congr_hom (lerayCohomologyIso_naturality f g n) x

/-! ### The unit `Γ ⟶ RΓ` across the Leray identification -/

/-- The identification `RΓ(X, -) ⋙ res ≅ RΓ(f⁻¹⊤, -)` on units. -/
theorem preimageSectionsIso_unit
    (Kh : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (restrictGlobal f).mapDerivedCategory.map ((derivedSectionsOverOpenUnit X ⊤).app Kh) ≫
        (preimageSectionsIso f).hom.app (DerivedCategory.Qh.obj Kh) =
      (mapDerivedCategorySourceIso (sectionsOverOpen X ⊤) (restrictGlobal f)).hom.app Kh ≫
        (derivedPreimageSectionsUnit f ⊤).app Kh := by
  have := isRightDerivedFunctor_totalRightDerived_comp
    (A := SheafOfModules.{u} (structureSheafRing X)) (homotopySectionsOverOpen X ⊤)
    (restrictGlobal f).mapDerivedCategory
  have h := Functor.rightDerivedNatTrans_app _ _
    (totalRightDerivedCompUnit (homotopySectionsOverOpen X ⊤)
      (restrictGlobal f).mapDerivedCategory)
    (derivedPreimageSectionsUnit f ⊤)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
    (mapDerivedCategorySourceIso (sectionsOverOpen X ⊤) (restrictGlobal f)).hom Kh
  rwa [totalRightDerivedCompUnit_app] at h

/-- The Leray unit at the class of a complex. -/
theorem lerayUnit_app_quotient' (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    (lerayUnit f ⊤).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) =
      (derivedSectionsOverOpenUnit Y ⊤).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            (((RingedSpaceModuleAdjunction.modulePushforward f).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K)) ≫
        (derivedSectionsOverOpen Y ⊤).map
          ((derivedPushforwardUnit f).app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) := by
  have hid : DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
      (pushforwardPreimageSectionsIso f ⊤) (ComplexShape.up ℤ)).inv.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) = 𝟙 _ :=
    DerivedCategory.Qh.map_id _
  show DerivedCategory.Qh.map _ ≫ _ ≫ _ = _
  rw [hid]
  exact Category.id_comp _

/-- The comparison of sources of the two derived functors of `res ∘ Γ`, at the class of a
complex. -/
theorem mapDerivedCategorySourceIso_hom_app_quotient'
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    (restrictGlobal f).mapDerivedCategoryFactors.inv.app
          (((sectionsOverOpen X ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        (restrictGlobal f).mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso _).inv.app
          (((sectionsOverOpen X ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
        (mapDerivedCategorySourceIso (sectionsOverOpen X ⊤) (restrictGlobal f)).hom.app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) =
      (DerivedCategory.quotientCompQhIso _).inv.app
        (((restrictGlobal f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((sectionsOverOpen X ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) := by
  have hh := (restrictGlobal f).mapDerivedCategoryFactorsh_hom_app
    (((sectionsOverOpen X ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
  have hid₁ : DerivedCategory.Qh.map
      (((restrictGlobal f).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app
        (((sectionsOverOpen X ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) = 𝟙 _ :=
    DerivedCategory.Qh.map_id _
  have hid₂ : DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
      (Iso.refl (sectionsOverOpen X ⊤ ⋙ restrictGlobal f)) (ComplexShape.up ℤ)).hom.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) = 𝟙 _ :=
    DerivedCategory.Qh.map_id _
  rw [hid₁] at hh
  show _ ≫ _ ≫ (restrictGlobal f).mapDerivedCategoryFactorsh.hom.app _ ≫
    DerivedCategory.Qh.map _ = _
  exact bridge_cancel _ ((DerivedCategory.quotientCompQhIso _).app _)
    ((restrictGlobal f).mapDerivedCategoryFactors.app _) _ _ _ hid₂ hh

/-- The unit `Γ(Y, f_*K) ⟶ RΓ(Y, f_*K)` followed by the comparison `f_* ⟶ Rf_*`, written out
on the homotopy category. -/
theorem pushforwardSectionsUnit_eq
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    sectionsUnitQ Y ⊤ ((pushforwardComplex f).obj K) ≫
        (baseSections Y).map (pushforwardComparisonQ f K) =
      (DerivedCategory.quotientCompQhIso _).inv.app
          (((sectionsOverOpen Y ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((pushforwardComplex f).obj K)) ≫
        (derivedSectionsOverOpenUnit Y ⊤).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            ((pushforwardComplex f).obj K)) ≫
        (derivedSectionsOverOpen Y ⊤).map
          ((derivedPushforwardUnit f).app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) ≫
        (derivedSectionsOverOpen Y ⊤).map ((derivedPushforward f).map
          ((DerivedCategory.quotientCompQhIso _).hom.app K)) :=
  map_cancel_mid (derivedSectionsOverOpen Y ⊤) _ _ _ _ _ _
    (Iso.hom_inv_id_app (DerivedCategory.quotientCompQhIso _)
      ((pushforwardComplex f).obj K))

/-- **The unit `Γ ⟶ RΓ` across the Leray identification**: the unit of `RΓ(Y, -)` at `f_*K`,
followed by the comparison `f_* ⟶ Rf_*` and the Leray identification, is the unit of `RΓ(X, -)`
at `K` with scalars restricted along `f^♯`. -/
theorem sectionsUnitQ_comp_lerayRestrictIso
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    sectionsUnitQ Y ⊤ ((pushforwardComplex f).obj K) ≫
        (baseSections Y).map (pushforwardComparisonQ f K) ≫
        (lerayRestrictIso f).hom.app (DerivedCategory.Q.obj K) =
      (restrictGlobal f).mapDerivedCategoryFactors.inv.app
          (((sectionsOverOpen X ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        (restrictGlobal f).mapDerivedCategory.map (sectionsUnitQ X ⊤ K) := by
  have := isIso_lerayComparison f ⊤
  have main := unit_paste _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ((preimageSectionsIso f).hom.naturality
      ((DerivedCategory.quotientCompQhIso _).hom.app K))
    ((lerayComparison f ⊤).naturality
      ((DerivedCategory.quotientCompQhIso _).hom.app K))
    (preimageSectionsIso_unit f ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
    (NatTrans.congr_app (lerayComparison_fac f ⊤)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
    (lerayUnit_app_quotient' f K) (mapDerivedCategorySourceIso_hom_app_quotient' f K)
    (pushforwardSectionsUnit_eq f K)
  have hc := cancel_two _ _ _ _ _ ((preimageSectionsIso f).app (DerivedCategory.Q.obj K))
    ((lerayIso f).symm.app (DerivedCategory.Q.obj K)) main
  rw [← Category.assoc]
  refine hc.trans ?_
  rw [sectionsUnitQ, Functor.map_comp]
  exact congrArg (fun z => _ ≫ _ ≫ z)
    ((restrictGlobal f).mapDerivedCategory.map_comp _ _).symm

/-! ### Classes of global cocycles across the Leray identification -/

/-- A diagram chase in a category: the composite `π ≫ fi ≫ u ≫ c ≫ l ≫ m` is `mc ≫ t` given the
commutation relations `key`, `hnat`, `hQ`, `hπ`, `ht` and the cancellations `ha`, `hf`. -/
private theorem leray_paste {C : Type*} [Category* C]
    {P Q0 Q1 Q2 Q3 Q4 Q5 R1 R2 R5 M0 : C}
    (π : P ⟶ Q0) (fi : Q0 ⟶ Q1) (u : Q1 ⟶ Q2) (c : Q2 ⟶ Q3) (l : Q3 ⟶ Q4) (m : Q4 ⟶ Q5)
    (a : Q1 ⟶ R1) (b : R1 ⟶ Q4) (m' : R1 ⟶ R2) (r : R2 ⟶ Q5) (a' : R1 ⟶ Q1) (fh : Q1 ⟶ Q0)
    (mh : Q0 ⟶ R5) (rf : R5 ⟶ R2) {mc : P ⟶ M0} {rπ : M0 ⟶ R5} {t : M0 ⟶ Q5}
    (key : u ≫ c ≫ l = a ≫ b) (hnat : b ≫ m = m' ≫ r) (hQ : m' = a' ≫ fh ≫ mh ≫ rf)
    (ha : a ≫ a' = 𝟙 _) (hf : fi ≫ fh = 𝟙 _) (hπ : π ≫ mh = mc ≫ rπ) (ht : t = rπ ≫ rf ≫ r) :
    π ≫ fi ≫ u ≫ c ≫ l ≫ m = mc ≫ t := by
  rw [reassoc_of% key, hnat, hQ]
  simp only [Category.assoc]
  rw [reassoc_of% ha, reassoc_of% hf, reassoc_of% hπ, ht]

/-- **The class of a global cocycle across the Leray identification**, at the level of
morphisms: a cocycle of `Γ(Y, f_*N)`, sent to `Hⁿ(Y, Rf_*N)` and then by the Leray
identification to `Hⁿ(X, N)`, is the same cocycle of `Γ(X, N)` sent to `Hⁿ(X, N)`. -/
theorem homologyπ_comp_lerayCohomologyIso
    (N : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (n : ℤ) :
    (sectionsComplex Y ((pushforwardComplex f).obj N)).homologyπ n ≫
        (DerivedCategory.homologyFunctorFactors _ n).inv.app
          (sectionsComplex Y ((pushforwardComplex f).obj N)) ≫
        (DerivedCategory.homologyFunctor _ n).map
          (sectionsUnitQ Y ⊤ ((pushforwardComplex f).obj N)) ≫
        (DerivedCategory.homologyFunctor _ n).map
          ((baseSections Y).map (pushforwardComparisonQ f N)) ≫
        (lerayCohomologyIso f (DerivedCategory.Q.obj N) n).hom =
      (((sectionsComplex X N).sc n).mapCyclesIso (restrictGlobal f)).hom ≫
        (restrictGlobal f).map ((sectionsComplex X N).homologyπ n ≫
          (DerivedCategory.homologyFunctorFactors _ n).inv.app (sectionsComplex X N) ≫
          (DerivedCategory.homologyFunctor _ n).map (sectionsUnitQ X ⊤ N)) := by
  have key : (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing Y)) n).map
        (sectionsUnitQ Y ⊤ ((pushforwardComplex f).obj N)) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing Y)) n).map
        ((baseSections Y).map (pushforwardComparisonQ f N)) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing Y)) n).map
        ((lerayRestrictIso f).hom.app (DerivedCategory.Q.obj N)) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing Y)) n).map
        ((restrictGlobal f).mapDerivedCategoryFactors.inv.app (sectionsComplex X N)) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing Y)) n).map
        ((restrictGlobal f).mapDerivedCategory.map (sectionsUnitQ X ⊤ N)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing Y)) n).map
      (sectionsUnitQ_comp_lerayRestrictIso f N)
  have hQ := (restrictGlobal f).mapDerivedCategoryHomologyFunctorIso_hom_app_Q n
    (sectionsComplex X N)
  have hnat := ((restrictGlobal f).mapDerivedCategoryHomologyFunctorIso n).hom.naturality
    (sectionsUnitQ X ⊤ N)
  have hπ := ((sectionsComplex X N).sc n).homologyπ_comp_mapHomologyIso_hom (restrictGlobal f)
  exact leray_paste _ _ _ _ _ _ _ _ _ _ _ _ _ _ key hnat hQ
    ((CategoryTheory.Functor.map_comp _ _ _).symm.trans ((congrArg _ (Iso.inv_hom_id_app _ _)).trans
      (CategoryTheory.Functor.map_id _ _)))
    (Iso.inv_hom_id_app _ _) hπ ((restrictGlobal f).map_comp _ _ |>.trans
      (congrArg ((restrictGlobal f).map _ ≫ ·) ((restrictGlobal f).map_comp _ _)))

/-- **The class of a global cocycle across the Leray identification**, on elements: for a
cocycle `s` of `Γ(Y, f_*N) = Γ(X, N)`, the Leray identification sends the image in
`Hⁿ(Y, Rf_*N)` of its class on `Y` to its class on `X`. -/
theorem lerayCohomologyIso_globalClass
    (N : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (n : ℤ)
    (sY : (sectionsComplex Y ((pushforwardComplex f).obj N)).cycles n)
    (sX : (sectionsComplex X N).cycles n)
    (h : ((sectionsComplex Y ((pushforwardComplex f).obj N)).iCycles n).hom sY =
      ((sectionsComplex X N).iCycles n).hom sX) :
    (lerayCohomologyIso f (DerivedCategory.Q.obj N) n).hom
        (((DerivedCategory.homologyFunctor _ n).map
          ((baseSections Y).map (pushforwardComparisonQ f N))).hom
            (globalClass ((pushforwardComplex f).obj N) n sY)) =
      globalClass N n sX := by
  have e := ConcreteCategory.congr_hom (homologyπ_comp_lerayCohomologyIso f N n) sY
  have hc : (((sectionsComplex X N).sc n).mapCyclesIso (restrictGlobal f)).hom.hom sY = sX :=
    (ModuleCat.mono_iff_injective ((sectionsComplex X N).iCycles n)).1 inferInstance
      ((ConcreteCategory.congr_hom
        (((sectionsComplex X N).sc n).mapCyclesIso_hom_iCycles (restrictGlobal f)) sY).trans h)
  exact e.trans (congrArg (ConcreteCategory.hom ((restrictGlobal f).map
    ((sectionsComplex X N).homologyπ n ≫
      (DerivedCategory.homologyFunctorFactors _ n).inv.app (sectionsComplex X N) ≫
      (DerivedCategory.homologyFunctor _ n).map (sectionsUnitQ X ⊤ N)))) hc)

/-! ### The naive cup product of `f` on global sections -/

section Naive

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
open scoped Stacks.Topology.SheafTensorAdditiveOnOpens

open Stacks.Cohomology.NaiveCupProductOnRingedSpaces Stacks.RingedSpace
open _root_.PresheafOfModules
open scoped TensorProduct

/-- **The naive cup product of `f` on a summand of global sections**: for global sections `x` of
`K^a` and `y` of `M^b`, the sheafification-unit image of `x ⊗ y` on the `(a, b)` summand of
`Tot(f_*K ⊗ f_*M)` is carried by the naive cup product of Tag 0FP3 to the sheafification-unit
image of `x ⊗ y` on the `(a, b)` summand of `Tot(K ⊗ M)`. -/
theorem naiveCupProduct_unit_tmul
    (K M : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)
    (a b n : ℤ) (h : a + b = n)
    (x : ((pushforwardFunctor f).obj (K.X a)).val.obj (op ⊤))
    (y : ((pushforwardFunctor f).obj (M.X b)).val.obj (op ⊤)) :
    Hom.app ((naiveCupProduct f K M).f n).val (op ⊤)
        (Hom.app (HomologicalComplex.ιMapBifunctor
            ((pushforwardComplex f).obj K) ((pushforwardComplex f).obj M)
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf)
            (ComplexShape.up ℤ) a b n h).val (op ⊤)
          (Hom.app ((PresheafOfModules.sheafificationAdjunction (R := structureRingSheaf Y)
              (𝟙 (structureRingSheaf Y).obj)).unit.app
            (PresheafOfModules.tensorObj (O := Y.presheaf)
              ((pushforwardFunctor f).obj (K.X a)).val
              ((pushforwardFunctor f).obj (M.X b)).val)) (op ⊤) (x ⊗ₜ y))) =
      Hom.app (HomologicalComplex.ιMapBifunctor K M
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)
          (ComplexShape.up ℤ) a b n h).val (op ⊤)
        (Hom.app ((PresheafOfModules.sheafificationAdjunction (R := structureRingSheaf X)
            (𝟙 (structureRingSheaf X).obj)).unit.app
          (PresheafOfModules.tensorObj (O := X.presheaf) (K.X a).val (M.X b).val))
          (op ⊤) (x ⊗ₜ y)) :=
  (hom_congr_apply' (congrArg (fun z ↦ SheafOfModules.Hom.val z)
      (Stacks.Cohomology.NaiveCupProductSummand.ι_naiveCupProduct f K M a b n h)) (op ⊤) _).trans
    (congrArg
      (fun z => Hom.app ((pushforwardFunctor f).map
        (HomologicalComplex.ιMapBifunctor K M
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)
          (ComplexShape.up ℤ) a b n h)).val (op ⊤) z)
      (pushforwardTensorMap_unit_tmul f (K.X a) (M.X b) (op ⊤) x y))

/-- **The naive cup product on global sections, on a pure tensor**: on the `(a, b)` summand, the
naive cup product `Tot(Γ(Z, K) ⊗ Γ(Z, M)) ⟶ Γ(Z, Tot(K ⊗ M))` sends `x ⊗ y` to the
sheafification-unit image of `x ⊗ y` on the `(a, b)` summand of `Tot(K ⊗ M)`. -/
theorem naiveCupProductEval_ι_tmul (Z : RingedSpace.{u, u})
    (K M : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z.sheaf)) ℤ)
    (a b n : ℤ) (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (a, b) = n)
    (x : (Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ K).X a)
    (y : (Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ M).X b) :
    ((HomologicalComplex.ιMapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ K)
        (Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ M)
        (Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing Z.sheaf ⊤))
        (ComplexShape.up ℤ) a b n h ≫
      (Stacks.Cech.SheafTensorPairing.naiveCupProductEval Z.sheaf ⊤ K M).f n).hom (x ⊗ₜ y)) =
      Hom.app (HomologicalComplex.ιMapBifunctor K M
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf)
          (ComplexShape.up ℤ) a b n h).val (op ⊤)
        (Hom.app ((PresheafOfModules.sheafificationAdjunction (R := structureRingSheaf Z)
            (𝟙 (structureRingSheaf Z).obj)).unit.app
          (PresheafOfModules.tensorObj (O := Z.presheaf) (K.X a).val (M.X b).val))
          (op ⊤) (x ⊗ₜ y)) := by
  rw [Stacks.Cech.SheafTensorPairing.naiveCupProductEval_ι]
  rfl

end Naive

/-! ### The total cup pairing on classes of global cocycles, on elements -/

section Base

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
open scoped Stacks.Topology.SheafTensorAdditiveOnOpens
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces Stacks.RingedSpace
open Stacks.Cohomology.DerivedPullbackTensor (derivedToTensorNatTrans totalComplexPair)
open _root_.PresheafOfModules
open scoped TensorProduct

/-- **The total cup pairing on classes of global cocycles, on elements**: for global cocycles `s`
of `K` and `t` of `M`, the cup product of their classes followed by `RΓ` of the canonical map to
the total tensor complex is the class of the global cocycle of `Tot(K ⊗ M)` whose underlying
section is the naive cup product of the two underlying sections. -/
theorem totalCupPairing_globalClass (Z : RingedSpace.{u, u})
    (K M : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z.sheaf)) ℤ) (i j : ℤ)
    (s : (sectionsComplex Z K).cycles i) (t : (sectionsComplex Z M).cycles j)
    (z₀ : ((Stacks.Cech.CupProduct.tensorModules
          (Stacks.Cech.ModuleCupProduct.CoeffRing Z.sheaf ⊤)).obj
          ((Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ K).cycles i)).obj
          ((Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ M).cycles j) ⟶
        (HomologicalComplex.mapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ K)
          (Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ M)
          (Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing Z.sheaf ⊤))
          (ComplexShape.up ℤ)).cycles (i + j))
    (hz₀ : z₀ ≫ (HomologicalComplex.mapBifunctor
          (Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ K)
          (Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ M)
          (Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing Z.sheaf ⊤))
          (ComplexShape.up ℤ)).iCycles (i + j) =
        Stacks.Cech.SheafTensorPairing.tensorMap Z.sheaf ⊤
            ((Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ K).iCycles i)
            ((Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ M).iCycles j) ≫
          HomologicalComplex.ιMapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ K)
            (Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ M)
            (Stacks.Cech.CupProduct.tensorModules
              (Stacks.Cech.ModuleCupProduct.CoeffRing Z.sheaf ⊤))
            (ComplexShape.up ℤ) i j (i + j) rfl) :
    (totalCupPairing K M i j).hom (globalClass K i s ⊗ₜ globalClass M j t) =
      globalClass _ (i + j) ((z₀ ≫ HomologicalComplex.cyclesMap
          (Stacks.Cech.SheafTensorPairing.naiveCupProductEval Z.sheaf ⊤ K M) (i + j)).hom
        (s ⊗ₜ t)) := by
  let z := ModuleCat.ofHom (LinearMap.toSpanSingleton (baseRing Z) _ s)
  let w := ModuleCat.ofHom (LinearMap.toSpanSingleton (baseRing Z) _ t)
  have e := ConcreteCategory.congr_hom (totalCupPairing_globalCycleClass_naive K M z w z₀ hz₀)
    (1 : baseRing Z)
  have hu : ∀ {P Q T : ModuleCat.{u} (baseRing Z)} (u : ModuleCat.of (baseRing Z) (baseRing Z) ⟶ P)
      (v : ModuleCat.of (baseRing Z) (baseRing Z) ⟶ Q) (h : P ⊗ Q ⟶ T) (p : P) (q : Q),
      u 1 = p → v 1 = q → ((λ_ (ModuleCat.of (baseRing Z) (baseRing Z))).inv ≫
        (u ⊗ₘ v) ≫ h).hom 1 = h.hom (p ⊗ₜ q) := fun u v h _ _ hp hq =>
    (leftUnitor_inv_tensorHom_comp_apply_one u v h).trans
      (congrArg h.hom (congrArg₂ (· ⊗ₜ ·) hp hq))
  have hL := hu (globalCycleClass z) (globalCycleClass w) (totalCupPairing K M i j)
    (globalClass K i s) (globalClass M j t)
    (congrArg (globalClass K i) (one_smul (baseRing Z) s))
    (congrArg (globalClass M j) (one_smul (baseRing Z) t))
  have hR := hu z w (z₀ ≫ HomologicalComplex.cyclesMap
    (Stacks.Cech.SheafTensorPairing.naiveCupProductEval Z.sheaf ⊤ K M) (i + j)) s t
    (one_smul (baseRing Z) s) (one_smul (baseRing Z) t)
  exact hL.symm.trans (e.trans (congrArg (globalClass _ (i + j))
    ((congrArg (fun g => ((λ_ (ModuleCat.of (baseRing Z) (baseRing Z))).inv ≫ g ≫ _).hom 1)
      (Stacks.Cech.SheafTensorPairing.tensorMap_eq_tensorHom Z.sheaf ⊤ z w)).trans hR)))

/-- The cocycle `z₀ ≫ cyclesMap (naiveCupProductEval K M)` has, as underlying section of
`Tot(K ⊗ M)`, the naive cup product of the underlying sections of the two factors. -/
theorem iCycles_totalCupPairing_cycle (Z : RingedSpace.{u, u})
    (K M : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z.sheaf)) ℤ) (i j : ℤ)
    (z₀ : ((Stacks.Cech.CupProduct.tensorModules
          (Stacks.Cech.ModuleCupProduct.CoeffRing Z.sheaf ⊤)).obj
          ((Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ K).cycles i)).obj
          ((Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ M).cycles j) ⟶
        (HomologicalComplex.mapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ K)
          (Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ M)
          (Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing Z.sheaf ⊤))
          (ComplexShape.up ℤ)).cycles (i + j))
    (hz₀ : z₀ ≫ (HomologicalComplex.mapBifunctor
          (Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ K)
          (Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ M)
          (Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing Z.sheaf ⊤))
          (ComplexShape.up ℤ)).iCycles (i + j) =
        Stacks.Cech.SheafTensorPairing.tensorMap Z.sheaf ⊤
            ((Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ K).iCycles i)
            ((Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ M).iCycles j) ≫
          HomologicalComplex.ιMapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ K)
            (Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ M)
            (Stacks.Cech.CupProduct.tensorModules
              (Stacks.Cech.ModuleCupProduct.CoeffRing Z.sheaf ⊤))
            (ComplexShape.up ℤ) i j (i + j) rfl) :
    (z₀ ≫ HomologicalComplex.cyclesMap
          (Stacks.Cech.SheafTensorPairing.naiveCupProductEval Z.sheaf ⊤ K M) (i + j)) ≫
        (Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤
          (HomologicalComplex.mapBifunctor K M (Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf)
            (ComplexShape.up ℤ))).iCycles (i + j) =
      Stacks.Cech.SheafTensorPairing.tensorMap Z.sheaf ⊤
          ((Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ K).iCycles i)
          ((Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ M).iCycles j) ≫
        HomologicalComplex.ιMapBifunctor (Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ K)
          (Stacks.Cech.SheafTensorPairing.evalComplex Z.sheaf ⊤ M)
          (Stacks.Cech.CupProduct.tensorModules (Stacks.Cech.ModuleCupProduct.CoeffRing Z.sheaf ⊤))
          (ComplexShape.up ℤ) i j (i + j) rfl ≫
        (Stacks.Cech.SheafTensorPairing.naiveCupProductEval Z.sheaf ⊤ K M).f (i + j) := by
  rw [Category.assoc, HomologicalComplex.cyclesMap_i, reassoc_of% hz₀]
  simp only [Stacks.Cech.SheafTensorPairing.tensorMap, Category.assoc]

end Base

end Stacks.Cohomology.LerayCupPairing

end

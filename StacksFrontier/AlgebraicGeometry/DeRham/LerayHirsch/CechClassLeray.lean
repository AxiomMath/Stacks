module

public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.CechClassRingChange
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayCupPairing
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayCupPairingBase
public import StacksFrontier.Homology.KFlat.Flat
public import Mathlib.Algebra.Homology.Factorizations.CM5a

/-!
# Čech classes and the Leray identification for a change of rings over the identity

Let `h : (X, 𝒜) ⟶ (X, 𝒜')` be a morphism of ringed spaces which is the identity on the underlying
space, `U` an open covering of `X` and `M` a bounded below complex of `𝒜`-modules vanishing in
negative degrees. There are two ways to send a cocycle of the total Čech complex of `h_*M` (over
`𝒜'`) to `Hⁿ(X, M)`: the Čech class over `𝒜'` followed by the comparison `h_* ⟶ Rh_*` and the
Leray identification (`Stacks.Cech.RingChange.sideA'`), and the Čech class over `𝒜` of the same
cocycle, read through the identification `Stacks.Cech.RingChange.ecl` of the two total Čech
complexes (`Stacks.Cech.RingChange.sideA`). This file sets up both, with their naturality in `M`,
and the compatibility of `ecl` with differentials and with the augmentation of
[Stacks, Tag 07M9].

## Main definitions

* `Stacks.Cech.RingChange.cls`: the class of a cocycle.
* `Stacks.Cech.RingChange.sideA`, `Stacks.Cech.RingChange.sideA'`, `Stacks.Cech.RingChange.ecl`.

## Main results

* `Stacks.Cech.RingChange.ecl_d`, `Stacks.Cech.RingChange.ecl_naturality`,
  `Stacks.Cech.RingChange.ecl_sectionsToTotalCech`.
* `Stacks.Cech.RingChange.sideA_naturality`, `Stacks.Cech.RingChange.sideA'_naturality`.
* `Stacks.Cech.RingChange.sideA'_cls`: the two class maps agree on every cocycle.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace ComplexShape
open AlgebraicGeometry
open AlgebraicGeometry.SheafOfModules (baseRingedSpace)
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing coverObject)
open Stacks.CategoryTheory.CechComplex
open Stacks.Cech.Hypercohomology (cechClass hypercohomologyMap toMor toMor_comp unitModule)
open Stacks.Cohomology.GlobalKunneth Stacks.Cohomology.DerivedGlobalCupProduct
open Stacks.Cohomology.DerivedSectionsLeray Stacks.Cohomology.LerayCupPairing
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces

universe u

namespace Stacks.Cech.RingChange

/-! ### Classes of cocycles -/

section Classes

variable {R : Type u} [Ring R] (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- The morphism `R ⟶ K.X n` sending `1` to a cocycle `z` composes to zero with the
differential. -/
theorem toMor_comp_d_eq_zero {n : ℤ} {z : K.X n} (hz : (K.d n (n + 1)).hom z = 0) :
    toMor z ≫ K.d n (n + 1) = 0 := by
  rw [toMor_comp, hz]
  ext : 1
  exact LinearMap.ext_ring (by simp [toMor])

/-- The cohomology class of a cocycle. -/
def cls (n : ℤ) (z : K.X n) (hz : (K.d n (n + 1)).hom z = 0) : K.homology n :=
  (K.homologyπ n).hom
    ((K.liftCycles (toMor z) (n + 1) (CochainComplex.next ℤ n) (toMor_comp_d_eq_zero K hz)).hom 1)

/-- The cycle lifting `toMor x` maps back to `x`. -/
private theorem iCycles_liftCycles_toMor_apply (n : ℤ) (x : K.X n)
    (hx : (K.d n (n + 1)).hom x = 0) :
    (K.iCycles n).hom ((K.liftCycles (toMor x) (n + 1) (CochainComplex.next ℤ n)
      (toMor_comp_d_eq_zero K hx)).hom 1) = x :=
  (ConcreteCategory.congr_hom (K.liftCycles_i _ _ _ _) 1).trans
    (Stacks.Cech.Hypercohomology.toMor_apply_one _)

/-- The cycles lifting two cocycles `z`, `z'` have difference mapping to `z - z'`. -/
private theorem iCycles_liftCycles_toMor_sub_apply (n : ℤ) (z z' : K.X n)
    (hz : (K.d n (n + 1)).hom z = 0) (hz' : (K.d n (n + 1)).hom z' = 0) :
    (K.iCycles n).hom ((K.liftCycles (toMor z) (n + 1) (CochainComplex.next ℤ n)
        (toMor_comp_d_eq_zero K hz)).hom 1 -
      (K.liftCycles (toMor z') (n + 1) (CochainComplex.next ℤ n)
        (toMor_comp_d_eq_zero K hz')).hom 1) = z - z' := by
  rw [map_sub, iCycles_liftCycles_toMor_apply K n z hz, iCycles_liftCycles_toMor_apply K n z' hz']

/-- The image of a cycle is a cocycle. -/
private theorem d_iCycles_apply (n : ℤ) (c : K.cycles n) :
    (K.d n (n + 1)).hom ((K.iCycles n).hom c) = 0 :=
  (ConcreteCategory.congr_hom (K.iCycles_d n (n + 1)) c).trans rfl

/-- The class of the image of a cycle `c` in `K.X n` is the image of `c` in cohomology. -/
theorem cls_iCycles (n : ℤ) (c : K.cycles n) (hz : (K.d n (n + 1)).hom ((K.iCycles n).hom c) = 0) :
    cls K n ((K.iCycles n).hom c) hz = (K.homologyπ n).hom c :=
  congrArg (K.homologyπ n).hom ((ModuleCat.mono_iff_injective (K.iCycles n)).1 inferInstance
    (iCycles_liftCycles_toMor_apply K n _ hz))

/-- A morphism of complexes sends the class of a cocycle `z` to the class of the image of `z`. -/
theorem homologyMap_cls {L : CochainComplex (ModuleCat.{u} R) ℤ} (φ : K ⟶ L) (n : ℤ) (z : K.X n)
    (hz : (K.d n (n + 1)).hom z = 0) (hz' : (L.d n (n + 1)).hom ((φ.f n).hom z) = 0) :
    (HomologicalComplex.homologyMap φ n).hom (cls K n z hz) = cls L n ((φ.f n).hom z) hz' := by
  refine (ConcreteCategory.congr_hom
    (Stacks.Cech.Hypercohomology.cocycleClass_comp_homologyMap φ n (toMor z)
      (toMor_comp_d_eq_zero K hz)) 1).trans ?_
  refine congrArg (L.homologyπ n).hom ?_
  apply (ModuleCat.mono_iff_injective (L.iCycles n)).1 inferInstance
  refine (ConcreteCategory.congr_hom (L.liftCycles_i _ _ _ _) 1).trans ?_
  refine Eq.trans ?_ (ConcreteCategory.congr_hom (L.liftCycles_i _ _ _ _) 1).symm
  rw [toMor_comp]

/-- Equal cocycles have equal classes. -/
theorem cls_congr (n : ℤ) {z z' : K.X n} (e : z = z') (hz : (K.d n (n + 1)).hom z = 0)
    (hz' : (K.d n (n + 1)).hom z' = 0) : cls K n z hz = cls K n z' hz' := by
  subst e
  rfl

/-- A morphism of complexes sends cocycles to cocycles. -/
theorem d_f_apply_eq_zero {L : CochainComplex (ModuleCat.{u} R) ℤ} (φ : K ⟶ L) (n : ℤ)
    (z : K.X n) (hz : (K.d n (n + 1)).hom z = 0) : (L.d n (n + 1)).hom ((φ.f n).hom z) = 0 := by
  rw [← ConcreteCategory.comp_apply, φ.comm, ConcreteCategory.comp_apply, hz, map_zero]

/-- Cocycles differing by a coboundary have the same class. -/
theorem cls_eq_of_sub_eq_d (n : ℤ) (z z' : K.X n) (hz : (K.d n (n + 1)).hom z = 0)
    (hz' : (K.d n (n + 1)).hom z' = 0) (w : K.X (n - 1))
    (hw : z - z' = (K.d (n - 1) n).hom w) : cls K n z hz = cls K n z' hz' := by
  have e1 : (K.liftCycles (toMor z) (n + 1) (CochainComplex.next ℤ n)
        (toMor_comp_d_eq_zero K hz)).hom 1 -
      (K.liftCycles (toMor z') (n + 1) (CochainComplex.next ℤ n)
        (toMor_comp_d_eq_zero K hz')).hom 1 = (K.toCycles (n - 1) n).hom w := by
    apply (ModuleCat.mono_iff_injective (K.iCycles n)).1 inferInstance
    rw [iCycles_liftCycles_toMor_sub_apply K n z z' hz hz']
    exact hw.trans (ConcreteCategory.congr_hom (K.toCycles_i (n - 1) n) w).symm
  rw [← sub_eq_zero, cls, cls, ← map_sub, e1]
  exact ConcreteCategory.congr_hom (K.toCycles_comp_homologyπ (n - 1) n) w

/-- For an isomorphism `e : K ≅ L`, the degree `n` component of `e.inv` followed by that of `e.hom`
is the identity on elements. -/
theorem iso_inv_hom_f_apply {L : CochainComplex (ModuleCat.{u} R) ℤ} (e : K ≅ L) (n : ℤ)
    (w : L.X n) : (e.hom.f n).hom ((e.inv.f n).hom w) = w :=
  ConcreteCategory.congr_hom (HomologicalComplex.congr_hom e.inv_hom_id n) w

/-- For an isomorphism `e : K ≅ L`, the degree `n` component of `e.hom` followed by that of `e.inv`
is the identity on elements. -/
theorem iso_hom_inv_f_apply {L : CochainComplex (ModuleCat.{u} R) ℤ} (e : K ≅ L) (n : ℤ)
    (w : K.X n) : (e.inv.f n).hom ((e.hom.f n).hom w) = w :=
  ConcreteCategory.congr_hom (HomologicalComplex.congr_hom e.hom_inv_id n) w

/-- Every class is the class of a cocycle. -/
theorem exists_cls_eq (n : ℤ) (c : K.homology n) :
    ∃ (z : K.X n) (hz : (K.d n (n + 1)).hom z = 0), cls K n z hz = c := by
  obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ n)).1 inferInstance c
  exact ⟨_, d_iCycles_apply K n y, cls_iCycles K n y _⟩

omit [Ring R] in
/-- Four commutative squares pasted, stated with every object and morphism a variable. -/
theorem paste_four {C : Type*} [Category* C] {X₀ X₁ X₂ X₃ X₄ Y₀ Y₁ Y₂ Y₃ Y₄ : C}
    (cM : X₀ ⟶ X₁) (dM : X₁ ⟶ X₂) (pM : X₂ ⟶ X₃) (lM : X₃ ⟶ X₄)
    (cI : Y₀ ⟶ Y₁) (dI : Y₁ ⟶ Y₂) (pI : Y₂ ⟶ Y₃) (lI : Y₃ ⟶ Y₄)
    (v₀ : X₀ ⟶ Y₀) (v₁ : X₁ ⟶ Y₁) (v₂ : X₂ ⟶ Y₂) (v₃ : X₃ ⟶ Y₃) (v₄ : X₄ ⟶ Y₄)
    (s₁ : cM ≫ v₁ = v₀ ≫ cI) (s₂ : dM ≫ v₂ = v₁ ≫ dI) (s₃ : pM ≫ v₃ = v₂ ≫ pI)
    (s₄ : lM ≫ v₄ = v₃ ≫ lI) :
    (cM ≫ dM ≫ pM ≫ lM) ≫ v₄ = v₀ ≫ cI ≫ dI ≫ pI ≫ lI := by
  simp only [Category.assoc]
  rw [s₄, reassoc_of% s₃, reassoc_of% s₂, reassoc_of% s₁]

/-- Cocycles with the same class differ by a coboundary. -/
theorem exists_sub_eq_d_of_cls_eq {R : Type u} [Ring R] (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (n : ℤ) (z z' : K.X n) (hz : (K.d n (n + 1)).hom z = 0) (hz' : (K.d n (n + 1)).hom z' = 0)
    (e : cls K n z hz = cls K n z' hz') : ∃ w : K.X (n - 1), z - z' = (K.d (n - 1) n).hom w := by
  have h0 : (K.homologyπ n).hom ((K.liftCycles (toMor z) (n + 1) (CochainComplex.next ℤ n)
        (toMor_comp_d_eq_zero K hz)).hom 1 -
      (K.liftCycles (toMor z') (n + 1) (CochainComplex.next ℤ n)
        (toMor_comp_d_eq_zero K hz')).hom 1) = 0 :=
    (map_sub _ _ _).trans (sub_eq_zero.2 e)
  obtain ⟨w, hw⟩ := (CochainComplex.KFlat.homologyπ_eq_zero_iff K n _).1 h0
  refine ⟨w, Eq.trans ?_ hw.symm⟩
  exact (iCycles_liftCycles_toMor_sub_apply K n z z' hz hz').symm

/-- If `f ≫ g = homologyMap φ n ≫ f'`, then `g ∘ f` sends the class of a cocycle `z` to `f'` of the
class of its image under `φ`. -/
private theorem apply_cls_of_comp_eq {L : CochainComplex (ModuleCat.{u} R) ℤ}
    {P Q : ModuleCat.{u} R} (φ : K ⟶ L) (n : ℤ) (z : K.X n) (hz : (K.d n (n + 1)).hom z = 0)
    (hz' : (L.d n (n + 1)).hom ((φ.f n).hom z) = 0) {f : K.homology n ⟶ P} {g : P ⟶ Q}
    {f' : L.homology n ⟶ Q} (e : f ≫ g = HomologicalComplex.homologyMap φ n ≫ f') :
    g.hom (f.hom (cls K n z hz)) = f'.hom (cls L n ((φ.f n).hom z) hz') :=
  (ConcreteCategory.congr_hom e (cls K n z hz)).trans
    (congrArg f'.hom (homologyMap_cls K φ n z hz hz'))

/-- A cocycle differing by a coboundary from the image of a cycle `c` under `φ` has class the image
of the class of `c`. -/
private theorem cls_eq_homologyMap_homologyπ_of_sub_eq_d {L : CochainComplex (ModuleCat.{u} R) ℤ}
    (φ : K ⟶ L) (n : ℤ) (c : K.cycles n) (y : L.X n) (hy : (L.d n (n + 1)).hom y = 0)
    (w : L.X (n - 1)) (hw : y - (φ.f n).hom ((K.iCycles n).hom c) = (L.d (n - 1) n).hom w) :
    cls L n y hy = (HomologicalComplex.homologyMap φ n).hom ((K.homologyπ n).hom c) :=
  have hc := d_iCycles_apply K n c
  have hφ := d_f_apply_eq_zero K φ n _ hc
  (cls_eq_of_sub_eq_d L n _ _ hy hφ w hw).trans <| (homologyMap_cls K φ n _ hc hφ).symm.trans <|
    congrArg (HomologicalComplex.homologyMap φ n).hom (cls_iCycles K n c hc)

/-- The class of a cocycle in a zero object is zero. -/
theorem cls_eq_zero_of_isZero (n : ℤ) (hK : IsZero (K.X n)) (z : K.X n)
    (hz : (K.d n (n + 1)).hom z = 0) : cls K n z hz = 0 := by
  have : Subsingleton (K.X n) := ModuleCat.isZero_iff_subsingleton.1 hK
  have h0 : (K.liftCycles (toMor z) (n + 1) (CochainComplex.next ℤ n)
      (toMor_comp_d_eq_zero K hz)).hom 1 = 0 :=
    (ModuleCat.mono_iff_injective (K.iCycles n)).1 inferInstance (Subsingleton.elim _ _)
  rw [cls, h0, map_zero]

end Classes

/-! ### The comparison -/

section Comparison

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize
attribute [local instance] totIndexFintype
attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X : AlgebraicGeometry.RingedSpace.{u, u}}
  {A A' : Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}}
  (h : baseRingedSpace A ⟶ baseRingedSpace A') (hh : h.hom.base = 𝟙 X.carrier)
  {ι : Type u} (U : ι → Opens X.carrier) (hU : ⊤ = ⨆ i, U i)

/-- The pushforward along `h` of a complex vanishing in negative degrees vanishes in negative
degrees. -/
theorem isZero_pushC_X (M : CochainComplex (SheafOfModules.{u} (ringSheaf A)) ℤ)
    (hM : ∀ a : ℤ, a < 0 → IsZero (M.X a)) (a : ℤ) (ha : a < 0) : IsZero ((pushC h M).X a) :=
  (StacksDraft.KFlat.modulePushforward h).map_isZero (hM a ha)

/-- The pushforward along `h` of a bounded below complex vanishing in negative degrees. -/
def pushPlus (M : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf A)))
    (hM : M.obj.IsStrictlyGE 0) : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf A')) :=
  ⟨pushC h M.obj, 0, (CochainComplex.isStrictlyGE_iff _ 0).2 fun i hi =>
    isZero_pushC_X h M.obj (fun a ha => M.obj.isZero_of_isStrictlyGE 0 a ha) i hi⟩

/-- The class map on the side of `𝒜`: Čech classes, read in the unbounded model of derived global
sections. -/
def sideA (M : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf A))) (n : ℤ) :
    ((Stacks.Cech.Hypercohomology.cech A U hU).obj M.obj).homology n ⟶
      cohomologyModule (S := baseRingedSpace A) (DerivedCategory.Q.obj M.obj) n :=
  cechClass A U hU M n ≫ (DerivedCategory.homologyFunctor _ n).map
    ((Stacks.Cohomology.DerivedSectionsModels.derivedSectionsFunctorIso (baseRingedSpace A)
      ⊤).hom.app M)

/-- The class map on the side of `𝒜'`, carried back to `𝒜` by the comparison `h_* ⟶ Rh_*` and the
Leray identification. -/
def sideA' (M : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf A)))
    (hM : M.obj.IsStrictlyGE 0) (n : ℤ) :
    ((Stacks.Cech.Hypercohomology.cech A' U hU).obj (pushC h M.obj)).homology n ⟶
      (restrictGlobal h).obj (cohomologyModule (S := baseRingedSpace A)
        (DerivedCategory.Q.obj M.obj) n) :=
  cechClass A' U hU (pushPlus h M hM) n ≫ (DerivedCategory.homologyFunctor _ n).map
    ((Stacks.Cohomology.DerivedSectionsModels.derivedSectionsFunctorIso (baseRingedSpace A')
      ⊤).hom.app (pushPlus h M hM)) ≫
    (DerivedCategory.homologyFunctor _ n).map
      ((baseSections (baseRingedSpace A')).map (pushforwardComparisonQ h M.obj)) ≫
    (lerayCohomologyIso h (DerivedCategory.Q.obj M.obj) n).hom

/-- **The comparison of the total Čech complexes of `h_*M` over `𝒜'` and of `M` over `𝒜`**,
degreewise: both are the elementwise total Čech complex of the sections of `M`. -/
def ecl (M : CochainComplex (SheafOfModules.{u} (ringSheaf A)) ℤ)
    (hM : ∀ a : ℤ, a < 0 → IsZero (M.X a)) (n : ℤ) :
    ((Stacks.Cech.Hypercohomology.cech A' U hU).obj (pushC h M)).X n ≃+
      ((Stacks.Cech.Hypercohomology.cech A U hU).obj M).X n :=
  (((HomologicalComplex.eval _ _ n).mapIso
      (cechNatIso A' U hU (pushC h M) (isZero_pushC_X h M hM))).toLinearEquiv.toAddEquiv.trans
    ((HomologicalComplex.eval _ _ n).mapIso
      (pushCechIso h hh U hU M)).toLinearEquiv.toAddEquiv).trans
    ((AddEquiv.refl (TotX (coverObject U hU) (natSections A M) n)).trans
      ((HomologicalComplex.eval _ _ n).mapIso
        (cechNatIso A U hU M hM).symm).toLinearEquiv.toAddEquiv)

/-- The comparison `ecl` is the composite of the identification of the total Čech complex over `𝒜'`
with its elementwise model, the comparison of sections, and the inverse identification over `𝒜`. -/
theorem ecl_apply (M : CochainComplex (SheafOfModules.{u} (ringSheaf A)) ℤ)
    (hM : ∀ a : ℤ, a < 0 → IsZero (M.X a)) (n : ℤ)
    (z : ((Stacks.Cech.Hypercohomology.cech A' U hU).obj (pushC h M)).X n) :
    ecl h hh U hU M hM n z = ((cechNatIso A U hU M hM).inv.f n).hom
      (show TotX (coverObject U hU) (natSections A M) n from
        totMap (pushSectionsIso h hh M).hom n
          (((cechNatIso A' U hU (pushC h M) (isZero_pushC_X h M hM)).hom.f n).hom z)) :=
  rfl

/-- The comparison `ecl` commutes with the differentials of the total Čech complexes. -/
theorem ecl_d (M : CochainComplex (SheafOfModules.{u} (ringSheaf A)) ℤ)
    (hM : ∀ a : ℤ, a < 0 → IsZero (M.X a)) (n : ℤ)
    (z : ((Stacks.Cech.Hypercohomology.cech A' U hU).obj (pushC h M)).X n) :
    ecl h hh U hU M hM (n + 1)
        ((((Stacks.Cech.Hypercohomology.cech A' U hU).obj (pushC h M)).d n (n + 1)).hom z) =
      (((Stacks.Cech.Hypercohomology.cech A U hU).obj M).d n (n + 1)).hom
        (ecl h hh U hU M hM n z) := by
  rw [ecl_apply, ecl_apply]
  have e1 := (ConcreteCategory.congr_hom
    ((cechNatIso A' U hU (pushC h M) (isZero_pushC_X h M hM)).hom.comm n (n + 1)) z).symm
  have e2 := (ConcreteCategory.congr_hom
    ((cechTotMap (coverObject U hU) _ (pushSectionsIso h hh M).hom).comm n (n + 1))
    (((cechNatIso A' U hU (pushC h M) (isZero_pushC_X h M hM)).hom.f n).hom z)).symm
  have e3 := (ConcreteCategory.congr_hom ((cechNatIso A U hU M hM).inv.comm n (n + 1))
    (show TotX (coverObject U hU) (natSections A M) n from
      totMap (pushSectionsIso h hh M).hom n
        (((cechNatIso A' U hU (pushC h M) (isZero_pushC_X h M hM)).hom.f n).hom z))).symm
  refine Eq.trans ?_ e3
  refine congrArg ((cechNatIso A U hU M hM).inv.f (n + 1)).hom ?_
  refine (congrArg (totMap (pushSectionsIso h hh M).hom (n + 1)) e1).trans ?_
  refine e2.trans ((cechTot_d_apply _ _ n _).trans ?_)
  exact (cechTot_d_apply (coverObject U hU) (natSections A M) n
    (totMap (pushSectionsIso h hh M).hom n
      (((cechNatIso A' U hU (pushC h M) (isZero_pushC_X h M hM)).hom.f n).hom z))).symm

/-- The comparison `ecl` commutes with the differential from degree `n` to degree `m = n + 1`. -/
theorem ecl_d' (M : CochainComplex (SheafOfModules.{u} (ringSheaf A)) ℤ)
    (hM : ∀ a : ℤ, a < 0 → IsZero (M.X a)) (n m : ℤ) (hnm : n + 1 = m)
    (z : ((Stacks.Cech.Hypercohomology.cech A' U hU).obj (pushC h M)).X n) :
    ecl h hh U hU M hM m
        ((((Stacks.Cech.Hypercohomology.cech A' U hU).obj (pushC h M)).d n m).hom z) =
      (((Stacks.Cech.Hypercohomology.cech A U hU).obj M).d n m).hom
        (ecl h hh U hU M hM n z) := by
  subst hnm
  exact ecl_d h hh U hU M hM n z

/-- The comparison `ecl` sends cocycles to cocycles. -/
theorem ecl_cocycle (M : CochainComplex (SheafOfModules.{u} (ringSheaf A)) ℤ)
    (hM : ∀ a : ℤ, a < 0 → IsZero (M.X a)) (n : ℤ)
    (z : ((Stacks.Cech.Hypercohomology.cech A' U hU).obj (pushC h M)).X n)
    (hz : (((Stacks.Cech.Hypercohomology.cech A' U hU).obj (pushC h M)).d n (n + 1)).hom z = 0) :
    (((Stacks.Cech.Hypercohomology.cech A U hU).obj M).d n (n + 1)).hom
      (ecl h hh U hU M hM n z) = 0 :=
  (ecl_d h hh U hU M hM n z).symm.trans ((congrArg _ hz).trans (map_zero _))

/-- The identification `cechNatIso` of the total Čech complex with its elementwise model is natural
in the complex, on elements. -/
theorem cechNatIso_hom_f_naturality_apply
    {O : Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}}
    {M M' : CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ}
    (hM : ∀ a : ℤ, a < 0 → IsZero (M.X a)) (hM' : ∀ a : ℤ, a < 0 → IsZero (M'.X a))
    (j : M ⟶ M') (n : ℤ) (z : ((Stacks.Cech.Hypercohomology.cech O U hU).obj M).X n) :
    ((cechNatIso O U hU M' hM').hom.f n).hom
        ((((Stacks.Cech.Hypercohomology.cech O U hU).map j).f n).hom z) =
      totMap (natSectionsMap O j) n (((cechNatIso O U hU M hM).hom.f n).hom z) :=
  ConcreteCategory.congr_hom (HomologicalComplex.congr_hom
    (cechNatIso_hom_naturality O U hU hM hM' j) n) z

/-- The inverse of the identification `cechNatIso` is natural in the complex, on elements. -/
theorem cechNatIso_inv_f_naturality_apply
    {O : Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}}
    {M M' : CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ}
    (hM : ∀ a : ℤ, a < 0 → IsZero (M.X a)) (hM' : ∀ a : ℤ, a < 0 → IsZero (M'.X a))
    (j : M ⟶ M') (n : ℤ) (w : TotX (coverObject U hU) (natSections O M) n) :
    ((cechNatIso O U hU M' hM').inv.f n).hom (totMap (natSectionsMap O j) n w) =
      (((Stacks.Cech.Hypercohomology.cech O U hU).map j).f n).hom
        (((cechNatIso O U hU M hM).inv.f n).hom w) := by
  have H := cechNatIso_hom_f_naturality_apply U hU hM hM' j n
    (((cechNatIso O U hU M hM).inv.f n).hom w)
  have hw := iso_inv_hom_f_apply _ (cechNatIso O U hU M hM) n w
  have H' := H.trans (congrArg (totMap (natSectionsMap O j) n) hw)
  refine (congrArg ((cechNatIso O U hU M' hM').inv.f n).hom H'.symm).trans ?_
  exact iso_hom_inv_f_apply _ (cechNatIso O U hU M' hM') n _

/-- The comparison `pushSectionsIso` of sections of `h_*M` and of `M` is natural in `M`, on the
elementwise total Čech complexes. -/
theorem totMap_pushSectionsIso_naturality
    {M M' : CochainComplex (SheafOfModules.{u} (ringSheaf A)) ℤ}
    (j : M ⟶ M') (n : ℤ) (y : TotX (coverObject U hU) (natSections A' (pushC h M)) n) :
    (totMap (pushSectionsIso h hh M').hom n (totMap (natSectionsMap A'
        (((StacksDraft.KFlat.modulePushforward h).mapHomologicalComplex _).map j)) n y) :
      TotX (coverObject U hU) (natSections A M') n) =
      totMap (natSectionsMap A j) n
        (show TotX (coverObject U hU) (natSections A M) n from
          totMap (pushSectionsIso h hh M).hom n y) :=
  funext fun i => funext fun t => by
    change ((M'.X i.1.2).val.map
        (eqToHom (map_obj_eq h hh (inter (coverObject U hU) t).left).symm).op).hom
        (((j.f i.1.2).val.app
          (op ((Opens.map h.hom.base).obj (inter (coverObject U hU) t).left))).hom (y i t)) =
      ((j.f i.1.2).val.app (op (inter (coverObject U hU) t).left)).hom
        (((M.X i.1.2).val.map
          (eqToHom (map_obj_eq h hh (inter (coverObject U hU) t).left).symm).op).hom (y i t))
    exact (PresheafOfModules.naturality_apply (j.f i.1.2).val
      (eqToHom (map_obj_eq h hh (inter (coverObject U hU) t).left).symm).op (y i t)).symm

/-- The comparison `ecl` is natural in the complex `M`. -/
theorem ecl_naturality {M M' : CochainComplex (SheafOfModules.{u} (ringSheaf A)) ℤ}
    (hM : ∀ a : ℤ, a < 0 → IsZero (M.X a)) (hM' : ∀ a : ℤ, a < 0 → IsZero (M'.X a))
    (j : M ⟶ M') (n : ℤ)
    (z : ((Stacks.Cech.Hypercohomology.cech A' U hU).obj (pushC h M)).X n) :
    ecl h hh U hU M' hM' n ((((Stacks.Cech.Hypercohomology.cech A' U hU).map
        (((StacksDraft.KFlat.modulePushforward h).mapHomologicalComplex _).map j)).f n).hom z) =
      (((Stacks.Cech.Hypercohomology.cech A U hU).map j).f n).hom (ecl h hh U hU M hM n z) := by
  rw [ecl_apply, ecl_apply]
  refine (congrArg (fun y => ((cechNatIso A U hU M' hM').inv.f n).hom
    (show TotX (coverObject U hU) (natSections A M') n from
      totMap (pushSectionsIso h hh M').hom n y))
    (cechNatIso_hom_f_naturality_apply U hU (isZero_pushC_X h M hM) (isZero_pushC_X h M' hM')
      _ n z)).trans ?_
  refine (congrArg (fun y => ((cechNatIso A U hU M' hM').inv.f n).hom y)
    (totMap_pushSectionsIso_naturality h hh U hU j n _)).trans ?_
  exact cechNatIso_inv_f_naturality_apply U hU hM hM' j n _

/-- **The comparison respects the augmentation of [Stacks, Tag 07M9].** -/
theorem ecl_sectionsToTotalCech (M : CochainComplex (SheafOfModules.{u} (ringSheaf A)) ℤ)
    (hM : ∀ a : ℤ, a < 0 → IsZero (M.X a)) (k : ℕ)
    (s : (SheafOfModules.evaluation.{u} (ringSheaf A) (op ⊤)).obj (M.X k)) :
    ecl h hh U hU M hM k ((((Stacks.Cech.Linear.sectionsToTotalCech X.carrier (ringSheaf A') ⊤ U
        hU).app (pushC h M)).f k).hom s) =
      (((Stacks.Cech.Linear.sectionsToTotalCech X.carrier (ringSheaf A) ⊤ U hU).app M).f k).hom
        s := by
  rw [ecl_apply]
  refine (congrArg (fun y => ((cechNatIso A U hU M hM).inv.f k).hom
    (show TotX (coverObject U hU) (natSections A M) k from totMap (pushSectionsIso h hh M).hom k y))
    (cechNatIso_hom_sectionsToTotalCech A' U hU (pushC h M) (isZero_pushC_X h M hM) k s)).trans ?_
  refine (congrArg (fun y => ((cechNatIso A U hU M hM).inv.f k).hom y)
    (totMap_pushSectionsIso_restrictTotS h hh U hU M k s)).trans ?_
  refine (congrArg ((cechNatIso A U hU M hM).inv.f k).hom
    (cechNatIso_hom_sectionsToTotalCech A U hU M hM k s).symm).trans ?_
  exact iso_hom_inv_f_apply _ (cechNatIso A U hU M hM) k _

/-- The pushforward of a morphism of bounded below complexes. -/
def pushPlusMap {M I : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf A))}
    (hM : M.obj.IsStrictlyGE 0) (hI : I.obj.IsStrictlyGE 0) (j : M ⟶ I) :
    pushPlus h M hM ⟶ pushPlus h I hI :=
  ObjectProperty.homMk (((StacksDraft.KFlat.modulePushforward h).mapHomologicalComplex _).map j.hom)

/-- The class map `sideA` is natural in the bounded below complex `M`. -/
theorem sideA_naturality {M I : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf A))}
    (j : M ⟶ I) (n : ℤ) :
    sideA U hU M n ≫ (DerivedCategory.homologyFunctor
        (ModuleCat.{u} (baseRing (baseRingedSpace A))) n).map
        ((baseSections (baseRingedSpace A)).map (DerivedCategory.Q.map j.hom)) =
      HomologicalComplex.homologyMap ((Stacks.Cech.Hypercohomology.cech A U hU).map j.hom) n ≫
        sideA U hU I n := by
  have h1 := Stacks.Cech.Hypercohomology.cechClass_naturality A U hU j n
  have h2 := congrArg (DerivedCategory.homologyFunctor
    (ModuleCat.{u} (baseRing (baseRingedSpace A))) n).map
    ((Stacks.Cohomology.DerivedSectionsModels.derivedSectionsFunctorIso (baseRingedSpace A)
      ⊤).hom.naturality j)
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (cechClass A U hU M n ≫ ·)
    ((Functor.map_comp _ _ _).symm.trans (h2.symm.trans (Functor.map_comp _ _ _)))).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) h1.symm).trans ?_
  exact Category.assoc _ _ _

/-- The class map `sideA'` is natural in the bounded below complex `M`. -/
theorem sideA'_naturality {M I : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf A))}
    (hM : M.obj.IsStrictlyGE 0) (hI : I.obj.IsStrictlyGE 0) (j : M ⟶ I) (n : ℤ) :
    sideA' h U hU M hM n ≫ (restrictGlobal h).map ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} (baseRing (baseRingedSpace A))) n).map
        ((baseSections (baseRingedSpace A)).map (DerivedCategory.Q.map j.hom))) =
      HomologicalComplex.homologyMap ((Stacks.Cech.Hypercohomology.cech A' U hU).map
        (((StacksDraft.KFlat.modulePushforward h).mapHomologicalComplex _).map j.hom)) n ≫
        sideA' h U hU I hI n := by
  let pj := pushPlusMap h hM hI j
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (baseRingedSpace A'))) n
  have s₁ := (Stacks.Cech.Hypercohomology.cechClass_naturality A' U hU pj n).symm
  have s₂ := (Functor.map_comp _ _ _).symm.trans ((congrArg H.map
    ((Stacks.Cohomology.DerivedSectionsModels.derivedSectionsFunctorIso (baseRingedSpace A')
      ⊤).hom.naturality pj)).symm.trans (Functor.map_comp _ _ _))
  have e₃ := congrArg (fun φ => H.map ((baseSections (baseRingedSpace A')).map φ))
    (pushforwardComparisonQ_naturality h j.hom)
  have s₃ := (H.map_comp _ _).symm.trans ((congrArg H.map
    ((baseSections (baseRingedSpace A')).map_comp _ _).symm).trans (e₃.symm.trans
      ((congrArg H.map ((baseSections (baseRingedSpace A')).map_comp _ _)).trans
        (H.map_comp _ _))))
  have s₄ := (lerayCohomologyIso_naturality h (DerivedCategory.Q.map j.hom) n).symm
  exact paste_four _ _ _ _ _ _ _ _ _ _ _ _ _ s₁ s₂ s₃ s₄

/-- A complex strictly concentrated in nonnegative degrees vanishes in every negative degree. -/
theorem isZero_of_isStrictlyGE_zero {C : Type*} [Category* C] [HasZeroMorphisms C]
    {M : CochainComplex C ℤ} (hM : M.IsStrictlyGE 0) (a : ℤ) (ha : a < 0) : IsZero (M.X a) :=
  M.isZero_of_isStrictlyGE 0 a ha

/-- The naturality of `sideA'` on the class of a cocycle. -/
theorem sideA'_cls_naturality {M I : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf A))}
    (hM : M.obj.IsStrictlyGE 0) (hI : I.obj.IsStrictlyGE 0) (j : M ⟶ I) (n : ℤ)
    (z : ((Stacks.Cech.Hypercohomology.cech A' U hU).obj (pushC h M.obj)).X n)
    (hz : (((Stacks.Cech.Hypercohomology.cech A' U hU).obj (pushC h M.obj)).d n (n + 1)).hom z = 0)
    (hz₁ : (((Stacks.Cech.Hypercohomology.cech A' U hU).obj (pushC h I.obj)).d n (n + 1)).hom
      ((((Stacks.Cech.Hypercohomology.cech A' U hU).map
        (((StacksDraft.KFlat.modulePushforward h).mapHomologicalComplex (up ℤ)).map j.hom)).f n).hom
          z) = 0) :
    ((restrictGlobal h).map ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} (baseRing (baseRingedSpace A))) n).map
        ((baseSections (baseRingedSpace A)).map (DerivedCategory.Q.map j.hom)))).hom
        ((sideA' h U hU M hM n).hom (cls _ n z hz)) =
      (sideA' h U hU I hI n).hom (cls _ n _ hz₁) :=
  apply_cls_of_comp_eq _ _ n z hz hz₁ (sideA'_naturality h U hU hM hI j n)

/-- The naturality of `sideA` on the class of a cocycle. -/
theorem sideA_cls_naturality {M I : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf A))}
    (j : M ⟶ I) (n : ℤ) (y : ((Stacks.Cech.Hypercohomology.cech A U hU).obj M.obj).X n)
    (hy : (((Stacks.Cech.Hypercohomology.cech A U hU).obj M.obj).d n (n + 1)).hom y = 0)
    (hy₁ : (((Stacks.Cech.Hypercohomology.cech A U hU).obj I.obj).d n (n + 1)).hom
      ((((Stacks.Cech.Hypercohomology.cech A U hU).map j.hom).f n).hom y) = 0) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing (baseRingedSpace A))) n).map
        ((baseSections (baseRingedSpace A)).map (DerivedCategory.Q.map j.hom))).hom
        ((sideA U hU M n).hom (cls _ n y hy)) =
      (sideA U hU I n).hom (cls _ n _ hy₁) :=
  apply_cls_of_comp_eq _ _ n y hy hy₁ (sideA_naturality U hU j n)

/-- The class map on the side of `𝒜` sends the image of the class of a global cocycle under the
augmentation to the class of the cocycle. -/
theorem sideA_augmentation (I : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf A))) (n : ℤ)
    (c : (sectionsComplex (baseRingedSpace A) I.obj).cycles n) :
    (sideA U hU I n).hom ((HomologicalComplex.homologyMap
        ((Stacks.Cech.Linear.sectionsToTotalCech X.carrier (ringSheaf A) ⊤ U hU).app I.obj) n).hom
        (((sectionsComplex (baseRingedSpace A) I.obj).homologyπ n).hom c)) =
      globalClass (X := baseRingedSpace A) I.obj n c :=
  Stacks.Cech.Hypercohomology.cechClass_augmentation_eq_globalClass (baseRingedSpace A) U hU I n c

/-- The class map `sideA'` is `sideA` for `h_*M` over `𝒜'`, followed by the comparison `h_* ⟶ Rh_*`
and the Leray identification. -/
theorem sideA'_apply (M : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf A)))
    (hM : M.obj.IsStrictlyGE 0) (n : ℤ)
    (x : ((Stacks.Cech.Hypercohomology.cech A' U hU).obj (pushC h M.obj)).homology n) :
    (sideA' h U hU M hM n).hom x = (lerayCohomologyIso h (DerivedCategory.Q.obj M.obj) n).hom
      (((DerivedCategory.homologyFunctor _ n).map
        ((baseSections (baseRingedSpace A')).map (pushforwardComparisonQ h M.obj))).hom
        ((sideA U hU (pushPlus h M hM) n).hom x)) :=
  rfl

/-- The class map on the side of `𝒜'` sends the image of the class of a global cocycle under the
augmentation to the class of the cocycle. -/
theorem sideA'_augmentation (I : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf A)))
    (hI : I.obj.IsStrictlyGE 0) (n : ℤ)
    (c : (sectionsComplex (baseRingedSpace A) I.obj).cycles n) :
    (sideA' h U hU I hI n).hom ((HomologicalComplex.homologyMap
        ((Stacks.Cech.Linear.sectionsToTotalCech X.carrier (ringSheaf A') ⊤ U hU).app
          (pushC h I.obj)) n).hom
        (((sectionsComplex (baseRingedSpace A') (pushC h I.obj)).homologyπ n).hom
          (pushCycle h I.obj n c))) =
      globalClass (X := baseRingedSpace A) I.obj n c := by
  have e := sideA_augmentation (A := A') U hU (pushPlus h I hI) n (pushCycle h I.obj n c)
  have e' := lerayCohomologyIso_globalClass h I.obj n (pushCycle h I.obj n c) c
    (iCycles_pushCycle h I.obj n c)
  refine (sideA'_apply h U hU I hI n _).trans (Eq.trans ?_ e')
  exact congrArg (fun x => (lerayCohomologyIso h (DerivedCategory.Q.obj I.obj) n).hom
    (((DerivedCategory.homologyFunctor _ n).map
      ((baseSections (baseRingedSpace A')).map (pushforwardComparisonQ h I.obj))).hom x)) e

/-- On a bounded below complex of injectives every Čech class over `𝒜` is the image under the
augmentation of the class of a global cocycle `c`, and a cocycle over `𝒜'` with the same image
under `ecl` differs from the restriction of `c` by a coboundary. -/
theorem exists_augmentation_of_injective
    (I : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf A)))
    (hI : I.obj.IsStrictlyGE 0) (hinj : ∀ k, Injective (I.obj.X k)) (k : ℕ)
    (z : ((Stacks.Cech.Hypercohomology.cech A' U hU).obj (pushC h I.obj)).X k)
    (hz : (((Stacks.Cech.Hypercohomology.cech A' U hU).obj (pushC h I.obj)).d k (k + 1)).hom z =
      0) :
    ∃ (c : (sectionsComplex (baseRingedSpace A) I.obj).cycles k)
      (w : ((Stacks.Cech.Hypercohomology.cech A U hU).obj I.obj).X (k - 1)),
      ecl h hh U hU I.obj (isZero_of_isStrictlyGE_zero hI) k z -
        (((Stacks.Cech.Linear.sectionsToTotalCech X.carrier (ringSheaf A) ⊤ U hU).app I.obj).f
          k).hom (((sectionsComplex (baseRingedSpace A) I.obj).iCycles k).hom c) =
        (((Stacks.Cech.Hypercohomology.cech A U hU).obj I.obj).d (k - 1) k).hom w := by
  have := Stacks.Cech.Linear.quasiIso_sectionsToTotalCech_of_injective X.carrier (ringSheaf A) ⊤
    U hU I.obj 0 hinj
  have hy := ecl_cocycle h hh U hU I.obj (isZero_of_isStrictlyGE_zero hI) k z hz
  obtain ⟨c0, hc0⟩ := (ModuleCat.epi_iff_surjective (HomologicalComplex.homologyMap
    ((Stacks.Cech.Linear.sectionsToTotalCech X.carrier (ringSheaf A) ⊤ U hU).app I.obj) k)).1
      inferInstance (cls _ k _ hy)
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((sectionsComplex (baseRingedSpace A) I.obj).homologyπ k)).1 inferInstance c0
  have hs := d_iCycles_apply _ k c
  have hs' := d_f_apply_eq_zero _
    ((Stacks.Cech.Linear.sectionsToTotalCech X.carrier (ringSheaf A) ⊤ U hU).app I.obj) k _ hs
  have e1 := homologyMap_cls _
    ((Stacks.Cech.Linear.sectionsToTotalCech X.carrier (ringSheaf A) ⊤ U hU).app I.obj) k _ hs hs'
  have e2 := cls_iCycles (sectionsComplex (baseRingedSpace A) I.obj) k c hs
  have e3 : cls _ k _ hy = cls _ k _ hs' :=
    hc0.symm.trans ((congrArg (HomologicalComplex.homologyMap
      ((Stacks.Cech.Linear.sectionsToTotalCech X.carrier (ringSheaf A) ⊤ U hU).app I.obj) k).hom
        e2.symm).trans e1)
  exact ⟨c, exists_sub_eq_d_of_cls_eq _ k _ _ hy hs' e3⟩

/-- A coboundary relation through `ecl` lifts to the total Čech complex over `𝒜'`. -/
theorem sub_augmentation_eq_d_of_ecl (M : CochainComplex (SheafOfModules.{u} (ringSheaf A)) ℤ)
    (hM : ∀ a : ℤ, a < 0 → IsZero (M.X a)) (k : ℕ)
    (z : ((Stacks.Cech.Hypercohomology.cech A' U hU).obj (pushC h M)).X k)
    (s : (SheafOfModules.evaluation.{u} (ringSheaf A) (op ⊤)).obj (M.X k))
    (w : ((Stacks.Cech.Hypercohomology.cech A U hU).obj M).X (k - 1))
    (hw : ecl h hh U hU M hM k z -
        (((Stacks.Cech.Linear.sectionsToTotalCech X.carrier (ringSheaf A) ⊤ U hU).app M).f
          k).hom s = (((Stacks.Cech.Hypercohomology.cech A U hU).obj M).d (k - 1) k).hom w) :
    z - (((Stacks.Cech.Linear.sectionsToTotalCech X.carrier (ringSheaf A') ⊤ U hU).app
        (pushC h M)).f k).hom s =
      (((Stacks.Cech.Hypercohomology.cech A' U hU).obj (pushC h M)).d (k - 1) k).hom
        ((ecl h hh U hU M hM (k - 1)).symm w) := by
  apply (ecl h hh U hU M hM k).injective
  refine ((ecl h hh U hU M hM k).map_sub _ _).trans ?_
  refine Eq.trans ?_ (ecl_d' h hh U hU M hM (k - 1) k (by omega) _).symm
  refine Eq.trans ?_ (congrArg _ ((ecl h hh U hU M hM (k - 1)).apply_symm_apply w).symm)
  refine Eq.trans ?_ hw
  exact congrArg (ecl h hh U hU M hM k z - ·) (ecl_sectionsToTotalCech h hh U hU M hM k s)

/-- **The comparison of class maps on a bounded below complex of injectives**, in degree
`k : ℕ`. -/
theorem sideA'_cls_of_injective_nat (I : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf A)))
    (hI : I.obj.IsStrictlyGE 0) (hinj : ∀ k, Injective (I.obj.X k)) (k : ℕ)
    (z : ((Stacks.Cech.Hypercohomology.cech A' U hU).obj (pushC h I.obj)).X k)
    (hz : (((Stacks.Cech.Hypercohomology.cech A' U hU).obj (pushC h I.obj)).d k (k + 1)).hom z =
      0) :
    (sideA' h U hU I hI k).hom (cls _ k z hz) =
      (sideA U hU I k).hom (cls _ k _
        (ecl_cocycle h hh U hU I.obj (isZero_of_isStrictlyGE_zero hI) k z hz)) := by
  obtain ⟨c, w, hw⟩ := exists_augmentation_of_injective h hh U hU I hI hinj k z hz
  have hw' : z - (((Stacks.Cech.Linear.sectionsToTotalCech X.carrier (ringSheaf A') ⊤ U hU).app
        (pushC h I.obj)).f k).hom
        (((sectionsComplex (baseRingedSpace A') (pushC h I.obj)).iCycles k).hom
          (pushCycle h I.obj k c)) =
      (((Stacks.Cech.Hypercohomology.cech A' U hU).obj (pushC h I.obj)).d (k - 1) k).hom
        ((ecl h hh U hU I.obj (isZero_of_isStrictlyGE_zero hI) (k - 1)).symm w) :=
    (congrArg (fun x => z - (((Stacks.Cech.Linear.sectionsToTotalCech X.carrier (ringSheaf A') ⊤
      U hU).app (pushC h I.obj)).f k).hom x) (iCycles_pushCycle h I.obj k c)).trans
      (sub_augmentation_eq_d_of_ecl h hh U hU I.obj (isZero_of_isStrictlyGE_zero hI) k z _ w hw)
  exact ((congrArg (sideA' h U hU I hI k).hom
      (cls_eq_homologyMap_homologyπ_of_sub_eq_d _ _ k _ z hz _ hw')).trans
      (sideA'_augmentation h U hU I hI k c)).trans
    ((congrArg (sideA U hU I k).hom (cls_eq_homologyMap_homologyπ_of_sub_eq_d _ _ k c _
      (ecl_cocycle h hh U hU I.obj (isZero_of_isStrictlyGE_zero hI) k z hz) w hw)).trans
      (sideA_augmentation U hU I k c)).symm

/-- The total Čech complex of a complex vanishing in negative degrees vanishes in negative
degrees. -/
theorem isZero_cech_X_of_neg {O : Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}}
    (M : CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ)
    (hM : ∀ a : ℤ, a < 0 → IsZero (M.X a)) {n : ℤ} (hn : n < 0) :
    IsZero (((Stacks.Cech.Hypercohomology.cech O U hU).obj M).X n) := by
  have : IsEmpty (TotIndex n) := ⟨fun ⟨⟨p, a⟩, h⟩ => by omega⟩
  exact (ModuleCat.isZero_of_subsingleton ((cechTot (coverObject U hU) (natSections O M)).X n))
    |>.of_iso ((HomologicalComplex.eval _ _ n).mapIso (cechNatIso O U hU M hM))

/-- **The comparison of class maps on a bounded below complex of injectives.** -/
theorem sideA'_cls_of_injective (I : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf A)))
    (hI : I.obj.IsStrictlyGE 0) (hinj : ∀ k, Injective (I.obj.X k)) (n : ℤ)
    (z : ((Stacks.Cech.Hypercohomology.cech A' U hU).obj (pushC h I.obj)).X n)
    (hz : (((Stacks.Cech.Hypercohomology.cech A' U hU).obj (pushC h I.obj)).d n (n + 1)).hom z =
      0) :
    (sideA' h U hU I hI n).hom (cls _ n z hz) =
      (sideA U hU I n).hom (cls _ n _
        (ecl_cocycle h hh U hU I.obj (isZero_of_isStrictlyGE_zero hI) n z hz)) := by
  rcases lt_or_ge n 0 with hn | hn
  · rw [cls_eq_zero_of_isZero _ n (isZero_cech_X_of_neg U hU _
        (isZero_pushC_X h I.obj (isZero_of_isStrictlyGE_zero hI)) hn) z hz,
      cls_eq_zero_of_isZero _ n (isZero_cech_X_of_neg U hU _ (isZero_of_isStrictlyGE_zero hI) hn),
      map_zero, map_zero]
    rfl
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact sideA'_cls_of_injective_nat h hh U hU I hI hinj k z hz

/-- A quasi-isomorphism induces an injection on cohomology, read over `Γ(X, 𝒜')`. -/
theorem injective_restrictGlobal_homology_of_quasiIso
    {M I : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf A))} (j : M ⟶ I)
    (hj : QuasiIso j.hom) (n : ℤ) :
    Function.Injective ((restrictGlobal h).map ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (baseRingedSpace A))) n).map
        ((baseSections (baseRingedSpace A)).map (DerivedCategory.Q.map j.hom)))).hom := by
  have : IsIso ((DerivedCategory.Q (C := SheafOfModules.{u}
      (structureSheafRing (baseRingedSpace A)))).map j.hom) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso
      (SheafOfModules.{u} (structureSheafRing (baseRingedSpace A))) j.hom).2 hj
  exact (ModuleCat.mono_iff_injective _).1 inferInstance

/-- The comparison on the image of a cocycle in the total Čech complex of a complex of
injectives. -/
theorem sideA'_cls_map_of_injective {M I : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf A))}
    (hM : M.obj.IsStrictlyGE 0) (hI : I.obj.IsStrictlyGE 0) (hinj : ∀ k, Injective (I.obj.X k))
    (j : M ⟶ I) (n : ℤ)
    (z : ((Stacks.Cech.Hypercohomology.cech A' U hU).obj (pushC h M.obj)).X n)
    (hz₁ : (((Stacks.Cech.Hypercohomology.cech A' U hU).obj (pushC h I.obj)).d n (n + 1)).hom
      ((((Stacks.Cech.Hypercohomology.cech A' U hU).map
        (((StacksDraft.KFlat.modulePushforward h).mapHomologicalComplex (up ℤ)).map j.hom)).f n).hom
          z) = 0)
    (hz₂ : (((Stacks.Cech.Hypercohomology.cech A U hU).obj I.obj).d n (n + 1)).hom
      ((((Stacks.Cech.Hypercohomology.cech A U hU).map j.hom).f n).hom
        (ecl h hh U hU M.obj (isZero_of_isStrictlyGE_zero hM) n z)) = 0) :
    (sideA' h U hU I hI n).hom (cls _ n _ hz₁) = (sideA U hU I n).hom (cls _ n _ hz₂) :=
  (sideA'_cls_of_injective h hh U hU I hI hinj n _ hz₁).trans
    (congrArg (sideA U hU I n).hom (cls_congr _ n (ecl_naturality h hh U hU
      (isZero_of_isStrictlyGE_zero hM) (isZero_of_isStrictlyGE_zero hI) j.hom n z) _ _))

/-- The two class maps agree on the class of a cocycle of `M`, given a quasi-isomorphism from `M`
to a bounded below complex of injectives `I`. -/
theorem sideA'_cls_of_resolution {M I : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf A))}
    (hM : M.obj.IsStrictlyGE 0) (hI : I.obj.IsStrictlyGE 0) (hinj : ∀ k, Injective (I.obj.X k))
    (j : M ⟶ I) (hj : QuasiIso j.hom) (n : ℤ)
    (z : ((Stacks.Cech.Hypercohomology.cech A' U hU).obj (pushC h M.obj)).X n)
    (hz : (((Stacks.Cech.Hypercohomology.cech A' U hU).obj (pushC h M.obj)).d n (n + 1)).hom z =
      0) :
    (sideA' h U hU M hM n).hom (cls _ n z hz) = (sideA U hU M n).hom (cls _ n _
      (ecl_cocycle h hh U hU M.obj (isZero_of_isStrictlyGE_zero hM) n z hz)) := by
  have hz₁ := d_f_apply_eq_zero _ ((Stacks.Cech.Hypercohomology.cech A' U hU).map
    (((StacksDraft.KFlat.modulePushforward h).mapHomologicalComplex (up ℤ)).map j.hom)) n z hz
  have hz' := ecl_cocycle h hh U hU M.obj (isZero_of_isStrictlyGE_zero hM) n z hz
  have hz₂ := d_f_apply_eq_zero _ ((Stacks.Cech.Hypercohomology.cech A U hU).map j.hom) n _ hz'
  refine injective_restrictGlobal_homology_of_quasiIso h j hj n
    ((sideA'_cls_naturality h U hU hM hI j n z hz hz₁).trans
      (Eq.trans ?_ (sideA_cls_naturality U hU j n _ hz' hz₂).symm))
  exact sideA'_cls_map_of_injective h hh U hU hM hI hinj j n z hz₁ hz₂

/-- **Čech classes across the change of rings `h`** ([Stacks, Tags 08BN, 0D5W]): for a bounded
below complex `M` of `𝒜`-modules vanishing in negative degrees, the Čech class over `𝒜'` of a
cocycle of `Tot(Č(U, h_*M))`, carried to `Hⁿ(X, M)` by `h_* ⟶ Rh_*` and the Leray
identification, is the Čech class over `𝒜` of the same cocycle. -/
theorem sideA'_cls (M : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf A)))
    (hM : M.obj.IsStrictlyGE 0) (n : ℤ)
    (z : ((Stacks.Cech.Hypercohomology.cech A' U hU).obj (pushC h M.obj)).X n)
    (hz : (((Stacks.Cech.Hypercohomology.cech A' U hU).obj (pushC h M.obj)).d n (n + 1)).hom z =
      0) :
    (sideA' h U hU M hM n).hom (cls _ n z hz) = (sideA U hU M n).hom (cls _ n _
      (ecl_cocycle h hh U hU M.obj (isZero_of_isStrictlyGE_zero hM) n z hz)) := by
  have := SheafOfModules.enoughInjectives_opens.{u, u, u} (X := X.carrier) (ringSheaf A)
  obtain ⟨I₀, j₀, hj, hinj, hI⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective M.obj 0
  exact sideA'_cls_of_resolution h hh U hU (I := ⟨I₀, 0, hI⟩) hM hI hinj
    (ObjectProperty.homMk j₀) hj n z hz

end Comparison

end Stacks.Cech.RingChange

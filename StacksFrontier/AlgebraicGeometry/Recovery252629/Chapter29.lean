module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.Topology.Sheaves.Modules.Differentials
public import StacksFrontier.AlgebraicGeometry.DifferentialsAffine.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Derivations on an affine scheme

For a morphism of affine schemes, a derivation of a sheaf of modules is uniquely
determined by, and can be constructed from, its action on global sections.

## Main definitions

* `AlgebraicGeometry.AffineDerivations.globalSectionsDerivation` evaluates a sheaf
  derivation on the top open.

## Main results

* `AlgebraicGeometry.AffineDerivations.globalSectionsDerivation_bijective` says that
  evaluation on global sections is a bijection for an affine scheme.

## Implementation notes

The canonical isomorphisms from the rings of global functions on `Spec R` and
`Spec A` to `R` and `A` are used to transport the derivation on global sections.
In particular, the target is literally the source's set of `R`-derivations on
`Γ(Spec A, F)`.

The two ring-theoretic inputs are reused rather than reproved: a derivation into a
module over a localization is determined by its restriction to the base, and extends
from it. Both come from `Stacks.AlgebraicGeometry.DifferentialsAffine`, whose
`existsUnique_restrictions` is the same tag read on an affine open of an arbitrary
scheme and without a base ring.

## References

* [Stacks Project, Tag 01UO](https://stacks.math.columbia.edu/tag/01UO)
-/

@[expose] public section

open CategoryTheory PresheafOfModules TopologicalSpace AlgebraicGeometry
open Opposite

universe u v

namespace AlgebraicGeometry.AffineDerivations

open scoped RightActions

private noncomputable def structureAddSheaf (A : CommRingCat.{u}) :
    TopCat.Sheaf AddCommGrpCat.{max u v} (Spec A) :=
  (sheafCompose (Opens.grothendieckTopology (Spec A))
    AddCommGrpCat.uliftFunctor.{max u v, u}).obj
      ((SheafOfModules.toSheaf (Spec A).ringCatSheaf).obj
        (SheafOfModules.unit.{u, u, u} (Spec A).ringCatSheaf))

private noncomputable def targetAddSheaf (A : CommRingCat.{u})
    (F : SheafOfModules.{v} (SheafOfModules.underlyingRingSheaf (Spec A).sheaf)) :
    TopCat.Sheaf AddCommGrpCat.{max u v} (Spec A) :=
  (sheafCompose (Opens.grothendieckTopology (Spec A))
    AddCommGrpCat.uliftFunctor.{max u v, v}).obj
      ((SheafOfModules.toSheaf
        (SheafOfModules.underlyingRingSheaf (Spec A).sheaf)).obj F)

private noncomputable def basicAddNatTrans (A : CommRingCat.{u})
    (F : SheafOfModules.{v} (SheafOfModules.underlyingRingSheaf (Spec A).sheaf))
    (d : ∀ a : A,
      (Spec A).presheaf.obj (.op (PrimeSpectrum.basicOpen a)) →+
        F.val.obj (.op (PrimeSpectrum.basicOpen a)))
    (hd : ∀ {a b : A} (i : PrimeSpectrum.basicOpen a ≤ PrimeSpectrum.basicOpen b)
        (x : (Spec A).presheaf.obj (.op (PrimeSpectrum.basicOpen b))),
      d a ((Spec A).presheaf.map (homOfLE i).op x) =
        F.val.map (homOfLE i).op (d b x)) :
    (inducedFunctor (PrimeSpectrum.basicOpen (R := A))).op ⋙
        (structureAddSheaf A).obj ⟶
      (inducedFunctor (PrimeSpectrum.basicOpen (R := A))).op ⋙
        (targetAddSheaf A F).obj := by
  refine { app := fun a => ?_, naturality := ?_ }
  · exact AddCommGrpCat.ofHom
      (AddMonoidHom.mk' (fun x => ULift.up (d a.unop x.down)) fun x y =>
        congrArg ULift.up (map_add (d a.unop) x.down y.down))
  · intro a b i
    ext x
    exact congrArg ULift.up (hd i.1.hom.le x.down)

private noncomputable def extendBasicAddMap (A : CommRingCat.{u})
    (F : SheafOfModules.{v} (SheafOfModules.underlyingRingSheaf (Spec A).sheaf))
    (d : ∀ a : A,
      (Spec A).presheaf.obj (.op (PrimeSpectrum.basicOpen a)) →+
        F.val.obj (.op (PrimeSpectrum.basicOpen a)))
    (hd : ∀ {a b : A} (i : PrimeSpectrum.basicOpen a ≤ PrimeSpectrum.basicOpen b)
        (x : (Spec A).presheaf.obj (.op (PrimeSpectrum.basicOpen b))),
      d a ((Spec A).presheaf.map (homOfLE i).op x) =
        F.val.map (homOfLE i).op (d b x)) :
    structureAddSheaf A ⟶ targetAddSheaf A F :=
  ⟨TopCat.Sheaf.restrictHomEquivHom (structureAddSheaf A).obj
    (targetAddSheaf A F) PrimeSpectrum.isBasis_basic_opens
    (basicAddNatTrans A F d hd)⟩

private theorem extendBasicAddMap_apply (A : CommRingCat.{u})
    (F : SheafOfModules.{v} (SheafOfModules.underlyingRingSheaf (Spec A).sheaf))
    (d : ∀ a : A,
      (Spec A).presheaf.obj (.op (PrimeSpectrum.basicOpen a)) →+
        F.val.obj (.op (PrimeSpectrum.basicOpen a)))
    (hd : ∀ {a b : A} (i : PrimeSpectrum.basicOpen a ≤ PrimeSpectrum.basicOpen b)
        (x : (Spec A).presheaf.obj (.op (PrimeSpectrum.basicOpen b))),
      d a ((Spec A).presheaf.map (homOfLE i).op x) =
        F.val.map (homOfLE i).op (d b x)) (a : A)
    (x : (Spec A).presheaf.obj (.op (PrimeSpectrum.basicOpen a))) :
    (extendBasicAddMap A F d hd).hom.app (.op (PrimeSpectrum.basicOpen a)) (ULift.up x) =
      ULift.up (d a x) := by
  have h := TopCat.Sheaf.extend_hom_app
    (structureAddSheaf A).obj (targetAddSheaf A F)
    PrimeSpectrum.isBasis_basic_opens (basicAddNatTrans A F d hd) a
  convert (congrArg (fun f => f.hom (ULift.up x)) h) using 1
  rfl

open Stacks.AlgebraicGeometry.DifferentialsAffine in
private noncomputable def liftAddHomData
    {R A S M : Type*} [CommRing R] [CommRing A] [CommRing S]
    [AddCommGroup M] [Algebra R A] [Algebra A S] [Algebra R S]
    [IsScalarTower R A S] [Module S M] [Module A M] [Module R M]
    [IsScalarTower A S M] [IsScalarTower R S M]
    (T : Submonoid A) [IsLocalization T S] (D : Derivation R A M) :
    { E : S →+ M // (∀ x y : S, E (x * y) = x • E y + y • E x) ∧
      ∀ a : A, E (algebraMap A S a) = D a } :=
  Classical.indefiniteDescription _
    (exists_addMonoidHom_of_isLocalization T D.toLinearMap.toAddMonoidHom
      (fun a b => by
        simp only [IsScalarTower.algebraMap_smul]
        exact D.leibniz a b))

private noncomputable def derivation_lift_isLocalization
    {R A S M : Type*} [CommRing R] [CommRing A] [CommRing S]
    [AddCommGroup M] [Algebra R A] [Algebra A S] [Algebra R S]
    [IsScalarTower R A S] [Module S M] [Module A M] [Module R M]
    [IsScalarTower A S M] [IsScalarTower R S M]
    (T : Submonoid A) [IsLocalization T S]
    (D : Derivation R A M) : Derivation R S M :=
  Derivation.mk'
    { toFun := ⇑(liftAddHomData T D).val
      map_add' := map_add (liftAddHomData T D).val
      map_smul' := fun r s => by
        have hz : (liftAddHomData T D).val (algebraMap R S r) = 0 := by
          rw [IsScalarTower.algebraMap_apply R A S r,
            (liftAddHomData T D).property.2]
          exact D.map_algebraMap r
        have h := (liftAddHomData T D).property.1 (algebraMap R S r) s
        rw [hz, smul_zero, add_zero] at h
        rw [Algebra.smul_def, h, IsScalarTower.algebraMap_smul]
        rfl }
    (fun a b => (liftAddHomData T D).property.1 a b)

private theorem derivation_lift_isLocalization_apply
    {R A S M : Type*} [CommRing R] [CommRing A] [CommRing S]
    [AddCommGroup M] [Algebra R A] [Algebra A S] [Algebra R S]
    [IsScalarTower R A S] [Module S M] [Module A M] [Module R M]
    [IsScalarTower A S M] [IsScalarTower R S M]
    (T : Submonoid A) [IsLocalization T S]
    (D : Derivation R A M) (a : A) :
    derivation_lift_isLocalization T D (algebraMap A S a) = D a :=
  (liftAddHomData T D).property.2 a

open Stacks.AlgebraicGeometry.DifferentialsAffine in
private theorem additiveDerivation_naturality_of_isLocalization
    {A S T M N : Type*} [CommRing A] [CommRing S] [CommRing T]
    [Algebra A S] [AddCommGroup M] [AddCommGroup N]
    [Module S M] [Module T N]
    (U : Submonoid A) [IsLocalization U S]
    (ρ : S →+* T) (f : M →+ N)
    (hf : ∀ (s : S) (m : M), f (s • m) = ρ s • f m)
    (D : S →+ M) (E : T →+ N)
    (hD : ∀ s t, D (s * t) = s • D t + t • D s)
    (hE : ∀ s t, E (s * t) = s • E t + t • E s)
    (hA : ∀ a : A, f (D (algebraMap A S a)) = E (ρ (algebraMap A S a)))
    (s : S) : f (D s) = E (ρ s) :=
  DFunLike.congr_fun
    (addMonoidHom_eq_of_isLocalization (B := T) U ρ (f.comp D)
      (E.comp ρ.toAddMonoidHom)
      (fun x y => by
        show f (D (x * y)) = ρ x • f (D y) + ρ y • f (D x)
        rw [hD, map_add, hf, hf])
      (fun x y => by
        show E (ρ (x * y)) = ρ x • E (ρ y) + ρ y • E (ρ x)
        rw [map_mul, hE])
      hA)
    s

open Stacks.AlgebraicGeometry.DifferentialsAffine in
private theorem additiveDerivation_ext_of_isLocalization
    {A S M : Type*} [CommRing A] [CommRing S] [Algebra A S]
    [AddCommGroup M] [Module S M]
    (U : Submonoid A) [IsLocalization U S]
    (D E : S →+ M)
    (hD : ∀ s t, D (s * t) = s • D t + t • D s)
    (hE : ∀ s t, E (s * t) = s • E t + t • E s)
    (hA : ∀ a : A, D (algebraMap A S a) = E (algebraMap A S a)) :
    D = E :=
  addMonoidHom_eq_of_isLocalization U (RingHom.id S) D E hD hE hA

open Stacks.AlgebraicGeometry.DifferentialsAffine in
private theorem additiveDerivation_zero_on_localization
    {R S T M : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [AddCommGroup M] [Module T M]
    (U : Submonoid R) [IsLocalization U S]
    (ρ : S →+* T) (D : T →+ M)
    (hD : ∀ s t, D (s * t) = s • D t + t • D s)
    (hR : ∀ r : R, D (ρ (algebraMap R S r)) = 0)
    (s : S) : D (ρ s) = 0 :=
  DFunLike.congr_fun
    (addMonoidHom_eq_of_isLocalization (B := T) U ρ (D.comp ρ.toAddMonoidHom) 0
      (fun x y => by
        show D (ρ (x * y)) = ρ x • D (ρ y) + ρ y • D (ρ x)
        rw [map_mul]
        exact hD (ρ x) (ρ y))
      (fun _ _ => by simp)
      hR)
    s

/-- Evaluate a derivation of a sheaf of modules on the global sections of an
affine scheme, transporting the module structure along the canonical
identification `Γ(Spec A, ⊤) ≅ A`. -/
@[ega "IV 16.5.2"]
noncomputable def globalSectionsDerivation {R A : CommRingCat.{u}} (φ : R ⟶ A)
    (F : SheafOfModules.{v} (SheafOfModules.underlyingRingSheaf (Spec A).sheaf))
    (D : F.val.Derivation (Spec.map φ).c) :
    ((ModuleCat.restrictScalars (Scheme.ΓSpecIso A).inv.hom).obj
      (F.val.obj (op ⊤))).Derivation φ :=
  ModuleCat.Derivation.mk
    (fun a ↦ D.d ((Scheme.ΓSpecIso A).inv a))
    (by
      intro a b
      rw [map_add]
      exact D.d.map_add _ _)
    (by
      intro a b
      let M := F.val.obj (op ⊤)
      let f := (Scheme.ΓSpecIso A).inv.hom
      have ha : a • (show (ModuleCat.restrictScalars f).obj M from
          D.d ((Scheme.ΓSpecIso A).inv b)) =
          (M.smul ((Scheme.ΓSpecIso A).inv a)).hom
            (D.d ((Scheme.ΓSpecIso A).inv b)) :=
        ModuleCat.restrictScalars.smul_def' f a _
      have hb : b • (show (ModuleCat.restrictScalars f).obj M from
          D.d ((Scheme.ΓSpecIso A).inv a)) =
          (M.smul ((Scheme.ΓSpecIso A).inv b)).hom
            (D.d ((Scheme.ΓSpecIso A).inv a)) :=
        ModuleCat.restrictScalars.smul_def' f b _
      rw [map_mul, ha, hb]
      exact D.d_mul _ _)
    (by
      intro r
      rw [← show (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r) =
        (Scheme.ΓSpecIso A).inv (φ r) by
          simpa only [CommRingCat.comp_apply] using
            congrArg (fun f : R ⟶ Γ(Spec A, ⊤) => f r)
              (Scheme.ΓSpecIso_inv_naturality φ).symm]
      exact D.d_app ((Scheme.ΓSpecIso R).inv r))

private noncomputable def basicOpenRingHom (A : CommRingCat.{u}) (a : A) :
    A ⟶ (Spec A).presheaf.obj (.op (PrimeSpectrum.basicOpen a)) :=
  (Scheme.ΓSpecIso A).inv ≫
    (Spec A).presheaf.map (homOfLE le_top).op

/-- The ring map `A ⟶ Γ(Spec A, D(a))` is the structure map of the localization. -/
private theorem basicOpenRingHom_apply (A : CommRingCat.{u}) (a b : A) :
    letI : Algebra A ((Spec A).presheaf.obj (.op (PrimeSpectrum.basicOpen a))) :=
      StructureSheaf.openAlgebra A (.op (PrimeSpectrum.basicOpen a))
    basicOpenRingHom A a b =
      algebraMap A ((Spec A).presheaf.obj (.op (PrimeSpectrum.basicOpen a))) b :=
  congrFun (congrArg DFunLike.coe (congrArg CommRingCat.Hom.hom
    (Scheme.toOpen_eq (R := A) (PrimeSpectrum.basicOpen a)).symm)) b

/-- Two sections of a sheaf of modules that agree on a cover of the open are equal. -/
private theorem sections_ext_of_cover {A : CommRingCat.{u}}
    (F : SheafOfModules.{v} (SheafOfModules.underlyingRingSheaf (Spec A).sheaf))
    {U : Opens (Spec A)} {κ : Type*} (V : κ → Opens (Spec A)) (hle : ∀ k, V k ≤ U)
    (hcov : U ≤ ⨆ k, V k) (x y : F.val.obj (.op U))
    (h : ∀ k, F.val.map (homOfLE (hle k)).op x = F.val.map (homOfLE (hle k)).op y) :
    x = y := by
  apply ULift.up_injective
  refine TopCat.Sheaf.eq_of_locally_eq' (targetAddSheaf A F) V U (fun k => homOfLE (hle k))
    hcov (ULift.up x) (ULift.up y) fun k => by
      apply ULift.ext
      exact h k

/-- Two sections of a sheaf of modules that agree on every basic open inside `U` are equal. -/
private theorem sections_ext_of_basicOpen {A : CommRingCat.{u}}
    (F : SheafOfModules.{v} (SheafOfModules.underlyingRingSheaf (Spec A).sheaf))
    {U : Opens (Spec A)} (x y : F.val.obj (.op U))
    (h : ∀ (a : A) (hle : PrimeSpectrum.basicOpen a ≤ U),
      F.val.map (homOfLE hle).op x = F.val.map (homOfLE hle).op y) : x = y := by
  obtain ⟨κ, a, hU⟩ := PrimeSpectrum.isBasis_basic_opens.exists_iSup_eq U
  have hle (k : κ) : PrimeSpectrum.basicOpen (a k) ≤ U :=
    hU ▸ le_iSup (fun k => PrimeSpectrum.basicOpen (a k)) k
  exact sections_ext_of_cover F _ hle (le_of_eq hU) x y fun k => h (a k) (hle k)

private noncomputable def restrictedGlobalDerivation {R A : CommRingCat.{u}}
    (φ : R ⟶ A)
    (F : SheafOfModules.{v} (SheafOfModules.underlyingRingSheaf (Spec A).sheaf))
    (d : ((ModuleCat.restrictScalars (Scheme.ΓSpecIso A).inv.hom).obj
      (F.val.obj (op ⊤))).Derivation φ) (a : A) :
    ((ModuleCat.restrictScalars (basicOpenRingHom A a).hom).obj
      (F.val.obj (.op (PrimeSpectrum.basicOpen a)))).Derivation φ :=
  ModuleCat.Derivation.mk
    (fun b ↦ F.val.map (homOfLE le_top).op (d.d b))
    (by
      intro b c
      rw [d.d_add]
      exact map_add (F.val.map (homOfLE le_top).op).hom _ _)
    (by
      intro b c
      rw [d.d_mul]
      change (F.val.map (homOfLE le_top).op).hom
          ((show (SheafOfModules.underlyingRingSheaf (Spec A).sheaf).obj.obj (op ⊤)
              from (Scheme.ΓSpecIso A).inv b) •
              (show F.val.obj (op ⊤) from d.d c) +
            (show (SheafOfModules.underlyingRingSheaf (Spec A).sheaf).obj.obj (op ⊤)
              from (Scheme.ΓSpecIso A).inv c) •
              (show F.val.obj (op ⊤) from d.d b)) =
        (show (SheafOfModules.underlyingRingSheaf (Spec A).sheaf).obj.obj
            (.op (PrimeSpectrum.basicOpen a)) from basicOpenRingHom A a b) •
            (show F.val.obj (.op (PrimeSpectrum.basicOpen a)) from
              F.val.map (homOfLE le_top).op (d.d c)) +
          (show (SheafOfModules.underlyingRingSheaf (Spec A).sheaf).obj.obj
            (.op (PrimeSpectrum.basicOpen a)) from basicOpenRingHom A a c) •
            (show F.val.obj (.op (PrimeSpectrum.basicOpen a)) from
              F.val.map (homOfLE le_top).op (d.d b))
      rw [map_add, F.val.map_smul, F.val.map_smul]
      rfl)
    (by
      intro r
      change F.val.map (homOfLE le_top).op (d.d (φ r)) = 0
      rw [d.d_map]
      exact map_zero (F.val.map (homOfLE le_top).op).hom)

private noncomputable def basicOpenDerivationData {R A : CommRingCat.{u}}
    (φ : R ⟶ A)
    (F : SheafOfModules.{v} (SheafOfModules.underlyingRingSheaf (Spec A).sheaf))
    (d : ((ModuleCat.restrictScalars (Scheme.ΓSpecIso A).inv.hom).obj
      (F.val.obj (op ⊤))).Derivation φ) (a : A) :
    { e : (F.val.obj (.op (PrimeSpectrum.basicOpen a))).Derivation
        (φ ≫ basicOpenRingHom A a) //
      ∀ b : A, e.d (basicOpenRingHom A a b) =
        F.val.map (homOfLE le_top).op (d.d b) } := by
  let S := (Spec A).presheaf.obj (.op (PrimeSpectrum.basicOpen a))
  let M := F.val.obj (.op (PrimeSpectrum.basicOpen a))
  letI : Algebra R A := φ.hom.toAlgebra
  letI : Algebra A S := StructureSheaf.openAlgebra A
    (.op (PrimeSpectrum.basicOpen a))
  have hρ : (basicOpenRingHom A a).hom = algebraMap A S :=
    RingHom.ext (basicOpenRingHom_apply A a)
  letI : Algebra R S := (φ ≫ basicOpenRingHom A a).hom.toAlgebra
  letI : IsScalarTower R A S := IsScalarTower.of_algebraMap_smul fun r s => by
    simp only [Algebra.smul_def]
    change (algebraMap A S (φ r)) * s = ((φ ≫ basicOpenRingHom A a) r) * s
    rw [← hρ]
    rfl
  letI : Module S M := by
    change Module ((SheafOfModules.underlyingRingSheaf (Spec A).sheaf).obj.obj
      (.op (PrimeSpectrum.basicOpen a))) M
    infer_instance
  letI : Module A M := Module.compHom M (basicOpenRingHom A a).hom
  letI : Module R M := Module.compHom M (φ ≫ basicOpenRingHom A a).hom
  letI : IsScalarTower A S M := IsScalarTower.of_algebraMap_smul fun r m => by
    rw [← hρ]
    rfl
  letI : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : IsLocalization (.powers a) S := inferInstanceAs
    (IsLocalization.Away a ((Spec.structureSheaf A).obj.obj
      (.op (PrimeSpectrum.basicOpen a))))
  let d₀ : Derivation R A M := restrictedGlobalDerivation φ F d a
  let d₁ : Derivation R S M :=
    derivation_lift_isLocalization (R := R) (A := A) (S := S) (M := M)
      (.powers a) d₀
  refine ⟨d₁, fun b => ?_⟩
  change d₁ (basicOpenRingHom A a b) =
    F.val.map (homOfLE le_top).op (d.d b)
  rw [show basicOpenRingHom A a b = algebraMap A S b from
    congrFun (congrArg DFunLike.coe hρ) b, derivation_lift_isLocalization_apply]
  rfl

private noncomputable def basicOpenDerivation {R A : CommRingCat.{u}}
    (φ : R ⟶ A)
    (F : SheafOfModules.{v} (SheafOfModules.underlyingRingSheaf (Spec A).sheaf))
    (d : ((ModuleCat.restrictScalars (Scheme.ΓSpecIso A).inv.hom).obj
      (F.val.obj (op ⊤))).Derivation φ) (a : A) :
    (F.val.obj (.op (PrimeSpectrum.basicOpen a))).Derivation
      (φ ≫ basicOpenRingHom A a) :=
  (basicOpenDerivationData φ F d a).val

private theorem basicOpenDerivation_on_algebraMap {R A : CommRingCat.{u}}
    (φ : R ⟶ A)
    (F : SheafOfModules.{v} (SheafOfModules.underlyingRingSheaf (Spec A).sheaf))
    (d : ((ModuleCat.restrictScalars (Scheme.ΓSpecIso A).inv.hom).obj
      (F.val.obj (op ⊤))).Derivation φ) (a b : A) :
    (basicOpenDerivation φ F d a).d (basicOpenRingHom A a b) =
      F.val.map (homOfLE le_top).op (d.d b) :=
  (basicOpenDerivationData φ F d a).property b

private theorem basicOpenDerivation_natural {R A : CommRingCat.{u}}
    (φ : R ⟶ A)
    (F : SheafOfModules.{v} (SheafOfModules.underlyingRingSheaf (Spec A).sheaf))
    (d : ((ModuleCat.restrictScalars (Scheme.ΓSpecIso A).inv.hom).obj
      (F.val.obj (op ⊤))).Derivation φ)
    {a b : A} (i : PrimeSpectrum.basicOpen a ≤ PrimeSpectrum.basicOpen b)
    (x : (Spec A).presheaf.obj (.op (PrimeSpectrum.basicOpen b))) :
    (basicOpenDerivation φ F d a).d
        ((Spec A).presheaf.map (homOfLE i).op x) =
      F.val.map (homOfLE i).op ((basicOpenDerivation φ F d b).d x) := by
  let S := (Spec A).presheaf.obj (.op (PrimeSpectrum.basicOpen b))
  let T := (Spec A).presheaf.obj (.op (PrimeSpectrum.basicOpen a))
  let M := F.val.obj (.op (PrimeSpectrum.basicOpen b))
  let N := F.val.obj (.op (PrimeSpectrum.basicOpen a))
  let ρ : S →+* T := ((Spec A).presheaf.map (homOfLE i).op).hom
  let f : M →+ N := (F.val.map (homOfLE i).op).hom.toAddMonoidHom
  let : Algebra A S := StructureSheaf.openAlgebra A (.op (PrimeSpectrum.basicOpen b))
  let : Module S M := by
    show Module ((SheafOfModules.underlyingRingSheaf (Spec A).sheaf).obj.obj
      (.op (PrimeSpectrum.basicOpen b))) M
    infer_instance
  let : Module T N := by
    show Module ((SheafOfModules.underlyingRingSheaf (Spec A).sheaf).obj.obj
      (.op (PrimeSpectrum.basicOpen a))) N
    infer_instance
  let : IsLocalization (.powers b) S := inferInstanceAs
    (IsLocalization.Away b ((Spec.structureSheaf A).obj.obj
      (.op (PrimeSpectrum.basicOpen b))))
  let Db : S →+ M := AddMonoidHom.mk'
    (fun s => (basicOpenDerivation φ F d b).d s)
    (fun s t => (basicOpenDerivation φ F d b).d_add s t)
  let Ea : T →+ N := AddMonoidHom.mk'
    (fun t => (basicOpenDerivation φ F d a).d t)
    (fun s t => (basicOpenDerivation φ F d a).d_add s t)
  exact (additiveDerivation_naturality_of_isLocalization (.powers b) ρ f
    (fun s m => F.val.map_smul (homOfLE i).op s m) Db Ea
    (fun s t => (basicOpenDerivation φ F d b).d_mul s t)
    (fun s t => (basicOpenDerivation φ F d a).d_mul s t)
    (by
      intro c
      show F.val.map (homOfLE i).op
          ((basicOpenDerivation φ F d b).d (algebraMap A S c)) =
        (basicOpenDerivation φ F d a).d
          ((Spec A).presheaf.map (homOfLE i).op (algebraMap A S c))
      rw [← basicOpenRingHom_apply A b c, basicOpenDerivation_on_algebraMap]
      rw [show (Spec A).presheaf.map (homOfLE i).op
          (basicOpenRingHom A b c) = basicOpenRingHom A a c by
        let p := (homOfLE (show PrimeSpectrum.basicOpen b ≤ ⊤ from le_top)).op
        let q := (homOfLE i).op
        let r := (homOfLE (show PrimeSpectrum.basicOpen a ≤ ⊤ from le_top)).op
        have hpqr : p ≫ q = r := Subsingleton.elim _ _
        have hm : (Spec A).presheaf.map p ≫ (Spec A).presheaf.map q =
            (Spec A).presheaf.map r :=
          (Functor.map_comp (Spec A).presheaf p q).symm.trans
            (congrArg (Spec A).presheaf.map hpqr)
        exact congrArg (fun g : A ⟶ T => g c) (by
          show ((Scheme.ΓSpecIso A).inv ≫ (Spec A).presheaf.map p) ≫
            (Spec A).presheaf.map q =
            (Scheme.ΓSpecIso A).inv ≫ (Spec A).presheaf.map r
          exact (Category.assoc _ _ _).trans
            (congrArg ((Scheme.ΓSpecIso A).inv ≫ ·) hm))]
      rw [basicOpenDerivation_on_algebraMap]
      let p := (homOfLE (show PrimeSpectrum.basicOpen b ≤ ⊤ from le_top)).op
      let q := (homOfLE i).op
      let r := (homOfLE (show PrimeSpectrum.basicOpen a ≤ ⊤ from le_top)).op
      exact (F.val.map_comp_apply p q (d.d c)).symm.trans
        (F.val.congr_map_apply (Subsingleton.elim (p ≫ q) r) (d.d c)))
    x).symm

private noncomputable def basicOpenAddHom {R A : CommRingCat.{u}}
    (φ : R ⟶ A)
    (F : SheafOfModules.{v} (SheafOfModules.underlyingRingSheaf (Spec A).sheaf))
    (d : ((ModuleCat.restrictScalars (Scheme.ΓSpecIso A).inv.hom).obj
      (F.val.obj (op ⊤))).Derivation φ) (a : A) :
    (Spec A).presheaf.obj (.op (PrimeSpectrum.basicOpen a)) →+
      F.val.obj (.op (PrimeSpectrum.basicOpen a)) :=
  AddMonoidHom.mk' (fun x => (basicOpenDerivation φ F d a).d x)
    (fun x y => (basicOpenDerivation φ F d a).d_add x y)

private noncomputable def affineAddMap {R A : CommRingCat.{u}}
    (φ : R ⟶ A)
    (F : SheafOfModules.{v} (SheafOfModules.underlyingRingSheaf (Spec A).sheaf))
    (d : ((ModuleCat.restrictScalars (Scheme.ΓSpecIso A).inv.hom).obj
      (F.val.obj (op ⊤))).Derivation φ) :
    structureAddSheaf A ⟶ targetAddSheaf A F :=
  extendBasicAddMap A F (basicOpenAddHom φ F d)
    (fun i x => basicOpenDerivation_natural φ F d i x)

private noncomputable def affineSectionAddHom {R A : CommRingCat.{u}}
    (φ : R ⟶ A)
    (F : SheafOfModules.{v} (SheafOfModules.underlyingRingSheaf (Spec A).sheaf))
    (d : ((ModuleCat.restrictScalars (Scheme.ΓSpecIso A).inv.hom).obj
      (F.val.obj (op ⊤))).Derivation φ) (U : (Opens (Spec A))ᵒᵖ) :
    (Spec A).presheaf.obj U →+ F.val.obj U :=
  AddMonoidHom.mk'
    (fun x => ((affineAddMap φ F d).hom.app U (ULift.up x)).down)
    (fun x y => congrArg ULift.down
      (((affineAddMap φ F d).hom.app U).hom.map_add (ULift.up x) (ULift.up y)))

private theorem affineSectionAddHom_basic {R A : CommRingCat.{u}}
    (φ : R ⟶ A)
    (F : SheafOfModules.{v} (SheafOfModules.underlyingRingSheaf (Spec A).sheaf))
    (d : ((ModuleCat.restrictScalars (Scheme.ΓSpecIso A).inv.hom).obj
      (F.val.obj (op ⊤))).Derivation φ) (a : A)
    (x : (Spec A).presheaf.obj (.op (PrimeSpectrum.basicOpen a))) :
    affineSectionAddHom φ F d (.op (PrimeSpectrum.basicOpen a)) x =
      (basicOpenDerivation φ F d a).d x := by
  show ((affineAddMap φ F d).hom.app (.op (PrimeSpectrum.basicOpen a))
    (ULift.up x)).down = _
  unfold affineAddMap
  exact congrArg ULift.down
    (extendBasicAddMap_apply A F (basicOpenAddHom φ F d)
      (fun i x => basicOpenDerivation_natural φ F d i x) a x)

private theorem affineSectionAddHom_natural {R A : CommRingCat.{u}}
    (φ : R ⟶ A)
    (F : SheafOfModules.{v} (SheafOfModules.underlyingRingSheaf (Spec A).sheaf))
    (d : ((ModuleCat.restrictScalars (Scheme.ΓSpecIso A).inv.hom).obj
      (F.val.obj (op ⊤))).Derivation φ)
    {U V : (Opens (Spec A))ᵒᵖ} (f : U ⟶ V)
    (x : (Spec A).presheaf.obj U) :
    affineSectionAddHom φ F d V ((Spec A).presheaf.map f x) =
      F.val.map f (affineSectionAddHom φ F d U x) := by
  have h := congrArg (fun g => g.hom (ULift.up x))
    ((affineAddMap φ F d).hom.naturality f)
  convert congrArg ULift.down h using 1
  rfl

private theorem affineSectionAddHom_mul {R A : CommRingCat.{u}}
    (φ : R ⟶ A)
    (F : SheafOfModules.{v} (SheafOfModules.underlyingRingSheaf (Spec A).sheaf))
    (d : ((ModuleCat.restrictScalars (Scheme.ΓSpecIso A).inv.hom).obj
      (F.val.obj (op ⊤))).Derivation φ)
    (U : Opens (Spec A)) (x y : (Spec A).presheaf.obj (.op U)) :
    affineSectionAddHom φ F d (.op U) (x * y) =
      (show (SheafOfModules.underlyingRingSheaf (Spec A).sheaf).obj.obj (.op U)
        from x) • affineSectionAddHom φ F d (.op U) y +
        (show (SheafOfModules.underlyingRingSheaf (Spec A).sheaf).obj.obj (.op U)
          from y) • affineSectionAddHom φ F d (.op U) x := by
  refine sections_ext_of_basicOpen F _ _ fun a hle => ?_
  refine (affineSectionAddHom_natural φ F d (homOfLE hle).op (x * y)).symm.trans ?_
  refine (congrArg (affineSectionAddHom φ F d (.op (PrimeSpectrum.basicOpen a)))
    (((Spec A).presheaf.map (homOfLE hle).op).hom.map_mul x y)).trans ?_
  have hsmul (u v : (Spec A).presheaf.obj (.op U)) :
      (show (SheafOfModules.underlyingRingSheaf (Spec A).sheaf).obj.obj
        (.op (PrimeSpectrum.basicOpen a)) from (Spec A).presheaf.map (homOfLE hle).op u) •
        affineSectionAddHom φ F d (.op (PrimeSpectrum.basicOpen a))
          ((Spec A).presheaf.map (homOfLE hle).op v) =
      F.val.map (homOfLE hle).op
        ((show (SheafOfModules.underlyingRingSheaf (Spec A).sheaf).obj.obj (.op U)
          from u) • affineSectionAddHom φ F d (.op U) v) :=
    (congrArg _ (affineSectionAddHom_natural φ F d (homOfLE hle).op v)).trans
      (F.val.map_smul (homOfLE hle).op _ _).symm
  refine Eq.trans ?_ (map_add (F.val.map (homOfLE hle).op).hom _ _).symm
  rw [← hsmul, ← hsmul]
  refine (affineSectionAddHom_basic φ F d a _).trans
    (((basicOpenDerivation φ F d a).d_mul _ _).trans ?_)
  erw [affineSectionAddHom_basic, affineSectionAddHom_basic]
  rfl

private theorem existingDerivation_basic {R A : CommRingCat.{u}}
    (φ : R ⟶ A)
    (F : SheafOfModules.{v} (SheafOfModules.underlyingRingSheaf (Spec A).sheaf))
    (D : F.val.Derivation (Spec.map φ).c) (a : A)
    (x : (Spec A).presheaf.obj (.op (PrimeSpectrum.basicOpen a))) :
    D.d x = (basicOpenDerivation φ F (globalSectionsDerivation φ F D) a).d x := by
  let S := (Spec A).presheaf.obj (.op (PrimeSpectrum.basicOpen a))
  let M := F.val.obj (.op (PrimeSpectrum.basicOpen a))
  let : Algebra A S := StructureSheaf.openAlgebra A (.op (PrimeSpectrum.basicOpen a))
  let : Module S M := by
    show Module ((SheafOfModules.underlyingRingSheaf (Spec A).sheaf).obj.obj
      (.op (PrimeSpectrum.basicOpen a))) M
    infer_instance
  let : IsLocalization (.powers a) S := inferInstanceAs
    (IsLocalization.Away a ((Spec.structureSheaf A).obj.obj
      (.op (PrimeSpectrum.basicOpen a))))
  let D₁ : S →+ M := D.d
  let D₂ : S →+ M := basicOpenAddHom φ F (globalSectionsDerivation φ F D) a
  exact DFunLike.congr_fun (additiveDerivation_ext_of_isLocalization (.powers a)
    D₁ D₂ (fun s t => D.d_mul s t)
    (fun s t => (basicOpenDerivation φ F (globalSectionsDerivation φ F D) a).d_mul s t)
    (by
      intro b
      show D.d (algebraMap A S b) =
        (basicOpenDerivation φ F (globalSectionsDerivation φ F D) a).d
          (algebraMap A S b)
      rw [← basicOpenRingHom_apply A a b, basicOpenDerivation_on_algebraMap]
      exact D.d_map (homOfLE le_top).op ((Scheme.ΓSpecIso A).inv b))) x

private theorem globalSectionsDerivation_injective {R A : CommRingCat.{u}}
    (φ : R ⟶ A)
    (F : SheafOfModules.{v} (SheafOfModules.underlyingRingSheaf (Spec A).sheaf)) :
    Function.Injective (globalSectionsDerivation φ F) := by
  intro D E h
  ext U x
  refine sections_ext_of_basicOpen F _ _ fun a hle => ?_
  have hbasic : D.d ((Spec A).presheaf.map (homOfLE hle).op x) =
      E.d ((Spec A).presheaf.map (homOfLE hle).op x) :=
    (existingDerivation_basic φ F D a _).trans
      ((congrArg (fun d => (basicOpenDerivation φ F d a).d
        ((Spec A).presheaf.map (homOfLE hle).op x)) h).trans
        (existingDerivation_basic φ F E a _).symm)
  exact (D.d_map (homOfLE hle).op x).symm.trans (hbasic.trans (E.d_map (homOfLE hle).op x))

private theorem basicOpenDerivation_base {R A : CommRingCat.{u}}
    (φ : R ⟶ A)
    (F : SheafOfModules.{v} (SheafOfModules.underlyingRingSheaf (Spec A).sheaf))
    (d : ((ModuleCat.restrictScalars (Scheme.ΓSpecIso A).inv.hom).obj
      (F.val.obj (op ⊤))).Derivation φ) (r : R)
    (x : (Spec R).presheaf.obj (.op (PrimeSpectrum.basicOpen r))) :
    (basicOpenDerivation φ F d (φ r)).d
      ((Spec.map φ).app (PrimeSpectrum.basicOpen r) x) = 0 := by
  let S := (Spec R).presheaf.obj (.op (PrimeSpectrum.basicOpen r))
  let T := (Spec A).presheaf.obj (.op (PrimeSpectrum.basicOpen (φ r)))
  let M := F.val.obj (.op (PrimeSpectrum.basicOpen (φ r)))
  let : Algebra R S := StructureSheaf.openAlgebra R (.op (PrimeSpectrum.basicOpen r))
  let : IsLocalization (.powers r) S := inferInstanceAs
    (IsLocalization.Away r ((Spec.structureSheaf R).obj.obj
      (.op (PrimeSpectrum.basicOpen r))))
  let ρ : S →+* T := ((Spec.map φ).app (PrimeSpectrum.basicOpen r)).hom
  let : Module T M := by
    show Module ((SheafOfModules.underlyingRingSheaf (Spec A).sheaf).obj.obj
      (.op (PrimeSpectrum.basicOpen (φ r)))) M
    infer_instance
  let D : T →+ M := basicOpenAddHom φ F d (φ r)
  have hcomm (s : R) : ρ (algebraMap R S s) = basicOpenRingHom A (φ r) (φ s) := by
    have he : basicOpenRingHom R r ≫ (Spec.map φ).app (PrimeSpectrum.basicOpen r) =
        φ ≫ basicOpenRingHom A (φ r) := by
      unfold basicOpenRingHom
      have hn : (Spec R).presheaf.map
          (homOfLE (show PrimeSpectrum.basicOpen r ≤ ⊤ from le_top)).op ≫
          (Spec.map φ).app (PrimeSpectrum.basicOpen r) =
          (Spec.map φ).appTop ≫ (Spec A).presheaf.map
            (homOfLE (show PrimeSpectrum.basicOpen (φ r) ≤ ⊤ from le_top)).op := by
        convert (Spec.map φ).naturality
            (homOfLE (show PrimeSpectrum.basicOpen r ≤ ⊤ from le_top)).op using 1
        rfl
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (fun g => (Scheme.ΓSpecIso R).inv ≫ g) hn).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (fun g => g ≫ (Spec A).presheaf.map
          (homOfLE (show PrimeSpectrum.basicOpen (φ r) ≤ ⊤ from le_top)).op)
        (Scheme.ΓSpecIso_inv_naturality φ).symm).trans ?_
      exact Category.assoc _ _ _
    rw [← basicOpenRingHom_apply R r s]
    exact congrArg (fun f : R ⟶ T => f s) he
  exact additiveDerivation_zero_on_localization (.powers r) ρ D
    (fun s t => (basicOpenDerivation φ F d (φ r)).d_mul s t)
    (fun s => by
      rw [hcomm]
      show (basicOpenDerivation φ F d (φ r)).d
        (basicOpenRingHom A (φ r) (φ s)) = 0
      rw [basicOpenDerivation_on_algebraMap, d.d_map]
      exact map_zero (F.val.map (homOfLE le_top).op).hom) x

private theorem affineSectionAddHom_base {R A : CommRingCat.{u}}
    (φ : R ⟶ A)
    (F : SheafOfModules.{v} (SheafOfModules.underlyingRingSheaf (Spec A).sheaf))
    (d : ((ModuleCat.restrictScalars (Scheme.ΓSpecIso A).inv.hom).obj
      (F.val.obj (op ⊤))).Derivation φ)
    (W : Opens (Spec R)) (x : (Spec R).presheaf.obj (.op W)) :
    affineSectionAddHom φ F d (.op ((Spec.map φ) ⁻¹ᵁ W))
      ((Spec.map φ).app W x) = 0 := by
  obtain ⟨κ, r, hW⟩ := PrimeSpectrum.isBasis_basic_opens.exists_iSup_eq W
  have hr (k : κ) : PrimeSpectrum.basicOpen (r k) ≤ W := by
    rw [hW]
    exact le_iSup (fun k => PrimeSpectrum.basicOpen (r k)) k
  have hpre : (Spec.map φ) ⁻¹ᵁ W =
      ⨆ k, (Spec.map φ) ⁻¹ᵁ PrimeSpectrum.basicOpen (r k) := by
    rw [hW]
    exact TopologicalSpace.Opens.map_iSup _ _
  have hcover : (⨆ k, PrimeSpectrum.basicOpen (φ (r k))) =
      (Spec.map φ) ⁻¹ᵁ W :=
    (iSup_congr fun k => (SpecMap_preimage_basicOpen φ (r k)).symm).trans hpre.symm
  have hle (k : κ) : PrimeSpectrum.basicOpen (φ (r k)) ≤
      (Spec.map φ) ⁻¹ᵁ W := by
    rw [← hcover]
    exact le_iSup (fun k => PrimeSpectrum.basicOpen (φ (r k))) k
  refine sections_ext_of_cover F (fun k : κ => PrimeSpectrum.basicOpen (φ (r k))) hle
    (le_of_eq hcover.symm) _ 0 fun k => ?_
  rw [map_zero]
  let y := (Spec R).presheaf.map (homOfLE (hr k)).op x
  have hn : (Spec A).presheaf.map (homOfLE (hle k)).op
      ((Spec.map φ).app W x) =
      (Spec.map φ).app (PrimeSpectrum.basicOpen (r k)) y := by
    convert (congrArg (fun f => f x)
      ((Spec.map φ).naturality (homOfLE (hr k)).op)).symm using 1
    rfl
  refine (affineSectionAddHom_natural φ F d (homOfLE (hle k)).op
    ((Spec.map φ).app W x)).symm.trans ?_
  refine (congrArg (affineSectionAddHom φ F d
    (.op (PrimeSpectrum.basicOpen (φ (r k))))) hn).trans ?_
  refine (affineSectionAddHom_basic φ F d (φ (r k)) _).trans ?_
  exact basicOpenDerivation_base φ F d (r k) y

/-- **Stacks Project, Tag 01UO.** On an affine scheme, evaluation on global
sections gives a bijection from relative sheaf derivations to relative ring
derivations. -/
@[stacks 01UO, ega "IV 16.5.2"]
theorem globalSectionsDerivation_bijective {R A : CommRingCat.{u}} (φ : R ⟶ A)
    (F : SheafOfModules.{v} (SheafOfModules.underlyingRingSheaf (Spec A).sheaf)) :
    Function.Bijective (globalSectionsDerivation φ F) := by
  refine ⟨globalSectionsDerivation_injective φ F, ?_⟩
  intro d
  let D : F.val.Derivation (Spec.map φ).c := {
    d := affineSectionAddHom φ F d _
    d_mul := fun {U} x y => affineSectionAddHom_mul φ F d U.unop x y
    d_map := affineSectionAddHom_natural φ F d
    d_app := fun {W} x => affineSectionAddHom_base φ F d W.unop x }
  refine ⟨D, ?_⟩
  let : Algebra R A := φ.hom.toAlgebra
  let : Module R ((ModuleCat.restrictScalars (Scheme.ΓSpecIso A).inv.hom).obj
      (F.val.obj (op ⊤))) := Module.compHom _ φ.hom
  apply _root_.Derivation.ext
  intro a
  show affineSectionAddHom φ F d (.op ⊤) ((Scheme.ΓSpecIso A).inv a) = d.d a
  let p := (homOfLE (show PrimeSpectrum.basicOpen (1 : A) ≤ ⊤ from le_top)).op
  refine sections_ext_of_cover F (fun _ : Unit => PrimeSpectrum.basicOpen (1 : A))
    (fun _ => le_top) (by
      rw [PrimeSpectrum.basicOpen_one]
      exact le_iSup_of_le () le_rfl) _ _ fun _ => ?_
  have hx : (Spec A).presheaf.map p ((Scheme.ΓSpecIso A).inv a) =
      basicOpenRingHom A 1 a := rfl
  refine (affineSectionAddHom_natural φ F d p
    ((Scheme.ΓSpecIso A).inv a)).symm.trans ?_
  refine (congrArg (affineSectionAddHom φ F d
    (.op (PrimeSpectrum.basicOpen (1 : A)))) hx).trans ?_
  refine (affineSectionAddHom_basic φ F d 1 _).trans ?_
  exact basicOpenDerivation_on_algebraMap φ F d 1 a

end AlgebraicGeometry.AffineDerivations

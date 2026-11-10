module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedBoundedCohomologicalDimension
public import StacksFrontier.CategoryTheory.Triangulated.CompactObjectsFromCoyoneda
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroUnitSections
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Homology.Injectives.DerivedCategory.ProductsAndCoproducts
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.SheafifiedCohomologyPresheaf
import StacksCore.Tactic.StacksAttribute

/-!
# Compactness of extension by zero from an object of a ringed site

Let `(C, O)` be a ringed site and let `U` be an object of `C`. If there is an integer `d` with
`H^p(U, F) = 0` for all `p > d` and all `O`-modules `F`, and if the functors `F ↦ H^p(U, F)`
commute with direct sums, then the `O`-module `j_{U!} O_U` — the extension by zero of the
structure sheaf of the localized site — is a compact object of the unbounded derived category
`D(O)`.

## Main results

* `Stacks.Cohomology.CompactExtensionByZero.coyonedaIsoEvaluation`: the isomorphism of additive
  functors `Hom(j_{U!}O_U, -) ≅ Γ(U, -)`.
* `Stacks.Cohomology.CompactExtensionByZero.isCompactObject_extensionByZeroUnit`:
  `j_{U!}O_U` is a compact object of the abelian category of `O`-modules as soon as
  `H^0(U, -)` commutes with direct sums.
* `Stacks.Cohomology.CompactExtensionByZero.rightAcyclic_coproduct_of_injectives`: a direct sum
  of injective objects is right acyclic for a left exact functor whose higher right derived
  functors commute with that direct sum.
* `Stacks.Cohomology.CompactExtensionByZero.hasRightDerivedFunctor_and_computed_by_rightAcyclic`:
  a left exact functor of finite cohomological dimension on a category with enough injectives has
  a right derived functor on the unbounded derived category, computed by complexes of right
  acyclic objects.
* `Stacks.Cohomology.CompactExtensionByZero.Q_map_surjective_of_rightAcyclic_terms`: a morphism
  of `D(A)` out of `M[0]` into a complex with right acyclic terms is represented by a morphism of
  complexes, provided `Hom(M, -)` is the functor being derived.
* `Stacks.Cohomology.CompactExtensionByZero.exists_finsum_derived`: the finite decomposition of a
  morphism from `j_{U!}O_U[0]` into a direct sum.
* `Stacks.Cohomology.CompactExtensionByZero.isCompactObject_singleFunctor_extensionByZeroUnit`:
  if `Γ(U, -)` has finite cohomological dimension and its right derived functors commute with
  direct sums, then `j_{U!}O_U[0]` is a compact object of `D(O)`.

## References

* [Stacks Project, Tag 094D](https://stacks.math.columbia.edu/tag/094D)
* [Stacks Project, Tag 0G1V](https://stacks.math.columbia.edu/tag/0G1V)
* [Stacks Project, Tag 07K7](https://stacks.math.columbia.edu/tag/07K7)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 07D9](https://stacks.math.columbia.edu/tag/07D9)
* [Stacks Project, Tag 0936](https://stacks.math.columbia.edu/tag/0936)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CochainComplex CochainComplex.HomComplex

namespace Stacks.Cohomology.CompactExtensionByZero

universe u w wg v₁ u₁ v₂ u₂

/-! ## Generic: Hom complexes out of a single object -/

section GenericHom

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasZeroObject C]

/-- **The Hom complex out of an object in degree zero is the degreewise corepresented
complex.** In degree `i` both are the group of morphisms `M ⟶ Lⁱ`. -/
def homComplexSingleIso (M : C) (L : CochainComplex C ℤ) :
    ((CochainComplex.singleFunctor C 0).obj M).HomComplex L ≅
      ((preadditiveCoyoneda.obj (op M)).mapHomologicalComplex (ComplexShape.up ℤ)).obj L :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ (Cochain.fromSingleEquiv (X := M) (K := L) (p := 0) (q := i) (n := i)
      (by omega)).toAddCommGrpIso)
    (by
      intro i j _
      ext x
      obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective x i (by omega)
      symm
      change Cochain.fromSingleEquiv (by omega : (0 : ℤ) + j = j)
          (δ i j (Cochain.fromSingleMk f (by omega : (0 : ℤ) + i = i))) =
        Cochain.fromSingleEquiv (by omega : (0 : ℤ) + i = i)
          (Cochain.fromSingleMk f (by omega : (0 : ℤ) + i = i)) ≫ L.d i j
      rw [Cochain.δ_fromSingleMk f (by omega : (0 : ℤ) + i = i) j j (by omega),
        Cochain.fromSingleEquiv_fromSingleMk, Cochain.fromSingleEquiv_fromSingleMk])

/-- **The cohomology of the degreewise corepresented complex is the group of morphisms in the
homotopy category.** -/
def homologyCoyonedaAddEquiv (M : C) (L : CochainComplex C ℤ) (n : ℤ) :
    (((preadditiveCoyoneda.obj (op M)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        L).homology n ≃+
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
          ((CochainComplex.singleFunctor C 0).obj M) ⟶
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
          ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) n).obj L)) :=
  (HomologicalComplex.homologyMapIso (homComplexSingleIso M L)
      n).symm.addCommGroupIsoToAddEquiv.trans
    ((HomComplex.homologyAddEquiv _ L n).trans HomComplex.CohomologyClass.homAddEquiv)

/-- **Vanishing of the degree-zero cohomology of the corepresented complex kills every
morphism out of `M[0]` in the homotopy category.** -/
theorem eq_zero_of_isZero_homology_zero (M : C) (L : HomotopyCategory C (ComplexShape.up ℤ))
    (h : IsZero ((((preadditiveCoyoneda.obj (op M)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L.as).homology 0))
    (f : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
      ((CochainComplex.singleFunctor C 0).obj M) ⟶ L) : f = 0 := by
  have e := homologyCoyonedaAddEquiv M L.as 0
  have hsub := AddCommGrpCat.subsingleton_of_isZero h
  have hf : f ≫ (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
      ((shiftFunctorZero (CochainComplex C ℤ) ℤ).inv.app L.as) = 0 := by
    have he : e.symm (f ≫ (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((shiftFunctorZero (CochainComplex C ℤ) ℤ).inv.app L.as)) = 0 :=
      Subsingleton.elim _ _
    exact (e.apply_symm_apply _).symm.trans ((congrArg e he).trans e.map_zero)
  exact (cancel_mono ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
    ((shiftFunctorZero (CochainComplex C ℤ) ℤ).inv.app L.as))).1 (hf.trans zero_comp.symm)

end GenericHom

/-! ## Generic: derived functors of finite cohomological dimension -/

section GenericDerived

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

omit [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C] in
/-- The quasi-isomorphisms of `K⁺(A)` admit a left calculus of fractions. -/
lemma quasiIsoPlusLeftFractions :
    (HomotopyCategory.Plus.quasiIso C).HasLeftCalculusOfFractions := by
  rw [HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW]
  infer_instance

omit [HasDerivedCategory C] in
/-- Over a category with enough injectives, every additive functor has a right derived functor
on the bounded below derived category. -/
theorem hasRightDerivedFunctorPlus (G : C ⥤ D) [G.Additive] :
    (G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso C) :=
  have := (HomotopyCategory.Plus.localizerMorphism_derives
    (G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)).hasPointwiseRightDerivedFunctor
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _

variable (F : C ⥤ D) [F.Additive]
  [(F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso C)]

/-- Over a category with enough injectives, `A` is right acyclic for `F` (the unit of `RF⁺` is
invertible at `A[0]`) if and only if `A[0]` computes `RF⁺`. -/
theorem rightAcyclic_iff_computesRightDerived (A : C) :
    F.rightAcyclic A ↔ (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
      (HomotopyCategory.Plus.quasiIso C)
      ((HomotopyCategory.Plus.singleFunctor C 0).obj A) := by
  have := quasiIsoPlusLeftFractions (C := C)
  have hres : ∀ K : HomotopyCategory.Plus C, ∃ (I : HomotopyCategory.Plus C) (s : K ⟶ I)
      (_ : HomotopyCategory.Plus.quasiIso C s),
      IsIso (((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
        DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)).app I) := by
    intro K
    let r : (HomotopyCategory.Plus.localizerMorphism C).RightResolution K := Classical.arbitrary _
    exact ⟨(InjectiveObject.ι C).mapHomotopyCategoryPlus.obj r.X₁, r.w, r.hw, inferInstance⟩
  exact (CategoryTheory.Functor.computesRightDerived_iff_isIso_app
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) DerivedCategory.Plus.Qh _
    (HomotopyCategory.Plus.quasiIso C) _ _ hres).symm

/-- An injective object is right acyclic for a left exact functor. -/
theorem rightAcyclic_of_injective [PreservesFiniteLimits F] (A : C) [Injective A] :
    F.rightAcyclic A :=
  ((Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus F A).2 inferInstance).2
    (fun i hi ↦ Functor.isZero_rightDerivedPlus_obj_injective F i (by omega) A)

/-- Every object embeds into a right acyclic one. -/
theorem exists_mono_rightAcyclic [PreservesFiniteLimits F] (A : C) :
    ∃ (Y : C) (i : A ⟶ Y) (_ : Mono i), F.rightAcyclic Y :=
  ⟨Injective.under A, Injective.ι A, inferInstance, rightAcyclic_of_injective F _⟩

/-- If `F` is left exact and `R^n F = 0`, then the right derived functor of `F` exists on the
whole unbounded derived category and is computed by any complex all of whose terms are right
acyclic. -/
@[sga "4 XVII 1.2.10" "Right-derived case"]
theorem hasRightDerivedFunctor_and_computed_by_rightAcyclic [PreservesFiniteLimits F]
    (n : ℕ) (hn : ∀ A : C, IsZero ((F.rightDerived n).obj A)) :
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) ∧
      ∀ (RF : DerivedCategory C ⥤ DerivedCategory D)
        (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
          DerivedCategory.Qh ⋙ RF)
        [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
        (L : CochainComplex C ℤ), (∀ i : ℤ, F.rightAcyclic (L.X i)) →
          IsIso (α.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj L)) := by
  have hn' : ∀ A : C, IsZero ((DerivedCategory.Plus.homologyFunctor D (n : ℤ)).obj
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor C 0).obj A))) :=
    fun A ↦ (hn A).of_iso
      ((Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandard F n).app A)
  obtain ⟨h1, -, h3⟩ := Functor.hasRightDerivedFunctor_of_isZero_rightDerived F
    F.rightDerivedFunctorPlus F.rightDerivedFunctorPlusUnith F.rightAcyclic
    (rightAcyclic_iff_computesRightDerived F) (exists_mono_rightAcyclic F) n hn'
  exact ⟨h1, fun RF α _ ↦ (h3 RF α).1⟩

/-- `F` applied to a morphism of complexes is inverted by `Qh` in the homotopy category exactly
when the morphism `F f` is a quasi-isomorphism. -/
private theorem isIso_Qh_map_iff_quasiIso {A : Type u₁} [Category.{v₁} A] [Abelian A]
    [HasDerivedCategory A] {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory B]
    (G : A ⥤ B) [G.Additive] {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    IsIso (DerivedCategory.Qh.map ((G.mapHomotopyCategory (ComplexShape.up ℤ)).map
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f))) ↔
    QuasiIso ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map f) :=
  (NatIso.isIso_map_iff
    (Functor.isoWhiskerRight (G.mapHomotopyCategoryFactors (ComplexShape.up ℤ))
        DerivedCategory.Qh ≪≫
      Functor.isoWhiskerLeft (G.mapHomologicalComplex (ComplexShape.up ℤ))
        (DerivedCategory.quotientCompQhIso B)) f).trans
    (DerivedCategory.isIso_Q_map_iff_quasiIso B _)

omit [EnoughInjectives C] in
/-- If complexes of right acyclic objects compute `RF`, then `F` applied degreewise to a
quasi-isomorphism between two such complexes is a quasi-isomorphism. -/
theorem quasiIso_mapHomologicalComplex_of_rightAcyclic_terms [PreservesFiniteLimits F]
    (hRD : (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)))
    (hcomp : ∀ (RF : DerivedCategory C ⥤ DerivedCategory D)
        (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
          DerivedCategory.Qh ⋙ RF)
        [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
        (L : CochainComplex C ℤ), (∀ i : ℤ, F.rightAcyclic (L.X i)) →
          IsIso (α.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj L)))
    {K L : CochainComplex C ℤ} (f : K ⟶ L) [QuasiIso f]
    (hK : ∀ i : ℤ, F.rightAcyclic (K.X i)) (hL : ∀ i : ℤ, F.rightAcyclic (L.X i)) :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  have := hRD
  set q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  set G := F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  let RF := G.totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
  let α := G.totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
  have : IsIso (α.app (q.obj K)) := hcomp RF α K hK
  have : IsIso (α.app (q.obj L)) := hcomp RF α L hL
  have : IsIso (DerivedCategory.Qh.map (q.map f)) :=
    Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff f).2
        ((HomologicalComplex.mem_quasiIso_iff f).2 inferInstance))
  have heq : G.map (q.map f) =
      α.app (q.obj K) ≫ (DerivedCategory.Qh ⋙ RF).map (q.map f) ≫ inv (α.app (q.obj L)) := by
    rw [← Category.assoc, ← α.naturality (q.map f), Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have hiso : IsIso (G.map (q.map f)) := by
    rw [heq]
    change IsIso (α.app (q.obj K) ≫ RF.map (DerivedCategory.Qh.map (q.map f)) ≫
      inv (α.app (q.obj L)))
    infer_instance
  exact (isIso_Qh_map_iff_quasiIso F f).1 hiso

/-- A direct sum of injective objects is right acyclic for a left exact functor whose right
derived functors commute with that direct sum. -/
theorem rightAcyclic_coproduct_of_injectives [PreservesFiniteLimits F]
    (I : Type*) (G : I → C) [HasColimit (Discrete.functor G)]
    (hG : ∀ i, Injective (G i))
    (hsums : ∀ p : ℕ, PreservesColimitsOfShape (Discrete I) (F.rightDerived p)) :
    F.rightAcyclic (∐ G) := by
  rw [(Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus F (∐ G)).2 inferInstance]
  intro p hp
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, p = ((q + 1 : ℕ) : ℤ) := ⟨p.toNat - 1, by omega⟩
  have := hsums (q + 1)
  have hz : IsZero (Discrete.functor G ⋙ F.rightDerived (q + 1)) := by
    refine (Discrete.functor G ⋙ _).isZero_iff.mpr (fun i ↦ ?_)
    have : Injective (G i.as) := hG i.as
    exact Functor.isZero_rightDerived_obj_injective_succ F q (G i.as)
  exact ((isColimitOfPreserves _ (coproductIsCoproduct G)).isZero_pt hz).of_iso
    ((Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandard F (q + 1)).app (∐ G))

omit [HasDerivedCategory C] [EnoughInjectives C]
  [(F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso C)] in
/-- If `Hom(M, -)` is the composite of `F` with a homology-preserving functor `V` to abelian
groups, and the `F`-image of `L` is acyclic, then there is no nonzero morphism `M[0] ⟶ L` in the
homotopy category. -/
theorem eq_zero_of_isZero_Qh_obj (M : C) (V : D ⥤ AddCommGrpCat.{v₁}) [V.Additive]
    [V.PreservesHomology]
    (hiso : preadditiveCoyoneda.obj (op M) ≅ F ⋙ V)
    (L : HomotopyCategory C (ComplexShape.up ℤ))
    (h : IsZero (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj L)))
    (f : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
      ((CochainComplex.singleFunctor C 0).obj M) ⟶ L) : f = 0 := by
  have hz0 : IsZero (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L.as).homology 0) :=
    IsZero.of_iso ((DerivedCategory.homologyFunctor D 0).map_isZero h)
      (((DerivedCategory.homologyFunctorFactorsh D 0).app
          ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj L)) ≪≫
        (HomotopyCategory.homologyFunctor D (ComplexShape.up ℤ) 0).mapIso
          ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app L.as) ≪≫
        (HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℤ) 0).app _).symm
  exact eq_zero_of_isZero_homology_zero M L (IsZero.of_iso (V.map_isZero hz0)
    (HomologicalComplex.homologyMapIso
        ((NatIso.mapHomologicalComplex hiso (ComplexShape.up ℤ)).app L.as) 0 ≪≫
      (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L.as).sc 0).mapHomologyIso V)) f

/-- Let `F` be left exact with a right derived functor computed by complexes of right acyclic
objects, and let `Hom(M, -)` be the composite of `F` with a homology-preserving functor to abelian
groups. Then every morphism of the derived category from `M[0]` to a complex of right acyclic
objects is the image of a morphism of complexes. -/
theorem Q_map_surjective_of_rightAcyclic_terms [PreservesFiniteLimits F]
    [IsGrothendieckAbelian.{wg} C]
    (hRD : (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)))
    (hcomp : ∀ (RF : DerivedCategory C ⥤ DerivedCategory D)
        (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
          DerivedCategory.Qh ⋙ RF)
        [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
        (L : CochainComplex C ℤ), (∀ i : ℤ, F.rightAcyclic (L.X i)) →
          IsIso (α.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj L)))
    (M : C) (V : D ⥤ AddCommGrpCat.{v₁}) [V.Additive] [V.PreservesHomology]
    (hiso : preadditiveCoyoneda.obj (op M) ≅ F ⋙ V)
    (K : CochainComplex C ℤ) (hK : ∀ i : ℤ, F.rightAcyclic (K.X i)) :
    Function.Surjective (DerivedCategory.Q.map :
      ((CochainComplex.singleFunctor C 0).obj M ⟶ K) → _) := by
  obtain ⟨R, i0, hqi0, hRinj, hRkinj⟩ : ∃ (R : CochainComplex C ℤ) (i0 : K ⟶ R),
      QuasiIso i0 ∧ (∀ n : ℤ, Injective (R.X n)) ∧ R.IsKInjective :=
    ⟨(Stacks.Injectives.kInjectiveResolutionFunctor C).obj K,
      (Stacks.Injectives.kInjectiveResolutionInclusion C).app K, inferInstance,
      fun n ↦ inferInstance, inferInstance⟩
  have : QuasiIso i0 := hqi0
  have : R.IsKInjective := hRkinj
  have hRac : ∀ i : ℤ, F.rightAcyclic (R.X i) := fun i ↦
    have := hRinj i
    rightAcyclic_of_injective F (R.X i)
  have hqi : QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map i0) :=
    quasiIso_mapHomologicalComplex_of_rightAcyclic_terms F hRD hcomp i0 hK hRac
  have hz : IsZero ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).obj
      (CochainComplex.mappingCone.triangleh i0).obj₃) := by
    refine ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).mapTriangle.obj
      (CochainComplex.mappingCone.triangleh i0)).isZero₃_of_isIso₁
      ((F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map_distinguished _
        (HomotopyCategory.mappingCone_triangleh_distinguished i0)) ?_
    exact (isIso_Qh_map_iff_quasiIso F i0).2 hqi
  intro f
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
      ((CochainComplex.singleFunctor C 0).obj M)) R).2
    ((DerivedCategory.quotientCompQhIso C).hom.app ((CochainComplex.singleFunctor C 0).obj M) ≫
      f ≫ DerivedCategory.Q.map i0 ≫ (DerivedCategory.quotientCompQhIso C).inv.app R)
  have hgzero : g ≫ (CochainComplex.mappingCone.triangleh i0).mor₂ = 0 :=
    eq_zero_of_isZero_Qh_obj F M V hiso _ hz _
  obtain ⟨l, hl⟩ := (CochainComplex.mappingCone.triangleh i0).coyoneda_exact₂
    (HomotopyCategory.mappingCone_triangleh_distinguished i0) g hgzero
  obtain ⟨l, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective l
  refine ⟨l, ?_⟩
  have hl' : DerivedCategory.Qh.map
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map l) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map i0) =
      (DerivedCategory.quotientCompQhIso C).hom.app ((CochainComplex.singleFunctor C 0).obj M) ≫
        f ≫ DerivedCategory.Q.map i0 ≫ (DerivedCategory.quotientCompQhIso C).inv.app R := by
    rw [← Functor.map_comp, ← hg]
    exact congrArg (fun t ↦ (DerivedCategory.Qh (C := C)).map t) hl.symm
  have key : DerivedCategory.Qh.map
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map l) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map i0) ≫
        (DerivedCategory.quotientCompQhIso C).hom.app R =
      (DerivedCategory.quotientCompQhIso C).hom.app ((CochainComplex.singleFunctor C 0).obj M) ≫
        DerivedCategory.Q.map l ≫ DerivedCategory.Q.map i0 := by
    have n1 : DerivedCategory.Qh.map
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map i0) ≫
        (DerivedCategory.quotientCompQhIso C).hom.app R =
        (DerivedCategory.quotientCompQhIso C).hom.app K ≫ DerivedCategory.Q.map i0 :=
      (DerivedCategory.quotientCompQhIso C).hom.naturality i0
    have n2 : DerivedCategory.Qh.map
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map l) ≫
        (DerivedCategory.quotientCompQhIso C).hom.app K =
        (DerivedCategory.quotientCompQhIso C).hom.app
          ((CochainComplex.singleFunctor C 0).obj M) ≫ DerivedCategory.Q.map l :=
      (DerivedCategory.quotientCompQhIso C).hom.naturality l
    exact (congrArg (fun t ↦ DerivedCategory.Qh.map
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map l) ≫ t) n1).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun t ↦ t ≫ DerivedCategory.Q.map i0) n2).trans (Category.assoc _ _ _)))
  refine (cancel_mono (DerivedCategory.Q.map i0)).1 ?_
  refine (cancel_epi ((DerivedCategory.quotientCompQhIso C).hom.app
    ((CochainComplex.singleFunctor C 0).obj M))).1 ?_
  refine key.symm.trans (((Category.assoc _ _ _).symm.trans
    (congrArg (fun t ↦ t ≫ (DerivedCategory.quotientCompQhIso C).hom.app R) hl')).trans ?_)
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

end GenericDerived

/-! ## The ringed-site setting -/

variable (X : RingedSite.{u, u, u}) (U : X.C)

/-- Evaluation of a sheaf of modules at an object is additive. -/
local instance evaluationAdditive :
    (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)).Additive := by
  dsimp [SheafOfModules.evaluation]
  infer_instance

/-- Sheaves of modules on a ringed site have enough injectives. -/
@[ega "0 12.2.1" "partial",
  sga "4 II 6.9" "Remark 6.9, special case",
  sga "4 V 0.2.1" "special case"]
local instance modulesEnoughInjectives :
    EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  IsGrothendieckAbelian.enoughInjectives.{u}

/-- Restriction to a slice site is additive. -/
private lemma pushforwardOver_additive :
    (SheafOfModules.pushforward.{u} (F := Over.forget U)
      (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))).Additive where
  map_add {_ _ p q} := by
    ext V z
    rfl

/-- Extension by zero is additive. -/
private lemma pullbackOver_additive :
    (SheafOfModules.pullback.{u} (F := Over.forget U)
      (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))).Additive :=
  have := pushforwardOver_additive X U
  (SheafOfModules.pullbackPushforwardAdjunction.{u} (F := Over.forget U)
    (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))).left_adjoint_additive

/-- The bijection `extensionByZeroUnitHomEquiv` between morphisms out of `j_{U!} O_U` and
sections over `U` is additive. -/
private lemma extensionByZeroUnitHomEquiv_add
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (f g : (SheafOfModules.pullback.{u} (F := Over.forget U)
      (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))).obj
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) ⟶ F) :
    Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv X.J
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U F (f + g) =
      Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv X.J
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U F f +
        Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv X.J
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U F g := by
  have := pushforwardOver_additive X U
  have := pullbackOver_additive X U
  let R := Stacks.SheafOfModules.Tensor.ringSheaf X.O
  let adj := SheafOfModules.pullbackPushforwardAdjunction.{u} (F := Over.forget U)
    (𝟙 (R.over U))
  change (((F.over U).unitHomEquiv
      (adj.homEquiv (SheafOfModules.unit (R.over U)) F (f + g))).val
        (op (Over.mk (𝟙 U)))) = _
  rw [adj.homAddEquiv_add (SheafOfModules.unit (R.over U)) F f g]
  rfl

/-- The isomorphism of additive functors `Hom(j_{U!} O_U, -) ≅ Γ(U, -)`: morphisms out of
`j_{U!} O_U` are the sections over `U`, naturally and additively. -/
@[no_expose] def coyonedaIsoEvaluation :
    preadditiveCoyoneda.obj (op ((SheafOfModules.pullback.{u} (F := Over.forget U)
      (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))).obj
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)))) ≅
      SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U) ⋙
        forget₂ (ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)))
          AddCommGrpCat.{u} :=
  NatIso.ofComponents
    (fun F ↦ AddEquiv.toAddCommGrpIso
      { __ := Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv X.J
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U F
        map_add' := extensionByZeroUnitHomEquiv_add X U F })
    (fun f ↦ AddCommGrpCat.ext fun h ↦
      Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv_naturality X.J
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U h f)

/-- The forgetful functor from `S`-modules to abelian groups preserves coproducts indexed by
any type `I`. -/
theorem forgetToAddCommGrp_preservesCoproducts (S : RingCat.{u}) (I : Type w) :
    PreservesColimitsOfShape (Discrete I)
      (forget₂ (ModuleCat.{u} S) AddCommGrpCat.{u}) := by
  have : (ModuleCat.restrictScalars.{u} (Int.castRingHom S)).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{u, 0, u} (Int.castRingHom S)).isLeftAdjoint
  exact preservesColimitsOfShape_of_natIso
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl) :
      ModuleCat.restrictScalars.{u} (Int.castRingHom S) ⋙
        forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u} ≅
          forget₂ (ModuleCat.{u} S) AddCommGrpCat.{u})

section Part2

attribute [local instance] HasDerivedCategory.standard

/-- If `H⁰(U, -)` commutes with direct sums indexed by types in `Type w`, then the extension by
zero `j_{U!} O_U` of the structure sheaf is a compact object of the category of `O`-modules. -/
theorem isCompactObject_extensionByZeroUnit
    (hsums0 : ∀ I : Type w, PreservesColimitsOfShape (Discrete I)
      ((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (op U)).rightDerived 0)) :
    IsCompactObject.{w} ((SheafOfModules.pullback.{u} (F := Over.forget U)
      (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))).obj
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))) := by
  apply CategoryTheory.isCompactObject_of_preservesColimitsOfShape_preadditiveCoyoneda
  intro I
  have h0 := hsums0 I
  have h1 : PreservesColimitsOfShape (Discrete I)
      (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)) :=
    preservesColimitsOfShape_of_natIso
      (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (op U)).rightDerivedZeroIsoSelf
  have hV := forgetToAddCommGrp_preservesCoproducts
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)) I
  exact preservesColimitsOfShape_of_natIso (coyonedaIsoEvaluation X U).symm

end Part2

/-! ## Generic: finite decompositions out of a compact object -/

section CompactSums

variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]

/-- **A morphism from a compact object into a direct sum is a finite sum.** -/
theorem exists_finsum_of_isCompactObject (P : D) (hP : IsCompactObject.{w} P)
    {I : Type w} {E : I → D} {S : D} (j : ∀ i, E i ⟶ S) (hc : IsColimit (Cofan.mk S j))
    (f : P ⟶ S) : ∃ (s : Finset I) (a : ∀ i, P ⟶ E i), ∑ i ∈ s, a i ≫ j i = f := by
  classical
  obtain ⟨x, hx⟩ := (bijective_cofanMap P hP j hc).2 f
  refine ⟨x.support, fun i ↦ x i, ?_⟩
  have hs : (∑ i ∈ x.support, DirectSum.of (fun i ↦ (P ⟶ E i)) i (x i)) = x :=
    DFinsupp.sum_single
  simpa only [map_sum, cofanMap_of] using (congrArg (cofanMap P j) hs).trans hx

end CompactSums

section CompactSingle

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasZeroObject C]

/-- **A map of complexes from an object in degree zero into a termwise direct sum factors
through a finite subsum**, when the object is compact in the underlying category. -/
theorem exists_finsum_single_of_isCompactObject (P : C) (hP : IsCompactObject.{w} P)
    {I : Type w} [HasCoproductsOfShape I C] (J : I → CochainComplex C ℤ) [HasCoproduct J]
    (f : (CochainComplex.singleFunctor C 0).obj P ⟶ ∐ J) :
    ∃ (s : Finset I) (g : ∀ i, (CochainComplex.singleFunctor C 0).obj P ⟶ J i),
      ∑ i ∈ s, g i ≫ Limits.Sigma.ι J i = f := by
  classical
  have hPX : IsCompactObject.{w} ((HomologicalComplex.eval C (ComplexShape.up ℤ) 0).obj
      ((CochainComplex.singleFunctor C 0).obj P)) :=
    isCompactObject_of_iso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 P).symm hP
  have hc : IsColimit (Cofan.mk ((HomologicalComplex.eval C (ComplexShape.up ℤ) 0).obj (∐ J))
      fun i ↦ (HomologicalComplex.eval C (ComplexShape.up ℤ) 0).map (Limits.Sigma.ι J i)) :=
    (isColimitMapCoconeCofanMkEquiv (HomologicalComplex.eval C (ComplexShape.up ℤ) 0) J
      (Limits.Sigma.ι J))
      (isColimitOfPreserves (HomologicalComplex.eval C (ComplexShape.up ℤ) 0)
        (coproductIsCoproduct J))
  obtain ⟨s, a, ha⟩ := exists_finsum_of_isCompactObject _ hPX _ hc
    ((HomologicalComplex.eval C (ComplexShape.up ℤ) 0).map f)
  have hp (i : I) (hi : i ∈ s) :
      (HomologicalComplex.eval C (ComplexShape.up ℤ) 0).map f ≫
        (HomologicalComplex.eval C (ComplexShape.up ℤ) 0).map
          (Limits.Sigma.desc (Pi.single i (𝟙 (J i)))) = a i := by
    rw [← ha, Preadditive.sum_comp]
    have ht (k : I) : (a k ≫ (HomologicalComplex.eval C (ComplexShape.up ℤ) 0).map
        (Limits.Sigma.ι J k)) ≫ (HomologicalComplex.eval C (ComplexShape.up ℤ) 0).map
          (Limits.Sigma.desc (Pi.single i (𝟙 (J i)))) = if h : k = i then a i else 0 := by
      rw [Category.assoc, ← Functor.map_comp, Limits.Sigma.ι_comp_desc]
      split_ifs with h
      · subst h
        simp
      · rw [Pi.single_eq_of_ne h, Functor.map_zero, comp_zero]
    simp only [ht]
    simp [hi]
  refine ⟨s, fun i ↦ f ≫ Limits.Sigma.desc (Pi.single i (𝟙 (J i))),
    HomologicalComplex.from_single_hom_ext ?_⟩
  change (HomologicalComplex.eval C (ComplexShape.up ℤ) 0).map
    (∑ i ∈ s, (f ≫ Limits.Sigma.desc (Pi.single i (𝟙 (J i)))) ≫ Limits.Sigma.ι J i) =
      (HomologicalComplex.eval C (ComplexShape.up ℤ) 0).map f
  simp only [Functor.map_sum, Functor.map_comp]
  calc _ = ∑ i ∈ s, a i ≫ (HomologicalComplex.eval C (ComplexShape.up ℤ) 0).map
        (Limits.Sigma.ι J i) := Finset.sum_congr rfl fun i hi ↦ by rw [hp i hi]
    _ = _ := ha

end CompactSingle

/-! ## Generic: smallness of morphism sets, and reduction to the nonzero summands -/

section Smallness

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory C]

/-- **Morphism sets of the unbounded derived category of a Grothendieck abelian category are
small** relative to the morphisms of the category. -/
theorem small_hom_derivedCategory [IsGrothendieckAbelian.{wg} C] (M N : DerivedCategory C) :
    Small.{v₁} (M ⟶ N) := by
  have hK : Small.{v₁} ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
      (DerivedCategory.Q.objPreimage M) ⟶
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        ((Stacks.Injectives.kInjectiveResolutionFunctor C).obj
          (DerivedCategory.Q.objPreimage N))) :=
    small_of_surjective (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective
  have hD : Small.{v₁} (DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        (DerivedCategory.Q.objPreimage M)) ⟶
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
        ((Stacks.Injectives.kInjectiveResolutionFunctor C).obj
          (DerivedCategory.Q.objPreimage N)))) :=
    small_of_surjective (CochainComplex.IsKInjective.Qh_map_bijective _
      ((Stacks.Injectives.kInjectiveResolutionFunctor C).obj
        (DerivedCategory.Q.objPreimage N))).2
  have eM : DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
      (DerivedCategory.Q.objPreimage M)) ≅ M :=
    (DerivedCategory.quotientCompQhIso C).app (DerivedCategory.Q.objPreimage M) ≪≫
      DerivedCategory.Q.objObjPreimageIso M
  have eN : DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
      ((Stacks.Injectives.kInjectiveResolutionFunctor C).obj
        (DerivedCategory.Q.objPreimage N))) ≅ N :=
    (DerivedCategory.quotientCompQhIso C).app _ ≪≫
      (asIso (DerivedCategory.Q.map
        ((Stacks.Injectives.kInjectiveResolutionInclusion C).app
          (DerivedCategory.Q.objPreimage N)))).symm ≪≫
      DerivedCategory.Q.objObjPreimageIso N
  exact small_of_surjective (Iso.homCongr eM eN).surjective

end Smallness

section NonzeroSummands

variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]

/-- **Only small-many summands of an existing direct sum are nonzero**, when the endomorphisms
of the direct sum form a small type. -/
theorem small_nonzero_summands {I : Type*} (E : I → D) [HasCoproduct E]
    [Small.{v₁} (∐ E ⟶ ∐ E)] : Small.{v₁} {i : I // ¬ IsZero (E i)} := by
  classical
  refine small_of_injective
    (f := fun i : {i : I // ¬ IsZero (E i)} ↦
      Limits.Sigma.desc (Pi.single i.1 (𝟙 (E i.1))) ≫ Limits.Sigma.ι E i.1) ?_
  intro i j hij
  refine Subtype.ext ?_
  by_contra h
  have hh := congrArg (fun t ↦ Limits.Sigma.ι E i.1 ≫ t ≫
    Limits.Sigma.desc (Pi.single i.1 (𝟙 (E i.1)))) hij
  exact i.property ((IsZero.iff_id_eq_zero _).2 (by simpa [Category.assoc, h, Ne.symm h] using hh))

/-- **The nonzero summands of a direct sum already form a colimit cofan.** -/
def nonzeroSummandsIsColimit {I : Type*} (E : I → D) [HasCoproduct E] :
    IsColimit (Cofan.mk (∐ E) fun i : {i : I // ¬ IsZero (E i)} => Limits.Sigma.ι E i.1) := by
  classical
  refine Cofan.IsColimit.mk _
    (fun c ↦ Limits.Sigma.desc fun i ↦ if hi : ¬ IsZero (E i) then c.inj ⟨i, hi⟩ else 0) ?_ ?_
  · intro c i
    simp [i.property]
  · intro c m hm
    refine Limits.Sigma.hom_ext (f := E) _ _ fun i ↦ ?_
    by_cases hi : IsZero (E i)
    · exact hi.eq_of_src _ _
    · simpa [hi] using hm ⟨i, hi⟩

end NonzeroSummands

/-! ## Compactness of `j_{U!}O_U[0]` in the derived category -/

section CompactInDerivedCategory

attribute [local instance] HasDerivedCategory.standard

/-- Under the hypotheses of `isCompactObject_singleFunctor_extensionByZeroUnit`, a morphism from
`j_{U!}O_U[0]` to a direct sum of a `u`-small family of objects of `D(O)` is a finite sum of
morphisms into the summands. -/
theorem exists_finsum_derived
    (n : ℕ)
    (hn : ∀ G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O),
      IsZero (((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (op U)).rightDerived n).obj G))
    (hsums : ∀ (p : ℕ) (I : Type w), PreservesColimitsOfShape (Discrete I)
      ((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (op U)).rightDerived p))
    (I : Type w) [Small.{u} I]
    (Mfam : I → DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (N : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (j : ∀ i, Mfam i ⟶ N) (hc : IsColimit (Cofan.mk N j))
    (f : (DerivedCategory.singleFunctor (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
        ((SheafOfModules.pullback.{u} (F := Over.forget U)
          (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))).obj
          (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))) ⟶ N) :
    ∃ (s : Finset I) (g : ∀ i,
      (DerivedCategory.singleFunctor (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
        ((SheafOfModules.pullback.{u} (F := Over.forget U)
          (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))).obj
          (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))) ⟶ Mfam i),
      ∑ i ∈ s, g i ≫ j i = f := by
  classical
  revert f
  set A := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  set ev := SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)
  set E := (SheafOfModules.pullback.{u} (F := Over.forget U)
    (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))).obj
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
  intro f
  have := hasRightDerivedFunctorPlus ev
  obtain ⟨hRD, hcomp⟩ := hasRightDerivedFunctor_and_computed_by_rightAcyclic ev n hn
  have hEc : IsCompactObject.{w} E := isCompactObject_extensionByZeroUnit X U (fun I ↦ hsums 0 I)
  have hIA : HasColimitsOfShape (Discrete I) A :=
    hasColimitsOfShape_of_equivalence (Discrete.equivalence (equivShrink.{u} I).symm)
  have hcopD : HasCoproducts.{u} (DerivedCategory A) :=
    Stacks.Injectives.hasCoproducts_derivedCategory A
  have hID : HasColimitsOfShape (Discrete I) (DerivedCategory A) :=
    hasColimitsOfShape_of_equivalence (Discrete.equivalence (equivShrink.{u} I).symm)
  have hQ : PreservesColimitsOfShape (Discrete I) (DerivedCategory.Q (C := A)) :=
    have := Stacks.Injectives.derivedCategoryQ_preservesCoproducts A (Shrink.{u} I)
    preservesColimitsOfShape_of_equiv
      (Discrete.equivalence (equivShrink.{u} I).symm) DerivedCategory.Q
  have hrep : ∀ i : I, ∃ (L : CochainComplex A ℤ) (_ : ∀ k : ℤ, Injective (L.X k)),
      Nonempty (DerivedCategory.Q.obj L ≅ Mfam i) := by
    intro i
    refine ⟨(Stacks.Injectives.kInjectiveResolutionFunctor A).obj
      (DerivedCategory.Q.objPreimage (Mfam i)), fun k ↦ inferInstance,
      ⟨(asIso (DerivedCategory.Q.map ((Stacks.Injectives.kInjectiveResolutionInclusion A).app
        (DerivedCategory.Q.objPreimage (Mfam i))))).symm ≪≫
          DerivedCategory.Q.objObjPreimageIso (Mfam i)⟩⟩
  choose L hLinj eL' using hrep
  let eL : ∀ i, DerivedCategory.Q.obj (L i) ≅ Mfam i := fun i ↦ (eL' i).some
  have hLA : ∀ k : ℤ, ev.rightAcyclic ((∐ L).X k) := fun k ↦
    ev.rightAcyclic.prop_of_iso
      (PreservesCoproduct.iso (HomologicalComplex.eval A (ComplexShape.up ℤ) k) L).symm
      (rightAcyclic_coproduct_of_injectives ev I (fun i ↦ (L i).X k)
        (fun i ↦ hLinj i k) (fun p ↦ hsums p I))
  let eS := (DerivedCategory.singleFunctorIsoCompQ A 0).app E
  let e : DerivedCategory.Q.obj (∐ L) ≅ N :=
    PreservesCoproduct.iso DerivedCategory.Q L ≪≫ Limits.Sigma.mapIso eL ≪≫
      (coproductIsCoproduct Mfam).coconePointUniqueUpToIso hc
  have he : ∀ i : I, DerivedCategory.Q.map (Limits.Sigma.ι L i) ≫ e.hom = (eL i).hom ≫ j i := by
    intro i
    have hiota : DerivedCategory.Q.map (Limits.Sigma.ι L i) ≫
        (PreservesCoproduct.iso DerivedCategory.Q L).hom =
          Limits.Sigma.ι (fun k ↦ DerivedCategory.Q.obj (L k)) i := by
      refine (cancel_mono (PreservesCoproduct.iso DerivedCategory.Q L).inv).1 ?_
      rw [Category.assoc, Iso.hom_inv_id, Category.comp_id, PreservesCoproduct.inv_hom,
        Limits.ι_comp_sigmaComparison]
    dsimp only [e, Iso.trans_hom]
    rw [← Category.assoc, hiota]
    change Limits.Sigma.ι (fun k ↦ DerivedCategory.Q.obj (L k)) i ≫
      Limits.Sigma.map (fun k ↦ (eL k).hom) ≫
        ((coproductIsCoproduct Mfam).coconePointUniqueUpToIso hc).hom = _
    rw [Limits.Sigma.ι_map_assoc]
    exact congrArg (fun t ↦ (eL i).hom ≫ t)
      ((coproductIsCoproduct Mfam).comp_coconePointUniqueUpToIso_hom hc ⟨i⟩)
  obtain ⟨l, hl⟩ := Q_map_surjective_of_rightAcyclic_terms ev hRD hcomp E
    (forget₂ (ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)))
      AddCommGrpCat.{u})
    (coyonedaIsoEvaluation X U) (∐ L) hLA (eS.inv ≫ f ≫ e.inv)
  obtain ⟨s, g, hg⟩ := exists_finsum_single_of_isCompactObject E hEc L l
  refine ⟨s, fun i ↦ eS.hom ≫ DerivedCategory.Q.map (g i) ≫ (eL i).hom, ?_⟩
  calc ∑ i ∈ s, (eS.hom ≫ DerivedCategory.Q.map (g i) ≫ (eL i).hom) ≫ j i
      = eS.hom ≫ DerivedCategory.Q.map (∑ i ∈ s, g i ≫ Limits.Sigma.ι L i) ≫ e.hom := by
        simp only [Functor.map_sum, Functor.map_comp, Preadditive.comp_sum,
          Preadditive.sum_comp, Category.assoc, he]
    _ = f := by
      rw [hg, hl]
      simp

/-- Let `(C, O)` be a ringed site and `U` an object of `C`. If cohomology over
`U` has finite cohomological dimension and `H^p(U, -)` commutes with direct sums for every `p`,
then `j_{U!} O_U`, placed in degree zero, is a compact object of the unbounded derived category
of `O`-modules. Compactness is tested against families indexed by types in `Type w`, the
universe of the hypothesis on direct sums. -/
@[stacks 094D]
theorem isCompactObject_singleFunctor_extensionByZeroUnit
    (hcd : ∃ d : ℤ, ∀ (p : ℕ) (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)),
      d < (p : ℤ) →
      IsZero (((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (op U)).rightDerived p).obj G))
    (hsums : ∀ (p : ℕ) (I : Type w), PreservesColimitsOfShape (Discrete I)
      ((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (op U)).rightDerived p)) :
    IsCompactObject.{w}
      ((DerivedCategory.singleFunctor (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
        ((SheafOfModules.pullback.{u} (F := Over.forget U)
          (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))).obj
          (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)))) := by
  classical
  obtain ⟨d, hd⟩ := hcd
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ∀ G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O),
      IsZero (((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (op U)).rightDerived n).obj G) :=
    ⟨(max d 0 + 1).toNat, fun G ↦ hd _ G (by omega)⟩
  constructor
  intro I _ Mfam _
  have hsmallHom : Small.{u} (∐ Mfam ⟶ ∐ Mfam) := small_hom_derivedCategory _ _
  have hsmall : Small.{u} {i : I // ¬ IsZero (Mfam i)} := small_nonzero_summands Mfam
  refine ⟨injective_cofanMap _ (Limits.Sigma.ι Mfam) (coproductIsCoproduct Mfam), fun f ↦ ?_⟩
  obtain ⟨s, g, hg⟩ := exists_finsum_derived X U n hn hsums
    {i : I // ¬ IsZero (Mfam i)} (fun i ↦ Mfam i.1) (∐ Mfam)
    (fun i ↦ Limits.Sigma.ι Mfam i.1) (nonzeroSummandsIsColimit Mfam) f
  exact ⟨∑ i ∈ s, DirectSum.of _ i.1 (g i), by
    simpa only [map_sum, DirectSum.toAddMonoid_of, Preadditive.rightComp,
      AddMonoidHom.mk'_apply] using hg⟩

end CompactInDerivedCategory

end Stacks.Cohomology.CompactExtensionByZero

end

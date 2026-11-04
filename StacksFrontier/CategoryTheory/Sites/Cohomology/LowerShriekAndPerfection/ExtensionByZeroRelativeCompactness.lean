module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.Resolution.InjectiveResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriekAndPerfection.SliceUnitModule
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksFrontier.CategoryTheory.Sites.Modules.GrothendieckAbelian
public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects
public import StacksFrontier.CategoryTheory.Triangulated.CompactObjectsFromCoyoneda
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Homology.DerivedIndexing.Extend
public import StacksFrontier.Homology.Injectives.Sheaf.ModulesOnRingedSite
public import StacksFrontier.Homology.Injectives.DerivedCategory.ProductsAndCoproducts
public import StacksFrontier.Homology.Ext.DerivedCoyoneda
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import StacksFrontier.Homology.Perfect.Characterizing
import StacksCore.Tactic.StacksAttribute

/-!
# Relative compactness of extension by zero on a ringed site

Let `(C, O)` be a ringed site and `U` an object of `C`. If cohomology over `U` commutes with
direct sums in every degree, then `j_{U!} O_U` is compact relative to the bounded-below part of
the derived category: for a family of objects whose coproduct is bounded below, the canonical
map from the direct sum of the groups `Hom(j_{U!} O_U, M i)` to `Hom(j_{U!} O_U, ∐ M i)` is
bijective.

Injectivity is formal. For surjectivity one replaces the coproduct by a coproduct of complexes
of injectives: each summand, being bounded below, is quasi-isomorphic to a bounded-below complex
of injectives, and a coproduct of injectives is right-acyclic for evaluation at `U` because the
hypothesis makes the higher right derived functors commute with that coproduct. A morphism out
of `j_{U!} O_U` into a complex with right-acyclic terms is then realised by an actual map of
complexes, and `j_{U!} O_U` is compact in the abelian category, so that map factors through
finitely many summands.

## Main results

* `Stacks.Cohomology.extensionByZero_unit_hom_coproduct_bijective`: the statement above,
  Tag 0G21.

* `Stacks.Cohomology.enoughInjectives_of_ringedSite` and
  `Stacks.Cohomology.evaluation_additive_of_ringedSite`: the two standing facts the statement
  needs in order to be written down, namely that sheaves of modules on a ringed site have
  enough injectives and that evaluation at an object is additive. Both already exist elsewhere
  in the library, but only in forms that are `local` or `private` to their own files and so
  cannot be imported; the `_of_ringedSite` suffix keeps these copies from colliding with them.

## Implementation notes

The source states qualified compactness in `D⁺`. Here that is expressed by bijectivity of the
canonical map for families whose coproduct lies in `D⁺`, rather than by `IsCompactObject` in
all of `D`; the hypothesis `hM` is exactly the membership of the coproduct in the plus part of
the standard t-structure.

The module universe is `max u v r m` for a site with objects in `Type u`, morphisms in
`Type v` and ring sections in `Type r`, and `j_{U!} O_U` is
`Stacks.Sites.OverModules.extensionByZeroUnit`, the extension by zero of the `ULift`ed
rank-one module on the slice site; at this universe the plain `SheafOfModules.unit` is not an
object of the category at all.

The index type `I` of the family lives in an unrelated universe `w`, which is why compactness
of `j_{U!} O_U` is established through
`CategoryTheory.isCompactObject_of_preservesColimitsOfShape_preadditiveCoyoneda` from
preservation of `w`-indexed coproducts by evaluation, rather than from the
`max u v r m`-indexed statement.

## References

* [Stacks Project, Tag 0G21](https://stacks.math.columbia.edu/tag/0G21)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Stacks.Sites.OverModules
open scoped DirectSum

universe u v r w m z
universe u₁ v₁ u₂ v₂

namespace Stacks.Cohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

public theorem enoughInjectives_of_ringedSite (X : RingedSite.{u, v, r}) :
    EnoughInjectives (SheafOfModules.{max u v r m}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) := by
  have : IsGrothendieckAbelian.{max u v r m}
      (SheafOfModules.{max u v r m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    Stacks.SheafOfModules.sheafModulesGrothendieck.{u, v, r, m} X.J
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  exact IsGrothendieckAbelian.enoughInjectives

public theorem evaluation_additive_of_ringedSite (X : RingedSite.{u, v, r}) (U : X.C) :
    (SheafOfModules.evaluation.{max u v r m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (op U)).Additive := by
  have : (SheafOfModules.forget.{max u v r m}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).Additive :=
    SheafOfModules.instAdditivePresheafOfModulesObjFunctorOppositeRingCatIsSheafForget
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  show (SheafOfModules.forget.{max u v r m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
    PresheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj (op U)).Additive
  infer_instance

private theorem rightAcyclic_coproduct_of_injectives
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] (E : C ⥤ D) [E.Additive]
    [EnoughInjectives C] (I : Type w) (F : I → C) [HasColimit (Discrete.functor F)]
    [(E.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso C)]
    (hF : ∀ i, Injective (F i))
    (hE : PreservesFiniteLimits E)
    (hsums : ∀ (p : ℕ), PreservesColimitsOfShape (Discrete I) (E.rightDerived p)) :
    E.rightAcyclic (∐ F) := by
  apply ((Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus E (∐ F)).2 hE).2
  intro p hp
  have hn : ((Int.toNat p : ℕ) : ℤ) = p := Int.toNat_of_nonneg hp.le
  have hn0 : Int.toNat p ≠ 0 := by omega
  obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have := hsums (q + 1)
  have hz : IsZero (Discrete.functor F ⋙ E.rightDerived (q + 1)) := by
    apply (Discrete.functor F ⋙ E.rightDerived (q + 1)).isZero_iff.mpr
    intro i
    have := hF i.as
    exact Functor.isZero_rightDerived_obj_injective_succ E q (F i.as)
  have hsum : IsZero ((E.rightDerived (q + 1)).obj (∐ F)) :=
    (isColimitOfPreserves (E.rightDerived (q + 1)) (coproductIsCoproduct F)).isZero_pt hz
  rw [← hn, hq]
  exact IsZero.of_iso hsum
    ((Stacks.DerivedIndexing.rightDerivedIso E (q + 1)).app (∐ F)).symm

private noncomputable def smallCoyonedaIsoEvaluation
    (X : RingedSite.{u, v, r}) (U : X.C) :
    StacksDraft.DerivedCoyoneda.smallCoyoneda
        (extensionByZeroUnit.{v, u, r, m} X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) ≅
      SheafOfModules.evaluation.{max u v r m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U) ⋙
        (forget₂
          (ModuleCat.{max u v r m} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)))
          AddCommGrpCat.{max u v r m}) ⋙
          AddCommGrpCat.uliftFunctor.{max u v r m + 1, max u v r m} := by
  let A := SheafOfModules.{max u v r m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let E := extensionByZeroUnit.{v, u, r, m} X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
  let S := DerivedCategory.singleFunctor A 0
  let ev₀ := SheafOfModules.evaluation.{max u v r m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (op U) ⋙
    (forget₂ (ModuleCat.{max u v r m} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)))
      AddCommGrpCat.{max u v r m})
  let ev := ev₀ ⋙ AddCommGrpCat.uliftFunctor.{max u v r m + 1, max u v r m}
  let e₁ (F : A) : (E ⟶ F) ≃+ (S.obj E ⟶ S.obj F) :=
    AddEquiv.ofBijective S.mapAddHom ⟨S.map_injective, S.map_surjective⟩
  let e₂ (F : A) : (E ⟶ F) ≃+ ev.obj F :=
    (extensionByZeroHomAddEquiv.{v, u, r, m} X.J
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U F).trans AddEquiv.ulift.symm
  refine NatIso.ofComponents (fun F => (e₁ F).symm.trans (e₂ F) |>.toAddCommGrpIso) ?_
  intro F G f
  ext g
  change (S.obj E ⟶ S.obj F) at g
  change ULift.up (extensionByZeroHomEquiv X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U G
      ((e₁ G).symm (g ≫ S.map f))) =
    (ev.map f) (ULift.up (extensionByZeroHomEquiv X.J
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U F
      ((e₁ F).symm g)))
  have hmap : (e₁ G).symm (g ≫ S.map f) = (e₁ F).symm g ≫ f := by
    apply S.map_injective
    calc
      S.map ((e₁ G).symm (g ≫ S.map f)) = g ≫ S.map f := by
        change (e₁ G) ((e₁ G).symm (g ≫ S.map f)) = _
        exact (e₁ G).apply_symm_apply _
      _ = S.map ((e₁ F).symm g) ≫ S.map f := by
        have hg : S.map ((e₁ F).symm g) = g := (e₁ F).apply_symm_apply g
        exact congrArg (fun h : S.obj E ⟶ S.obj F => h ≫ S.map f) hg.symm
      _ = S.map ((e₁ F).symm g ≫ f) := (S.map_comp _ _).symm
  rw [hmap]
  exact congrArg ULift.up
    (extensionByZeroHomEquiv_naturality.{v, u, r, m} X.J
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U ((e₁ F).symm g) f)

private noncomputable def smallCoyonedaHomotopyEquiv
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    (M : C) (L : CochainComplex C ℤ) (n : ℤ) :
    (((StacksDraft.DerivedCoyoneda.smallCoyoneda M).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj L).homology n ≃+
      ((HomotopyCategory.quotient C (.up ℤ)).obj ((CochainComplex.singleFunctor C 0).obj M) ⟶
        (HomotopyCategory.quotient C (.up ℤ)).obj (L⟦n⟧)) := by
  let S := (CochainComplex.singleFunctor C 0).obj M
  let F := DerivedCategory.singleFunctor C 0
  let e (i : ℤ) : (S.HomComplex L).X i ≃+
      (((StacksDraft.DerivedCoyoneda.smallCoyoneda M).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L).X i :=
    (CochainComplex.HomComplex.Cochain.fromSingleEquiv (X := M) (K := L) (p := 0) (q := i) (n := i)
      (by omega)).trans (AddEquiv.ofBijective F.mapAddHom ⟨F.map_injective, F.map_surjective⟩)
  have he (i j : ℤ) (x : (S.HomComplex L).X i) :
      e j (((S.HomComplex L).d i j).hom x) =
        ((((StacksDraft.DerivedCoyoneda.smallCoyoneda M).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L).d i j).hom (e i x) := by
    obtain ⟨f, rfl⟩ := CochainComplex.HomComplex.Cochain.fromSingleMk_surjective x i (by omega)
    change F.map (CochainComplex.HomComplex.Cochain.fromSingleEquiv (by omega : (0 : ℤ) + j = j)
      (CochainComplex.HomComplex.δ i j
        (CochainComplex.HomComplex.Cochain.fromSingleMk f (by omega : (0 : ℤ) + i = i)))) =
      F.map (CochainComplex.HomComplex.Cochain.fromSingleEquiv (by omega : (0 : ℤ) + i = i)
        (CochainComplex.HomComplex.Cochain.fromSingleMk f (by omega : (0 : ℤ) + i = i))) ≫
        F.map (L.d i j)
    rw [CochainComplex.HomComplex.Cochain.δ_fromSingleMk f (by omega : (0 : ℤ) + i = i) j j
        (by omega),
      CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk,
      CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk, F.map_comp]
  exact (StacksDraft.DerivedCoyoneda.homologyAddEquivOfComponents (S.HomComplex L)
      (((StacksDraft.DerivedCoyoneda.smallCoyoneda M).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L) e he n).symm.trans
    ((CochainComplex.HomComplex.homologyAddEquiv S L n).trans
      CochainComplex.HomComplex.CohomologyClass.homAddEquiv)

private theorem homotopyHom_eq_zero_of_evaluation_isZero
    (X : RingedSite.{u, v, r}) (U : X.C)
    (L : HomotopyCategory (SheafOfModules.{max u v r m}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (.up ℤ))
    (h : letI : (SheafOfModules.evaluation.{max u v r m}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)).Additive :=
      evaluation_additive_of_ringedSite.{u, v, r, m} X U
      IsZero ((DerivedCategory.Qh).obj
      (((SheafOfModules.evaluation.{max u v r m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (op U)).mapHomotopyCategory
        (.up ℤ)).obj L)))
    (f : (HomotopyCategory.quotient _ (.up ℤ)).obj
      ((CochainComplex.singleFunctor _ 0).obj
        (extensionByZeroUnit.{v, u, r, m} X.J
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)) ⟶ L) :
    f = 0 := by
  let A := SheafOfModules.{max u v r m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let B := ModuleCat.{max u v r m} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
  let ev := SheafOfModules.evaluation.{max u v r m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (op U)
  have : ev.Additive := evaluation_additive_of_ringedSite.{u, v, r, m} X U
  let E := extensionByZeroUnit.{v, u, r, m} X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
  let F := StacksDraft.DerivedCoyoneda.smallCoyoneda E
  let V := forget₂ B AddCommGrpCat.{max u v r m} ⋙
    AddCommGrpCat.uliftFunctor.{max u v r m + 1, max u v r m}
  have : PreservesColimits (forget₂ B AddCommGrpCat.{max u v r m}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{max u v r m, r, max u v r m, max u v r m} _
  have : PreservesLimits (forget₂ B AddCommGrpCat.{max u v r m}) :=
    ModuleCat.forget₂AddCommGroup_preservesLimits.{max u v r m, r}
  have hz : IsZero (((ev.mapHomologicalComplex (.up ℤ)).obj L.as).homology 0) :=
    IsZero.of_iso ((DerivedCategory.homologyFunctor B 0).map_isZero h)
      (((DerivedCategory.homologyFunctorFactorsh B 0).app
        ((ev.mapHomotopyCategory (.up ℤ)).obj L)) ≪≫
        (HomotopyCategory.homologyFunctor B (.up ℤ) 0).mapIso
          ((ev.mapHomotopyCategoryFactors (.up ℤ)).app L.as) ≪≫
        (HomotopyCategory.homologyFunctorFactors B (.up ℤ) 0).app _).symm
  have hz' : IsZero (((F.mapHomologicalComplex (.up ℤ)).obj L.as).homology 0) :=
    IsZero.of_iso (V.map_isZero hz)
      (HomologicalComplex.homologyMapIso ((NatIso.mapHomologicalComplex
        (smallCoyonedaIsoEvaluation.{u, v, r, m} X U) (.up ℤ)).app L.as) 0 ≪≫
        (((ev.mapHomologicalComplex (.up ℤ)).obj L.as).sc 0).mapHomologyIso V)
  let e := smallCoyonedaHomotopyEquiv E L.as 0
  have hf : f ≫ (HomotopyCategory.quotient A (.up ℤ)).map
      ((shiftFunctorZero (CochainComplex A ℤ) ℤ).inv.app L.as) = 0 := by
    let g := f ≫ (HomotopyCategory.quotient A (.up ℤ)).map
      ((shiftFunctorZero (CochainComplex A ℤ) ℤ).inv.app L.as)
    have he : e.symm g = 0 :=
      (have := AddCommGrpCat.subsingleton_of_isZero hz'; Subsingleton.elim _ _)
    exact (e.apply_symm_apply g).symm.trans ((congrArg e he).trans e.map_zero)
  exact (cancel_mono ((HomotopyCategory.quotient A (.up ℤ)).map
    ((shiftFunctorZero (CochainComplex A ℤ) ℤ).inv.app L.as))).1 (hf.trans zero_comp.symm)

/-- On the homotopy category, `F` sends `φ` to an isomorphism in `D` iff it sends `φ` to a
quasi-isomorphism. -/
private theorem isIso_Qh_map_mapHomotopyCategory_iff
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] {K L : CochainComplex A ℤ} (φ : K ⟶ L) :
    IsIso (DerivedCategory.Qh.map
      ((F.mapHomotopyCategory (.up ℤ)).map ((HomotopyCategory.quotient A (.up ℤ)).map φ))) ↔
      QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map φ) := by
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact NatIso.isIso_map_iff (Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ))
    DerivedCategory.Qh ≪≫ Functor.isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso B)) φ

private theorem map_quasiIso_of_rightAcyclic_terms
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive]
    [(F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    {K L : CochainComplex A ℤ} (f : K ⟶ L) [QuasiIso f]
    (hK : CochainComplex.plus A K) (hL : CochainComplex.plus A L)
    (hKA : ∀ n, F.rightAcyclic (K.X n)) (hLA : ∀ n, F.rightAcyclic (L.X n)) :
    QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f) := by
  let KP : CochainComplex.Plus A := ⟨K, hK⟩
  let LP : CochainComplex.Plus A := ⟨L, hL⟩
  let fp : KP ⟶ LP := ObjectProperty.homMk f
  let q := HomotopyCategory.Plus.quotient A
  let α := F.rightDerivedFunctorPlusUnit
  have : IsIso (α.app (q.obj KP)) :=
    Functor.isIso_totalRightDerivedUnit_app_of_rightAcyclic F K hK hKA
  have : IsIso (α.app (q.obj LP)) :=
    Functor.isIso_totalRightDerivedUnit_app_of_rightAcyclic F L hL hLA
  have : IsIso (DerivedCategory.Plus.Qh.map (q.map fp)) :=
    Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 (show QuasiIso f from inferInstance))
  have heq : (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map (q.map fp) =
      α.app (q.obj KP) ≫
        (DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus).map (q.map fp) ≫
          inv (α.app (q.obj LP)) := by
    rw [← Category.assoc, ← α.naturality (q.map fp), Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have : IsIso ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map (q.map fp)) := by
    rw [heq]
    show IsIso (α.app (q.obj KP) ≫
      F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map (q.map fp)) ≫
        inv (α.app (q.obj LP)))
    infer_instance
  have : IsIso ((DerivedCategory.Plus.ι (C := B)).map
      ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map (q.map fp))) := inferInstance
  exact (isIso_Qh_map_mapHomotopyCategory_iff F f).1 this

/-- If `F` sends `φ` to a quasi-isomorphism, the derived image of the cone of `φ` vanishes. -/
private theorem isZero_map_mappingCone_triangleh_obj₃_of_quasiIso
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] {K L : CochainComplex A ℤ} (φ : K ⟶ L)
    [QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map φ)] :
    IsZero ((F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).obj
      (CochainComplex.mappingCone.triangleh φ).obj₃) := by
  apply ((F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).mapTriangle.obj
    (CochainComplex.mappingCone.triangleh φ)).isZero₃_of_isIso₁
      ((F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).map_distinguished _
        (HomotopyCategory.mappingCone_triangleh_distinguished φ))
  show IsIso (DerivedCategory.Qh.map
    ((F.mapHomotopyCategory (.up ℤ)).map ((HomotopyCategory.quotient A (.up ℤ)).map φ)))
  exact (isIso_Qh_map_mapHomotopyCategory_iff F φ).2 inferInstance

private theorem derived_map_surjective_of_rightAcyclic_terms
    (X : RingedSite.{u, v, r}) (U : X.C)
    (K : CochainComplex (SheafOfModules.{max u v r m}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hK : CochainComplex.plus _ K)
    (hKA :
      letI : EnoughInjectives (SheafOfModules.{max u v r m}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
        enoughInjectives_of_ringedSite.{u, v, r, m} X
      letI : (SheafOfModules.evaluation.{max u v r m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (op U)).Additive :=
        evaluation_additive_of_ringedSite.{u, v, r, m} X U
      ∀ n, (SheafOfModules.evaluation.{max u v r m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (op U)).rightAcyclic (K.X n)) :
    Function.Surjective (DerivedCategory.Q.map :
      (((CochainComplex.singleFunctor _ 0).obj
        (extensionByZeroUnit.{v, u, r, m} X.J
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)) ⟶ K) → _) := by
  let A := SheafOfModules.{max u v r m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let ev := SheafOfModules.evaluation.{max u v r m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (op U)
  have : ev.Additive := evaluation_additive_of_ringedSite.{u, v, r, m} X U
  have : PreservesFiniteLimits ev := SheafOfModules.Finite.evaluationPreservesFiniteLimits _ _
  have : EnoughInjectives A := enoughInjectives_of_ringedSite.{u, v, r, m} X
  let E := extensionByZeroUnit.{v, u, r, m} X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
  let S := (CochainComplex.singleFunctor A 0).obj E
  let q := HomotopyCategory.quotient A (.up ℤ)
  obtain ⟨a, ha⟩ := hK
  have : K.IsStrictlyGE a := ha
  obtain ⟨R, _, hR⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE a K
  have : R.cocomplex.IsStrictlyGE a := hR
  have : ∀ n, Injective (R.cocomplex.X n) := R.injective
  have : R.cocomplex.IsKInjective := CochainComplex.isKInjective_of_injective _ a
  have : QuasiIso ((ev.mapHomologicalComplex (.up ℤ)).map R.ι) :=
    map_quasiIso_of_rightAcyclic_terms ev R.ι ⟨a, ha⟩ ⟨a, hR⟩ hKA
      (fun n => ((Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus ev
        (R.cocomplex.X n)).2 (by infer_instance)).2 (fun p hp =>
          Functor.isZero_rightDerivedPlus_obj_injective ev p (ne_of_gt hp) _))
  let T := CochainComplex.mappingCone.triangleh R.ι
  have hT := HomotopyCategory.mappingCone_triangleh_distinguished R.ι
  have hz : IsZero ((ev.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).obj T.obj₃) :=
    isZero_map_mappingCone_triangleh_obj₃_of_quasiIso ev R.ι
  intro f
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (q.obj S) R.cocomplex).2
    ((DerivedCategory.quotientCompQhIso A).hom.app S ≫ f ≫
      DerivedCategory.Q.map R.ι ≫ (DerivedCategory.quotientCompQhIso A).inv.app R.cocomplex)
  have hgzero : g ≫ T.mor₂ = 0 := homotopyHom_eq_zero_of_evaluation_isZero.{u, v, r, m} X U _ hz _
  obtain ⟨l, hl⟩ := T.coyoneda_exact₂ hT g hgzero
  -- `T.obj₁` is `q.obj K`, but only up to unfolding the mapping cone triangle; naming the
  -- lift at the spelling `S ⟶ K` performs that identification once, so that the naturality
  -- of `quotientCompQhIso` below has a syntactic match to rewrite with.
  obtain ⟨l, hl⟩ : ∃ l' : S ⟶ K, g = q.map l' ≫ T.mor₁ := by
    obtain ⟨l', rfl⟩ := q.map_surjective l
    exact ⟨l', hl⟩
  refine ⟨l, ?_⟩
  have hl' : DerivedCategory.Qh.map (q.map l) ≫ DerivedCategory.Qh.map T.mor₁ =
      (DerivedCategory.quotientCompQhIso A).hom.app S ≫ f ≫
        DerivedCategory.Q.map R.ι ≫ (DerivedCategory.quotientCompQhIso A).inv.app R.cocomplex :=
    (((DerivedCategory.Qh (C := A)).map_comp (q.map l) T.mor₁).symm.trans
      (congrArg (fun t => (DerivedCategory.Qh (C := A)).map t) hl.symm)).trans hg
  change DerivedCategory.Qh.map (q.map l) ≫ DerivedCategory.Qh.map (q.map R.ι) = _ at hl'
  apply (cancel_mono (DerivedCategory.Q.map R.ι)).1
  apply (cancel_epi ((DerivedCategory.quotientCompQhIso A).hom.app S)).1
  simpa only [DerivedCategory.quotientCompQhIso_hom_naturality, Category.assoc,
    DerivedCategory.quotientCompQhIso_hom_naturality_assoc,
    Iso.inv_hom_id_app, Category.comp_id, q, A] using congrArg
      (fun t => t ≫ (DerivedCategory.quotientCompQhIso A).hom.app R.cocomplex) hl'

private noncomputable def coyonedaIsoEvaluation
    (X : RingedSite.{u, v, r}) (U : X.C) :
    preadditiveCoyoneda.obj (op
        (extensionByZeroUnit.{v, u, r, m} X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)) ≅
      SheafOfModules.evaluation.{max u v r m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U) ⋙
        forget₂
          (ModuleCat.{max u v r m} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)))
          AddCommGrpCat.{max u v r m} := by
  refine NatIso.ofComponents
    (fun F => (extensionByZeroHomAddEquiv.{v, u, r, m} X.J
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U F).toAddCommGrpIso) ?_
  intro F G f
  ext g
  exact extensionByZeroHomEquiv_naturality.{v, u, r, m} X.J
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U g f

private theorem extensionByZeroUnit_isCompact
    (X : RingedSite.{u, v, r}) (U : X.C)
    (hsums : ∀ I : Type w, PreservesColimitsOfShape (Discrete I)
      (SheafOfModules.evaluation.{max u v r m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (op U))) :
    IsCompactObject.{w}
      (extensionByZeroUnit.{v, u, r, m} X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) := by
  apply CategoryTheory.isCompactObject_of_preservesColimitsOfShape_preadditiveCoyoneda
  intro I
  have := hsums I
  -- Preservation of a possibly large existing coproduct can be tested on its underlying groups.
  let V := forget₂
    (ModuleCat.{max u v r m} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)))
    AddCommGrpCat.{max u v r m}
  let G := ModuleCat.restrictScalars.{max u v r m} (Int.castRingHom
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))) ⋙
    forget₂ (ModuleCat.{max u v r m} ℤ) AddCommGrpCat.{max u v r m}
  have : (ModuleCat.restrictScalars.{max u v r m}
      (Int.castRingHom ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj
          (op U)))).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{max u v r m, 0, r}
      (Int.castRingHom ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)))).isLeftAdjoint
  have : PreservesColimitsOfShape (Discrete I) G := by
    dsimp [G]
    infer_instance
  have : PreservesColimitsOfShape (Discrete I) V := preservesColimitsOfShape_of_natIso
    (NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl) : G ≅ V)
  exact preservesColimitsOfShape_of_natIso (coyonedaIsoEvaluation.{u, v, r, m} X U).symm

private theorem small_hom_of_plus
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory A]
    [EnoughInjectives A] (M N : DerivedCategory A)
    (hN : (DerivedCategory.TStructure.t (C := A)).plus N) : Small.{v} (M ⟶ N) := by
  let NP : DerivedCategory.Plus A := ⟨N, hN⟩
  obtain ⟨n, hn⟩ := hN
  have : NP.IsGE n := (NP.isGE_ι_obj_iff n).1 hn
  obtain ⟨J, hJ, ⟨e⟩⟩ := NP.exists_injective_nonempty_iso n
  let L := ((InjectiveObject.ι A).mapCochainComplexPlus.obj J).obj
  let q := HomotopyCategory.quotient A (.up ℤ)
  have : L.IsKInjective := inferInstanceAs
    (CochainComplex.IsKInjective (((InjectiveObject.ι A).mapHomologicalComplex (.up ℤ)).obj J.obj))
  let K := DerivedCategory.Q.objPreimage M
  let eK : DerivedCategory.Qh.obj (q.obj K) ≅ M :=
    (DerivedCategory.quotientCompQhIso A).app K ≪≫ DerivedCategory.Q.objObjPreimageIso M
  let eL : DerivedCategory.Qh.obj (q.obj L) ≅ N :=
    (DerivedCategory.quotientCompQhIso A).app L ≪≫ DerivedCategory.Plus.ι.mapIso e
  have : Small.{v} (DerivedCategory.Qh.obj (q.obj K) ⟶ DerivedCategory.Qh.obj (q.obj L)) :=
    small_of_surjective (CochainComplex.IsKInjective.Qh_map_bijective (q.obj K) L).2
  exact small_of_surjective (Iso.homCongr eK eL).surjective

/-- The coproduct inclusion `ι i` has a retraction killing all the other inclusions. -/
private theorem exists_sigma_ι_retraction
    {C : Type*} [Category C] [HasZeroMorphisms C] {I : Type*} (M : I → C) [HasCoproduct M]
    (i : I) :
    ∃ p : ∐ M ⟶ M i, Sigma.ι M i ≫ p = 𝟙 _ ∧ ∀ j, j ≠ i → Sigma.ι M j ≫ p = 0 := by
  classical
  exact ⟨Sigma.desc (Pi.single i (𝟙 (M i))), by simp, fun j hj => by simp [hj]⟩

private theorem small_nonzero_summands
    {C : Type*} [Category C] [Preadditive C] {I : Type*}
    (M : I → C) [HasCoproduct M] [Small.{z} (∐ M ⟶ ∐ M)] :
    Small.{z} {i : I // ¬ IsZero (M i)} := by
  classical
  choose p hp₁ hp₀ using exists_sigma_ι_retraction M
  apply small_of_injective (f := fun i : {i : I // ¬ IsZero (M i)} => p i ≫ Sigma.ι M i)
  intro i j hij
  apply Subtype.ext
  by_contra h
  have hh := congrArg (fun f => Sigma.ι M i ≫ f ≫ p i) hij
  have hid : 𝟙 (M i) = 0 := by
    simpa [hp₁, hp₀ i j (Ne.symm h)] using hh
  exact i.property ((IsZero.iff_id_eq_zero _).2 hid)

private noncomputable def nonzeroSummandsIsColimit
    {C : Type*} [Category C] [Preadditive C] {I : Type*}
    (M : I → C) [HasCoproduct M] :
    IsColimit (Cofan.mk (∐ M) (fun i : {i : I // ¬ IsZero (M i)} => Sigma.ι M i)) := by
  classical
  refine Cofan.IsColimit.mk _
    (fun s => Sigma.desc fun i => if hi : ¬ IsZero (M i) then s.inj ⟨i, hi⟩ else 0) ?_ ?_
  · intro s i
    simp [i.property]
  · intro s f hf
    refine Sigma.hom_ext (f := M) _ _ fun i => ?_
    by_cases hi : IsZero (M i)
    · exact hi.eq_of_src _ _
    · simpa [hi] using hf ⟨i, hi⟩

private theorem exists_sum_single
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
    (P : C) [IsCompactObject.{w} P]
    {I : Type w} [HasCoproductsOfShape I C]
    (J : I → CochainComplex C ℤ) [HasCoproduct J]
    (f : (CochainComplex.singleFunctor C 0).obj P ⟶ ∐ J) :
    ∃ (s : Finset I) (g : ∀ i, (CochainComplex.singleFunctor C 0).obj P ⟶ J i),
      ∑ i ∈ s, g i ≫ Sigma.ι J i = f := by
  classical
  let S := (CochainComplex.singleFunctor C 0).obj P
  let F := HomologicalComplex.eval C (.up ℤ) 0
  have : IsCompactObject.{w} (F.obj S) :=
    isCompactObject_of_iso (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P) inferInstance
  let ι (i : I) := F.map (Sigma.ι J i)
  have hc : IsColimit (Cofan.mk (F.obj (∐ J)) ι) :=
    (isColimitMapCoconeCofanMkEquiv F J (Sigma.ι J))
      (isColimitOfPreserves F (coproductIsCoproduct J))
  obtain ⟨s, a, ha⟩ :=
    StacksDraft.Perfect.exists_sum_cofan_of_isCompactObject (F.obj S) ι hc (F.map f)
  choose p hp₁ hp₀ using exists_sigma_ι_retraction J
  have hp (i : I) (hi : i ∈ s) : F.map f ≫ F.map (p i) = a i := by
    rw [← ha, Preadditive.sum_comp]
    have ht (j : I) : (a j ≫ ι j) ≫ F.map (p i) = if h : j = i then a i else 0 := by
      dsimp only [ι]
      rw [Category.assoc, ← F.map_comp]
      split_ifs with h
      · subst j
        simp [hp₁]
      · rw [hp₀ i j h, F.map_zero, comp_zero]
    simp only [ht]
    simp [hi]
  refine ⟨s, fun i => f ≫ p i, HomologicalComplex.from_single_hom_ext ?_⟩
  show F.map (∑ i ∈ s, (f ≫ p i) ≫ Sigma.ι J i) = F.map f
  simp only [Functor.map_sum, Functor.map_comp]
  calc
    _ = ∑ i ∈ s, a i ≫ ι i := Finset.sum_congr rfl fun i hi => by rw [hp i hi]
    _ = _ := ha

/-- An object of `D⁺` above `n` is represented by a strictly-`≥ n` complex of injectives. -/
private theorem exists_injective_complex_isStrictlyGE_iso
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A] [EnoughInjectives A]
    (M : DerivedCategory A) (n : ℤ) (hM : M.IsGE n) :
    ∃ L : CochainComplex A ℤ, L.IsStrictlyGE n ∧ (∀ k, Injective (L.X k)) ∧
      Nonempty (DerivedCategory.Q.obj L ≅ M) := by
  let MP : DerivedCategory.Plus A := ⟨M, ⟨n, hM⟩⟩
  have : MP.IsGE n := (MP.isGE_ι_obj_iff n).1 hM
  obtain ⟨J, hJ, ⟨e⟩⟩ := MP.exists_injective_nonempty_iso n
  have : J.obj.IsStrictlyGE n := hJ
  refine ⟨((InjectiveObject.ι A).mapCochainComplexPlus.obj J).obj, ?_,
    fun k => (J.obj.X k).property, ⟨DerivedCategory.Plus.ι.mapIso e⟩⟩
  show CochainComplex.IsStrictlyGE
    (((InjectiveObject.ι A).mapHomologicalComplex (.up ℤ)).obj J.obj) n
  infer_instance

/-- A coproduct of strictly-`≥ n` cochain complexes lies in the plus part. -/
private theorem plus_sigma_of_isStrictlyGE
    {A : Type*} [Category* A] [Abelian A] {I : Type*} [HasColimitsOfShape (Discrete I) A]
    (L : I → CochainComplex A ℤ) (n : ℤ) [∀ i, (L i).IsStrictlyGE n] :
    CochainComplex.plus A (∐ L) := by
  refine ⟨n, (CochainComplex.isStrictlyGE_iff _ _).2 fun k hk => ?_⟩
  exact IsZero.of_iso ((coproductIsCoproduct fun i => (L i).X k).isZero_pt
      ((Discrete.functor _).isZero_iff.2 fun i => (L i.as).isZero_of_isStrictlyGE n k hk))
    (PreservesCoproduct.iso (HomologicalComplex.eval A (.up ℤ) k) L)

/-- The coproduct inclusions are compatible with the comparison of `G.obj (∐ L)` with a
colimit cofan on objects isomorphic to the `G.obj (L i)`. -/
private theorem map_sigma_ι_comp_preservesCoproductIso_hom
    {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D) {I : Type*}
    (L : I → C) [HasCoproduct L] [HasCoproductsOfShape I D]
    [PreservesColimit (Discrete.functor L) G] (M : I → D)
    (eL : ∀ i, G.obj (L i) ≅ M i) {N : D} (ι : ∀ i, M i ⟶ N) (hc : IsColimit (Cofan.mk N ι))
    (i : I) :
    G.map (Sigma.ι L i) ≫ (PreservesCoproduct.iso G L ≪≫ Sigma.mapIso eL ≪≫
      (coproductIsCoproduct M).coconePointUniqueUpToIso hc).hom = (eL i).hom ≫ ι i := by
  have hι : G.map (Sigma.ι L i) ≫ (PreservesCoproduct.iso G L).hom =
      Sigma.ι (fun j => G.obj (L j)) i := by
    apply (cancel_mono (PreservesCoproduct.iso G L).inv).1
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id,
      PreservesCoproduct.inv_hom, ι_comp_sigmaComparison]
  dsimp only [Iso.trans_hom]
  rw [← Category.assoc, hι]
  show Sigma.ι (fun j => G.obj (L j)) i ≫ Limits.Sigma.map (fun j => (eL j).hom) ≫
    ((coproductIsCoproduct M).coconePointUniqueUpToIso hc).hom = _
  rw [Sigma.ι_map_assoc]
  exact congrArg (fun t => (eL i).hom ≫ t)
    ((coproductIsCoproduct M).comp_coconePointUniqueUpToIso_hom hc ⟨i⟩)

private theorem exists_sum_derived_of_small
    (X : RingedSite.{u, v, r}) (U : X.C)
    (hsums :
      letI : EnoughInjectives (SheafOfModules.{max u v r m}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
        enoughInjectives_of_ringedSite.{u, v, r, m} X
      letI : (SheafOfModules.evaluation.{max u v r m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (op U)).Additive :=
        evaluation_additive_of_ringedSite.{u, v, r, m} X U
      ∀ (p : ℕ) (I : Type w), PreservesColimitsOfShape (Discrete I)
        ((SheafOfModules.evaluation.{max u v r m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            (op U)).rightDerived p))
    (I : Type w) [Small.{max u v r m} I]
    (M : I → DerivedCategory (SheafOfModules.{max u v r m}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (N : DerivedCategory (SheafOfModules.{max u v r m}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (ι : ∀ i, M i ⟶ N) (hc : IsColimit (Cofan.mk N ι))
    (n : ℤ) (hMi : ∀ i, (M i).IsGE n)
    (f : ((DerivedCategory.singleFunctor _ 0).obj
      (extensionByZeroUnit.{v, u, r, m} X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)) ⟶ N) :
    ∃ (s : Finset I) (g : ∀ i, _ ⟶ M i), ∑ i ∈ s, g i ≫ ι i = f := by
  classical
  let A := SheafOfModules.{max u v r m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let ev := SheafOfModules.evaluation.{max u v r m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (op U)
  have : IsGrothendieckAbelian.{max u v r m} A :=
    Stacks.SheafOfModules.sheafModulesGrothendieck.{u, v, r, m} X.J
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  have : EnoughInjectives A := enoughInjectives_of_ringedSite.{u, v, r, m} X
  have : ev.Additive := evaluation_additive_of_ringedSite.{u, v, r, m} X U
  have : PreservesFiniteLimits ev := SheafOfModules.Finite.evaluationPreservesFiniteLimits _ _
  have : HasColimitsOfShape (Discrete I) A :=
    HasColimitsOfShape.of_small.{max u v r m, max u v r m} A _
  have : HasColimitsOfShape (Discrete I) (DerivedCategory A) :=
    hasColimitsOfShape_of_equivalence (Discrete.equivalence (equivShrink.{max u v r m} I).symm)
  have : PreservesColimitsOfShape (Discrete I) (DerivedCategory.Q (C := A)) :=
    preservesColimitsOfShape_of_equiv
      (Discrete.equivalence (equivShrink.{max u v r m} I).symm) DerivedCategory.Q
  have hpres (I : Type w) : PreservesColimitsOfShape (Discrete I) ev := by
    have := hsums 0 I
    exact preservesColimitsOfShape_of_natIso ev.rightDerivedZeroIsoSelf
  let E := extensionByZeroUnit.{v, u, r, m} X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
  have : IsCompactObject.{w} E := extensionByZeroUnit_isCompact.{u, v, r, w, m} X U hpres
  choose L hLGE hLI heL using fun i => exists_injective_complex_isStrictlyGE_iso (M i) n (hMi i)
  have (i : I) : (L i).IsStrictlyGE n := hLGE i
  have (i : I) (k : ℤ) : Injective ((L i).X k) := hLI i k
  let eL (i : I) : DerivedCategory.Q.obj (L i) ≅ M i := (heL i).some
  have hLA (k : ℤ) : ev.rightAcyclic ((∐ L).X k) :=
    ev.rightAcyclic.prop_of_iso
      (PreservesCoproduct.iso (HomologicalComplex.eval A (.up ℤ) k) L).symm
      (rightAcyclic_coproduct_of_injectives ev I (fun i => (L i).X k)
        (fun i => inferInstance) inferInstance (fun p => hsums p I))
  let eS := (DerivedCategory.singleFunctorIsoCompQ A 0).app E
  let e : DerivedCategory.Q.obj (∐ L) ≅ N :=
    PreservesCoproduct.iso DerivedCategory.Q L ≪≫ Sigma.mapIso eL ≪≫
      (coproductIsCoproduct M).coconePointUniqueUpToIso hc
  have he (i : I) : DerivedCategory.Q.map (Sigma.ι L i) ≫ e.hom = (eL i).hom ≫ ι i :=
    map_sigma_ι_comp_preservesCoproductIso_hom DerivedCategory.Q L M eL ι hc i
  obtain ⟨l, hl⟩ := derived_map_surjective_of_rightAcyclic_terms.{u, v, r, m} X U (∐ L)
    (plus_sigma_of_isStrictlyGE L n) hLA (eS.inv ≫ f ≫ e.inv)
  obtain ⟨s, g, hg⟩ := exists_sum_single E L l
  refine ⟨s, fun i => eS.hom ≫ DerivedCategory.Q.map (g i) ≫ (eL i).hom, ?_⟩
  calc
    _ = eS.hom ≫ DerivedCategory.Q.map (∑ i ∈ s, g i ≫ Sigma.ι L i) ≫ e.hom := by
      simp only [Functor.map_sum, Functor.map_comp, Preadditive.comp_sum,
        Preadditive.sum_comp, Category.assoc, he]
    _ = f := by
      rw [hg, hl]
      simp

/-- Extension by zero of the unit module on `U` is compact with respect to
bounded-below direct sums, provided cohomology on `U` commutes with direct sums. -/
@[stacks 0G21]
public theorem extensionByZero_unit_hom_coproduct_bijective
    (X : RingedSite.{u, v, r}) (U : X.C)
    (hsums :
      letI : EnoughInjectives (SheafOfModules.{max u v r m}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
        enoughInjectives_of_ringedSite.{u, v, r, m} X
      letI : (SheafOfModules.evaluation.{max u v r m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (op U)).Additive :=
        evaluation_additive_of_ringedSite.{u, v, r, m} X U
      ∀ (p : ℕ) (I : Type w),
      PreservesColimitsOfShape (Discrete I)
        ((SheafOfModules.evaluation.{max u v r m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            (op U)).rightDerived p))
    (I : Type w) [DecidableEq I]
    (M : I → DerivedCategory (SheafOfModules.{max u v r m}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) [HasCoproduct M]
    (hM : (DerivedCategory.TStructure.t
      (C := SheafOfModules.{max u v r m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).plus
          (∐ M)) :
    let K : DerivedCategory (SheafOfModules.{max u v r m}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{max u v r m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
        (extensionByZeroUnit.{v, u, r, m} X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U))
    Function.Bijective
      (DirectSum.toAddMonoid (β := fun i : I => K ⟶ M i) (γ := K ⟶ ∐ M)
        fun i => Preadditive.rightComp K (Limits.Sigma.ι M i)) := by
  let A := SheafOfModules.{max u v r m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let ev := SheafOfModules.evaluation.{max u v r m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (op U)
  have : IsGrothendieckAbelian.{max u v r m} A :=
    Stacks.SheafOfModules.sheafModulesGrothendieck.{u, v, r, m} X.J
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  have : EnoughInjectives A := enoughInjectives_of_ringedSite.{u, v, r, m} X
  have : ev.Additive := evaluation_additive_of_ringedSite.{u, v, r, m} X U
  obtain ⟨n, hn⟩ := hM
  have hMiGE (i : I) : (M i).IsGE n := by
    rw [DerivedCategory.isGE_iff]
    intro k hk
    let H := DerivedCategory.homologyFunctor A k
    obtain ⟨p, hp, -⟩ := exists_sigma_ι_retraction M i
    have : (∐ M).IsGE n := hn
    refine (IsZero.iff_id_eq_zero _).2 ?_
    rw [← H.map_id, ← hp, H.map_comp,
      (DerivedCategory.isZero_of_isGE (∐ M) n k hk).eq_of_tgt (H.map (Sigma.ι M i)) 0, zero_comp]
  classical
  have : Small.{max u v r m} (∐ M ⟶ ∐ M) := small_hom_of_plus (∐ M) (∐ M) ⟨n, hn⟩
  have : Small.{max u v r m} {i : I // ¬ IsZero (M i)} := small_nonzero_summands M
  refine ⟨StacksDraft.Perfect.injective_directSumToHom _ M, ?_⟩
  intro f
  obtain ⟨s, g, hg⟩ := exists_sum_derived_of_small.{u, v, r, w, m} X U hsums
    {i : I // ¬ IsZero (M i)} (fun i => M i) (∐ M) (fun i => Sigma.ι M i)
    (nonzeroSummandsIsColimit M) n (fun i => hMiGE i) f
  refine ⟨∑ i ∈ s, DirectSum.of _ i.val (g i), ?_⟩
  simpa only [map_sum, DirectSum.toAddMonoid_of, Preadditive.rightComp,
    AddMonoidHom.mk'_apply] using hg

end Stacks.Cohomology

end

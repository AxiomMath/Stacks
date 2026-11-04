module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.Injective.Extend
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Whiskering
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.Coproducts
public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedBoundedCohomologicalDimension
public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution

/-!
# Finite-dimensional derived functors and direct sums

A left exact functor between Grothendieck abelian categories whose higher derived functors
have uniformly bounded degree and preserve direct sums has an unbounded right derived functor
which preserves direct sums.

## Main results

* `Stacks.DerivedFunctor.Coproducts.preservesCoproductsOfShape_of_finiteCohomologicalDimension`:
  an unbounded right derived functor preserves coproducts when all the ordinary right derived
  functors do and they vanish in sufficiently high degrees.

## Implementation notes

Left exactness is expressed by preservation of finite limits. The unbounded right derived
functor and its canonical comparison are allowed to be any right derived functor in the sense
of localization; consequently the assertion does not depend on a choice of construction.
Finite cohomological dimension is recorded by a chosen uniform bound `n`. Arbitrary direct
sums mean coproducts indexed by any type in the universe controlled by the Grothendieck
axioms.

## References

* [Stacks Project, Tag 0F5Z](https://stacks.math.columbia.edu/tag/0F5Z)
-/

public section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe z w v₁ v₂ u₁ u₂

namespace Stacks.DerivedFunctor.Coproducts

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

private noncomputable def isColimit_mapCocone_of_isIso_comparison
    {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D]
    {J : Type w} [Category J]
    (K : J ⥤ C) (c : Cocone K) (G H : C ⥤ D) (α : G ⟶ H)
    (hlegs : ∀ j : J, IsIso (α.app (K.obj j)))
    (hapex : IsIso (α.app c.pt))
    (hG : IsColimit (G.mapCocone c)) : IsColimit (H.mapCocone c) := by
  let (j : J) : IsIso (α.app (K.obj j)) := hlegs j
  have : IsIso (Functor.whiskerLeft K α) :=
    (NatTrans.isIso_iff_isIso_app _).2 hlegs
  let e : K ⋙ G ≅ K ⋙ H := asIso (Functor.whiskerLeft K α)
  have h : IsColimit ((Cocone.precompose e.inv).obj (G.mapCocone c)) :=
    (IsColimit.precomposeHomEquiv e.symm (G.mapCocone c)).symm hG
  let : IsIso (α.app c.pt) := hapex
  exact IsColimit.ofIsoColimit h (Cocone.ext (asIso (α.app c.pt)) fun j => by
    simp only [Cocone.precompose_obj_ι, e, Functor.mapCocone_ι_app]
    simp)

private lemma rightAcyclic_of_injective
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [EnoughInjectives A]
    [HasDerivedCategory A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (X : A) [Injective X] : F.rightAcyclic X := by
  apply (CategoryTheory.rightAcyclic_iff_isZero_rightDerived F X).2
  intro q hq
  cases q with
  | zero => omega
  | succ k => exact F.isZero_rightDerived_obj_injective_succ k X

private lemma rightAcyclic_complexCoproduct_terms
    (A : Type u₁) [Category.{v₁} A] [Abelian A] [EnoughInjectives A]
    [HasDerivedCategory A]
    (B : Type u₂) [Category.{v₂} B] [Abelian B] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (I : Type w) [HasColimitsOfShape (Discrete I) A]
    (hcoproducts : ∀ q : ℕ, PreservesColimitsOfShape (Discrete I) (F.rightDerived q))
    (K : I → CochainComplex A ℤ)
    (hK : ∀ i n, F.rightAcyclic ((K i).X n)) (n : ℤ) :
    F.rightAcyclic ((∐ K).X n) := by
  apply (CategoryTheory.rightAcyclic_iff_isZero_rightDerived F _).2
  intro q hq
  let E := HomologicalComplex.eval A (ComplexShape.up ℤ) n
  have : PreservesColimitsOfShape (Discrete I) E := inferInstance
  let := hcoproducts q
  have : PreservesColimitsOfShape (Discrete I) (E ⋙ F.rightDerived q) := inferInstance
  have hz : IsZero (Discrete.functor K ⋙ E ⋙ F.rightDerived q) :=
    (Discrete.functor K ⋙ E ⋙ F.rightDerived q).isZero_iff.mpr fun i =>
      (CategoryTheory.rightAcyclic_iff_isZero_rightDerived F _).1 (hK i.as n) q hq
  exact (isColimitOfPreserves (E ⋙ F.rightDerived q) (coproductIsCoproduct K)).isZero_pt hz

private lemma rightAcyclic_iff_computesRightDerived
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [EnoughInjectives A]
    [HasDerivedCategory A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] (X : A) :
    F.rightAcyclic X ↔
      (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).ComputesRightDerived
        (HomotopyCategory.Plus.quasiIso A)
        ((HomotopyCategory.Plus.singleFunctor A 0).obj X) := by
  classical
  have hres (K : HomotopyCategory.Plus A) :
      ∃ (Y : HomotopyCategory.Plus A) (f : K ⟶ Y)
        (_ : HomotopyCategory.Plus.quasiIso A f),
        IsIso (F.rightDerivedFunctorPlusUnit.app Y) := by
    obtain ⟨a, ha⟩ := (HomotopyCategory.plus_quotient_obj_iff K.obj.as).1 K.property
    let P : ObjectProperty A := Injective
    have : P.ContainsZero := ⟨0, isZero_zero A, inferInstance⟩
    obtain ⟨L, f, hf, hL, _, hge⟩ :=
      CochainComplex.exists_quasiIso_prop_isStrictlyGE P
        (fun X => ⟨Injective.under X, inferInstance, Injective.ι X, inferInstance⟩)
        a K.obj.as
    let Y : HomotopyCategory.Plus A :=
      (HomotopyCategory.Plus.quotient A).obj ⟨L, ⟨a, hge⟩⟩
    have hY : ∀ i : ℤ, Injective (Y.obj.as.X i) := fun i => hL i
    have hunit : IsIso (F.rightDerivedFunctorPlusUnit.app Y) := by
      let (i : ℤ) : Injective (Y.obj.as.X i) := hY i
      infer_instance
    exact ⟨Y, ObjectProperty.homMk ((HomotopyCategory.quotient A _).map f),
      (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf, hunit⟩
  have : (HomotopyCategory.Plus.quasiIso A).HasLeftCalculusOfFractions := by
    rw [HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW]
    infer_instance
  exact (Functor.computesRightDerived_iff_isIso_app
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
    DerivedCategory.Plus.Qh F.rightDerivedFunctorPlus
    (HomotopyCategory.Plus.quasiIso A) F.rightDerivedFunctorPlusUnit
    ((HomotopyCategory.Plus.singleFunctor A 0).obj X) hres).symm

private lemma isIso_alpha_of_rightAcyclic_terms
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [EnoughInjectives A]
    [HasDerivedCategory A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (n : ℕ) (hvanish : ∀ X : A, IsZero ((F.rightDerived n).obj X))
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (K : CochainComplex A ℤ) (hK : ∀ i : ℤ, F.rightAcyclic (K.X i)) :
    IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) := by
  have hmono (X : A) : ∃ (Y : A) (i : X ⟶ Y) (_ : Mono i), F.rightAcyclic Y := by
    exact ⟨Injective.under X, Injective.ι X, inferInstance, rightAcyclic_of_injective F _⟩
  have hn (X : A) : IsZero ((DerivedCategory.Plus.homologyFunctor B n).obj
      (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X))) := by
    show IsZero ((F.rightDerivedPlus (n : ℤ)).obj X)
    exact (hvanish X).of_iso (CategoryTheory.rightDerivedPlusObjIso F X n)
  have h := Functor.hasRightDerivedFunctor_of_isZero_rightDerived
    F F.rightDerivedFunctorPlus F.rightDerivedFunctorPlusUnit F.rightAcyclic
    (rightAcyclic_iff_computesRightDerived F) hmono n hn
  exact (h.2.2 RF α).1 K hK

private noncomputable def complexComparison
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF) :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RF := by
  let qA := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let qB := HomotopyCategory.quotient B (ComplexShape.up ℤ)
  let FM := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let FH := F.mapHomotopyCategory (ComplexShape.up ℤ)
  let e₀ : FM ⋙ DerivedCategory.Q ≅ qA ⋙ (FH ⋙ DerivedCategory.Qh) :=
    Functor.isoWhiskerLeft FM (DerivedCategory.quotientCompQhIso B).symm ≪≫
      (Functor.associator FM qB DerivedCategory.Qh).symm ≪≫
      Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).symm
        DerivedCategory.Qh ≪≫
      Functor.associator qA FH DerivedCategory.Qh
  let e₁ : qA ⋙ (DerivedCategory.Qh ⋙ RF) ≅ DerivedCategory.Q ⋙ RF :=
    (Functor.associator qA DerivedCategory.Qh RF).symm ≪≫
      Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A) RF
  exact e₀.hom ≫ Functor.whiskerLeft qA α ≫ e₁.hom

private lemma complexComparison_isIso
    {A : Type u₁} [Category.{v₁} A] [Abelian A] [EnoughInjectives A]
    [HasDerivedCategory A]
    {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (n : ℕ) (hvanish : ∀ X : A, IsZero ((F.rightDerived n).obj X))
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (K : CochainComplex A ℤ) (hK : ∀ i : ℤ, F.rightAcyclic (K.X i)) :
    IsIso ((complexComparison F RF α).app K) := by
  have := isIso_alpha_of_rightAcyclic_terms F n hvanish RF α K hK
  unfold complexComparison
  dsimp
  infer_instance

/-- A functor preserves coproducts of shape `I` if it preserves those of every `I`-indexed
family. -/
private lemma preservesColimitsOfShape_discrete_of_forall {C : Type*} [Category C] {D : Type*}
    [Category D] {I : Type*} (G : C ⥤ D)
    (h : ∀ K : I → C, PreservesColimit (Discrete.functor K) G) :
    PreservesColimitsOfShape (Discrete I) G := by
  constructor
  intro K
  have := h fun i => K.obj ⟨i⟩
  exact preservesColimit_of_iso_diagram (K₁ := Discrete.functor fun i => K.obj ⟨i⟩) G
    (Discrete.natIso fun ⟨i⟩ => Iso.refl _)

private theorem derivedCategoryQ_preservesCoproducts
    (A : Type u₁) [Category.{v₁} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{z} A] (I : Type w) :
    PreservesColimitsOfShape (Discrete I) (DerivedCategory.Q (C := A)) := by
  have hK (K : I → CochainComplex A ℤ) :
      PreservesColimit (Discrete.functor K) (DerivedCategory.Q (C := A)) := by
    let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
    have hc := (isColimit_mapCofan_of_exists_map_bijective DerivedCategory.Qh
      (exists_map_bijective_Qh_of_exists_quasiIso_isKInjective A
        (fun M => by
          obtain ⟨L, f, hL, hf⟩ :=
            Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian A M
          exact ⟨L, f, hf, hL⟩))
      (fun i => q.map (Sigma.ι K i))
      (HomotopyCategoryCoproduct.cleanColimit A K)).some
    have : PreservesColimit (Discrete.functor K) (q ⋙ DerivedCategory.Qh) :=
      preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct K)
        ((isColimitMapCoconeCofanMkEquiv (q ⋙ DerivedCategory.Qh) K (Sigma.ι K)).symm hc)
    exact preservesColimit_of_natIso _ (DerivedCategory.quotientCompQhIso A)
  exact preservesColimitsOfShape_discrete_of_forall _ hK

private lemma preservesCoproducts_complexMapped
    (A : Type u₁) [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    (B : Type u₂) [Category.{v₂} B] [Abelian B] [IsGrothendieckAbelian.{w} B]
    [HasDerivedCategory.{z} A] [HasDerivedCategory.{z} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (I : Type w) [PreservesColimitsOfShape (Discrete I) (F.rightDerived 0)] :
    PreservesColimitsOfShape (Discrete I)
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) := by
  let := preservesColimitsOfShape_of_natIso (J := Discrete I) F.rightDerivedZeroIsoSelf
  let := derivedCategoryQ_preservesCoproducts B I
  have : HasColimitsOfShape (Discrete I) A := inferInstance
  have : PreservesColimitsOfShape (Discrete I)
      (F.mapHomologicalComplex (ComplexShape.up ℤ)) := inferInstance
  infer_instance

private lemma preservesColimit_of_rightAcyclic_terms
    (A : Type u₁) [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    (B : Type u₂) [Category.{v₂} B] [Abelian B] [IsGrothendieckAbelian.{w} B]
    [HasDerivedCategory.{z} A] [HasDerivedCategory.{z} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (n : ℕ) (hvanish : ∀ X : A, IsZero ((F.rightDerived n).obj X))
    (I : Type w)
    (hcoproducts : ∀ q : ℕ, PreservesColimitsOfShape (Discrete I) (F.rightDerived q))
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (K : I → CochainComplex A ℤ)
    (hK : ∀ i j, F.rightAcyclic ((K i).X j)) :
    PreservesColimit (Discrete.functor K) (DerivedCategory.Q (C := A) ⋙ RF) := by
  let := hcoproducts 0
  have := preservesCoproducts_complexMapped A B F I
  let G := F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q
  let H := DerivedCategory.Q (C := A) ⋙ RF
  let β := complexComparison F RF α
  have hlegs (j : Discrete I) : IsIso (β.app ((Discrete.functor K).obj j)) :=
    complexComparison_isIso F n hvanish RF α (K j.as) (hK j.as)
  have hapex : IsIso (β.app (∐ K)) :=
    complexComparison_isIso F n hvanish RF α (∐ K)
      (rightAcyclic_complexCoproduct_terms A B F I hcoproducts K hK)
  have hc := isColimit_mapCocone_of_isIso_comparison (Discrete.functor K)
    (Cofan.mk (∐ K) (Sigma.ι K)) G H β hlegs hapex
    (isColimitOfPreserves G (coproductIsCoproduct K))
  exact preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct K) hc

private lemma preservesColimit_of_resolved_family
    {C D E : Type*} [Category C] [Category D] [Category E]
    {I : Type*} [HasCoproductsOfShape I C] [HasCoproductsOfShape I D]
    (Q : C ⥤ D) [PreservesColimitsOfShape (Discrete I) Q] (H : D ⥤ E)
    (X Y : I → C) (p : ∀ i, X i ⟶ Y i)
    (hp : ∀ i, IsIso (Q.map (p i)))
    (hY : PreservesColimit (Discrete.functor Y) (Q ⋙ H)) :
    PreservesColimit (Discrete.functor X) (Q ⋙ H) := by
  classical
  let (i : I) : IsIso (Q.map (p i)) := hp i
  have hcomm : sigmaComparison Q X ≫ Q.map (Limits.Sigma.map p) =
      Limits.Sigma.map (fun i => Q.map (p i)) ≫ sigmaComparison Q Y := by
    ext i
    rw [ι_comp_sigmaComparison_assoc, ← Q.map_comp, Sigma.ι_map, Q.map_comp,
      Sigma.ι_map_assoc, ι_comp_sigmaComparison]
  have hQmap : IsIso (Q.map (Limits.Sigma.map p)) := by
    have heq : Q.map (Limits.Sigma.map p) =
        inv (sigmaComparison Q X) ≫ Limits.Sigma.map (fun i => Q.map (p i)) ≫
          sigmaComparison Q Y := by
      rw [← hcomm]
      simp
    rw [heq]
    infer_instance
  have hHmap : IsIso ((Q ⋙ H).map (Limits.Sigma.map p)) := by
    show IsIso (H.map (Q.map (Limits.Sigma.map p)))
    infer_instance
  have hHi (i : I) : IsIso ((Q ⋙ H).map (p i)) := by
    show IsIso (H.map (Q.map (p i)))
    infer_instance
  let e : Discrete.functor X ⋙ (Q ⋙ H) ≅ Discrete.functor Y ⋙ (Q ⋙ H) :=
    Discrete.natIso fun ⟨i⟩ => asIso ((Q ⋙ H).map (p i))
  let cX := (Q ⋙ H).mapCocone (Cofan.mk (∐ X) (Sigma.ι X))
  let cY := (Q ⋙ H).mapCocone (Cofan.mk (∐ Y) (Sigma.ι Y))
  let := hY
  have hcY : IsColimit cY := isColimitOfPreserves (Q ⋙ H) (coproductIsCoproduct Y)
  have hpre : IsColimit ((Cocone.precompose e.hom).obj cY) :=
    (IsColimit.precomposeHomEquiv e cY).symm hcY
  let u : cX ≅ (Cocone.precompose e.hom).obj cY :=
    Cocone.ext (asIso ((Q ⋙ H).map (Limits.Sigma.map p))) (by
      intro j
      simp only [Cocone.precompose_obj_ι]
      show (Q ⋙ H).map (Sigma.ι X j.as) ≫ (Q ⋙ H).map (Limits.Sigma.map p) =
        (Q ⋙ H).map (p j.as) ≫ (Q ⋙ H).map (Sigma.ι Y j.as)
      rw [← Functor.map_comp, ← Functor.map_comp, Sigma.ι_map])
  exact preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct X)
    (IsColimit.ofIsoColimit hpre u.symm)

/-- The derived category of a Grothendieck abelian category has coproducts of shape `I`. -/
private lemma hasCoproductsOfShape_derivedCategory
    (A : Type u₁) [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    [HasDerivedCategory.{z} A] (I : Type w) :
    HasCoproductsOfShape I (DerivedCategory A) := by
  have : PreservesColimitsOfShape (Discrete I) (DerivedCategory.Q (C := A)) :=
    derivedCategoryQ_preservesCoproducts A I
  constructor
  intro D
  let K : Discrete I ⥤ CochainComplex A ℤ :=
    Discrete.functor (fun i => (DerivedCategory.Q (C := A)).objPreimage (D.obj ⟨i⟩))
  have : PreservesColimit K (DerivedCategory.Q (C := A)) := inferInstance
  exact ⟨(hasColimit_of_iso (F := K ⋙ DerivedCategory.Q)
    (Discrete.natIso (fun i =>
      ((DerivedCategory.Q (C := A)).objObjPreimageIso (D.obj i)).symm))).exists_colimit⟩

private lemma preservesColimit_Q_comp_of_finiteCohomologicalDimension
    (A : Type u₁) [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    (B : Type u₂) [Category.{v₂} B] [Abelian B] [IsGrothendieckAbelian.{w} B]
    [HasDerivedCategory.{z} A] [HasDerivedCategory.{z} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (n : ℕ) (hvanish : ∀ q : ℕ, n ≤ q → ∀ X : A, IsZero ((F.rightDerived q).obj X))
    (hcoproducts : ∀ (q : ℕ) (I : Type w),
      PreservesColimitsOfShape (Discrete I) (F.rightDerived q))
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (I : Type w) (K : I → CochainComplex A ℤ) :
    PreservesColimit (Discrete.functor K) (DerivedCategory.Q (C := A) ⋙ RF) := by
  have : PreservesColimitsOfShape (Discrete I) (DerivedCategory.Q (C := A)) :=
    derivedCategoryQ_preservesCoproducts A I
  have := hasCoproductsOfShape_derivedCategory A I
  let R := Stacks.Injectives.kInjectiveResolutionFunctor A
  let η := Stacks.Injectives.kInjectiveResolutionInclusion A
  let L : I → CochainComplex A ℤ := fun i => R.obj (K i)
  let p : ∀ i, K i ⟶ L i := fun i => η.app (K i)
  have hp (i : I) : IsIso ((DerivedCategory.Q (C := A)).map (p i)) := by
    let : QuasiIso (p i) := inferInstance
    infer_instance
  have hL (i : I) (j : ℤ) : F.rightAcyclic ((L i).X j) := by
    have : Injective ((L i).X j) :=
      Stacks.Injectives.kInjectiveResolutionFunctor_obj_X_injective A (K i) j
    exact rightAcyclic_of_injective F _
  exact preservesColimit_of_resolved_family (DerivedCategory.Q (C := A)) RF K L p hp
    (preservesColimit_of_rightAcyclic_terms A B F n (hvanish n le_rfl) I
      (fun q => hcoproducts q I) RF α L hL)

/-- A finite-dimensional right derived functor preserves arbitrary direct sums provided all
of its ordinary right derived functors preserve them. -/
public lemma preservesCoproductsOfShape_of_finiteCohomologicalDimension
    (A : Type u₁) [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    (B : Type u₂) [Category.{v₂} B] [Abelian B] [IsGrothendieckAbelian.{w} B]
    [HasDerivedCategory.{z} A] [HasDerivedCategory.{z} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (n : ℕ) (hvanish : ∀ q : ℕ, n ≤ q → ∀ X : A, IsZero ((F.rightDerived q).obj X))
    (hcoproducts : ∀ (q : ℕ) (I : Type w),
      PreservesColimitsOfShape (Discrete I) (F.rightDerived q))
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (I : Type w) : PreservesColimitsOfShape (Discrete I) RF := by
  have : PreservesColimitsOfShape (Discrete I) (DerivedCategory.Q (C := A)) :=
    derivedCategoryQ_preservesCoproducts A I
  have := hasCoproductsOfShape_derivedCategory A I
  have := preservesColimitsOfShape_discrete_of_forall (DerivedCategory.Q (C := A) ⋙ RF)
    (preservesColimit_Q_comp_of_finiteCohomologicalDimension A B F n hvanish hcoproducts RF α I)
  exact preservesColimitsOfShape_discrete_of_essSurj_comp
    (DerivedCategory.Q (C := A)) RF I

end Stacks.DerivedFunctor.Coproducts

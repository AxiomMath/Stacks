module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.Preadditive.Opposite
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.KrullDimension.Module
public import StacksFrontier.Algebra.Module.InjectiveHull.Basic
public import StacksFrontier.Homology.HomComplex.DerivedAdjunction
public import StacksFrontier.RingTheory.Dualizing.Complex.Local
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.Duality
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.ExtComparison
public import StacksFrontier.RingTheory.Dualizing.DualizingDerivedHom
public import StacksFrontier.RingTheory.Dualizing.Normalized
public import StacksFrontier.RingTheory.Dualizing.ResidueFieldHull
public import StacksFrontier.RingTheory.Dualizing.ResidueFieldHull.Matlis
public import StacksFrontier.RingTheory.Support.Finite
import StacksCore.Tactic.EgaSgaAttribute
/-!
# Derived Hom into a dualizing complex on finite-length modules

For a normalized dualizing complex `K` over a Noetherian local ring, derived Hom into `K` sends
a finite-length module into the heart, and taking zeroth cohomology gives a contravariant
self-equivalence of the category of finite-length modules.

## Main definitions

* `Dualizing.FiniteLengthModules` is the full subcategory of finite-length modules.
* `Dualizing.derivedHomFiniteLengthFunctor` is derived Hom into a fixed object, restricted
  contravariantly to finite-length modules.
* `Dualizing.matlisDualFiniteLengthFunctor` sends `N` to `Hom_A(N, E)[0]`.
-/

@[expose] public noncomputable section

open CategoryTheory
open StacksDraft.DerivedHom

attribute [local instance] HasDerivedCategory.standard

universe u v u' v' w'

namespace Dualizing

private lemma injectiveHull_comp_iso
    {C : Type u'} [Category.{v'} C] [Limits.HasZeroObject C]
    [Limits.HasPullbacks C] {X Y Z : C}
    (e : X ≅ Y) (f : Y ⟶ Z) [Mono f]
    (hf : Module.IsInjectiveHull f) :
    Module.IsInjectiveHull (e.hom ≫ f) := by
  refine ⟨hf.1, ?_⟩
  intro Z' hZ'
  have heq : Subobject.mk (e.hom ≫ f) = Subobject.mk f :=
    Subobject.mk_eq_mk_of_comm _ _ e rfl
  simpa only [heq] using hf.2 Z' hZ'

private lemma isAdicComplete_of_nilpotentIdeal
    (R : Type u) [CommRing R] (I : Ideal R) (hI : IsNilpotent I) :
    IsAdicComplete I R := by
  obtain ⟨n, hn⟩ := hI
  have hzero : (I ^ n • (⊤ : Submodule R R)) = ⊥ := by
    rw [hn]
    simp
  refine { haus' := fun x hx => ?_, prec' := fun f hf => ?_ }
  · have hx' := hx n
    rw [hzero, SModEq.bot] at hx'
    exact hx'
  · refine ⟨f n, fun k => ?_⟩
    by_cases hk : k ≤ n
    · exact hf hk
    · have hnk : n ≤ k := le_of_lt (lt_of_not_ge hk)
      have heq : f n = f k := by
        have h := hf hnk
        rw [hzero, SModEq.bot] at h
        exact h
      exact heq.symm ▸ rfl

private lemma isSimpleModule_quotient_of_torsion
    (A : Type u) [CommRing A] (I : Ideal A)
    (M : Type (max v u)) [AddCommGroup M] [Module A M]
    [IsSimpleModule A M]
    (hT : Module.IsTorsionBySet A M (I : Set A)) :
    letI := hT.module
    IsSimpleModule (A ⧸ I) M := by
  let := hT.module
  let e := Submodule.orderIsoOfAlgebraMapSurjective
    (R := A) (S := A ⧸ I) (M := M) (Ideal.Quotient.mk_surjective (I := I))
  have : IsSimpleOrder (Submodule A M) :=
    (isSimpleModule_iff A M).mp inferInstance
  exact (isSimpleModule_iff (A ⧸ I) M).mpr e.isSimpleOrder

/-- The category of finite-length modules over `A` in an independently chosen module
universe. -/
@[sga "2 IV 4.2"]
public abbrev FiniteLengthModules (A : Type u) [CommRing A] :=
  ObjectProperty.FullSubcategory
    (fun M : ModuleCat.{max v u} A => IsFiniteLength A M)

/-- The contravariant functor `N ↦ RHom_A(N, K)` on finite-length modules. -/
public noncomputable def derivedHomFiniteLengthFunctor (A : Type u) [CommRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A)) :
    (FiniteLengthModules.{u, v} A)ᵒᵖ ⥤ DerivedCategory (ModuleCat.{max v u} A) :=
  Functor.prod'
      ((ObjectProperty.ι
          (P := fun M : ModuleCat.{max v u} A => IsFiniteLength A M)).op ⋙
        (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).op)
      ((Functor.const _).obj K) ⋙
    (derivedHomAdjunctionOverRing.{u, v} A).hom

/-- Matlis duality `N ↦ Hom_A(N, E)[0]` on finite-length modules. -/
public noncomputable abbrev matlisDualFiniteLengthFunctor (A : Type u) [CommRing A]
    (E : ModuleCat.{max v u} A) :
    (FiniteLengthModules.{u, v} A)ᵒᵖ ⥤ DerivedCategory (ModuleCat.{max v u} A) :=
  (ObjectProperty.ι
      (P := fun M : ModuleCat.{max v u} A => IsFiniteLength A M)).op ⋙
    MonoidalClosed.internalHom ⋙
  (evaluation (ModuleCat.{max v u} A) (ModuleCat.{max v u} A)).obj E ⋙
    DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0

private lemma derivedHomFiniteLengthFunctor_eq_restriction
    (A : Type u) [CommRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A)) :
    derivedHomFiniteLengthFunctor A K =
      ((ObjectProperty.ι
          (P := fun M : ModuleCat.{max v u} A => IsFiniteLength A M)).op ⋙
        (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).op) ⋙
          dualizingDerivedHomFunctor A K := by
  rfl

/-- A finite module placed in degree zero has finite cohomology in every degree. -/
lemma finiteCohomology_single
    (A : Type u) [CommRing A]
    (M : ModuleCat.{max v u} A) [Module.Finite A M] (i : ℤ) :
    Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj M)) := by
  let H : ModuleCat.{max v u} A :=
    (DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj M)
  by_cases hi : i = 0
  · subst i
    let e := (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{max v u} A) 0).app M
    let f : M →ₗ[A] H := ModuleCat.homEquiv e.inv
    have hf : Function.Surjective f := by
      intro x
      refine ⟨ModuleCat.homEquiv e.hom x, ?_⟩
      show e.inv (e.hom x) = x
      exact congrArg (fun g : H ⟶ H => g x) e.hom_inv_id
    exact Module.Finite.of_surjective f hf
  · let : ((DerivedCategory.Plus.singleFunctor (ModuleCat.{max v u} A) 0).obj M).IsGE
        0 := inferInstance
    let : ((DerivedCategory.Plus.singleFunctor (ModuleCat.{max v u} A) 0).obj M).IsLE
        0 := inferInstance
    let N := (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max v u} A) i).obj
      ((DerivedCategory.Plus.singleFunctor (ModuleCat.{max v u} A) 0).obj M)
    have hz : Limits.IsZero N := by
      by_cases hlt : i < 0
      · exact DerivedCategory.Plus.isZero_homology_of_isGE _ 0 i hlt
      · have hgt : 0 < i := by omega
        exact DerivedCategory.Plus.isZero_homology_of_isLE _ 0 i hgt
    have hzero : ∀ x : N, x = 0 := fun x => by
      have hh := congrArg (fun f : N ⟶ N => f x) (hz.eq_of_tgt (0 : N ⟶ N) (𝟙 N))
      simpa using hh.symm
    have htop : (⊤ : Submodule A N) = ⊥ := by ext x; simp [hzero x]
    show Module.Finite A N
    exact Module.Finite.of_fg_top (htop.symm ▸ Submodule.fg_bot)

private lemma simple_module_linearEquiv_residueField
    (A : Type u) [CommRing A] [IsLocalRing A]
    (M : Type (max v u)) [AddCommGroup M] [Module A M]
    [IsSimpleModule A M] :
    Nonempty (M ≃ₗ[A] IsLocalRing.ResidueField A) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp
    (show IsSimpleModule A M from inferInstance)
  rw [IsLocalRing.eq_maximalIdeal hI] at e
  exact ⟨e⟩

/-- A finite-length module is Noetherian. -/
private lemma isNoetherian_of_isFiniteLength
    {A : Type u} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
    (hM : IsFiniteLength A M) : IsNoetherian A M :=
  (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).1

private lemma finiteLength_annihilated_by_maximalIdeal_power
    (A : Type u) [CommRing A] [IsLocalRing A]
    (M : Type (max v u)) [AddCommGroup M] [Module A M]
    (hM : IsFiniteLength A M) :
    ∃ n : ℕ, IsLocalRing.maximalIdeal A ^ n ≤ Module.annihilator A M := by
  let : IsNoetherian A M := isNoetherian_of_isFiniteLength hM
  let : IsArtinian A M :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).2
  let f : ℕ →o (Submodule A M)ᵒᵈ :=
    ⟨fun n => OrderDual.toDual ((IsLocalRing.maximalIdeal A ^ n) • ⊤),
      fun n k hnk => Submodule.smul_mono_left (Ideal.pow_le_pow_right hnk)⟩
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes f
  let N : Submodule A M := (IsLocalRing.maximalIdeal A ^ n) • ⊤
  have hNfg : N.FG := IsNoetherian.noetherian N
  have hNle : N ≤ IsLocalRing.maximalIdeal A • N := by
    have hs := hn (n + 1) (Nat.le_succ n)
    change (IsLocalRing.maximalIdeal A ^ n) • (⊤ : Submodule A M) =
      (IsLocalRing.maximalIdeal A ^ (n + 1)) • ⊤ at hs
    simpa [N, pow_succ, smul_smul, mul_comm] using hs.le
  have hNbot : N = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
      (IsLocalRing.maximalIdeal A) N hNfg hNle (by
        rw [IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal A) bot_ne_top])
  refine ⟨n, ?_⟩
  rw [← Submodule.annihilator_top]
  exact Submodule.le_annihilator_iff.mpr hNbot

private lemma finiteLength_supportDim_le_zero
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (M : Type (max v u)) [AddCommGroup M] [Module A M]
    (hM : IsFiniteLength A M) : Module.supportDim A M ≤ 0 := by
  let : IsNoetherian A M := isNoetherian_of_isFiniteLength hM
  obtain ⟨n, hn⟩ := finiteLength_annihilated_by_maximalIdeal_power A M hM
  have hsupp : Module.support A M ⊆ {IsLocalRing.closedPoint A} := by
    intro p hp
    have hpann : Module.annihilator A M ≤ p.asIdeal :=
      (Module.mem_support_iff_of_finite (R := A) (M := M)).mp hp
    have hpow : IsLocalRing.maximalIdeal A ^ n ≤ p.asIdeal := hn.trans hpann
    have hmle : IsLocalRing.maximalIdeal A ≤ p.asIdeal :=
      Ideal.IsPrime.le_of_pow_le hpow
    have hpeq : p.asIdeal = IsLocalRing.maximalIdeal A :=
      le_antisymm (IsLocalRing.le_maximalIdeal p.2.ne_top) hmle
    exact Set.mem_singleton_iff.mpr (PrimeSpectrum.ext hpeq)
  by_cases htriv : Subsingleton M
  · rw [Module.supportDim_eq_bot_of_subsingleton]
    exact bot_le
  · let : Nontrivial M := not_subsingleton_iff_nontrivial.mp htriv
    have heq : Module.support A M = {IsLocalRing.closedPoint A} := by
      apply Set.eq_of_subset_of_subset hsupp
      intro p hp
      have hp' : p = IsLocalRing.closedPoint A := Set.mem_singleton_iff.mp hp
      subst p
      exact IsLocalRing.closedPoint_mem_support A M
    rw [Module.supportDim, heq]
    have : Nonempty ({IsLocalRing.closedPoint A} : Set (PrimeSpectrum A)) :=
      ⟨⟨IsLocalRing.closedPoint A, rfl⟩⟩
    exact (Order.krullDim_eq_zero :
      Order.krullDim ({IsLocalRing.closedPoint A} : Set _) = 0).le

private lemma annihilator_le_ext_annihilator
    (A : Type u) [CommRing A]
    (M : Type (max v u)) [AddCommGroup M] [Module A M]
    (K : DerivedCategory (ModuleCat.{max v u} A)) (i : ℤ) :
    Module.annihilator A M ≤
      Module.annihilator A
        (DerivedCategory.Ext
          ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
            (ModuleCat.of A M)) K i) := by
  intro a ha
  rw [Module.mem_annihilator] at ha ⊢
  intro x
  let S := (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
    (ModuleCat.of A M)
  have hzero : LinearMap.lsmul A M a = 0 := by
    ext m
    exact ha m
  have hmap : (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map
      (ModuleCat.ofHom (LinearMap.lsmul A M a)) = a • 𝟙 S := by
    have hcat : ModuleCat.ofHom (LinearMap.lsmul A M a) =
        a • 𝟙 (ModuleCat.of A M) := by
      apply ModuleCat.hom_ext
      ext m
      simp [LinearMap.lsmul_apply]
    rw [hcat, Functor.map_smul, CategoryTheory.Functor.map_id]
  show a • (x : S ⟶ K⟦i⟧) = 0
  calc
    a • x = (a • 𝟙 S) ≫ x := by simp
    _ = (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).map
          (ModuleCat.ofHom (LinearMap.lsmul A M a)) ≫ x := by rw [hmap]
    _ = 0 := by rw [hzero]; simp

private lemma ext_support_subset
    (A : Type u) [CommRing A]
    (M : Type (max v u)) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (K : DerivedCategory (ModuleCat.{max v u} A)) (i : ℤ) :
    Module.support A
        (DerivedCategory.Ext
          ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
            (ModuleCat.of A M)) K i) ⊆ Module.support A M := by
  intro p hp
  exact (Module.mem_support_iff_of_finite (R := A) (M := M)).2
    ((annihilator_le_ext_annihilator A M K i).trans
      (Module.annihilator_le_of_mem_support hp))

private lemma finiteLength_of_supportDim_le_zero
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hM : Module.supportDim A M ≤ 0) : IsFiniteLength A M := by
  classical
  by_cases hsub : Subsingleton M
  · exact IsFiniteLength.of_subsingleton
  · let : Nontrivial M := not_subsingleton_iff_nontrivial.mp hsub
    have hdim : Module.supportDim A M = 0 := by
      apply le_antisymm hM
      cases hd : Module.supportDim A M with
      | bot => exact (Module.supportDim_ne_bot_of_nontrivial A M hd).elim
      | coe n => exact WithBot.coe_le_coe.mpr bot_le
    have hsupp : Module.support A M = {IsLocalRing.closedPoint A} := by
      ext q
      rw [support_of_supportDim_eq_zero A M hdim]
      simp only [PrimeSpectrum.mem_zeroLocus, Set.mem_singleton_iff]
      constructor
      · intro h
        apply PrimeSpectrum.ext
        exact le_antisymm (IsLocalRing.le_maximalIdeal q.isPrime.ne_top) h
      · rintro rfl
        exact le_rfl
    exact isFiniteLength_of_support hsupp

/-- Support dimension is monotone along an inclusion of supports. -/
lemma supportDim_le_of_support_subset
    {A : Type u} [CommRing A]
    {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (h : Module.support A M ⊆ Module.support A N) :
    Module.supportDim A M ≤ Module.supportDim A N := by
  show Order.krullDim (Module.support A M) ≤
    Order.krullDim (Module.support A N)
  exact Order.krullDim_le_of_strictMono
    (fun p : Module.support A M => ⟨p.1, h p.2⟩) fun _ _ => id

private lemma finiteLength_ext_of_finiteLength
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (M : Type (max v u)) [AddCommGroup M] [Module A M]
    (K : DerivedCategory (ModuleCat.{max v u} A)) (i : ℤ)
    (hM : IsFiniteLength A M)
    [Module.Finite A
      (DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
          (ModuleCat.of A M)) K i)] :
    IsFiniteLength A
      (DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
          (ModuleCat.of A M)) K i) := by
  let : IsNoetherian A M := isNoetherian_of_isFiniteLength hM
  exact finiteLength_of_supportDim_le_zero
    ((supportDim_le_of_support_subset (ext_support_subset A M K i)).trans
      (finiteLength_supportDim_le_zero A M hM))

private lemma finiteLength_ext_into_dualizing
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (M : Type (max v u)) [AddCommGroup M] [Module A M]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsDualizingComplex K) (i : ℤ)
    (hM : IsFiniteLength A M) :
    IsFiniteLength A
      (DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
          (ModuleCat.of A M)) K i) := by
  let : IsNoetherian A M := isNoetherian_of_isFiniteLength hM
  let X := (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
    (ModuleCat.of A M)
  have hX : ∀ j : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) j).obj X) :=
    finiteCohomology_single A (ModuleCat.of A M)
  have hH := dualizingDerivedHom_finiteCohomology A K hK X hX i
  let e := extIntoOmegaAtLinearEquiv A K i (ModuleCat.of A M)
  have : Module.Finite A
      (DerivedCategory.Ext X K i) :=
    Module.Finite.equiv e.symm
  exact finiteLength_ext_of_finiteLength A M K i hM

private lemma residueField_ext_eq_zero_of_ne_zero
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex K)
    (n : ℤ) (hn : n ≠ 0) :
    ∀ φ : ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
      ((ModuleCat.uliftFunctor.{v} A).obj
        (ModuleCat.of A (IsLocalRing.ResidueField A)))) ⟶ K⟦n⟧,
      φ = 0 := by
  let k := IsLocalRing.ResidueField A
  let f := IsLocalRing.residue A
  let R := ModuleCat.restrictScalars.{max v u} f
  let F := derivedHom.{u, v} f
  let : F.CommShift ℤ := by
    dsimp [F, derivedHom]
    infer_instance
  let M_k := (ModuleCat.uliftFunctor.{v} k).obj (ModuleCat.of k k)
  let S_k := (DerivedCategory.singleFunctor (ModuleCat.{max v u} k) 0).obj M_k
  let S_A := (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
    ((ModuleCat.uliftFunctor.{v} A).obj (ModuleCat.of A k))
  obtain ⟨e⟩ := hK.2
  obtain ⟨adj⟩ := restrictScalarsDerived_adj_derivedHom.{u, v} f
  let α := R.mapDerivedCategorySingleFunctor 0
  intro φ
  let u : R.mapDerivedCategory.obj S_k ⟶ K⟦n⟧ := α.hom.app M_k ≫ φ
  let w : S_k ⟶ F.obj (K⟦n⟧) := (adj.homEquiv S_k (K⟦n⟧)) u
  let β := (F.commShiftIso n).app K
  let γ := (shiftFunctor (DerivedCategory (ModuleCat.{max v u} k)) n).mapIso e
  have hw : w ≫ β.hom ≫ γ.hom = 0 :=
    residueSingle_shift_hom_eq_zero k n hn _
  have hw' : w ≫ β.hom = 0 :=
    (Preadditive.IsIso.comp_right_eq_zero (w ≫ β.hom) γ.hom).mp
      (by simpa only [Category.assoc] using hw)
  have hw'' : w = 0 :=
    (Preadditive.IsIso.comp_right_eq_zero _ _).mp hw'
  have hu : u = 0 := by
    apply (adj.homEquiv S_k (K⟦n⟧)).injective
    simpa [w] using hw''
  have : IsIso (α.hom.app M_k) := (α.app M_k).isIso_hom
  exact (Preadditive.IsIso.comp_left_eq_zero (α.hom.app M_k) φ).mp hu

private lemma simpleModule_ext_eq_zero_of_ne_zero
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (M : Type (max v u)) [AddCommGroup M] [Module A M]
    [IsSimpleModule A M]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex K)
    (n : ℤ) (hn : n ≠ 0) :
    ∀ φ : ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
      (ModuleCat.of A M)) ⟶ K⟦n⟧, φ = 0 := by
  obtain ⟨e⟩ := simple_module_linearEquiv_residueField A M
  let e' : M ≃ₗ[A] ULift.{v} (IsLocalRing.ResidueField A) :=
    e.trans ULift.moduleEquiv.symm
  let eM : ModuleCat.of A M ≅
      (ModuleCat.uliftFunctor.{v} A).obj
        (ModuleCat.of A (IsLocalRing.ResidueField A)) := e'.toModuleIso
  let eD := (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).mapIso eM
  intro φ
  have hz := residueField_ext_eq_zero_of_ne_zero A K hK n hn
    (eD.inv ≫ φ)
  exact (Preadditive.IsIso.comp_left_eq_zero eD.inv φ).mp hz

private lemma finiteLength_ext_eq_zero_of_ne_zero
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (M : Type (max v u)) [AddCommGroup M] [Module A M]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex K)
    (n : ℤ) (hn : n ≠ 0) (hM : IsFiniteLength A M) :
    ∀ φ : ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
      (ModuleCat.of A M)) ⟶ K⟦n⟧, φ = 0 := by
  induction hM with
  | @of_subsingleton M _ _ _ =>
      have hzero : Limits.IsZero (ModuleCat.of A M) :=
        (ModuleCat.isZero_iff_subsingleton).2 inferInstance
      have hzero' : Limits.IsZero
          ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
            (ModuleCat.of A M)) :=
        Functor.map_isZero _ hzero
      intro φ
      exact hzero'.eq_of_src φ 0
  | @of_simple_quotient M _ _ N _ _ ih =>
      let S : ShortComplex (ModuleCat.{max v u} A) :=
        ModuleCat.shortComplexOfCompEqZero N.subtype N.mkQ
          (LinearMap.exact_subtype_mkQ N).linearMap_comp_eq_zero
      have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S
        (LinearMap.exact_subtype_mkQ N) N.subtype_injective N.mkQ_surjective
      let T := hS.singleTriangle
      have hT : T ∈ distTriang (DerivedCategory (ModuleCat.{max v u} A)) :=
        hS.singleTriangle_distinguished
      intro φ
      have hz : T.mor₁ ≫ φ = 0 := ih _
      obtain ⟨ψ, hψ⟩ := T.yoneda_exact₂ hT φ hz
      have hψ0 : ψ = 0 :=
        simpleModule_ext_eq_zero_of_ne_zero A (M ⧸ N) K hK n hn ψ
      rw [hψ0] at hψ
      simpa using hψ

private lemma finiteLength_derivedHom_isHeart
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (M : Type (max v u)) [AddCommGroup M] [Module A M]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex K)
    (hM : IsFiniteLength A M) :
    let X := (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
      (ModuleCat.of A M)
    let Y := (dualizingDerivedHomFunctor A K).obj (.op X)
    Y.IsGE 0 ∧ Y.IsLE 0 := by
  let X := (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
    (ModuleCat.of A M)
  let Y := (dualizingDerivedHomFunctor A K).obj (.op X)
  have hzero (i : ℤ) (hi : i ≠ 0) :
      Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj Y) := by
    let H := (DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj Y
    let e := extIntoOmegaAtLinearEquiv A K i (ModuleCat.of A M)
    have hz : ∀ x : H, x = 0 := by
      intro x
      obtain ⟨y, rfl⟩ := e.surjective x
      rw [finiteLength_ext_eq_zero_of_ne_zero A M K hK i hi hM y]
      exact map_zero e
    exact ModuleCat.isZero_iff_subsingleton.2 ⟨fun x y => (hz x).trans (hz y).symm⟩
  exact ⟨(DerivedCategory.isGE_iff Y 0).2 fun i hi => hzero i (by omega),
    (DerivedCategory.isLE_iff Y 0).2 fun i hi => hzero i (by omega)⟩

private lemma finiteLength_derivedHom_homologyZero
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (M : Type (max v u)) [AddCommGroup M] [Module A M]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex K)
    (hM : IsFiniteLength A M) :
    IsFiniteLength A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) 0).obj
        ((dualizingDerivedHomFunctor A K).obj (.op
          ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
            (ModuleCat.of A M))))) := by
  let e := extIntoOmegaAtLinearEquiv A K 0 (ModuleCat.of A M)
  exact e.isFiniteLength
    (finiteLength_ext_into_dualizing A M K hK.1 0 hM)

private noncomputable def derivedHomFiniteLengthHeartFunctor
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex K) :
    (FiniteLengthModules.{u, v} A)ᵒᵖ ⥤ FiniteLengthModules.{u, v} A where
  obj N := ⟨
    (DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) 0).obj
      ((derivedHomFiniteLengthFunctor A K).obj N),
    finiteLength_derivedHom_homologyZero A N.unop.obj K hK N.unop.property⟩
  map {N N'} f := ⟨
    (DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) 0).map
      ((derivedHomFiniteLengthFunctor A K).map f)⟩
  map_id N := by
    ext
    simp
  map_comp f g := by
    ext
    simp [Functor.map_comp]

private lemma derivedHomFiniteLength_obj_iso_singleHomology
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex K)
    (N : FiniteLengthModules.{u, v} A) :
    Nonempty
      ((derivedHomFiniteLengthFunctor A K).obj (.op N) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj
          ((derivedHomFiniteLengthHeartFunctor A K hK).obj (.op N)).obj) := by
  let Y := (derivedHomFiniteLengthFunctor A K).obj (.op N)
  have h := finiteLength_derivedHom_isHeart A N.obj K hK N.property
  have hGE : Y.IsGE 0 := h.1
  have hLE : Y.IsLE 0 := h.2
  let : Y.IsGE 0 := hGE
  let : Y.IsLE 0 := hLE
  obtain ⟨W, ⟨e⟩⟩ := Y.exists_iso_singleFunctor_obj_of_isGE_of_isLE 0
  let ε := DerivedCategory.singleFunctorCompHomologyFunctorIso
    (ModuleCat.{max v u} A) 0
  exact ⟨e ≪≫ (DerivedCategory.singleFunctor
      (ModuleCat.{max v u} A) 0).mapIso
        (((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) 0).mapIso e ≪≫
          ε.app W).symm)⟩

private lemma bijective_map_of_iso
    {C : Type u'} [Category.{v'} C] {D : Type u} [Category.{v} D]
    (F : C ⥤ D) {Y Y' Z Z' : C} (eY : Y ≅ Y') (eZ : Z ≅ Z')
    (h : Function.Bijective (fun f : Y' ⟶ Z' => F.map f)) :
    Function.Bijective (fun f : Y ⟶ Z => F.map f) := by
  refine ⟨fun f₁ f₂ hf => ?_, fun m => ?_⟩
  · have h' : F.map (eY.inv ≫ f₁ ≫ eZ.hom) =
        F.map (eY.inv ≫ f₂ ≫ eZ.hom) := by
      simp only [Functor.map_comp]
      rw [show F.map f₁ = F.map f₂ from hf]
    have h'' := h.injective h'
    exact (cancel_mono eZ.hom).mp ((cancel_epi eY.inv).mp h'')
  · obtain ⟨f, hf⟩ := h.surjective (F.map eY.inv ≫ m ≫ F.map eZ.hom)
    dsimp only at hf
    refine ⟨eY.hom ≫ f ≫ eZ.inv, ?_⟩
    dsimp only
    rw [Functor.map_comp, Functor.map_comp, hf]
    simp [← Functor.map_comp]

private lemma bijective_homologyFunctor_map_on_heart
    {C : Type u'} [Category.{v'} C] [Abelian C] [HasDerivedCategory.{w'} C]
    (Y Z : DerivedCategory C)
    [Y.IsLE 0] [Y.IsGE 0] [Z.IsLE 0] [Z.IsGE 0] :
    Function.Bijective (fun f : Y ⟶ Z =>
      (DerivedCategory.homologyFunctor C 0).map f) := by
  obtain ⟨Y₀, ⟨eY⟩⟩ := Y.exists_iso_singleFunctor_obj_of_isGE_of_isLE 0
  obtain ⟨Z₀, ⟨eZ⟩⟩ := Z.exists_iso_singleFunctor_obj_of_isGE_of_isLE 0
  refine bijective_map_of_iso _ eY eZ ?_
  have hS : Function.Bijective (fun g : Y₀ ⟶ Z₀ ↦
      (DerivedCategory.singleFunctor C 0).map g) :=
    ⟨fun _ _ h ↦ (DerivedCategory.singleFunctor C 0).map_injective h,
      fun f ↦ (DerivedCategory.singleFunctor C 0).map_surjective f⟩
  refine (Function.Bijective.of_comp_iff _ hS).mp ?_
  have key : ((fun f : (DerivedCategory.singleFunctor C 0).obj Y₀ ⟶
        (DerivedCategory.singleFunctor C 0).obj Z₀ ↦
        (DerivedCategory.homologyFunctor C 0).map f) ∘
      (fun g : Y₀ ⟶ Z₀ ↦ (DerivedCategory.singleFunctor C 0).map g)) =
      fun g : Y₀ ⟶ Z₀ ↦
        (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).hom.app Y₀ ≫
          g ≫ (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).inv.app Z₀ := by
    funext g
    exact (NatIso.naturality_2
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0) g).symm
  rw [key]
  exact (((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app Y₀).symm.homCongr
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app Z₀).symm).bijective

private noncomputable def isoCompSingleFunctorOfIsLEOfIsGE
    {J : Type u} [Category.{v} J]
    {C : Type u'} [Category.{v'} C] [Abelian C] [HasDerivedCategory.{w'} C]
    (B : J ⥤ DerivedCategory C)
    (hLE : ∀ j, (B.obj j).IsLE 0)
    (hGE : ∀ j, (B.obj j).IsGE 0) :
    B ≅ (B ⋙ DerivedCategory.homologyFunctor C 0) ⋙
      DerivedCategory.singleFunctor C 0 := by
  let ε := DerivedCategory.singleFunctorCompHomologyFunctorIso C 0
  have hbij : ∀ (Y Z : DerivedCategory C),
      Y.IsLE 0 → Y.IsGE 0 → Z.IsLE 0 → Z.IsGE 0 →
      Function.Bijective (fun f : Y ⟶ Z =>
        (DerivedCategory.homologyFunctor C 0).map f) := fun Y Z _ _ _ _ =>
    bijective_homologyFunctor_map_on_heart Y Z
  have hLE' : ∀ j, (((B ⋙ DerivedCategory.homologyFunctor C 0) ⋙
      DerivedCategory.singleFunctor C 0).obj j).IsLE 0 := fun j =>
        inferInstanceAs (DerivedCategory.TStructure.t.IsLE
          ((DerivedCategory.singleFunctor C 0).obj
            ((DerivedCategory.homologyFunctor C 0).obj (B.obj j))) 0)
  have hGE' : ∀ j, (((B ⋙ DerivedCategory.homologyFunctor C 0) ⋙
      DerivedCategory.singleFunctor C 0).obj j).IsGE 0 := fun j =>
        inferInstanceAs (DerivedCategory.TStructure.t.IsGE
          ((DerivedCategory.singleFunctor C 0).obj
            ((DerivedCategory.homologyFunctor C 0).obj (B.obj j))) 0)
  choose f hf using fun j =>
    (hbij (B.obj j) (((B ⋙ DerivedCategory.homologyFunctor C 0) ⋙
      DerivedCategory.singleFunctor C 0).obj j)
      (hLE j) (hGE j) (hLE' j) (hGE' j)).surjective
        (ε.inv.app ((DerivedCategory.homologyFunctor C 0).obj (B.obj j)))
  choose g hg using fun j =>
    (hbij (((B ⋙ DerivedCategory.homologyFunctor C 0) ⋙
      DerivedCategory.singleFunctor C 0).obj j) (B.obj j)
      (hLE' j) (hGE' j) (hLE j) (hGE j)).surjective
        (ε.hom.app ((DerivedCategory.homologyFunctor C 0).obj (B.obj j)))
  dsimp only at hf hg
  have hfg : ∀ j, f j ≫ g j = 𝟙 (B.obj j) := fun j => by
    refine (hbij (B.obj j) (B.obj j) (hLE j) (hGE j) (hLE j) (hGE j)).injective ?_
    rw [Functor.map_comp, hf, hg]
    simp
  have hgf : ∀ j, g j ≫ f j =
      𝟙 (((B ⋙ DerivedCategory.homologyFunctor C 0) ⋙
        DerivedCategory.singleFunctor C 0).obj j) := fun j => by
    refine (hbij _ _ (hLE' j) (hGE' j) (hLE' j) (hGE' j)).injective ?_
    rw [Functor.map_comp, hf, hg]
    simp
  have hnat : ∀ {j k : J} (u : j ⟶ k),
      B.map u ≫ f k = f j ≫
        ((B ⋙ DerivedCategory.homologyFunctor C 0) ⋙
          DerivedCategory.singleFunctor C 0).map u :=
    fun {j k} u => by
      refine (hbij (B.obj j) _ (hLE j) (hGE j) (hLE' k) (hGE' k)).injective ?_
      rw [Functor.map_comp, Functor.map_comp, hf, hf]
      exact ε.inv.naturality ((DerivedCategory.homologyFunctor C 0).map (B.map u))
  exact NatIso.ofComponents (fun j => ⟨f j, g j, hfg j, hgf j⟩) hnat

private noncomputable def derivedHomFiniteLengthIsoSingleHomology
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex K) :
    derivedHomFiniteLengthFunctor A K ≅
      (derivedHomFiniteLengthHeartFunctor A K hK ⋙
        ObjectProperty.ι
          (P := fun M : ModuleCat.{max v u} A => IsFiniteLength A M)) ⋙
        DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0 :=
  isoCompSingleFunctorOfIsLEOfIsGE _
    (fun N => (finiteLength_derivedHom_isHeart A N.unop.obj K hK N.unop.property).2)
    (fun N => (finiteLength_derivedHom_isHeart A N.unop.obj K hK N.unop.property).1)

private noncomputable def finiteLengthSingleToCoherent
    (A : Type u) [CommRing A] [IsNoetherianRing A] :
    FiniteLengthModules.{u, v} A ⥤
      CoherentDerivedCategory A where
  obj M := ⟨
    (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj M.obj,
    fun i => by
      let : IsNoetherian A M.obj := isNoetherian_of_isFiniteLength M.property
      exact finiteCohomology_single A M.obj i⟩
  map {M N} f := ⟨(DerivedCategory.singleFunctor
    (ModuleCat.{max v u} A) 0).map f.hom⟩
  map_id M := by
    ext
    simp
  map_comp f g := by
    ext
    simp [Functor.map_comp]

private noncomputable def finiteLengthSingleToCoherent_fullyFaithful
    (A : Type u) [CommRing A] [IsNoetherianRing A] :
    (finiteLengthSingleToCoherent.{u, v} A).FullyFaithful where
  preimage {X Y} f := ⟨(DerivedCategory.singleFunctor
    (ModuleCat.{max v u} A) 0).preimage f.hom⟩
  map_preimage f := by
    ext
    simp [finiteLengthSingleToCoherent]
  preimage_map f := by
    ext
    simp [finiteLengthSingleToCoherent]

private lemma derivedHomFiniteLengthFunctor_eq_coherentRestriction
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex K) :
    derivedHomFiniteLengthFunctor A K =
      (finiteLengthSingleToCoherent A).op ⋙
        coherentDualizingDerivedHomFunctor A K hK.1 ⋙
          ObjectProperty.ι
            (P := fun X : DerivedCategory (ModuleCat.{max v u} A) =>
              ∀ i : ℤ, Module.Finite A
                ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj X)) := by
  rfl

private noncomputable def derivedHomFiniteLengthHeartFunctor_fullyFaithful
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex K) :
    (derivedHomFiniteLengthHeartFunctor A K hK).FullyFaithful := by
  let G := coherentDualizingDerivedHomFunctor.{u, v} A K hK.1
  let P : ObjectProperty (DerivedCategory (ModuleCat.{max v u} A)) :=
    fun X => ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj X)
  let I := ObjectProperty.ι P
  haveI : G.IsEquivalence :=
    coherentDualizingDerivedHom_isEquivalence A K hK.1
  have hR : (derivedHomFiniteLengthFunctor A K).FullyFaithful := by
    rw [derivedHomFiniteLengthFunctor_eq_coherentRestriction A K hK]
    exact ((finiteLengthSingleToCoherent_fullyFaithful A).op.comp
      (Functor.FullyFaithful.ofFullyFaithful G)).comp
        (Functor.FullyFaithful.ofFullyFaithful I)
  let J := ObjectProperty.ι
    (P := fun M : ModuleCat.{max v u} A => IsFiniteLength A M)
  let S := DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0
  have hComp : ((derivedHomFiniteLengthHeartFunctor A K hK ⋙ J) ⋙ S).FullyFaithful :=
    hR.ofIso (derivedHomFiniteLengthIsoSingleHomology A K hK)
  exact Functor.FullyFaithful.ofCompFaithful
    (F := derivedHomFiniteLengthHeartFunctor A K hK) (G := J ⋙ S) hComp

private lemma derivedHomFiniteLengthHeartFunctor_essSurj
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex K) :
    (derivedHomFiniteLengthHeartFunctor A K hK).EssSurj := by
  let H := derivedHomFiniteLengthHeartFunctor A K hK
  let S := finiteLengthSingleToCoherent.{u, v} A
  let G := coherentDualizingDerivedHomFunctor.{u, v} A K hK.1
  let P : ObjectProperty (DerivedCategory (ModuleCat.{max v u} A)) :=
    fun X => ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) i).obj X)
  let I := ObjectProperty.ι P
  let h₀ := DerivedCategory.homologyFunctor (ModuleCat.{max v u} A) 0
  let σ := DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0
  let ε := DerivedCategory.singleFunctorCompHomologyFunctorIso
    (ModuleCat.{max v u} A) 0
  let β := coherentDerivedBidualityIso A K hK.1
  constructor
  intro N
  let M := H.obj (.op N)
  let X := S.obj N
  let Y := G.obj (.op X)
  let eD := (derivedHomFiniteLengthIsoSingleHomology A K hK).app (.op N)
  let eC : Y ≅ S.obj M := P.isoMk eD
  let eC' : G.obj (.op (S.obj M)) ≅ X :=
    G.mapIso eC.op ≪≫ (β.app X).symm
  let eH := h₀.mapIso (I.mapIso eC') ≪≫ ε.app N.obj
  exact ⟨.op M, ⟨(ObjectProperty.isoMk
    (P := fun L : ModuleCat.{max v u} A => IsFiniteLength A L) eH)⟩⟩

private lemma derivedHomFiniteLengthHeartFunctor_isEquivalence
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex K) :
    (derivedHomFiniteLengthHeartFunctor A K hK).IsEquivalence := by
  let hFF := derivedHomFiniteLengthHeartFunctor_fullyFaithful A K hK
  exact ⟨hFF.faithful, hFF.full,
    derivedHomFiniteLengthHeartFunctor_essSurj A K hK⟩

private lemma maximalIdeal_power_quotient_isLocalRing
    (A : Type u) [CommRing A] [IsLocalRing A] (n : ℕ) :
    IsLocalRing (A ⧸ IsLocalRing.maximalIdeal A ^ (n + 1)) := by
  let I : Ideal A := IsLocalRing.maximalIdeal A ^ (n + 1)
  have hI : I ≠ ⊤ := ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal A).ne_top
    (Ideal.pow_le_self n.succ_ne_zero)
  let : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective

private lemma maximalIdeal_power_quotient_isArtinianRing
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (n : ℕ) : IsArtinianRing (A ⧸ IsLocalRing.maximalIdeal A ^ (n + 1)) := by
  let I : Ideal A := IsLocalRing.maximalIdeal A ^ (n + 1)
  have : IsLocalRing (A ⧸ I) := maximalIdeal_power_quotient_isLocalRing A n
  have hnil : IsNilpotent (IsLocalRing.maximalIdeal (A ⧸ I)) := by
    use n + 1
    rw [← IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective,
      ← Ideal.map_pow]
    show Ideal.map (Ideal.Quotient.mk I) (IsLocalRing.maximalIdeal A ^ (n + 1)) = ⊥
    rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  exact (isArtinianRing_iff_isNilpotent_maximalIdeal (A ⧸ I)).mpr hnil

private lemma finiteLength_over_artinian_quotient
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (M : Type (max v u)) [AddCommGroup M] [Module A M]
    (hM : IsFiniteLength A M) (hI : I ≤ Module.annihilator A M)
    (hAI : IsArtinianRing (A ⧸ I)) :
    let hT : Module.IsTorsionBySet A M
      ((I : Ideal A) : Set A) := by
      intro x a
      exact Module.mem_annihilator.mp (hI a.2) x
    letI := hT.module
    IsFiniteLength (A ⧸ I) M := by
  let hT : Module.IsTorsionBySet A M
    ((I : Ideal A) : Set A) := by
    intro x a
    exact Module.mem_annihilator.mp (hI a.2) x
  let := hT.module
  let : IsScalarTower A (A ⧸ I) M := hT.isScalarTower
  let : IsNoetherian A M := isNoetherian_of_isFiniteLength hM
  exact ((IsArtinianRing.tfae (A ⧸ I) M).out 1 4).mp
    (Module.Finite.of_restrictScalars_finite A (A ⧸ I) M)

end Dualizing

end

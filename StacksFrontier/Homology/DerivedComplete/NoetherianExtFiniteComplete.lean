module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Homology.DerivedComplete.AdicKoszulCompletion
public import StacksFrontier.Homology.DerivedComplete.AdicKoszulPowerDefs
public import StacksFrontier.Homology.DerivedComplete.AdicWeakSerreClass
public import StacksFrontier.Homology.DerivedComplete.CompleteAdic
public import StacksFrontier.Homology.DerivedComplete.DerivedHomCompletionTorSequence
public import StacksFrontier.Homology.DerivedComplete.NakayamaModule
public import StacksFrontier.Homology.DerivedComplete.NoetherianCohomologyAdicCompletion
public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.RingTheory.AdicCompletion.Finiteness
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.AdicCompletion.QuotPow

section

/-!
# Finite modules from derived completeness

Let `I` be an ideal in a Noetherian ring `A`. If an `A`-module `M` is derived complete
with respect to `I` and its reduction `M / IM` is finite over `A / I`, then `M` is its
`I`-adic completion and is finite over the completed ring `Â`.

## Main results

* `FiniteDerivedComplete.exists_finite_adicCompletionModule_of_isDerivedCompleteModule`:
  the finite module structure over `AdicCompletion I A` together with the identification of
  `M` with its adic completion, Stacks 09BA.

## Implementation notes

The equality `M = lim M / IⁿM` is expressed by an equivalence whose underlying map is the
canonical map `AdicCompletion.of I M`. The module structure over the completed ring is included
in the conclusion, together with its compatibility with the original `A`-module structure.

The separatedness of `M` is the only step that leaves the module universe: it is proved for a
module in the same universe as the ring and then transported along the exact universe
enlargement `AdicKoszul.moduleUniverseLift`, which both preserves and reflects derived
completeness.

## References

* [The Stacks Project, Tag 09BA](https://stacks.math.columbia.edu/tag/09BA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace FiniteDerivedComplete

attribute [local instance] HasDerivedCategory.standard

/-- Restriction of scalars along a ring homomorphism preserves finite limits. -/
local instance (priority := 3000) {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) : PreservesFiniteLimits (ModuleCat.restrictScalars.{v} f) := by
  have h := ((Functor.exact_tfae (ModuleCat.restrictScalars.{v} f)).out 2 4).mp
    (ModuleCat.restrictScalars_map_exact f)
  exact h.1

/-- Restriction of scalars along a ring homomorphism preserves finite colimits. -/
local instance (priority := 3000) {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) : PreservesFiniteColimits (ModuleCat.restrictScalars.{v} f) := by
  have h := ((Functor.exact_tfae (ModuleCat.restrictScalars.{v} f)).out 2 4).mp
    (ModuleCat.restrictScalars_map_exact f)
  exact h.2

/-! ### Finiteness over the completed ring -/

/-- Finiteness of the reduction modulo `I` is unchanged by passing to the `I`-adic completion. -/
private theorem finite_quotient_adicCompletion_iff {A : Type u} [CommRing A] {I : Ideal A}
    (hI : I.FG) (M : Type v) [AddCommGroup M] [Module A M] :
    Module.Finite A (AdicCompletion I M ⧸ (I • ⊤ : Submodule A (AdicCompletion I M))) ↔
      Module.Finite A (M ⧸ (I • ⊤ : Submodule A M)) := by
  have e := AdicCompletion.quotPowSMulTopEquiv hI M 1
  rw [pow_one] at e
  exact ⟨fun h => h.equiv e, fun h => h.equiv e.symm⟩

/-- If the reduction of an `A`-module `M` modulo `I` is finite over `A`, then the reduction of
`M` modulo the extended ideal `I B` is finite over `B`, for any `A`-algebra `B` acting on `M`. -/
private theorem finite_quotient_map_smul_top {A : Type u} {B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] {M : Type*} [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    (I : Ideal A) (h : Module.Finite A (M ⧸ (I • ⊤ : Submodule A M))) :
    Module.Finite B (M ⧸ (I.map (algebraMap A B) • ⊤ : Submodule B M)) := by
  have h₁ : Module.Finite A
      (M ⧸ ((I.map (algebraMap A B) • ⊤ : Submodule B M).restrictScalars A)) := by
    rw [Submodule.restrictScalars_map_smul_eq, Submodule.restrictScalars_top]
    exact h
  have := h₁.equiv (Submodule.Quotient.restrictScalarsEquiv A _)
  exact Module.Finite.of_restrictScalars_finite A B _

/-- If `M / IM` is finite over `A`, then the completion of `M` is finite over the completion
of `A`. -/
private theorem finite_completion {A : Type u} [CommRing A] {I : Ideal A}
    (hI : I.FG) (M : Type v) [AddCommGroup M] [Module A M]
    (hfin : Module.Finite A (M ⧸ (I • ⊤ : Submodule A M))) :
    Module.Finite (AdicCompletion I A) (AdicCompletion I M) := by
  let B := AdicCompletion I A
  let J := I.map (algebraMap A B)
  have : IsPrecomplete J B := (AdicCompletion.isAdicComplete_self I hI).toIsPrecomplete
  apply Module.Finite.of_iInf_pow_smul_top_eq_bot_of_finite_quotient_smul_top J
    (IsHausdorff.map_algebraMap_iff.mpr (AdicCompletion.instIsHausdorff I M)).iInf_pow_smul
  have := finite_quotient_map_smul_top (B := B) I
    ((finite_quotient_adicCompletion_iff hI M).mpr hfin)
  exact Module.Finite.of_restrictScalars_finite B (B ⧸ J) _

/-! ### Separatedness -/

/-- Separatedness transports along a linear equivalence. -/
private theorem hausdorff_of_linearEquiv {A : Type u} [CommRing A] (I : Ideal A)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N] [IsHausdorff I N]
    (e : M ≃ₗ[A] N) : IsHausdorff I M := by
  rw [← AdicCompletion.of_injective_iff]
  intro x y hxy
  apply e.injective
  apply (AdicCompletion.of_injective I N)
  simpa only [AdicCompletion.map_of, LinearEquiv.coe_coe] using
    congrArg (AdicCompletion.map I e.toLinearMap) hxy

/-- A quotient of an adically complete module with finite reduction, by a submodule that is
precomplete, is separated. -/
private theorem hausdorff_of_complete_cover {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) {N : Type v} [AddCommGroup N] [Module A N] [IsAdicComplete I N]
    {M : Type w} [AddCommGroup M] [Module A M] (q : N →ₗ[A] M)
    (hq : Function.Surjective q) [IsPrecomplete I q.ker]
    (hfin : Module.Finite A (N ⧸ (I • ⊤ : Submodule A N))) : IsHausdorff I M := by
  let B := AdicCompletion I A
  let J := I.map (algebraMap A B)
  let e := AdicCompletion.ofLinearEquiv I N
  let f : AdicCompletion I N →ₗ[A] M := q ∘ₗ e.symm.toLinearMap
  have hf : Function.Surjective f := hq.comp e.symm.surjective
  let K : Submodule B (AdicCompletion I N) := (AdicCompletion.map I q.ker.subtype).range
  have heq : K.restrictScalars A = f.ker := by
    ext x
    refine ⟨?_, fun hx => ⟨AdicCompletion.of I q.ker ⟨e.symm x, hx⟩, ?_⟩⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨z, rfl⟩ := AdicCompletion.of_surjective I q.ker y
      show q (e.symm (AdicCompletion.map I q.ker.subtype (AdicCompletion.of I q.ker z))) = 0
      simp [AdicCompletion.map_of, e]
    · rw [AdicCompletion.map_of]
      exact e.apply_symm_apply x
  let E : M ≃ₗ[A] (AdicCompletion I N ⧸ K) :=
    (LinearMap.quotKerEquivOfSurjective f hf).symm |>.trans
      ((Submodule.quotEquivOfEq _ _ heq.symm).trans (Submodule.Quotient.restrictScalarsEquiv A K))
  have : Module.Finite B (AdicCompletion I N) := finite_completion I.fg_of_isNoetherianRing N hfin
  have : IsAdicComplete J B := AdicCompletion.isAdicComplete_self I I.fg_of_isNoetherianRing
  have : IsHausdorff J (AdicCompletion I N ⧸ K) :=
    IsHausdorff.of_le_jacobson J _ (IsAdicComplete.le_jacobson_bot J)
  have : IsHausdorff I (AdicCompletion I N ⧸ K) := IsHausdorff.map_algebraMap_iff.mp ‹_›
  exact hausdorff_of_linearEquiv I E

set_option backward.isDefEq.respectTransparency false in
/-- Finiteness of the reduction transports to the universe enlargement. -/
private theorem finite_quotient_ulift {A : Type u} [CommRing A] (I : Ideal A)
    {M : Type v} [AddCommGroup M] [Module A M]
    (hfin : Module.Finite A (M ⧸ (I • ⊤ : Submodule A M))) :
    Module.Finite (ULift.{v} A)
      (ULift.{u} M ⧸ (I.comap (ULift.ringEquiv : ULift.{v} A ≃+* A).toRingHom •
        ⊤ : Submodule (ULift.{v} A) (ULift.{u} M))) := by
  let R := ULift.{v} A
  let : Algebra A R := (ULift.ringEquiv.symm : A ≃+* R).toRingHom.toAlgebra
  let hTower : IsScalarTower A R (ULift.{u} M) := ⟨fun r a m => by
    apply ULift.ext
    exact mul_smul r a.down m.down⟩
  have he : (I • (⊤ : Submodule A (ULift.{u} M))).map
      (ULift.moduleEquiv : ULift.{u} M ≃ₗ[A] M).toLinearMap = I • ⊤ := by
    rw [Submodule.map_smul'', Submodule.map_top]
    simp
  have h₀ : Module.Finite A (ULift.{u} M ⧸ (I • ⊤ : Submodule A (ULift.{u} M))) :=
    hfin.equiv (Submodule.Quotient.equiv _ _ ULift.moduleEquiv he).symm
  have hj : I.comap (ULift.ringEquiv : R ≃+* A).toRingHom =
      I.map (algebraMap A R) :=
    (Ideal.map_comap_of_equiv (I := I) (ULift.ringEquiv.symm : A ≃+* R)).symm
  rw [hj]
  let := hTower
  exact finite_quotient_map_smul_top I h₀

/-! ### A complete cover of a derived complete module -/

/-- The derived Nakayama lemma: a map between derived complete modules that is surjective
modulo `I` is surjective. -/
private theorem surjective_of_derivedComplete_of_surjective_mod
    {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG)
    (N M : ModuleCat.{v} A) (q : N →ₗ[A] M)
    (hN : IsDerivedCompleteModule I N)
    (hM : IsDerivedCompleteModule I M)
    (hq : Function.Surjective ((I • (⊤ : Submodule A M)).mkQ ∘ₗ q)) :
    Function.Surjective q := by
  let C : ObjectProperty (ModuleCat.{v} A) := fun X => IsDerivedCompleteModule I X
  have : C.IsWeakSerreClass :=
    (AdicWeakSerre.derivedCompleteModules_isWeakSerreClass_and_homology_iff A I).1
  have hQ : C (ModuleCat.of A (M ⧸ q.range)) :=
    C.prop_of_iso (ModuleCat.cokernelIsoRangeQuotient (ModuleCat.ofHom q))
      (C.prop_cokernel (ModuleCat.ofHom q) hN hM)
  have htop : I • (⊤ : Submodule A (M ⧸ q.range)) = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨m, rfl⟩ := q.range.mkQ_surjective y
    obtain ⟨n, hn⟩ := hq ((I • (⊤ : Submodule A M)).mkQ m)
    change (I • (⊤ : Submodule A M)).mkQ (q n) = _ at hn
    have hd : m - q n ∈ I • (⊤ : Submodule A M) := by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      show (I • (⊤ : Submodule A M)).mkQ (m - q n) = 0
      rw [map_sub, hn, sub_self]
    have hm : q.range.mkQ (m - q n) ∈
        (I • (⊤ : Submodule A M)).map q.range.mkQ := ⟨m - q n, hd, rfl⟩
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at hm
    have hzero : q.range.mkQ (q n) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨n, rfl⟩
    simpa only [map_sub, hzero, sub_zero] using hm
  have : Subsingleton ((M ⧸ q.range) ⧸ (I • (⊤ : Submodule A (M ⧸ q.range)))) :=
    Submodule.Quotient.subsingleton_iff.mpr htop
  have : Subsingleton (M ⧸ q.range) :=
    subsingleton_of_isDerivedCompleteModule_of_quotient_smul A I
      (ModuleCat.of A (M ⧸ q.range)) hI hQ this
  exact LinearMap.range_eq_top.mp (Submodule.Quotient.subsingleton_iff.mp this)

/-- The homology of a finite module placed in degree zero is finite in every degree. -/
theorem finite_homology_singleFunctor_zero {A : Type u} [CommRing A] (F : ModuleCat.{u} A)
    [Module.Finite A F] (k : ℤ) : Module.Finite A ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} A) k).obj ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj F)) := by
  by_cases hk : k = 0
  · subst hk
    have : Module.Finite A ((𝟭 (ModuleCat.{u} A)).obj F) := ‹Module.Finite A F›
    exact Module.Finite.equiv
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) 0).app
        F).toLinearEquiv.symm
  · have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) k).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj F)) := by
      rcases lt_or_gt_of_ne hk with hk | hk
      · exact DerivedCategory.isZero_of_isGE _ 0 k hk
      · exact DerivedCategory.isZero_of_isLE _ 0 k hk
    have := ModuleCat.isZero_iff_subsingleton.mp hz
    infer_instance

/-- A derived complete module with finite reduction is covered by the completion of a finite
free module. -/
private theorem exists_complete_cover (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : ModuleCat.{u} A)
    (hM : IsDerivedCompleteModule I M)
    (hfin : Module.Finite A (M ⧸ (I • ⊤ : Submodule A M))) :
    ∃ (N : ModuleCat.{u} A) (q : N →ₗ[A] M),
      IsAdicComplete I N ∧ Module.Finite A (N ⧸ (I • ⊤ : Submodule A N)) ∧
        Function.Surjective q := by
  obtain ⟨n, g, hg⟩ :=
    Stacks.AdicCompletion.SeparatedFiniteness.exists_surjective_mkQ_comp
      (I • (⊤ : Submodule A M))
  let F := ModuleCat.of A (Fin n → A)
  let s := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
  let ε := DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) 0
  let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
    fun K => IsDerivedComplete I K
  obtain ⟨L, ⟨adj⟩, -, -, -⟩ := AdicCompletionTor.derivedCompletion_homology_shortExact A I
    (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A)
  have : Module.Finite A F := inferInstanceAs (Module.Finite A (Fin n → A))
  obtain ⟨c⟩ := AdicCompletionCohomology.derivedCompletion_homology_iso_adicCompletion A I
    (s.obj F) (finite_homology_singleFunctor_zero F) L adj 0
  let N := ModuleCat.of A (AdicCompletion I F)
  let c' : H.obj ((L ⋙ P.ι).obj (s.obj F)) ≅ N := c ≪≫
    ((AdicCompletion.congr I (ε.app F).toLinearEquiv).restrictScalars A).toModuleIso
  let qD := (adj.homEquiv (s.obj F) ⟨s.obj M, hM⟩).symm (s.map (ModuleCat.ofHom g))
  let q : N →ₗ[A] M := (c'.inv ≫ H.map qD.hom ≫ (ε.app M).hom).hom
  let j : F →ₗ[A] N := ((ε.app F).inv ≫ H.map (adj.unit.app (s.obj F)) ≫ c'.hom).hom
  have hjq : q ∘ₗ j = g := by
    have h := (adj.homEquiv (s.obj F) ⟨s.obj M, hM⟩).apply_symm_apply
      (s.map (ModuleCat.ofHom g))
    rw [adj.homEquiv_unit] at h
    change adj.unit.app (s.obj F) ≫ qD.hom = s.map (ModuleCat.ofHom g) at h
    have hn : H.map (s.map (ModuleCat.ofHom g)) ≫ (ε.app M).hom =
        (ε.app F).hom ≫ ModuleCat.ofHom g := ε.hom.naturality (ModuleCat.ofHom g)
    have hcat : (ε.app F).inv ≫ H.map (adj.unit.app (s.obj F)) ≫
        H.map qD.hom ≫ (ε.app M).hom = ModuleCat.ofHom g := by
      rw [← Functor.map_comp_assoc, h, hn, Iso.inv_hom_id_assoc]
    show ((ε.app F).inv ≫ H.map (adj.unit.app (s.obj F)) ≫ c'.hom ≫
      c'.inv ≫ H.map qD.hom ≫ (ε.app M).hom).hom = g
    simpa only [Iso.hom_inv_id_assoc, ModuleCat.hom_ofHom] using congrArg ModuleCat.Hom.hom hcat
  have hNc : IsAdicComplete I N := AdicCompletion.isAdicComplete I.fg_of_isNoetherianRing
  have hNd : IsDerivedCompleteModule I N :=
    (isAdicComplete_iff_isDerivedCompleteModule_and_iInf_pow_smul_top_eq_bot
      A I I.fg_of_isNoetherianRing (AdicCompletion I F)).mp hNc |>.1
  refine ⟨N, q, hNc, ?_, surjective_of_derivedComplete_of_surjective_mod I
    I.fg_of_isNoetherianRing N M q hNd hM ?_⟩
  · exact (finite_quotient_adicCompletion_iff I.fg_of_isNoetherianRing F).mpr inferInstance
  · intro y
    obtain ⟨x, hx⟩ := hg y
    exact ⟨j x, by simpa [← hjq] using hx⟩

/-- Separatedness of a derived complete module with finite reduction, in the same universe as
the ring. -/
private theorem hausdorff_of_derivedComplete_finite_quotient (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) (M : ModuleCat.{u} A)
    (hM : IsDerivedCompleteModule I M)
    (hfin : Module.Finite A (M ⧸ (I • ⊤ : Submodule A M))) : IsHausdorff I M := by
  obtain ⟨N, q, hN, hfinN, hq⟩ := exists_complete_cover A I M hM hfin
  have hNd := (isAdicComplete_iff_isDerivedCompleteModule_and_iInf_pow_smul_top_eq_bot
    A I I.fg_of_isNoetherianRing (N : Type u)).mp hN |>.1
  let C : ObjectProperty (ModuleCat.{u} A) := fun X => IsDerivedCompleteModule I X
  have : C.IsWeakSerreClass :=
    (AdicWeakSerre.derivedCompleteModules_isWeakSerreClass_and_homology_iff A I).1
  have hK : C (ModuleCat.of A q.ker) := C.prop_of_iso
    (ModuleCat.kernelIsoKer (ModuleCat.ofHom q)) (C.prop_kernel (ModuleCat.ofHom q) hNd hM)
  have : IsPrecomplete I q.ker := AdicCompletion.of_surjective_iff.mp
    ((isDerivedCompleteModule_of_isAdicComplete_and_adicCompletion_surjective A I q.ker).2
      I.fg_of_isNoetherianRing hK)
  exact hausdorff_of_complete_cover I q hq hfinN

/-- Derived completeness of a module is preserved by the exact universe enlargement. -/
private theorem derivedComplete_ulift {A : Type u} [CommRing A] (I : Ideal A)
    (M : ModuleCat.{v} A) (hM : IsDerivedCompleteModule I M) :
    IsDerivedCompleteModule
      (I.comap (ULift.ringEquiv : ULift.{v} A ≃+* A).toRingHom)
      ((AdicKoszul.moduleUniverseLift.{u, v} A).obj M) := by
  let e := ((AdicKoszul.moduleUniverseLift.{u, v} A).mapDerivedCategorySingleFunctor 0).app M
  refine DerivedCompleteRecurrence.isDerivedComplete_of_iso e fun f hf => ?_
  rw [isDerivedCompleteAt_iff_exists_isDerivedLimit_isZero]
  refine (KoszulCompletion.derivedUniverseLift_scalarTower_zero_iff f.down
    ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M)).mpr ?_
  rw [← isDerivedCompleteAt_iff_exists_isDerivedLimit_isZero]
  exact hM f.down hf

/-- Separatedness of a derived complete module with finite reduction, in an arbitrary module
universe. -/
private theorem separated_of_derivedComplete_finite_quotient (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) (M : ModuleCat.{v} A)
    (hM : IsDerivedCompleteModule I M)
    (hfin : Module.Finite A (M ⧸ (I • ⊤ : Submodule A M))) : IsHausdorff I M := by
  let R := ULift.{v} A
  let : Algebra A R := (ULift.ringEquiv.symm : A ≃+* R).toRingHom.toAlgebra
  let hTower : IsScalarTower A R (ULift.{u} M) := ⟨fun r a m => by
    apply ULift.ext
    exact mul_smul r a.down m.down⟩
  have : IsNoetherianRing R := isNoetherianRing_of_ringEquiv A (ULift.ringEquiv.symm : A ≃+* R)
  let J := I.comap (ULift.ringEquiv : R ≃+* A).toRingHom
  have h : IsHausdorff J (ULift.{u} M) :=
    hausdorff_of_derivedComplete_finite_quotient R J
      ((AdicKoszul.moduleUniverseLift.{u, v} A).obj M)
      (derivedComplete_ulift I M hM) (finite_quotient_ulift I hfin)
  have hj : J = I.map (algebraMap A R) :=
    (Ideal.map_comap_of_equiv (I := I) (ULift.ringEquiv.symm : A ≃+* R)).symm
  rw [hj] at h
  have : IsHausdorff I (ULift.{u} M) :=
    (@IsHausdorff.map_algebraMap_iff A R _ I (ULift.{u} M) _ _ _ _ _ hTower).mp h
  exact hausdorff_of_linearEquiv I (ULift.moduleEquiv : ULift.{u} M ≃ₗ[A] M).symm

/-! ### Stacks 09BA -/

/-- **Stacks 09BA.** A derived-complete module over a Noetherian ring whose reduction modulo
`I` is finite is canonically its `I`-adic completion and is finite over the completed ring. -/
@[stacks 09BA]
public theorem exists_finite_adicCompletionModule_of_isDerivedCompleteModule
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : ModuleCat.{v} A)
    (hM : IsDerivedCompleteModule I M)
    (hfin : Module.Finite (A ⧸ I) (M ⧸ (I • ⊤ : Submodule A M))) :
    ∃ moduleM : Module (AdicCompletion I A) M,
      letI := moduleM
      IsScalarTower A (AdicCompletion I A) M ∧
        Module.Finite (AdicCompletion I A) M ∧
        ∃ e : M ≃ₗ[AdicCompletion I A] AdicCompletion I M,
          ∀ m, e m = AdicCompletion.of I M m := by
  have hfinA : Module.Finite A (M ⧸ (I • ⊤ : Submodule A M)) := by
    rw [Module.finite_def]
    exact hfin.1.restrictScalars_of_surjective Ideal.Quotient.mk_surjective
  have hsep := separated_of_derivedComplete_finite_quotient A I M hM hfinA
  have hcomplete : IsAdicComplete I M :=
    (isAdicComplete_iff_isDerivedCompleteModule_and_iInf_pow_smul_top_eq_bot
      A I I.fg_of_isNoetherianRing (M : Type v)).mpr ⟨hM, hsep.iInf_pow_smul⟩
  let eA : M ≃ₗ[A] AdicCompletion I M :=
    LinearEquiv.ofBijective (AdicCompletion.of I M)
      (AdicCompletion.of_bijective_iff.mpr hcomplete)
  let moduleM : Module (AdicCompletion I A) M := eA.toAddEquiv.module _
  refine ⟨moduleM, eA.isScalarTower (AdicCompletion I A), ?_, ?_⟩
  · exact (finite_completion I.fg_of_isNoetherianRing M hfinA).equiv
      (eA.toAddEquiv.linearEquiv _).symm
  · exact ⟨eA.toAddEquiv.linearEquiv _, fun _ => rfl⟩

end FiniteDerivedComplete

end

end

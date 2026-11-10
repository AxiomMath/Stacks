module

public import StacksFrontier.FieldTheory.PerfectCoreSeparable
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppBaseChangeTransport
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppPrimeDegree
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppStep3Wild
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The perfect-core reduction for Epp's theorem

This module supplies the remaining reduction from a complete discrete valuation ring with an
arbitrary residue field to the complete perfect-residue case.  The base ring is replaced by a
Cohen ring, or a power-series ring, whose residue field is the perfect core of the original
residue field.  A weak solution over that smaller DVR is then transported back by
`exists_finite_extension_isWeakSolution_of_baseChange`.

The Cohen-ring lifting lemma below is deliberately stated independently of the false form of Tag
09ET: it lifts one prescribed residue homomorphism through successive adic quotients and makes no
claim about all factors of a tensor product.
-/

@[expose] public section

namespace Stacks.EppTheorem

open IsLocalRing IsDiscreteValuationRing
open scoped TensorProduct

universe u v

private theorem exists_formal_lift_square
    {R S : Type*} {E B : Type u} [CommRing R] [CommRing S]
    [CommRing E] [CommRing B] (f : R →+* S) (J : Ideal S)
    (hf : RingHom.FormallySmoothNAdic.{u} f J)
    (q : E →+* B) (hq : Function.Surjective q)
    (hker : (RingHom.ker q) ^ 2 = ⊥)
    (g : R →+* E) (ψ : S →+* B) (hcomm : ψ.comp f = q.comp g)
    (hψ : ∃ k : ℕ, 1 ≤ k ∧ J ^ k ≤ RingHom.ker ψ) :
    ∃ φ : S →+* E, q.comp φ = ψ ∧ φ.comp f = g := by
  let e : (E ⧸ RingHom.ker q) ≃+* B := RingHom.quotientKerEquivOfSurjective hq
  let ψ' := e.symm.toRingHom.comp ψ
  have he (x : E) : e (Ideal.Quotient.mk _ x) = q x :=
    RingHom.quotientKerEquivOfSurjective_apply_mk hq x
  have hcomm' : ψ'.comp f = (Ideal.Quotient.mk _).comp g := by
    ext r
    apply e.injective
    change e (e.symm (ψ (f r))) = e (Ideal.Quotient.mk _ (g r))
    rw [RingEquiv.apply_symm_apply, he]
    exact congrArg (fun h : R →+* B ↦ h r) hcomm
  have hψ' : ∃ k : ℕ, 1 ≤ k ∧ J ^ k ≤ RingHom.ker ψ' := by
    obtain ⟨k, hk, h⟩ := hψ
    refine ⟨k, hk, ?_⟩
    intro x hx
    change e.symm (ψ x) = 0
    rw [show ψ x = 0 from h hx, map_zero]
  obtain ⟨φ, hφ, hφf⟩ := hf E _ hker g ψ' hcomm' hψ'
  refine ⟨φ, ?_, hφf⟩
  ext s
  have h := congrArg e (congrArg (fun h : S →+* E ⧸ RingHom.ker q ↦ h s) hφ)
  change e (Ideal.Quotient.mk _ (φ s)) = e (e.symm (ψ s)) at h
  simpa only [RingEquiv.apply_symm_apply, he, RingHom.comp_apply] using h

private theorem exists_pow_le_ker_of_comp_sq_zero
    {S E B : Type*} [CommRing S] [CommRing E] [CommRing B]
    (J : Ideal S) (q : E →+* B) (φ : S →+* E)
    (hker : (RingHom.ker q) ^ 2 = ⊥)
    (hφ : ∃ k : ℕ, 1 ≤ k ∧ J ^ k ≤ RingHom.ker (q.comp φ)) :
    ∃ k : ℕ, 1 ≤ k ∧ J ^ k ≤ RingHom.ker φ := by
  obtain ⟨k, hk, h⟩ := hφ
  change J ^ k ≤ (RingHom.ker q).comap φ at h
  refine ⟨k * 2, by omega, (Ideal.map_eq_bot_iff_le_ker _).mp ?_⟩
  apply le_antisymm _ bot_le
  rw [pow_mul, Ideal.map_pow]
  calc
    (Ideal.map φ (J ^ k)) ^ 2 ≤ (RingHom.ker q) ^ 2 :=
      Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr h) 2
    _ = ⊥ := hker

private theorem exists_ringHom_of_compatible
    {S A : Type*} [CommRing S] [CommRing A] (I : Ideal A) [IsAdicComplete I A]
    (φ : ∀ n : ℕ, S →+* A ⧸ I ^ n)
    (hφ : ∀ n : ℕ, (Ideal.Quotient.factorPow I (Nat.le_succ n)).comp (φ (n + 1)) = φ n) :
    ∃ g : S →+* A, ∀ n : ℕ, (Ideal.Quotient.mk (I ^ n)).comp g = φ n := by
  have hc : ∀ {m n : ℕ} (h : m ≤ n),
      (Ideal.Quotient.factorPow I h).comp (φ n) = φ m := by
    intro m n h
    induction n, h using Nat.le_induction with
    | base => ext; simp [Ideal.Quotient.factorPow]
    | succ n hmn ih =>
      ext x
      have hh := congrArg (fun f : S →+* A ⧸ I ^ n ↦ f x) (hφ n)
      have hi := congrArg (fun f : S →+* A ⧸ I ^ m ↦ f x) ih
      simp only [RingHom.comp_apply] at hh hi ⊢
      rw [← hi, ← hh]
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (φ (n + 1) x)
      rw [← hy]
      rfl
  let g := (AdicCompletion.ofAlgEquiv I).symm.toRingHom.comp
    (AdicCompletion.liftRingHom I φ hc)
  refine ⟨g, ?_⟩
  intro n
  ext x
  exact (AdicCompletion.mk_ofAlgEquiv_symm I n _).trans
    (AdicCompletion.evalₐ_liftRingHom I φ hc n x)

/-- An adically formally smooth map lifts to a complete ring while preserving its base map. -/
private theorem exists_lift_to_adicComplete
    {R S : Type*} {A : Type u} [CommRing R] [CommRing S] [CommRing A]
    (f : R →+* S) (J : Ideal S) (hf : RingHom.FormallySmoothNAdic.{u} f J)
    (I : Ideal A) [IsAdicComplete I A]
    (g : R →+* A) (ψ : S →+* A ⧸ I ^ 1)
    (hcomm : ψ.comp f = (Ideal.Quotient.mk (I ^ 1)).comp g)
    (hψ : ∃ k : ℕ, 1 ≤ k ∧ J ^ k ≤ RingHom.ker ψ) :
    ∃ φ : S →+* A, φ.comp f = g ∧ (Ideal.Quotient.mk (I ^ 1)).comp φ = ψ := by
  classical
  let P (n : ℕ) (φ : S →+* A ⧸ I ^ n) : Prop :=
    φ.comp f = (Ideal.Quotient.mk (I ^ n)).comp g ∧
      ∃ k : ℕ, 1 ≤ k ∧ J ^ k ≤ RingHom.ker φ
  have hlift (n : ℕ) (hn : 1 ≤ n) (φ : S →+* A ⧸ I ^ n) (hφ : P n φ) :
      ∃ φ' : S →+* A ⧸ I ^ (n + 1), P (n + 1) φ' ∧
        (Ideal.Quotient.factorPow I (Nat.le_succ n)).comp φ' = φ := by
    let q := Ideal.Quotient.factorPow I (Nat.le_succ n)
    have hsq : (RingHom.ker q) ^ 2 = ⊥ := by
      rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow]
      apply (Ideal.map_eq_bot_iff_le_ker _).mpr
      rw [Ideal.mk_ker, ← pow_mul]
      exact Ideal.pow_le_pow_right (by omega)
    have hbase : φ.comp f = q.comp ((Ideal.Quotient.mk (I ^ (n + 1))).comp g) := by
      rw [hφ.1]
      rfl
    obtain ⟨φ', hφ'q, hφ'f⟩ := exists_formal_lift_square f J hf q
      (Ideal.Quotient.factor_surjective _) hsq _ φ hbase hφ.2
    refine ⟨φ', ⟨hφ'f, exists_pow_le_ker_of_comp_sq_zero J q φ' hsq ?_⟩, hφ'q⟩
    rw [hφ'q]
    exact hφ.2
  choose next hnext hnextq using hlift
  let ρ : ∀ n : ℕ, {φ : S →+* A ⧸ I ^ (n + 1) // P (n + 1) φ} :=
    fun n ↦ Nat.rec ⟨ψ, hcomm, hψ⟩
      (fun n ih ↦ ⟨next (n + 1) (by omega) ih.1 ih.2,
        hnext (n + 1) (by omega) ih.1 ih.2⟩) n
  have : Subsingleton (A ⧸ I ^ 0) := Ideal.Quotient.subsingleton_iff.mpr (by simp)
  let φ : ∀ n : ℕ, S →+* A ⧸ I ^ n := fun n ↦
    Nat.casesOn n
      ({ toFun := fun _ ↦ 0, map_one' := Subsingleton.elim _ _,
         map_mul' := fun _ _ ↦ Subsingleton.elim _ _, map_zero' := rfl,
         map_add' := fun _ _ ↦ Subsingleton.elim _ _ } : S →+* A ⧸ I ^ 0)
      (fun n ↦ (ρ n).1)
  obtain ⟨Φ, hΦ⟩ :=
    Stacks.CompleteLocalRing.CohenStructure.exists_ringHom_of_compatible' I φ (by
      intro n x
      cases n with
      | zero => exact Subsingleton.elim _ _
      | succ n =>
        exact congrArg (fun h : S →+* A ⧸ I ^ (n + 1) ↦ h x)
          (hnextq (n + 1) (by omega) (ρ n).1 (ρ n).2))
  refine ⟨Φ, ?_, RingHom.ext fun x ↦ hΦ 1 x⟩
  ext r
  apply AdicCompletion.of_injective I A
  apply AdicCompletion.ext_evalₐ
  intro n
  simp only [AdicCompletion.evalₐ_of]
  have heval := hΦ n (f r)
  cases n with
  | zero => exact Subsingleton.elim _ _
  | succ n =>
    exact heval.trans (congrArg (fun h : R →+* A ⧸ I ^ (n + 1) ↦ h r) (ρ n).2.1)

/-- A formally smooth `f` lifts a residue-field map killing `J` to the complete local ring `A`. -/
private theorem exists_lift_to_residueField
    {R S : Type*} {A : Type u} [CommRing R] [CommRing S] [CommRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (f : R →+* S) (J : Ideal S) (hf : RingHom.FormallySmoothNAdic.{u} f J)
    (g : R →+* A) (ψ : S →+* A ⧸ IsLocalRing.maximalIdeal A)
    (hcomm : ψ.comp f = (Ideal.Quotient.mk _).comp g) (hψ : J ≤ RingHom.ker ψ) :
    ∃ φ : S →+* A, φ.comp f = g ∧ (Ideal.Quotient.mk _).comp φ = ψ := by
  let I := IsLocalRing.maximalIdeal A
  let e := Ideal.quotEquivOfEq (pow_one I)
  obtain ⟨φ, hφf, hφ⟩ := exists_lift_to_adicComplete f J hf I g (e.symm.toRingHom.comp ψ)
    (by
      ext r
      apply e.injective
      change e (e.symm (ψ (f r))) = e (Ideal.Quotient.mk _ (g r))
      rw [RingEquiv.apply_symm_apply, Ideal.quotEquivOfEq_mk]
      exact congrArg (fun h : R →+* A ⧸ I ↦ h r) hcomm)
    ⟨1, le_rfl, by
      rw [pow_one]
      intro x hx
      exact (map_eq_zero_iff e.symm e.symm.injective).mpr (hψ hx)⟩
  refine ⟨φ, hφf, ?_⟩
  ext x
  have h := congrArg e (congrArg (fun h : S →+* A ⧸ _ ↦ h x) hφ)
  rw [RingHom.comp_apply, RingHom.comp_apply, Ideal.quotEquivOfEq_mk] at h
  exact h.trans (e.apply_symm_apply _)

set_option backward.isDefEq.respectTransparency false in
private theorem formallySmoothNAdic_int_cohenRing
    (Λ : Type*) [CommRing Λ] [IsDomain Λ] [IsCohenRing Λ]
    (p : ℕ) [CharP (ResidueField Λ) p]
    (hmax : IsLocalRing.maximalIdeal Λ = Ideal.span {(p : Λ)}) :
    RingHom.FormallySmoothNAdic.{u} (Int.castRingHom Λ)
      (IsLocalRing.maximalIdeal Λ) := by
  intro E _ J hJ f ψ _ hψ
  obtain ⟨k, hk, hψ⟩ := hψ
  have hp : (p : Λ) ^ k ∈ IsLocalRing.maximalIdeal Λ ^ k :=
    Ideal.pow_mem_pow (hmax ▸ Ideal.mem_span_singleton_self _) k
  have hpE : (p : E) ^ k ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_pow, map_natCast] using (show ψ ((p : Λ) ^ k) = 0 from hψ hp)
  have hpE2 : ((p ^ (k * 2) : ℕ) : E) = 0 := by
    have h := Ideal.pow_mem_pow hpE 2
    rw [hJ] at h
    simpa only [Nat.cast_pow, pow_mul, Ideal.zero_eq_bot, Submodule.mem_bot] using h
  let Q := Λ ⧸ Ideal.span {(p : Λ) ^ (k * 2)}
  let : Algebra (ZMod (p ^ (k * 2))) Q :=
    ZMod.algebra' Q (ringChar Q) (ringChar.dvd (by
      change ((p ^ (k * 2) : ℕ) : Λ ⧸ Ideal.span {(p : Λ) ^ (k * 2)}) = 0
      rw [← map_natCast (Ideal.Quotient.mk _), Nat.cast_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)))
  let : Algebra (ZMod (p ^ (k * 2))) E :=
    ZMod.algebra' E (ringChar E) (ringChar.dvd hpE2)
  let ψ' : Q →+* E ⧸ J := Ideal.Quotient.lift _ ψ (by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    have hpψ : ψ ((p : Λ) ^ (k * 2)) = 0 := by
      have h := congrArg (Ideal.Quotient.mk J) hpE2
      simpa only [Nat.cast_pow, map_pow, map_natCast, map_zero] using h
    simp only [map_mul, hpψ, mul_zero])
  let ψa : Q →ₐ[ZMod (p ^ (k * 2))] E ⧸ J :=
    { __ := ψ'
      commutes' := fun x ↦ DFunLike.congr_fun
        (Subsingleton.elim (ψ'.comp (algebraMap _ Q)) (algebraMap _ (E ⧸ J))) x }
  have : Algebra.FormallySmooth (ZMod (p ^ (k * 2))) Q :=
    IsCohenRing.formallySmooth_quotient_span_pow p (k * 2) Λ
  obtain ⟨φ, hφ⟩ := Algebra.FormallySmooth.exists_lift J ⟨2, hJ⟩ ψa
  refine ⟨φ.toRingHom.comp (Ideal.Quotient.mk _), ?_, Subsingleton.elim _ _⟩
  ext x
  exact congrArg (fun h : Q →ₐ[ZMod (p ^ (k * 2))] E ⧸ J ↦ h (Ideal.Quotient.mk _ x)) hφ

/-- A prescribed residue homomorphism from a Cohen ring lifts to a complete local ring. -/
@[ega "0 19.8.6" "(i), special case"]
theorem exists_cohenRing_lift
    (Λ A : Type u) [CommRing Λ] [IsDomain Λ] [IsCohenRing Λ]
    [CommRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (p : ℕ) [CharP (ResidueField Λ) p]
    (hmax : IsLocalRing.maximalIdeal Λ = Ideal.span {(p : Λ)})
    (ψ : ResidueField Λ →+* ResidueField A) :
    ∃ φ : Λ →+* A, (residue A).comp φ = ψ.comp (residue Λ) := by
  obtain ⟨φ, _, hφ⟩ := exists_lift_to_residueField (Int.castRingHom Λ)
    (IsLocalRing.maximalIdeal Λ) (formallySmoothNAdic_int_cohenRing Λ p hmax)
    (Int.castRingHom A) (ψ.comp (residue Λ)) (Subsingleton.elim _ _)
    (fun x hx ↦ by
      change ψ (residue Λ x) = 0
      rw [(residue_eq_zero_iff x).mpr hx, map_zero])
  exact ⟨φ, hφ⟩

private theorem injective_of_uniformizer_ne_zero
    {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsReduced B]
    (f : A →+* B) {π : A} (hπ : Irreducible π) (hfπ : f π ≠ 0) :
    Function.Injective f := by
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hker
  obtain ⟨n, hn⟩ := ideal_eq_span_pow_irreducible hker hπ
  have hm : π ^ n ∈ RingHom.ker f := by
    rw [hn]
    exact Ideal.subset_span (Set.mem_singleton _)
  exact hfπ (isNilpotent_iff_eq_zero.mp ⟨n, by simpa using hm⟩)

private theorem isLocalHom_of_residue_comp_eq
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) (ψ : ResidueField A →+* ResidueField B)
    (hf : (residue B).comp f = ψ.comp (residue A)) :
    IsLocalHom f := by
  have : IsLocalHom ((residue B).comp f) := by
    rw [hf]
    infer_instance
  exact isLocalHom_of_comp f (residue B)

private theorem residueField_map_eq_of_residue_comp_eq
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f]
    (ψ : ResidueField A →+* ResidueField B)
    (hf : (residue B).comp f = ψ.comp (residue A)) :
    ResidueField.map f = ψ := by
  ext x
  obtain ⟨a, rfl⟩ := residue_surjective x
  rw [ResidueField.map_residue]
  exact congrArg (fun h : A →+* ResidueField B ↦ h a) hf

/-- An injective local homomorphism of discrete valuation rings makes the target an extension. -/
private theorem isExtension_of_injective_of_isLocalHom
    {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    (hinj : Function.Injective (algebraMap A B)) (hloc : IsLocalHom (algebraMap A B)) :
    IsExtension A B :=
  { toFaithfulSMul := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
    toIsLocalHom := hloc }

set_option backward.isDefEq.respectTransparency false in
/-- A Cohen base factors through a Cohen ring with the target residue field. -/
private theorem exists_cohenRing_factorization
    (A B : Type u) [CommRing A] [IsDomain A] [IsCohenRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [Algebra A B] [IsExtension A B]
    [PerfectField (ResidueField A)]
    (p : ℕ) (hp : p.Prime) [CharP (ResidueField A) p]
    (hA : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)}) :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsDomain C) (_ : IsCohenRing C)
      (_ : Algebra A C) (_ : Algebra C B) (_ : IsScalarTower A C B)
      (_ : IsExtension A C) (_ : IsExtension C B),
      Irreducible (algebraMap A C (p : A)) ∧
        Function.Surjective (ResidueField.map (algebraMap C B)) := by
  have : CharP (ResidueField B) p := charP_of_injective_algebraMap
    (algebraMap (ResidueField A) (ResidueField B)).injective p
  obtain ⟨C, hCcomm, hCdom, hCcohen, hC, ⟨e⟩⟩ :=
    IsCohenRing.exists_residueField_ringEquiv p hp (ResidueField B)
  have : CharP (ResidueField C) p :=
    charP_of_injective_ringHom (f := e.symm.toRingHom) e.symm.injective p
  let ψ := e.symm.toRingHom.comp (algebraMap (ResidueField A) (ResidueField B))
  obtain ⟨f, hf⟩ := exists_cohenRing_lift A C p hA ψ
  have hfloc : IsLocalHom f := isLocalHom_of_residue_comp_eq f ψ hf
  have hpA : Irreducible (p : A) :=
    (irreducible_iff_uniformizer _).mpr hA
  have hpC : Irreducible (p : C) :=
    (irreducible_iff_uniformizer _).mpr hC
  have hfinj : Function.Injective f := injective_of_uniformizer_ne_zero f hpA
    (by simpa only [map_natCast] using hpC.ne_zero)
  let : Algebra A C := f.toAlgebra
  have : IsExtension A C := isExtension_of_injective_of_isLocalHom hfinj hfloc
  have hweak : IsWeaklyUnramified A C :=
    isWeaklyUnramified_of_irreducible_algebraMap A C (p : A)
      (by simpa only [map_natCast] using hpC)
  have hfs : RingHom.FormallySmoothNAdic.{u} (algebraMap A C)
      (IsLocalRing.maximalIdeal C) :=
    (formallySmooth_iff_weaklyUnramified_and_isSeparableExtension A C).mpr
      ⟨hweak, Algebra.isSeparableExtension_of_perfectField _ _⟩
  obtain ⟨g, hgf, hgres⟩ := exists_lift_to_residueField (algebraMap A C)
    (IsLocalRing.maximalIdeal C) hfs (algebraMap A B) (e.toRingHom.comp (residue C)) (by
      ext a
      have h := congrArg (fun h : A →+* ResidueField C ↦ h a) hf
      change e (residue C (f a)) = residue B (algebraMap A B a)
      rw [show residue C (f a) = ψ (residue A a) from h]
      exact e.apply_symm_apply _) (fun x hx ↦ by
      change e (residue C x) = 0
      rw [(residue_eq_zero_iff x).mpr hx, map_zero])
  have hgloc : IsLocalHom g := isLocalHom_of_residue_comp_eq g e.toRingHom hgres
  have hginj : Function.Injective g := injective_of_uniformizer_ne_zero g hpC (by
    rw [map_natCast]
    intro h
    apply hpA.ne_zero
    apply FaithfulSMul.algebraMap_injective A B
    simpa only [map_natCast, map_zero] using h)
  let : Algebra C B := g.toAlgebra
  have : IsScalarTower A C B := IsScalarTower.of_algebraMap_eq
    (fun a ↦ (congrArg (fun h : A →+* B ↦ h a) hgf).symm)
  have : IsExtension C B := isExtension_of_injective_of_isLocalHom hginj hgloc
  have hres : Function.Surjective (ResidueField.map (algebraMap C B)) := by
    change Function.Surjective (ResidueField.map g)
    rw [residueField_map_eq_of_residue_comp_eq g e.toRingHom hgres]
    exact e.surjective
  exact ⟨C, hCcomm, hCdom, hCcohen, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, by simpa only [map_natCast] using hpC, hres⟩

/-- The perfect-residue theorem for a Cohen-type tower `A ⊆ C ⊆ B`, with the fraction fields
`K ⊆ Frac C ⊆ L` supplied automatically. -/
private theorem exists_finite_extension_isWeakSolution_of_cohenTower_fractionRing
    (p : ℕ) [Fact p.Prime] (A C B K L : Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L]
    [Algebra A C] [Algebra C B] [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [IsScalarTower A C B] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsExtension A C] [IsExtension C B] [IsExtension A B]
    [IsFractionRing A K] [IsFractionRing B L]
    [CharP (ResidueField A) p] [ExpChar (ResidueField B) p] [PerfectField (ResidueField A)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal C) C]
    {π : A} (hπA : Irreducible π) (hπC : Irreducible (algebraMap A C π))
    (hres : Function.Surjective (ResidueField.map (algebraMap C B)))
    (hepp : EppCondition A B p) :
    ∃ (K₁ : Type u) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A B K L K₁,
        D.IsWeakSolution := by
  let E := FractionRing C
  let : Algebra C L := ((algebraMap B L).comp (algebraMap C B)).toAlgebra
  have : IsScalarTower C B L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A C L := IsScalarTower.to₁₂₄ A C B L
  have : FaithfulSMul C L := (faithfulSMul_iff_algebraMap_injective C L).mpr
    ((IsFractionRing.injective B L).comp (FaithfulSMul.algebraMap_injective C B))
  let : Algebra E L := FractionRing.liftAlgebra C L
  have : IsScalarTower C E L := FractionRing.isScalarTower_liftAlgebra C L
  have hAE : Function.Injective (algebraMap A E) :=
    (IsFractionRing.injective C E).comp (FaithfulSMul.algebraMap_injective A C)
  let : Algebra K E := (IsFractionRing.lift (K := K) hAE).toAlgebra
  have : IsScalarTower A K E := IsScalarTower.of_algebraMap_eq
    (fun a ↦ (IsFractionRing.lift_algebraMap hAE a).symm)
  have : IsScalarTower A E L := IsScalarTower.to₁₃₄ A C E L
  have : IsScalarTower K E L := by
    apply IsScalarTower.of_algebraMap_eq
    have h : (algebraMap E L).comp (algebraMap K E) = algebraMap K L := by
      apply IsFractionRing.ringHom_ext (A := A)
      intro a
      simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
    exact fun x ↦ (congrArg (fun f : K →+* L ↦ f x) h).symm
  exact exists_finite_extension_isWeakSolution_of_perfectField_of_cohenTower
    p A C B K E L hπA hπC hres hepp (familyTowerSolvable_all_proved p)

set_option backward.isDefEq.respectTransparency false in
/-- The complete perfect-residue theorem for a Cohen base, with both interposition and the
prime-degree recursion discharged. -/
theorem exists_finite_extension_isWeakSolution_of_cohenRing_proved
    (p : ℕ) [Fact p.Prime]
    (A B K L : Type u)
    [CommRing A] [IsDomain A] [IsCohenRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [PerfectField (ResidueField A)] [CharP (ResidueField A) p]
    [ExpChar (ResidueField B) p]
    (hA : IsLocalRing.maximalIdeal A = Ideal.span {(p : A)})
    (hepp : EppCondition A B p) :
    ∃ (K₁ : Type u) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁),
      ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A B K L K₁,
        D.IsWeakSolution := by
  obtain ⟨C, _, _, _, _, _, _, _, _, hpC, hres⟩ :=
    exists_cohenRing_factorization A B p Fact.out hA
  have hπA : Irreducible (p : A) := (irreducible_iff_uniformizer _).mpr hA
  exact exists_finite_extension_isWeakSolution_of_cohenTower_fractionRing
    p A C B K L hπA hpC hres hepp

private theorem powerSeries_hom_eq_constantCoeff
    {k R : Type*} [CommRing k] [CommRing R] (f : PowerSeries k →+* R)
    (hX : f PowerSeries.X = 0) (s : PowerSeries k) :
    f s = f (PowerSeries.C (PowerSeries.constantCoeff s)) := by
  obtain ⟨g, hg⟩ := PowerSeries.X_dvd_iff.mpr
    (show PowerSeries.constantCoeff (s - PowerSeries.C (PowerSeries.constantCoeff s)) = 0 by
      simp)
  have h := congrArg f hg
  rw [map_sub, map_mul, hX, zero_mul] at h
  exact sub_eq_zero.mp h

private theorem residueFieldOfPowerSeries_residue
    {k : Type*} [Field k] (s : PowerSeries k) :
    PowerSeries.residueFieldOfPowerSeries (residue _ s) =
      PowerSeries.constantCoeff s := by
  change (RingHom.quotientKerEquivOfSurjective PowerSeries.constantCoeff_surj)
    (Ideal.quotEquivOfEq PowerSeries.ker_coeff_eq_max_ideal.symm
      (Ideal.Quotient.mk _ s)) = _
  rw [Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]

set_option backward.isDefEq.respectTransparency false in
private theorem exists_powerSeries_factorization
    (k B : Type u) [Field k] [PerfectField k]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [Algebra (PowerSeries k) B] [IsExtension (PowerSeries k) B] :
    let C := PowerSeries (ResidueField B)
    ∃ (_ : Algebra (PowerSeries k) C) (_ : Algebra C B)
      (_ : IsScalarTower (PowerSeries k) C B)
      (_ : IsExtension (PowerSeries k) C) (_ : IsExtension C B),
      Irreducible (algebraMap (PowerSeries k) C PowerSeries.X) ∧
        Function.Surjective (ResidueField.map (algebraMap C B)) := by
  let A := PowerSeries k
  let C := PowerSeries (ResidueField B)
  let ψ : k →+* ResidueField B :=
    ((residue B).comp (algebraMap A B)).comp PowerSeries.C
  let f : A →+* C := PowerSeries.map ψ
  have hFX : f PowerSeries.X = PowerSeries.X := PowerSeries.map_X ψ
  have hmap : (IsLocalRing.maximalIdeal A).map f = IsLocalRing.maximalIdeal C := by
    change (IsLocalRing.maximalIdeal (PowerSeries k)).map f =
      IsLocalRing.maximalIdeal (PowerSeries (ResidueField B))
    rw [PowerSeries.maximalIdeal_eq_span_X, PowerSeries.maximalIdeal_eq_span_X,
      Ideal.map_span, Set.image_singleton, hFX]
  have hfloc : IsLocalHom f := ((local_hom_TFAE f).out 1 3).mpr hmap.le
  let : Algebra A C := f.toAlgebra
  have hfinj : Function.Injective f := PowerSeries.map_injective ψ ψ.injective
  have : IsExtension A C := isExtension_of_injective_of_isLocalHom hfinj hfloc
  have hXC : Irreducible (PowerSeries.X : C) := PowerSeries.X_irreducible
  have hπC : Irreducible (algebraMap A C PowerSeries.X) := by
    change Irreducible (f PowerSeries.X)
    rw [hFX]
    exact hXC
  have hweak : IsWeaklyUnramified A C :=
    isWeaklyUnramified_of_irreducible_algebraMap A C PowerSeries.X hπC
  have : PerfectField (ResidueField A) :=
    PerfectField.of_ringEquiv (PowerSeries.residueFieldOfPowerSeries (k := k)).symm
  have hfs : RingHom.FormallySmoothNAdic.{u} (algebraMap A C)
      (IsLocalRing.maximalIdeal C) :=
    (formallySmooth_iff_weaklyUnramified_and_isSeparableExtension A C).mpr
      ⟨hweak, Algebra.isSeparableExtension_of_perfectField _ _⟩
  obtain ⟨g, hgf, hg⟩ := exists_lift_to_residueField (algebraMap A C)
    (IsLocalRing.maximalIdeal C) hfs (algebraMap A B)
    (PowerSeries.constantCoeff : C →+* ResidueField B) (by
      ext s
      change ψ (PowerSeries.constantCoeff s) = residue B (algebraMap A B s)
      symm
      change (((residue B).comp (algebraMap A B)) s) =
        ((residue B).comp (algebraMap A B)) (PowerSeries.C (PowerSeries.constantCoeff s))
      apply powerSeries_hom_eq_constantCoeff
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      apply _root_.map_nonunit (algebraMap A B)
      rw [PowerSeries.maximalIdeal_eq_span_X]
      exact Ideal.mem_span_singleton_self _) (fun x hx ↦ by
      rwa [← PowerSeries.ker_coeff_eq_max_ideal] at hx)
  have hgres : (residue B).comp g =
      PowerSeries.residueFieldOfPowerSeries.toRingHom.comp (residue C) := by
    ext c
    change residue B (g c) = PowerSeries.residueFieldOfPowerSeries (residue C c)
    rw [residueFieldOfPowerSeries_residue]
    exact congrArg (fun h : C →+* ResidueField B ↦ h c) hg
  have hgloc : IsLocalHom g :=
    isLocalHom_of_residue_comp_eq g PowerSeries.residueFieldOfPowerSeries.toRingHom hgres
  have hginj : Function.Injective g := injective_of_uniformizer_ne_zero g
    PowerSeries.X_irreducible (by
      have h := congrArg (fun h : A →+* B ↦ h PowerSeries.X) hgf
      have hX : g PowerSeries.X = algebraMap A B PowerSeries.X := by
        change g (f PowerSeries.X) = algebraMap A B PowerSeries.X at h
        rwa [hFX] at h
      rw [hX]
      exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective A B)).mpr
        PowerSeries.X_ne_zero)
  let : Algebra C B := g.toAlgebra
  have : IsScalarTower A C B := IsScalarTower.of_algebraMap_eq
    (fun a ↦ (congrArg (fun h : A →+* B ↦ h a) hgf).symm)
  have : IsExtension C B := isExtension_of_injective_of_isLocalHom hginj hgloc
  have hres : Function.Surjective (ResidueField.map (algebraMap C B)) := by
    change Function.Surjective (ResidueField.map g)
    rw [residueField_map_eq_of_residue_comp_eq g _ hgres]
    exact PowerSeries.residueFieldOfPowerSeries.surjective
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    hπC, hres⟩

set_option backward.isDefEq.respectTransparency false in
/-- Let `B` be a complete discrete valuation ring extending `k⟦X⟧`, with `k` a perfect field of
characteristic `p`, satisfying Epp's condition. Then some finite extension `K₁` of the fraction
field `K` of `k⟦X⟧` yields a weak solution for `B` over `k⟦X⟧`. -/
theorem exists_finite_extension_isWeakSolution_of_powerSeries_proved
    (p : ℕ) [Fact p.Prime]
    (k B K L : Type u) [Field k] [PerfectField k] [CharP k p]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [Field K] [Field L]
    [Algebra (PowerSeries k) B] [Algebra (PowerSeries k) K]
    [Algebra (PowerSeries k) L] [Algebra B L] [Algebra K L]
    [IsScalarTower (PowerSeries k) B L] [IsScalarTower (PowerSeries k) K L]
    [IsExtension (PowerSeries k) B]
    [IsFractionRing (PowerSeries k) K] [IsFractionRing B L]
    [ExpChar (ResidueField B) p]
    (hepp : EppCondition (PowerSeries k) B p) :
    ∃ (K₁ : Type u) (_ : Field K₁) (_ : Algebra K K₁)
      (_ : Algebra (PowerSeries k) K₁)
      (_ : IsScalarTower (PowerSeries k) K K₁) (_ : Module.Finite K K₁),
      ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u}
        (PowerSeries k) B K L K₁, D.IsWeakSolution := by
  let A := PowerSeries k
  let C := PowerSeries (ResidueField B)
  obtain ⟨_, _, _, _, _, hπC, hres⟩ := exists_powerSeries_factorization k B
  have : IsAdicComplete (IsLocalRing.maximalIdeal A) A := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  have : IsAdicComplete (IsLocalRing.maximalIdeal C) C := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  have : PerfectField (ResidueField A) :=
    PerfectField.of_ringEquiv (PowerSeries.residueFieldOfPowerSeries (k := k)).symm
  have : CharP (ResidueField A) p := charP_of_injective_ringHom
    (f := (PowerSeries.residueFieldOfPowerSeries (k := k)).symm.toRingHom)
    PowerSeries.residueFieldOfPowerSeries.symm.injective p
  exact exists_finite_extension_isWeakSolution_of_cohenTower_fractionRing
    p A C B K L PowerSeries.X_irreducible hπC hres hepp

/-- The perfect core of the residue field lifts to a Cohen subring in mixed characteristic. -/
@[sga "7 IX 12.8" "special case"]
private theorem exists_cohenRing_perfectCore_subring
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p]
    (hpA : (p : A) ≠ 0) :
    ∃ (Λ : Type u) (_ : CommRing Λ) (_ : IsDomain Λ) (_ : IsCohenRing Λ)
      (φ : Λ →+* A), Function.Injective φ ∧ IsLocalHom φ ∧
      PerfectField (ResidueField Λ) ∧
      IsLocalRing.maximalIdeal Λ = Ideal.span {(p : Λ)} ∧
      ∃ e : ResidueField Λ ≃+* perfectCore (ResidueField A) p,
        (residue A).comp φ =
          (perfectCore (ResidueField A) p).subtype.comp
            (e.toRingHom.comp (residue Λ)) := by
  let k := perfectCore (ResidueField A) p
  obtain ⟨Λ, hΛcomm, hΛdom, hΛcohen, hΛ, ⟨e⟩⟩ :=
    IsCohenRing.exists_residueField_ringEquiv p Fact.out k
  have : CharP (ResidueField Λ) p :=
    charP_of_injective_ringHom (f := e.symm.toRingHom) e.symm.injective p
  let ψ := k.subtype.comp e.toRingHom
  obtain ⟨φ, hφ⟩ := exists_cohenRing_lift Λ A p hΛ ψ
  have hπ : Irreducible (p : Λ) := (irreducible_iff_uniformizer _).mpr hΛ
  have hφinj : Function.Injective φ :=
    injective_of_uniformizer_ne_zero φ hπ (by simpa only [map_natCast] using hpA)
  have hφloc : IsLocalHom φ := isLocalHom_of_residue_comp_eq φ ψ hφ
  have hperf : PerfectField (ResidueField Λ) := PerfectField.of_ringEquiv e.symm
  exact ⟨Λ, hΛcomm, hΛdom, hΛcohen, φ, hφinj, hφloc, hperf, hΛ, e, hφ⟩

/-- In equal characteristic the perfect core lifts through the power-series presentation. -/
private theorem exists_powerSeries_perfectCore_subring
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p]
    (hchar : (ringChar (ResidueField A) : A) = 0)
    (π : A) (hπ : Irreducible π) :
    ∃ φ : PowerSeries (perfectCore (ResidueField A) p) →+* A,
      φ PowerSeries.X = π ∧ Function.Injective φ ∧ IsLocalHom φ ∧
      (residue A).comp (φ.comp PowerSeries.C) =
        (perfectCore (ResidueField A) p).subtype := by
  let k := perfectCore (ResidueField A) p
  obtain ⟨e, heX, heC⟩ := exists_powerSeriesRingEquiv_of_irreducible A hchar hπ
  let φ : PowerSeries k →+* A :=
    e.toRingHom.comp (PowerSeries.map k.subtype)
  have hφX : φ PowerSeries.X = π := by
    change e (PowerSeries.map k.subtype PowerSeries.X) = π
    rw [PowerSeries.map_X, heX]
  have hφinj : Function.Injective φ :=
    e.injective.comp (PowerSeries.map_injective k.subtype k.subtype.injective)
  have hφloc : IsLocalHom φ := by
    apply ((local_hom_TFAE φ).out 1 3).mpr
    rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.map_span, Set.image_singleton,
      hφX, ← hπ.maximalIdeal_eq]
  refine ⟨φ, hφX, hφinj, hφloc, ?_⟩
  ext c
  change residue A (e (PowerSeries.map k.subtype (PowerSeries.C c))) = c
  rw [PowerSeries.map_C, heC]
  rfl

/-- Epp's residue condition survives replacing the lower residue field by its perfect core. -/
private theorem eppCondition_of_perfectCore_base
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [IsLocalRing R] [IsLocalRing A] [IsLocalRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [IsLocalHom (algebraMap R A)] [IsLocalHom (algebraMap A B)]
    [IsLocalHom (algebraMap R B)]
    (p : ℕ) [Fact p.Prime] [ExpChar (ResidueField A) p]
    [ExpChar (ResidueField B) p]
    (e : ResidueField R ≃+* perfectCore (ResidueField A) p)
    (hmap : ResidueField.map (algebraMap R A) =
      (perfectCore (ResidueField A) p).subtype.comp e.toRingHom)
    (hepp : EppCondition A B p) : EppCondition R B p := by
  intro x hx
  obtain ⟨q, hqmonic, hqsep, hqmap⟩ :=
    exists_monic_separable_map_eq_minpoly_of_forall_isSeparable hepp hx
  let f : perfectCore (ResidueField A) p →+* ResidueField R := e.symm.toRingHom
  refine Polynomial.Separable.of_dvd (Polynomial.Separable.map hqsep (f := f))
    (minpoly.dvd (ResidueField R) x ?_)
  have hcomp : (algebraMap (ResidueField R) (ResidueField B)).comp f =
      (algebraMap (ResidueField A) (ResidueField B)).comp
        (perfectCore (ResidueField A) p).subtype := by
    ext z
    change algebraMap (ResidueField R) (ResidueField B) (e.symm z) =
      algebraMap (ResidueField A) (ResidueField B) (z : ResidueField A)
    rw [IsScalarTower.algebraMap_apply (ResidueField R) (ResidueField A)
      (ResidueField B)]
    change algebraMap (ResidueField A) (ResidueField B)
      (ResidueField.map (algebraMap R A) (e.symm z)) = _
    rw [hmap]
    simp
  have hqmap' : q.map (perfectCore (ResidueField A) p).subtype =
      minpoly (ResidueField A) x := by
    have halg :
        algebraMap (perfectCore (ResidueField A) p) (ResidueField A) =
          (perfectCore (ResidueField A) p).subtype := by
      ext z
      rfl
    rw [← halg]
    exact hqmap
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp]
  calc
    Polynomial.eval₂
        ((algebraMap (ResidueField A) (ResidueField B)).comp
          (perfectCore (ResidueField A) p).subtype) x q =
        Polynomial.eval₂ (algebraMap (ResidueField A) (ResidueField B)) x
          (q.map (perfectCore (ResidueField A) p).subtype) :=
      (Polynomial.eval₂_map (p := q) (perfectCore (ResidueField A) p).subtype
        (algebraMap (ResidueField A) (ResidueField B)) x).symm
    _ = Polynomial.eval₂ (algebraMap (ResidueField A) (ResidueField B)) x
        (minpoly (ResidueField A) x) := by rw [hqmap']
    _ = 0 := by
      simpa only [← Polynomial.aeval_def] using minpoly.aeval (ResidueField A) x

/-- Separability above a simple subfield survives passage to a surjective tensor factor. -/
private theorem isSeparable_adjoin_of_tensor_factor
    (k K E F : Type*) [Field k] [Field K] [Field E] [Field F]
    [Algebra k K] [Algebra k E] [Algebra K F]
    [Algebra k F] [IsScalarTower k K F]
    (α : E) (hgen : IntermediateField.adjoin k {α} ⊔ separableClosure k E = ⊤)
    (g : K ⊗[k] E →ₐ[K] F) (hg : Function.Surjective g) :
    Algebra.IsSeparable (IntermediateField.adjoin K {g (1 ⊗ₜ[k] α)}) F := by
  let e : E →ₐ[k] F := (g.restrictScalars k).comp Algebra.TensorProduct.includeRight
  let P := IntermediateField.adjoin K {e α}
  have : IsScalarTower k P F := IsScalarTower.to₁₃₄ k K P F
  let T := separableClosure P F
  have hall (x : E) : e x ∈ T := by
    let U := (T.restrictScalars k).comap e
    have hle : IntermediateField.adjoin k {α} ⊔ separableClosure k E ≤ U := by
      refine sup_le ?_ ?_
      · apply IntermediateField.adjoin_le_iff.mpr
        intro x hx
        have hx' : x = α := Set.mem_singleton_iff.mp hx
        change IsSeparable P (e x)
        rw [hx']
        have hα : e α ∈ P := IntermediateField.subset_adjoin K {e α} (Set.mem_singleton _)
        simpa only [IntermediateField.algebraMap_apply] using
          (isSeparable_algebraMap (F := P) (K := F) ⟨e α, hα⟩)
      · intro x hx
        change IsSeparable P (e x)
        exact (hx.map e e.injective).tower_top P
    exact hle (hgen ▸ IntermediateField.mem_top)
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨z, rfl⟩ := hg x
  change g z ∈ T
  induction z with
  | add x y hx hy => simpa only [map_add] using T.add_mem hx hy
  | tmul a b =>
    have ha : algebraMap K F a ∈ T := by
      change IsSeparable P (algebraMap K F a)
      rw [IsScalarTower.algebraMap_apply K P F]
      exact isSeparable_algebraMap _
    have he : g (a ⊗ₜ[k] b) = algebraMap K F a * e b := by
      rw [← Algebra.smul_def]
      change g.toLinearMap (a ⊗ₜ[k] b) = a • g.toLinearMap (1 ⊗ₜ[k] b)
      rw [← g.toLinearMap.map_smul, TensorProduct.smul_tmul']
      simp
    rw [he]
    exact T.mul_mem ha (hall b)

set_option backward.isDefEq.respectTransparency false in
/-- The complete equal-characteristic case over an arbitrary residue field, with the condition-(b)
data retained for descent from the completion. -/
theorem exists_finite_extension_isWeakSolution_of_complete_equalCharacteristic_proved
    (p : ℕ) [Fact p.Prime]
    (A B K L : Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [CharP (ResidueField A) p] [ExpChar (ResidueField B) p]
    (hpA : (p : A) = 0) (π : A) (hπ : Irreducible π)
    (hepp : EppCondition A B p) :
    ∃ (F : Type u) (_ : Field F) (_ : Algebra K F) (_ : Algebra A F)
      (_ : IsScalarTower A K F) (_ : Module.Finite K F),
      ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A B K L F,
        D.IsWeakSolution ∧ ∃ (n : ℕ) (ρ : F),
          ρ ^ p ^ n = algebraMap K F (algebraMap A K π) ∧
          minpoly K ρ = Polynomial.X ^ p ^ n -
            Polynomial.C (algebraMap A K π) ∧
          Algebra.IsSeparable (IntermediateField.adjoin K {ρ}) F := by
  let c := perfectCore (ResidueField A) p
  have hchar : (ringChar (ResidueField A) : A) = 0 := by
    rwa [ringChar.eq (ResidueField A) p]
  obtain ⟨φ, hφX, hφinj, hφloc, hφres⟩ :=
    exists_powerSeries_perfectCore_subring A p hchar π hπ
  let R := PowerSeries c
  let e : ResidueField R ≃+* c := PowerSeries.residueFieldOfPowerSeries
  let : CharP c p := inferInstance
  let : PerfectField (ResidueField R) := PerfectField.of_ringEquiv e.symm
  let : CharP (ResidueField R) p :=
    charP_of_injective_ringHom (f := e.symm.toRingHom) e.symm.injective p
  let : Algebra R A := φ.toAlgebra
  have : IsExtension R A := isExtension_of_injective_of_isLocalHom hφinj hφloc
  let : Algebra R B := ((algebraMap A B).comp φ).toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsExtension R B := IsExtension.trans R A B
  let : Algebra R K := ((algebraMap A K).comp φ).toAlgebra
  have : IsScalarTower R A K := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Algebra R L := ((algebraMap A L).comp φ).toAlgebra
  have : IsScalarTower R A L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R B L := IsScalarTower.of_algebraMap_eq fun x ↦
    IsScalarTower.algebraMap_apply A B L (φ x)
  have : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq fun x ↦
    IsScalarTower.algebraMap_apply A K L (φ x)
  let k := FractionRing R
  have hinj : Function.Injective (algebraMap R K) :=
    (IsFractionRing.injective A K).comp hφinj
  let : Algebra k K := (IsFractionRing.lift (K := k) hinj).toAlgebra
  have : IsScalarTower R k K := IsScalarTower.of_algebraMap_eq fun x ↦
    (IsFractionRing.lift_algebraMap hinj x).symm
  let : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
  have : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R k L := IsScalarTower.to₁₂₄ R k K L
  have hmap : ResidueField.map (algebraMap R A) =
      c.subtype.comp e.toRingHom := by
    apply residueField_map_eq_of_residue_comp_eq
    ext x
    have hx := DFunLike.congr_fun hφres (PowerSeries.constantCoeff x)
    change residue A (φ x) = (e (residue R x) : c) at ⊢
    have hconst : e (residue R x) = PowerSeries.constantCoeff x :=
      residueFieldOfPowerSeries_residue x
    have hπres : residue A π = 0 := by
      rw [residue_eq_zero_iff]
      exact hπ.not_isUnit
    have hx0 := powerSeries_hom_eq_constantCoeff ((residue A).comp φ)
      (by simpa only [RingHom.comp_apply, hφX] using hπres) x
    simp only [RingHom.comp_apply] at hx0
    rw [hconst, hx0]
    exact hx
  obtain ⟨E, _, _, _, _, _, DE, hDE⟩ :=
    exists_finite_extension_isWeakSolution_of_powerSeries_proved p c B k L
      (eppCondition_of_perfectCore_base R A B p e hmap hepp)
  have : IsAdicComplete (IsLocalRing.maximalIdeal R) R := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    infer_instance
  obtain ⟨n, α, hαpow, hαmin, hαsep⟩ := exists_pow_eq_and_isSeparable_adjoin
    (A := R) (K := k) (M := E) p PowerSeries.X PowerSeries.X_irreducible
  have hgen : IntermediateField.adjoin k {α} ⊔ separableClosure k E = ⊤ := by
    have h := congrArg (IntermediateField.restrictScalars k)
      (separableClosure.adjoin_eq_of_isAlgebraic_of_isSeparable
        (F := k) (E := IntermediateField.adjoin k {α}) E)
    simpa only [IntermediateField.restrictScalars_adjoin_eq_sup,
      IntermediateField.adjoin_self, IntermediateField.restrictScalars_top] using h
  obtain ⟨F, _, _, _, _, _, g, hg, D, hD⟩ :=
    exists_field_factor_isWeakSolution_of_baseChange R A B k K L E DE hDE
  let : Algebra k F := ((algebraMap K F).comp (algebraMap k K)).toAlgebra
  have : IsScalarTower k K F := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let j : E →ₐ[k] F := (g.restrictScalars k).comp Algebra.TensorProduct.includeRight
  let ρ : F := g (1 ⊗ₜ[k] α)
  have hρpow : ρ ^ p ^ n = algebraMap K F (algebraMap A K π) := by
    calc
      ρ ^ p ^ n = j (α ^ p ^ n) := (map_pow j α (p ^ n)).symm
      _ = j (algebraMap k E (algebraMap R k PowerSeries.X)) := congrArg j hαpow
      _ = algebraMap K F (algebraMap k K (algebraMap R k PowerSeries.X)) := j.commutes _
      _ = algebraMap K F (algebraMap A K π) := by
        rw [← IsScalarTower.algebraMap_apply R k K,
          IsScalarTower.algebraMap_apply R A K]
        change algebraMap K F (algebraMap A K (φ PowerSeries.X)) = _
        rw [hφX]
  have hρsep : Algebra.IsSeparable (IntermediateField.adjoin K {ρ}) F :=
    isSeparable_adjoin_of_tensor_factor k K E F α hgen g hg
  have hm : 1 ≤ p ^ n := pow_pos (Fact.out : p.Prime).pos n
  have hpoly : Stacks.KummerExtension.kummerPoly K π (p ^ n) = minpoly K ρ :=
    minpoly.eq_of_irreducible_of_monic
      (Stacks.KummerExtension.kummerPoly_irreducible K π (p ^ n) hm hπ) (by
        simp only [Stacks.KummerExtension.kummerPoly, map_sub, map_pow,
          Polynomial.aeval_X, Polynomial.aeval_C]
        rw [hρpow, sub_self])
      (Polynomial.monic_X_pow_sub_C _ (Nat.one_le_iff_ne_zero.mp hm))
  refine ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    D, hD, n, ρ, hρpow, ?_, hρsep⟩
  rw [← hpoly]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The complete mixed-characteristic case over an arbitrary residue field. -/
theorem exists_finite_extension_isWeakSolution_of_complete_mixedCharacteristic_proved
    (p : ℕ) [Fact p.Prime]
    (A B K L : Type u)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    [Field K] [Field L]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [CharP (ResidueField A) p] [ExpChar (ResidueField B) p]
    (hpA : (p : A) ≠ 0) (hepp : EppCondition A B p) :
    ∃ (F : Type u) (_ : Field F) (_ : Algebra K F) (_ : Algebra A F)
      (_ : IsScalarTower A K F) (_ : Module.Finite K F),
      ∃ D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A B K L F,
        D.IsWeakSolution := by
  obtain ⟨R, _, _, _, φ, hφinj, hφloc, hRperf, hRmax, e, hφres⟩ :=
    exists_cohenRing_perfectCore_subring A p hpA
  let : PerfectField (ResidueField R) := hRperf
  let : Algebra R A := φ.toAlgebra
  have : IsExtension R A := isExtension_of_injective_of_isLocalHom hφinj hφloc
  let : Algebra R B := ((algebraMap A B).comp φ).toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsExtension R B := IsExtension.trans R A B
  let : Algebra R K := ((algebraMap A K).comp φ).toAlgebra
  have : IsScalarTower R A K := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Algebra R L := ((algebraMap A L).comp φ).toAlgebra
  have : IsScalarTower R A L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R B L := IsScalarTower.of_algebraMap_eq fun x ↦
    IsScalarTower.algebraMap_apply A B L (φ x)
  have : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq fun x ↦
    IsScalarTower.algebraMap_apply A K L (φ x)
  let k := FractionRing R
  have hinj : Function.Injective (algebraMap R K) :=
    (IsFractionRing.injective A K).comp hφinj
  let : Algebra k K := (IsFractionRing.lift (K := k) hinj).toAlgebra
  have : IsScalarTower R k K := IsScalarTower.of_algebraMap_eq fun x ↦
    (IsFractionRing.lift_algebraMap hinj x).symm
  let : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
  have : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R k L := IsScalarTower.to₁₂₄ R k K L
  have hmap : ResidueField.map (algebraMap R A) =
      (perfectCore (ResidueField A) p).subtype.comp e.toRingHom :=
    residueField_map_eq_of_residue_comp_eq φ _ hφres
  let : CharP (ResidueField R) p := charP_of_injective_ringHom
    (f := e.symm.toRingHom) e.symm.injective p
  exact exists_finite_extension_isWeakSolution_of_baseChange R A B k K L
    (exists_finite_extension_isWeakSolution_of_cohenRing_proved p R B k L hRmax
      (eppCondition_of_perfectCore_base R A B p e hmap hepp))

end Stacks.EppTheorem

end

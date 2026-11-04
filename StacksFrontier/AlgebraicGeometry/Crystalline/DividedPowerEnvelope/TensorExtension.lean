module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.RingTheory.DividedPowers.SubDPIdeal
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.SetTheory.Cardinal.Subfield
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.DividedPowers.Extend
public import StacksFrontier.RingTheory.DividedPowers.Ring
public import StacksFrontier.RingTheory.Flat.ShortExact
public import StacksFrontier.RingTheory.Flat.TorCriterion
public import StacksFrontier.RingTheory.Tor.Vanishing
public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerEnvelope.Quotient

/-!
# Divided power envelopes: extending divided powers to a flat base change

This file collects the flatness and Tor computations used for the base change of divided power
envelopes, the injectivity of the kernel of a free presentation after tensoring, and the
resulting statement that, for a base change `B → B'` which is flat modulo the divided power
ideal and has no first Tor obstruction, the divided powers of an envelope extend to its tensor
product with `B'`.
-/

@[expose] public section

namespace Crystalline

section BaseChange

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v w

variable {A : DividedPowerRing} {B B' : Type u} [CommRing B] [CommRing B']

/-- The image of the base divided power ideal is contained in the extended ideal after base
change. -/
public lemma map_baseIdeal_le_map (f : A →+* B) (g : B →+* B') (J : Ideal B)
    (hJ : A.ideal.map f ≤ J) : A.ideal.map (g.comp f) ≤ J.map g := by
  rw [← Ideal.map_map]
  exact Ideal.map_mono hJ

/-- The two flat base-change hypotheses force Tor₁ to vanish against every quotient by an ideal
containing the divided power ideal. -/
private lemma flat_quotient_smul_top_iff [Algebra B B'] (I : Ideal B) :
    Module.Flat (B ⧸ I) (B' ⧸ (I • (⊤ : Submodule B B'))) ↔
      Module.Flat (B ⧸ I) (B' ⧸ (I.map (algebraMap B B'))) := by
  let IM := I.map (algebraMap B B')
  have hsmul : I • (⊤ : Submodule B B') = IM.restrictScalars B := by
    rw [Ideal.smul_top_eq_map]
  exact Module.Flat.equiv_iff (LinearEquiv.extendScalarsOfSurjective
    (fun y => Ideal.Quotient.mk_surjective y)
    ((Submodule.quotEquivOfEq _ _ hsmul).trans
      (Submodule.Quotient.restrictScalarsEquiv B IM)))

/-- If `Tor'₁(B', B ⧸ I)` vanishes, then `Tor₁^B(B ⧸ I, B')` and `Tor₁^B(B', B ⧸ I)` both
vanish. -/
private lemma tor1_base_quotient_vanishes [Algebra B B'] (I : Ideal B)
    (hTor : IsZero (((Tor' (ModuleCat.{u} B) 1).obj (ModuleCat.of B B')).obj
      (ModuleCat.of B (B ⧸ I)))) :
    Tor1Vanishes B (B ⧸ I) B' ∧ Tor1Vanishes B B' (B ⧸ I) := by
  constructor
  · exact IsZero.of_iso hTor (((torFlip_iso_Tor' B 1).app (ModuleCat.of B B')).app
      (ModuleCat.of B (B ⧸ I)))
  · exact IsZero.of_iso hTor (((Tor_iso_Tor' B 1).app (ModuleCat.of B B')).app
      (ModuleCat.of B (B ⧸ I)))

/-- In a polynomial presentation of the base change, the kernel of the surjection remains
Tor-independent from the base quotient. -/
private lemma kernel_rTensor_injective [Algebra B B'] {P : Type u} [CommRing P]
    [Algebra B P] [Algebra P B'] [IsScalarTower B P B'] (I : Ideal B)
    (φ : P →ₐ[B] B') (hφ : Function.Surjective φ) (hTor : IsZero
      (((Tor' (ModuleCat.{u} B) 1).obj (ModuleCat.of B B')).obj
        (ModuleCat.of B (B ⧸ I)))) :
    Function.Injective (LinearMap.rTensor (B ⧸ I)
      ((RingHom.ker φ.toRingHom).restrictScalars B).subtype) := by
  have hQ : Tor1Vanishes B (P ⧸ (RingHom.ker φ.toRingHom).restrictScalars B)
      (B ⧸ I) := by
    let K := RingHom.ker φ.toRingHom
    let e₁ := Submodule.Quotient.restrictScalarsEquiv B K
    let L := Ideal.Quotient.liftₐ K φ (by
      intro x hx
      change x ∈ RingHom.ker φ.toRingHom at hx
      exact RingHom.mem_ker.mp hx)
    have hLmk (x : P) : L (Ideal.Quotient.mk K x) = φ x :=
      Ideal.Quotient.lift_mk K φ.toRingHom _
    have hLbij : Function.Bijective L := by
      constructor
      · intro x y hxy
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
        apply Ideal.Quotient.eq.mpr
        show x - y ∈ RingHom.ker φ.toRingHom
        change φ.toRingHom x = φ.toRingHom y at hxy
        apply RingHom.mem_ker.mpr
        rw [map_sub, hxy, sub_self]
      · intro y
        obtain ⟨x, rfl⟩ := hφ y
        exact ⟨Ideal.Quotient.mk K x, hLmk x⟩
    let q := AlgEquiv.ofBijective L hLbij
    let e : (P ⧸ (RingHom.ker φ.toRingHom).restrictScalars B) ≃ₗ[B] B' :=
      e₁.trans q.toLinearEquiv
    exact IsZero.of_iso (tor1_base_quotient_vanishes I hTor).2
      (((Tor (ModuleCat.{u} B) 1).mapIso e.toModuleIso).app (ModuleCat.of B (B ⧸ I)))
  exact rTensor_subtype_injective_of_tor1_vanishes
    (R := B) (M := B ⧸ I) (Fr := P) ((RingHom.ker φ.toRingHom).restrictScalars B) hQ

/-- The Tor₁ hypothesis identifies the intersection of the polynomial kernel with the extended
base ideal, in the quotient-module form used by the divided-power descent. -/
private lemma kernel_intersection_smul [Algebra B B'] {P : Type u} [CommRing P]
    [Algebra B P] [Algebra P B'] [IsScalarTower B P B'] (I : Ideal B)
    (φ : P →ₐ[B] B') (hφ : Function.Surjective φ)
    (hTor : IsZero (((Tor' (ModuleCat.{u} B) 1).obj (ModuleCat.of B B')).obj
      (ModuleCat.of B (B ⧸ I))))
    {x : P} (hxK : x ∈ RingHom.ker φ.toRingHom)
    (hxI : x ∈ I.map (algebraMap B P)) :
    (⟨x, hxK⟩ : (RingHom.ker φ.toRingHom).restrictScalars B) ∈
      I • (⊤ : Submodule B ((RingHom.ker φ.toRingHom).restrictScalars B)) := by
  let K : Submodule B P := (RingHom.ker φ.toRingHom).restrictScalars B
  let eK := TensorProduct.tensorQuotEquivQuotSMul K I
  let eP := TensorProduct.tensorQuotEquivQuotSMul P I
  have hmem : x ∈ I • (⊤ : Submodule B P) := by
    rwa [Ideal.smul_top_eq_map]
  have hzero : eP ((LinearMap.rTensor (B ⧸ I) K.subtype)
      (eK.symm (Submodule.Quotient.mk (⟨x, hxK⟩ : K)))) = 0 := by
    simp only [eK, eP, TensorProduct.tensorQuotEquivQuotSMul_symm_mk,
      LinearMap.rTensor_tmul]
    rw [show (1 : B ⧸ I) = Ideal.Quotient.mk I 1 from rfl,
      TensorProduct.tensorQuotEquivQuotSMul_tmul_mk, one_smul]
    exact (Submodule.Quotient.mk_eq_zero (I • (⊤ : Submodule B P))).mpr hmem
  have htensor : LinearMap.rTensor (B ⧸ I) K.subtype
      (eK.symm (Submodule.Quotient.mk (⟨x, hxK⟩ : K))) = 0 := by
    apply eP.injective
    simpa using hzero
  have hclass : eK.symm (Submodule.Quotient.mk (⟨x, hxK⟩ : K)) = 0 :=
    kernel_rTensor_injective I φ hφ hTor (by simpa only [map_zero] using htensor)
  have hmk : (Submodule.Quotient.mk (⟨x, hxK⟩ : K) :
      K ⧸ I • (⊤ : Submodule B K)) = 0 := by
    apply eK.symm.injective
    simpa only [map_zero] using hclass
  exact (Submodule.Quotient.mk_eq_zero
    (I • (⊤ : Submodule B ((RingHom.ker φ.toRingHom).restrictScalars B)))).mp hmk

section LargeUniverseTensorKernel

variable {P : Type u} [CommRing P] [Algebra B P] [Algebra B B']
variable (I : Ideal B) (φ : P →ₐ[B] B')

private abbrev kernelSmul : Submodule B ((RingHom.ker φ.toRingHom).restrictScalars B) :=
  I • ⊤
private abbrev presentationSmul : Submodule B P := I • ⊤
private abbrev targetSmul : Submodule B B' := I • ⊤
private def presentationKernelIncl : ((RingHom.ker φ.toRingHom).restrictScalars B) →ₗ[B] P :=
  ((RingHom.ker φ.toRingHom).restrictScalars B).subtype
/-- A linear map sends `I • ⊤` into `I • ⊤`. -/
private lemma smul_top_le_comap_smul_top {M M' : Type*} [AddCommGroup M] [Module B M]
    [AddCommGroup M'] [Module B M'] (g : M →ₗ[B] M') :
    I • (⊤ : Submodule B M) ≤ (I • (⊤ : Submodule B M')).comap g := by
  rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
  exact Submodule.smul_mono le_rfl le_top
private lemma kernelSmul_le_comap :
    kernelSmul (P := P) I φ ≤
      (presentationSmul (P := P) I).comap (presentationKernelIncl φ) :=
  smul_top_le_comap_smul_top I _
private def kernelQuotientIncl :
    (((RingHom.ker φ.toRingHom).restrictScalars B) ⧸ kernelSmul (P := P) I φ) →ₗ[B ⧸ I]
      (P ⧸ presentationSmul (P := P) I) :=
  LinearMap.extendScalarsOfSurjective (R := B) (S := B ⧸ I)
    Ideal.Quotient.mk_surjective
    ((kernelSmul (P := P) I φ).mapQ (presentationSmul (P := P) I)
      (presentationKernelIncl φ) (kernelSmul_le_comap (P := P) I φ))
private lemma presentationSmul_le_comap :
    presentationSmul (P := P) I ≤
      (targetSmul (B' := B') I).comap φ.toLinearMap :=
  smul_top_le_comap_smul_top I _
private def presentationQuotientMap : (P ⧸ presentationSmul (P := P) I) →ₗ[B ⧸ I]
    (B' ⧸ targetSmul (B' := B') I) :=
  LinearMap.extendScalarsOfSurjective (R := B) (S := B ⧸ I)
    Ideal.Quotient.mk_surjective
    ((presentationSmul (P := P) I).mapQ (targetSmul (B' := B') I)
      φ.toLinearMap (presentationSmul_le_comap I φ))
private lemma kernelQuotientIncl_injective
    (hInter : ∀ (x : (RingHom.ker φ.toRingHom).restrictScalars B),
      (x : P) ∈ presentationSmul (P := P) I → x ∈ kernelSmul (P := P) I φ) :
    Function.Injective (kernelQuotientIncl I φ) := by
  intro x y hxy
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (kernelSmul (P := P) I φ) x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (kernelSmul (P := P) I φ) y
  apply (Submodule.Quotient.eq (kernelSmul (P := P) I φ)).mpr
  have hxy' : (Submodule.Quotient.mk (x : P) : P ⧸ presentationSmul (P := P) I) =
      Submodule.Quotient.mk (y : P) := by
    change (Submodule.Quotient.mk (x : P) : P ⧸ presentationSmul (P := P) I) =
      Submodule.Quotient.mk (y : P) at hxy
    exact hxy
  have hmem : (x : P) - (y : P) ∈ presentationSmul (P := P) I :=
    (Submodule.Quotient.eq (presentationSmul (P := P) I)).mp hxy'
  exact hInter (x - y) hmem
private lemma presentationQuotientMap_surjective (hφ : Function.Surjective φ) :
    Function.Surjective (presentationQuotientMap I φ) := by
  intro z
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective (targetSmul (B' := B') I) z
  obtain ⟨p, rfl⟩ := hφ b
  refine ⟨Submodule.Quotient.mk p, ?_⟩
  rfl
private lemma kernelQuotient_exact (hφ : Function.Surjective φ) :
    Function.Exact (kernelQuotientIncl I φ) (presentationQuotientMap I φ) := by
  rw [LinearMap.exact_iff]
  apply le_antisymm
  · intro z hz
    obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective (presentationSmul (P := P) I) z
    have hφp : φ p ∈ targetSmul (B' := B') I := by
      have hz' : (presentationQuotientMap I φ) (Submodule.Quotient.mk p) = 0 :=
        LinearMap.mem_ker.mp hz
      change (Submodule.Quotient.mk (φ p) : B' ⧸ targetSmul (B' := B') I) = 0 at hz'
      exact (Submodule.Quotient.mk_eq_zero _).mp hz'
    have hmapPI : Submodule.map φ.toLinearMap (presentationSmul (P := P) I) =
        targetSmul (B' := B') I := by
      rw [Submodule.map_smul'']
      have hrange : φ.toLinearMap.range = ⊤ :=
        LinearMap.range_eq_top.mpr hφ
      rw [Submodule.map_top, hrange]
    rw [← hmapPI] at hφp
    obtain ⟨pI, hpI, heq⟩ := hφp
    let k : (RingHom.ker φ.toRingHom).restrictScalars B := ⟨p - pI, by
      show φ (p - pI) = 0
      change φ pI = φ p at heq
      rw [map_sub, heq, sub_self]⟩
    refine ⟨Submodule.Quotient.mk k, ?_⟩
    show (Submodule.Quotient.mk (k : P) : P ⧸ presentationSmul (P := P) I) =
      Submodule.Quotient.mk p
    apply (Submodule.Quotient.eq (presentationSmul (P := P) I)).mpr
    show (p - pI) - p ∈ presentationSmul (P := P) I
    convert (presentationSmul (P := P) I).neg_mem hpI using 1; abel
  · intro z hz
    obtain ⟨k, rfl⟩ := hz
    obtain ⟨k, rfl⟩ := Submodule.Quotient.mk_surjective (kernelSmul (P := P) I φ) k
    show (presentationQuotientMap I φ) ((kernelQuotientIncl I φ) (Submodule.Quotient.mk k)) = 0
    show (Submodule.Quotient.mk (φ (k : P)) : B' ⧸ targetSmul (B' := B') I) = 0
    have hk : φ (k : P) = 0 := RingHom.mem_ker.mp k.property
    rw [hk]
    rfl
private lemma kernelQuotient_lTensor_injective
    (hflat : Module.Flat (B ⧸ I) (B' ⧸ targetSmul (B' := B') I))
    (hφ : Function.Surjective φ)
    (hInter : ∀ (x : (RingHom.ker φ.toRingHom).restrictScalars B),
      (x : P) ∈ presentationSmul (P := P) I → x ∈ kernelSmul (P := P) I φ)
    (N : Type w) [AddCommGroup N] [Module (B ⧸ I) N] :
    Function.Injective (LinearMap.lTensor N (kernelQuotientIncl I φ)) := by
  let : Module.Flat (B ⧸ I) (B' ⧸ targetSmul (B' := B') I) := hflat
  exact (flat_tor_zero (kernelQuotientIncl I φ) (presentationQuotientMap I φ)
    (kernelQuotientIncl_injective I φ hInter) (kernelQuotient_exact I φ hφ)
    (presentationQuotientMap_surjective I φ hφ)).1

private noncomputable def tensorQuotEquiv (M : Type u) [AddCommGroup M] [Module B M]
    (N : Type w) [AddCommGroup N] [Module B N] [Module (B ⧸ I) N] [IsScalarTower B (B ⧸ I) N] :
    N ⊗[B] M ≃ₗ[B ⧸ I] N ⊗[B ⧸ I] (M ⧸ I • (⊤ : Submodule B M)) :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange B (B ⧸ I) (B ⧸ I) N M).symm.trans
    (LinearEquiv.lTensor N (quotTensorRIEquiv I))
private lemma tensorQuotEquiv_tmul (M : Type u) [AddCommGroup M] [Module B M]
    (N : Type w) [AddCommGroup N] [Module B N] [Module (B ⧸ I) N] [IsScalarTower B (B ⧸ I) N]
    (n : N) (m : M) :
    tensorQuotEquiv I M N (n ⊗ₜ[B] m) = n ⊗ₜ[B ⧸ I] (Submodule.Quotient.mk m) := by
  simp only [tensorQuotEquiv, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    LinearEquiv.lTensor_tmul]
  show n ⊗ₜ[B ⧸ I] ((TensorProduct.quotTensorEquivQuotSMul _ I)
      (1 ⊗ₜ[B] m)) = _
  rw [show (1 : B ⧸ I) = Ideal.Quotient.mk I 1 from rfl,
    TensorProduct.quotTensorEquivQuotSMul_mk_tmul, one_smul]
private lemma presentationKernel_tensor_injective
    (hflat : Module.Flat (B ⧸ I) (B' ⧸ targetSmul (B' := B') I))
    (hφ : Function.Surjective φ)
    (hInter : ∀ (x : (RingHom.ker φ.toRingHom).restrictScalars B),
      (x : P) ∈ presentationSmul (P := P) I → x ∈ kernelSmul (P := P) I φ)
    (N : Type w) [AddCommGroup N] [Module B N]
    (hkill : I • (⊤ : Submodule B N) = ⊥) :
    Function.Injective (LinearMap.lTensor N (presentationKernelIncl φ)) := by
  have htor : Module.IsTorsionBySet B N (I : Set B) := by
    intro n r
    have hmem : (r : B) • n ∈ I • (⊤ : Submodule B N) :=
      Submodule.smul_mem_smul r.2 Submodule.mem_top
    rw [hkill] at hmem
    simpa using hmem
  let : Module (B ⧸ I) N := htor.module
  have hST : IsScalarTower B (B ⧸ I) N := by
    refine ⟨fun r x n => ?_⟩
    obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [show (Ideal.Quotient.mk I r' : B ⧸ I) • n = r' • n from rfl,
      ← smul_assoc]
    rfl
  let : IsScalarTower B (B ⧸ I) N := hST
  have hnat : ∀ t : N ⊗[B] ((RingHom.ker φ.toRingHom).restrictScalars B),
      tensorQuotEquiv I P N
          ((LinearMap.lTensor N (presentationKernelIncl φ)) t) =
        (LinearMap.lTensor N (kernelQuotientIncl I φ)) (tensorQuotEquiv I _ N t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul n k =>
      simp only [LinearMap.lTensor_tmul, tensorQuotEquiv_tmul]
      rfl
  intro x y hxy
  apply (tensorQuotEquiv I _ N).injective
  apply kernelQuotient_lTensor_injective I φ hflat hφ hInter N
  calc
    (LinearMap.lTensor N (kernelQuotientIncl I φ)) (tensorQuotEquiv I _ N x) =
      tensorQuotEquiv I P N
        ((LinearMap.lTensor N (presentationKernelIncl φ)) x) := (hnat x).symm
    _ = tensorQuotEquiv I P N
        ((LinearMap.lTensor N (presentationKernelIncl φ)) y) := congrArg _ hxy
    _ = (LinearMap.lTensor N (kernelQuotientIncl I φ)) (tensorQuotEquiv I _ N y) := hnat y

end LargeUniverseTensorKernel

/-- Divided powers extend to the polynomial stage of a base change. -/
private lemma polynomialStageExtends (f : A →+* B) (J : Ideal B)
    (hJ : A.ideal.map f ≤ J) (D : DividedPowerEnvelope A f J hJ)
    [Algebra B D.object]
    (P : Type u) [CommRing P] [Algebra B P] [Module.Free B P] :
    DividedPowers.Extends D.object.dividedPowers
      (algebraMap D.object (D.object ⊗[B] P)) := by
  let : Module.Flat B P := Module.Flat.of_free
  let : Module.Flat D.object (D.object ⊗[B] P) :=
    Module.Flat.baseChange B D.object P
  exact DividedPowers.DividedPowerRing.dividedPowers_extends_of_map_eq_bot_or_isPrincipal_or_flat
    D.object (algebraMap D.object (D.object ⊗[B] P))
    (Or.inr (Or.inr ((RingHom.flat_algebraMap_iff).2 inferInstance)))

/-- An injective tensor map on a quotient identifies the intersection of the two
tensor-image submodules with the image of the tensor of both submodules. -/
private lemma tensor_range_intersection_le {R P : Type u} {M : Type max u v} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    (N : Submodule R M) (K : Submodule R P)
    (hβ : Function.Injective (LinearMap.lTensor (M ⧸ N) K.subtype)) :
    (LinearMap.rTensor P N.subtype).range ⊓
        (LinearMap.lTensor M K.subtype).range ≤
      ((LinearMap.lTensor M K.subtype).comp
        (LinearMap.rTensor K N.subtype)).range := by
  intro z hz
  obtain ⟨t, rfl⟩ := hz.2
  have hzero : (LinearMap.rTensor P N.mkQ)
      ((LinearMap.lTensor M K.subtype) t) = 0 := by
    have hker : (LinearMap.lTensor M K.subtype) t ∈
        (LinearMap.rTensor P N.mkQ).ker := by
      rw [rTensor_mkQ]
      exact hz.1
    exact LinearMap.mem_ker.mp hker
  have hcomm : (LinearMap.rTensor P N.mkQ).comp
      (LinearMap.lTensor M K.subtype) =
      (LinearMap.lTensor (M ⧸ N) K.subtype).comp
        (LinearMap.rTensor K N.mkQ) := by
    simp
  have hzeroβ : (LinearMap.lTensor (M ⧸ N) K.subtype)
      ((LinearMap.rTensor K N.mkQ) t) = 0 := by
    have ht := congrArg (fun h : M ⊗[R] K →ₗ[R] (M ⧸ N) ⊗[R] P => h t) hcomm
    exact ht.symm.trans hzero
  have htzero : (LinearMap.rTensor K N.mkQ) t = 0 :=
    hβ (by simpa only [map_zero] using hzeroβ)
  have htrange : t ∈ (LinearMap.rTensor K N.subtype).range := by
    rw [← rTensor_mkQ]
    exact LinearMap.mem_ker.mpr htzero
  obtain ⟨s, rfl⟩ := htrange
  exact ⟨s, rfl⟩

/-- The base ideal annihilates the envelope quotient as a module, without choosing
a ring structure on that quotient. -/
private lemma baseIdeal_smul_envelope_module_quotient_eq_bot
    (f : A →+* B) (J : Ideal B) (hJ : A.ideal.map f ≤ J)
    (D : DividedPowerEnvelope A f J hJ) :
    letI : Algebra B D.object := D.algebraMap.toRingHom.toAlgebra;
    (A.ideal.map f) •
      (⊤ : Submodule B (D.object ⧸ D.object.ideal.restrictScalars B)) = ⊥ := by
  let : Algebra B D.object := D.algebraMap.toRingHom.toAlgebra
  apply le_antisymm _ bot_le
  apply (Submodule.smul_le).mpr
  intro a ha q _
  obtain ⟨d, rfl⟩ :=
    Submodule.Quotient.mk_surjective
      (D.object.ideal.restrictScalars B : Submodule B D.object) q
  show a • (Submodule.Quotient.mk d :
    D.object ⧸ D.object.ideal.restrictScalars B) = 0
  rw [← Submodule.Quotient.mk_smul]
  apply (Submodule.Quotient.mk_eq_zero
    (D.object.ideal.restrictScalars B : Submodule B D.object)).mpr
  show a • d ∈ D.object.ideal
  rw [Algebra.smul_def]
  exact D.object.ideal.mul_mem_right d
    (D.algebraMap.ideal_comp (Ideal.mem_map_of_mem D.algebraMap.toRingHom
      (hJ ha)))

/-- The intersection used in descent comes from the tensor product of the two ideals. -/
private lemma envelope_tensor_range_intersection_le [Algebra B B']
    {A : DividedPowerRing.{max u v}}
    (f : A →+* B) (J : Ideal B) (hJ : A.ideal.map f ≤ J)
    (D : DividedPowerEnvelope A f J hJ)
    (hflat : Module.Flat (B ⧸ A.ideal.map f)
      (B' ⧸ (A.ideal.map f).map (algebraMap B B')))
    (hTor : IsZero (((Tor' (ModuleCat.{u} B) 1).obj (ModuleCat.of B B')).obj
      (ModuleCat.of B (B ⧸ A.ideal.map f))))
    {P : Type u} [CommRing P] [Algebra B P] [Algebra P B']
    [IsScalarTower B P B'] (φ : P →ₐ[B] B')
    (hφ : Function.Surjective φ) :
    letI : Algebra B D.object := D.algebraMap.toRingHom.toAlgebra;
    let N := D.object.ideal.restrictScalars B;
    let K := (RingHom.ker φ.toRingHom).restrictScalars B;
    (LinearMap.rTensor P N.subtype).range ⊓
        (LinearMap.lTensor D.object K.subtype).range ≤
      ((LinearMap.lTensor D.object K.subtype).comp
        (LinearMap.rTensor K N.subtype)).range := by
  let : Algebra B D.object := D.algebraMap.toRingHom.toAlgebra
  let N := D.object.ideal.restrictScalars B
  let K := (RingHom.ker φ.toRingHom).restrictScalars B
  let I := A.ideal.map f
  have hflat' : Module.Flat (B ⧸ I)
      (B' ⧸ (I • (⊤ : Submodule B B'))) :=
    (flat_quotient_smul_top_iff I).2 hflat
  have hInter : ∀ x : K, (x : P) ∈ presentationSmul (P := P) I →
      x ∈ kernelSmul (P := P) I φ := by
    intro x hx
    apply kernel_intersection_smul I φ hφ hTor x.property
    change (x : P) ∈ I • (⊤ : Submodule B P) at hx
    rwa [Ideal.smul_top_eq_map] at hx
  have hkill : I •
      (⊤ : Submodule B (D.object ⧸ D.object.ideal.restrictScalars B)) = ⊥ :=
    baseIdeal_smul_envelope_module_quotient_eq_bot f J hJ D
  have hβ : Function.Injective (LinearMap.lTensor
      (D.object ⧸ N) K.subtype) :=
    presentationKernel_tensor_injective I φ hflat' hφ hInter _ hkill
  exact tensor_range_intersection_le N K hβ

/-- A tensor of elements of two ideals lies in the product of their extensions to a
tensor product algebra. -/
private lemma tensor_ideal_range_le_prod {R Y : Type u} {X : Type max u v} [CommRing R]
    [CommRing X] [CommRing Y] [Algebra R X] [Algebra R Y]
    (I : Ideal X) (K : Ideal Y) :
    ((LinearMap.lTensor X (K.restrictScalars R).subtype).comp
      (LinearMap.rTensor (K.restrictScalars R) (I.restrictScalars R).subtype)).range ≤
      ((I.map (Algebra.TensorProduct.includeLeftRingHom : X →+* X ⊗[R] Y)) •
        (K.map (Algebra.TensorProduct.includeRight : Y →ₐ[R] X ⊗[R] Y))).restrictScalars R := by
  intro z hz
  obtain ⟨t, rfl⟩ := hz
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add t s ht hs => simpa only [map_add] using add_mem ht hs
  | tmul x y =>
    simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul,
      LinearMap.lTensor_tmul]
    have hx : Algebra.TensorProduct.includeLeftRingHom (x : X) ∈
        I.map (Algebra.TensorProduct.includeLeftRingHom : X →+* X ⊗[R] Y) :=
      Ideal.mem_map_of_mem _ x.property
    have hy : Algebra.TensorProduct.includeRight (y : Y) ∈
        K.map (Algebra.TensorProduct.includeRight : Y →ₐ[R] X ⊗[R] Y) :=
      Ideal.mem_map_of_mem _ y.property
    have hprod := Ideal.mul_mem_mul hx hy
    show (x : X) ⊗ₜ[R] (y : Y) ∈
      (I.map (Algebra.TensorProduct.includeLeftRingHom : X →+* X ⊗[R] Y)) •
        (K.map (Algebra.TensorProduct.includeRight : Y →ₐ[R] X ⊗[R] Y))
    rw [Ideal.smul_eq_mul]
    simpa only [Algebra.TensorProduct.includeLeftRingHom_apply,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, one_mul] using hprod

/-- The kernel of the tensor presentation meets the extended divided power ideal only in
the product of that ideal with the extended presentation kernel. -/
private lemma envelope_tensor_kernel_intersection_le_prod [Algebra B B']
    {A : DividedPowerRing.{max u v}}
    (f : A →+* B) (J : Ideal B) (hJ : A.ideal.map f ≤ J)
    (D : DividedPowerEnvelope A f J hJ)
    (hflat : Module.Flat (B ⧸ A.ideal.map f)
      (B' ⧸ (A.ideal.map f).map (algebraMap B B')))
    (hTor : IsZero (((Tor' (ModuleCat.{u} B) 1).obj (ModuleCat.of B B')).obj
      (ModuleCat.of B (B ⧸ A.ideal.map f))))
    {P : Type u} [CommRing P] [Algebra B P] [Algebra P B']
    [IsScalarTower B P B'] (φ : P →ₐ[B] B')
    (hφ : Function.Surjective φ) :
    letI : Algebra B D.object := D.algebraMap.toRingHom.toAlgebra;
    (RingHom.ker (Algebra.TensorProduct.lTensor (S := B) D.object φ).toRingHom ⊓
      D.object.ideal.map
        (Algebra.TensorProduct.includeLeftRingHom : D.object →+* D.object ⊗[B] P)) ≤
      (D.object.ideal.map
        (Algebra.TensorProduct.includeLeftRingHom : D.object →+* D.object ⊗[B] P)) •
        ((RingHom.ker φ).map
          (Algebra.TensorProduct.includeRight : P →ₐ[B] D.object ⊗[B] P)) := by
  let : Algebra B D.object := D.algebraMap.toRingHom.toAlgebra
  let N := D.object.ideal.restrictScalars B
  let K := (RingHom.ker φ).restrictScalars B
  intro x hx
  have hxN : x ∈ (LinearMap.rTensor P N.subtype).range := by
    rw [← Ideal.map_includeLeft_eq D.object.ideal]
    exact hx.2
  have hxK : x ∈ (LinearMap.lTensor D.object K.subtype).range := by
    have hker : x ∈ (RingHom.ker φ).map
        (Algebra.TensorProduct.includeRight : P →ₐ[B] D.object ⊗[B] P) := by
      rw [← Algebra.TensorProduct.lTensor_ker φ hφ]
      exact hx.1
    change x ∈ ((RingHom.ker φ).map
      (Algebra.TensorProduct.includeRight : P →ₐ[B] D.object ⊗[B] P)).restrictScalars B at hker
    simpa only [Ideal.map_includeRight_eq] using hker
  have hx' := envelope_tensor_range_intersection_le f J hJ D hflat hTor φ hφ
    ⟨hxN, hxK⟩
  exact tensor_ideal_range_le_prod D.object.ideal (RingHom.ker φ) hx'

/-- The divided powers at the polynomial stage preserve the part of the presentation
kernel lying in the extended divided power ideal. -/
private lemma envelope_tensor_kernel_isSubDPIdeal [Algebra B B']
    {A : DividedPowerRing.{max u v}}
    (f : A →+* B) (J : Ideal B) (hJ : A.ideal.map f ≤ J)
    (D : DividedPowerEnvelope A f J hJ)
    (hflat : Module.Flat (B ⧸ A.ideal.map f)
      (B' ⧸ (A.ideal.map f).map (algebraMap B B')))
    (hTor : IsZero (((Tor' (ModuleCat.{u} B) 1).obj (ModuleCat.of B B')).obj
      (ModuleCat.of B (B ⧸ A.ideal.map f))))
    {P : Type u} [CommRing P] [Algebra B P] [Algebra P B']
    [IsScalarTower B P B'] (φ : P →ₐ[B] B')
    (hφ : Function.Surjective φ) :
    letI : Algebra B D.object := D.algebraMap.toRingHom.toAlgebra;
    ∀ δ : DividedPowers
      (D.object.ideal.map
        (Algebra.TensorProduct.includeLeftRingHom :
          D.object →+* D.object ⊗[B] P)),
    δ.IsSubDPIdeal
      (RingHom.ker (Algebra.TensorProduct.lTensor (S := B) D.object φ).toRingHom ⊓
        D.object.ideal.map
          (Algebra.TensorProduct.includeLeftRingHom :
            D.object →+* D.object ⊗[B] P)) := by
  let : Algebra B D.object := D.algebraMap.toRingHom.toAlgebra
  intro δ
  let Istage := D.object.ideal.map
    (Algebra.TensorProduct.includeLeftRingHom : D.object →+* D.object ⊗[B] P)
  let Kstage := (RingHom.ker φ).map
    (Algebra.TensorProduct.includeRight : P →ₐ[B] D.object ⊗[B] P)
  have hle : RingHom.ker
      (Algebra.TensorProduct.lTensor (S := B) D.object φ).toRingHom ⊓ Istage ≤
      Istage • Kstage :=
    envelope_tensor_kernel_intersection_le_prod f J hJ D hflat hTor φ hφ
  have hK : Kstage = RingHom.ker
      (Algebra.TensorProduct.lTensor (S := B) D.object φ).toRingHom :=
    (Algebra.TensorProduct.lTensor_ker φ hφ).symm
  have heq : RingHom.ker
      (Algebra.TensorProduct.lTensor (S := B) D.object φ).toRingHom ⊓ Istage =
      Istage • Kstage := by
    apply le_antisymm hle
    rw [Ideal.smul_eq_mul, hK]
    exact le_inf Ideal.mul_le_right Ideal.mul_le_left
  rw [heq]
  exact (DividedPowers.SubDPIdeal.prod (hI := δ) Kstage).toIsSubDPIdeal

/-- A free presentation of the new base lets divided powers descend to the tensor product. -/
private lemma envelope_tensor_extends_of_free_presentation [Algebra B B']
    {A : DividedPowerRing.{max u v}}
    (f : A →+* B) (J : Ideal B) (hJ : A.ideal.map f ≤ J)
    (D : DividedPowerEnvelope A f J hJ)
    (hflat : Module.Flat (B ⧸ A.ideal.map f)
      (B' ⧸ (A.ideal.map f).map (algebraMap B B')))
    (hTor : IsZero (((Tor' (ModuleCat.{u} B) 1).obj (ModuleCat.of B B')).obj
      (ModuleCat.of B (B ⧸ A.ideal.map f))))
    {P : Type u} [CommRing P] [Algebra B P] [Module.Free B P]
    [Algebra P B'] [IsScalarTower B P B']
    (φ : P →ₐ[B] B') (hφ : Function.Surjective φ) :
    letI : Algebra B D.object := D.algebraMap.toRingHom.toAlgebra;
    DividedPowers.Extends D.object.dividedPowers
      (algebraMap D.object (D.object ⊗[B] B')) := by
  let : Algebra B D.object := D.algebraMap.toRingHom.toAlgebra
  obtain ⟨δP, hδP⟩ := polynomialStageExtends f J hJ D P
  let ψ := Algebra.TensorProduct.lTensor (S := B) D.object φ
  have hψ : Function.Surjective ψ :=
    Algebra.TensorProduct.map_surjective (AlgHom.id B D.object) φ
      (fun x => ⟨x, rfl⟩) hφ
  have hcomm : ψ.toRingHom.comp
      (algebraMap D.object (D.object ⊗[B] P)) =
      algebraMap D.object (D.object ⊗[B] B') := by
    ext x
    simp [ψ, Algebra.TensorProduct.lTensor]
  have hIJ : D.object.ideal.map (algebraMap D.object (D.object ⊗[B] B')) =
      (D.object.ideal.map (algebraMap D.object (D.object ⊗[B] P))).map
        ψ.toRingHom := by
    rw [Ideal.map_map, hcomm]
  have hSub : δP.IsSubDPIdeal
      (RingHom.ker ψ.toRingHom ⊓
        D.object.ideal.map (algebraMap D.object (D.object ⊗[B] P))) :=
    envelope_tensor_kernel_isSubDPIdeal f J hJ D hflat hTor φ hφ δP
  let δ' := DividedPowers.Quotient.OfSurjective.dividedPowers δP hψ hIJ hSub
  have hδ' : δP.IsDPMorphism δ' ψ.toRingHom :=
    DividedPowers.Quotient.OfSurjective.isDPMorphism δP hψ hIJ hSub
  refine ⟨δ', ?_⟩
  have hcomp := hδ'.comp δ' hδP
  simpa only [hcomm] using hcomp

/-- Divided powers on the envelope extend to the tensor product under the two flatness
hypotheses. -/
private lemma envelope_tensor_extends [Algebra B B']
    {A : DividedPowerRing.{max u v}}
    (f : A →+* B) (J : Ideal B) (hJ : A.ideal.map f ≤ J)
    (D : DividedPowerEnvelope A f J hJ)
    (hflat : Module.Flat (B ⧸ A.ideal.map f)
      (B' ⧸ (A.ideal.map f).map (algebraMap B B')))
    (hTor : IsZero (((Tor' (ModuleCat.{u} B) 1).obj (ModuleCat.of B B')).obj
      (ModuleCat.of B (B ⧸ A.ideal.map f)))) :
    letI : Algebra B D.object := D.algebraMap.toRingHom.toAlgebra;
    DividedPowers.Extends D.object.dividedPowers
      (algebraMap D.object (D.object ⊗[B] B')) := by
  let : Algebra B D.object := D.algebraMap.toRingHom.toAlgebra
  let P := MvPolynomial B' B
  let φ : P →ₐ[B] B' := MvPolynomial.aeval id
  have hφ : Function.Surjective φ := by
    intro y
    exact ⟨MvPolynomial.X y, MvPolynomial.aeval_X id y⟩
  let : Algebra P B' := φ.toRingHom.toAlgebra
  have hcomp : algebraMap B B' =
      (algebraMap P B').comp (algebraMap B P) := by
    ext b
    show algebraMap B B' b = φ (MvPolynomial.C b)
    exact (MvPolynomial.aeval_C id b).symm
  let : IsScalarTower B P B' := IsScalarTower.of_algebraMap_eq' hcomp
  exact envelope_tensor_extends_of_free_presentation f J hJ D hflat hTor φ hφ

end BaseChange

end Crystalline

end

module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import StacksFrontier.Algebra.Module.IPowerTorsion
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingEquivalence
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingFlatIsomorphism
public import StacksFrontier.RingTheory.Localization.Glueing.IdealPowerTorsion

/-!
# Power torsion and finiteness along an adic completion

Let `R` be a ring, `I ⊆ R` an ideal and `S` an `R`-algebra. This module collects facts about
`I`-power torsion, about finiteness after restricting scalars along `R → S`, and about the
identification of `ModuleCat.extendScalars` with the tensor product `S ⊗[R] M`.

## Main results

* `isIPowerTorsion_of_linearEquiv`, `isIPowerTorsion_restrictScalars_of_map`: transport of the
  power-torsion property along a linear equivalence and along restriction of scalars.
* `extendScalarsTensorEquiv`: the `S`-linear equivalence between `S ⊗[R] M` and the extension of
  scalars of an `R`-module `M`.
* `finite_restrictScalars_of_annihilated`, `finite_quotient_of_quotientMap_surjective`: finiteness
  over `R` of an `S`-module annihilated by a power of the extended ideal.
* `map_kernel_cokernel_isIPowerTorsion`: power torsion of the kernel and the cokernel passes from
  a map of `S`-modules to a map of `R`-modules with the same kernel and cokernel after restricting
  scalars.
-/

universe u v w

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct
open scoped ChangeOfRings

namespace Stacks.AdicCompletion.FiniteModule

/-- Power torsion is invariant under a linear equivalence. -/
public theorem isIPowerTorsion_of_linearEquiv
    {R : Type u} [CommRing R] {M N : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (I : Ideal R) (e : M ≃ₗ[R] N) (hM : IsIPowerTorsion R M I) :
    IsIPowerTorsion R N I := by
  intro x
  obtain ⟨n, hn, hx⟩ := hM (e.symm x)
  refine ⟨n, hn, fun a ha => ?_⟩
  simpa using congrArg e (hx a ha)

/-- Power torsion for an extended ideal descends to power torsion for the original ideal after
restricting scalars. -/
public theorem isIPowerTorsion_restrictScalars_of_map
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {M : Type w} [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] (I : Ideal R)
    (hM : IsIPowerTorsion S M (I.map (algebraMap R S))) :
    IsIPowerTorsion R M I := by
  intro x
  obtain ⟨n, hn, hx⟩ := hM x
  refine ⟨n, hn, fun r hr => ?_⟩
  rw [← IsScalarTower.algebraMap_smul S r x]
  exact hx _ (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem (algebraMap R S) hr)

/-- On a finite module, elementwise power torsion has a uniform exponent. -/
public theorem ideal_smul_eq_bot_of_finite_power_torsion
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : IsIPowerTorsion R M I) :
    ∃ n : ℕ, I ^ n • (⊤ : Submodule R M) = ⊥ := by
  have hsupp := support_subset_zeroLocus_of_isIPowerTorsion hM
  rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff] at hsupp
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hsupp hI
  refine ⟨n, le_antisymm (Submodule.smul_le.mpr fun a ha m _ => ?_) bot_le⟩
  simpa using (Module.mem_annihilator.mp (hn ha)) m

/-- The underlying module of `ModuleCat.extendScalars` is the tensor product `S ⊗[R] M`. -/
public noncomputable def extendScalarsTensorEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (M : ModuleCat.{w} R) :
    TensorProduct R S M ≃ₗ[S]
      (ModuleCat.extendScalars.{u, v, w} (algebraMap R S)).obj M := by
  let S' := (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)
  let eS : S ≃ₗ[S] S' :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  letI : IsScalarTower R S S' := ⟨by
    intro r s x
    rw [Algebra.smul_def]
    have hs : r • (s • x) = algebraMap R S r • (s • x) :=
      ModuleCat.restrictScalars.smul_def (algebraMap R S) r (s • x)
    rw [hs, mul_smul]⟩
  exact TensorProduct.AlgebraTensorModule.congr eS (LinearEquiv.refl R M)

/-- `extendScalarsTensorEquiv` sends `s ⊗ₜ m` to `s ⊗ₜ m`. -/
public lemma extendScalarsTensorEquiv_tmul
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (M : ModuleCat.{w} R) (s : S) (m : M) :
    extendScalarsTensorEquiv (S := S) M (s ⊗ₜ[R] m) = s ⊗ₜ[R, algebraMap R S] m :=
  rfl

/-- Extension of scalars of a map is base change of the corresponding linear map. -/
public lemma extendScalarsTensorEquiv_map
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {M N : ModuleCat.{w} R} (ψ : M ⟶ N) (x : TensorProduct R S M) :
    (ModuleCat.extendScalars.{u, v, w} (algebraMap R S)).map ψ
        (extendScalarsTensorEquiv M x) =
      extendScalarsTensorEquiv N (LinearMap.baseChange S ψ.hom x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
    rw [extendScalarsTensorEquiv_tmul, LinearMap.baseChange_tmul,
      extendScalarsTensorEquiv_tmul]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- A finite `S`-module killed by an ideal `J` of `S` is a finite `R`-module when `S ⧸ J` is a
finite `R`-module. -/
public theorem finite_restrictScalars_of_annihilated
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {M : Type w} [AddCommGroup M] [Module S M] [Module.Finite S M]
    (J : Ideal S) (hJ : J • (⊤ : Submodule S M) = ⊥)
    [Module.Finite R (S ⧸ J)] :
    let : Module R M := Module.compHom M (algebraMap R S)
    Module.Finite R M := by
  let : Module R M := Module.compHom M (algebraMap R S)
  have hkill : Module.IsTorsionBySet S M J := by
    intro x a
    have hmem : (a : S) • x ∈ J • (⊤ : Submodule S M) :=
      Submodule.smul_mem_smul a.property Submodule.mem_top
    rw [hJ] at hmem
    simpa using hmem
  let : Module (S ⧸ J) M := hkill.module
  let : IsScalarTower S (S ⧸ J) M :=
    IsScalarTower.of_algebraMap_smul fun s m => by
      show (Ideal.Quotient.mk J s) • m = s • m
      exact hkill.mk_smul s m
  let : IsScalarTower R (S ⧸ J) M :=
    IsScalarTower.of_algebraMap_smul fun r m => by
      show (Ideal.Quotient.mk J (algebraMap R S r)) • m = r • m
      rw [hkill.mk_smul]
      rfl
  let : Module.Finite (S ⧸ J) M := Module.Finite.of_restrictScalars_finite S (S ⧸ J) M
  exact Module.Finite.trans (S ⧸ J) M

/-- If `R → S` is surjective modulo an ideal, then `S` modulo the extended ideal is a finite
`R`-module. -/
public theorem finite_quotient_of_quotientMap_surjective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R)
    (hq : Function.Surjective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map)) :
    Module.Finite R (S ⧸ I.map (algebraMap R S)) := by
  have hsurj : Function.Surjective (algebraMap R (S ⧸ I.map (algebraMap R S))) := by
    intro x
    obtain ⟨y, hy⟩ := hq x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨r, hy⟩
  exact Module.Finite.of_surjective (Algebra.linearMap R _) hsurj

/-- A flat map which is an isomorphism modulo `I` is still surjective on quotients by every power
of `I`. -/
public theorem quotientMap_pow_surjective_of_flat
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (n : ℕ) :
    Function.Surjective
      (Ideal.quotientMap ((I ^ n).map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map) := by
  have ht : IsIPowerTorsion R (R ⧸ I ^ n) I := by
    intro x
    refine ⟨n + 1, Nat.succ_pos _, fun a ha => ?_⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    show Ideal.Quotient.mk (I ^ n) (a * b) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      ((I ^ n).mul_mem_right b (Ideal.pow_le_pow_right (Nat.le_succ n) ha))
  have hunit :=
    (IPowerTorsion.baseChange_bijective_iff_quotientMap_bijective
      R S I hflat).mpr hq (R ⧸ I ^ n) ht
  let E := Algebra.TensorProduct.quotIdealMapEquivQuotTensor S (I ^ n)
  have heq (x : R ⧸ I ^ n) :
      E (Ideal.quotientMap ((I ^ n).map (algebraMap R S))
          (algebraMap R S) Ideal.le_comap_map x) =
        ((TensorProduct.mk R (R ⧸ I ^ n) S).flip 1) x := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact E.commutes _
  intro z
  obtain ⟨x, hx⟩ := hunit.2 (E z)
  exact ⟨x, E.injective ((heq x).trans hx)⟩

/-- Power torsion of an `S`-module for the extended ideal transfers to any `R`-module identified
with it after restricting scalars. -/
private theorem isIPowerTorsion_of_restrictScalars_iso
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) {M' : ModuleCat.{w} S} {N : ModuleCat.{w} R}
    (e : (ModuleCat.restrictScalars.{w} (algebraMap R S)).obj M' ≅ N)
    (h : IsIPowerTorsion S M' (I.map (algebraMap R S))) :
    IsIPowerTorsion R N I := by
  let Mbase := (ModuleCat.restrictScalars.{w} (algebraMap R S)).obj M'
  let : Module R Mbase := Mbase.isModule
  let : Module S Mbase := M'.isModule
  let : IsScalarTower R S Mbase :=
    IsScalarTower.of_algebraMap_smul fun r x => by
      rw [ModuleCat.restrictScalars.smul_def]
      rfl
  exact isIPowerTorsion_of_linearEquiv I e.toLinearEquiv
    (isIPowerTorsion_restrictScalars_of_map I h)

/-- Let `φ` be a map of `S`-modules and `ψ` a map of `R`-modules whose kernel and cokernel are
identified with those of `φ` after restricting scalars. If the kernel and the cokernel of `φ` are
`I S`-power torsion, then the kernel and the cokernel of `ψ` are `I`-power torsion. -/
public theorem map_kernel_cokernel_isIPowerTorsion
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) {M N : ModuleCat.{w} R} {M' N' : ModuleCat.{w} S}
    (φ : M' ⟶ N') (ψ : M ⟶ N)
    (eK : (ModuleCat.restrictScalars.{w} (algebraMap R S)).obj (kernel φ) ≅ kernel ψ)
    (eC : (ModuleCat.restrictScalars.{w} (algebraMap R S)).obj (cokernel φ) ≅ cokernel ψ)
    (hK : IsIPowerTorsion S (↥(kernel φ : ModuleCat.{w} S)) (I.map (algebraMap R S)))
    (hC : IsIPowerTorsion S (↥(cokernel φ : ModuleCat.{w} S)) (I.map (algebraMap R S))) :
    IsIPowerTorsion R (↥(kernel ψ : ModuleCat.{w} R)) I ∧
      IsIPowerTorsion R (↥(cokernel ψ : ModuleCat.{w} R)) I := by
  exact ⟨isIPowerTorsion_of_restrictScalars_iso I eK hK,
    isIPowerTorsion_of_restrictScalars_iso I eC hC⟩

end Stacks.AdicCompletion.FiniteModule

module

import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.ENatToNat
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Algebra.Polynomial.Module.TensorProduct

public import StacksFrontier.RingTheory.Sequence.BaseChange
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.CohenMacaulay.Module
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.Depth.RingEquiv
public import StacksFrontier.RingTheory.Depth.AlgebraMap
public import StacksFrontier.RingTheory.Depth.Nakayama
public import StacksFrontier.Algebra.Module.LocalizedEquiv
public import StacksFrontier.RingTheory.CohenMacaulay.Support
import StacksFrontier.RingTheory.Flat.LocalCriteria

/-!
# Cohen–Macaulayness ascends along a polynomial extension

Let `R` be a Noetherian ring and `M` a finite Cohen–Macaulay `R`-module, that is, one whose
localization at every prime `𝔭` of its support satisfies `depth(M_𝔭) = dim Supp(M_𝔭)`. Then the
base change of `M` to a polynomial ring `R[x_i : i ∈ σ]` in finitely many variables is a
Cohen–Macaulay module over `R[x_i : i ∈ σ]`. Taking `M = R`, a polynomial algebra in finitely
many variables over a Noetherian Cohen–Macaulay ring is Cohen–Macaulay.

The proof is an induction on the number of variables, which reduces the statement to one variable.
For a prime `𝔮` of `A[X]` with `𝔭 = 𝔮 ∩ A`, the localization `M[X]_𝔮` is a localization of
`M_𝔭[X]`, and a maximal `M_𝔭`-regular sequence `f_1, …, f_d` in `𝔭` stays regular on it by
flatness. If `𝔮 = 𝔭A[X]`, the quotient by `f_1, …, f_d` is supported at `𝔮` alone. Otherwise `𝔮`
contains a polynomial `g` with a coefficient outside `𝔭` and all higher coefficients in `𝔭`; it
acts regularly on that quotient, and the quotient by `f_1, …, f_d, g` is supported at `𝔮` alone,
because the fibers of `Spec A[X] → Spec A` have dimension at most one. In both cases the sequence
has length `dim Supp(M[X]_𝔮)`.

## Main results

* `Module.IsCohenMacaulay.mvPolynomial_of_isBaseChange`: the base change of a finite
  Cohen–Macaulay module over a Noetherian ring to a polynomial ring in finitely many variables is
  Cohen–Macaulay.
* `Module.IsMaximalCohenMacaulay.of_isLocalization_atPrime_mvPolynomial`: every localization at a
  prime of a polynomial algebra in finitely many variables over a Noetherian Cohen–Macaulay ring
  is a Cohen–Macaulay local ring.

## Implementation notes

In `Module.IsCohenMacaulay.mvPolynomial_of_isBaseChange` the base change is presented abstractly,
as an `S`-module `N` with an `R`-linear map `f : M →ₗ[R] N` satisfying `IsBaseChange S f`, for
`S = MvPolynomial σ R` with `σ` an arbitrary finite type. The model `S ⊗[R] M` is the case
`f = TensorProduct.mk R S M 1`, and the ring itself is the case `N = S`,
`f = Algebra.linearMap R S`. Finiteness of `M` is assumed explicitly, since
`Module.IsCohenMacaulay` does not include it; finiteness of `N` over `S` follows from `hf`.

Cohen–Macaulayness of a Noetherian local ring `S` is `Module.IsMaximalCohenMacaulay S S`, and that
of a Noetherian ring is spelled out as a condition on its localizations at primes. In
`Module.IsMaximalCohenMacaulay.of_isLocalization_atPrime_mvPolynomial` the hypothesis is stated at
`Localization.AtPrime p`, and the conclusion at an arbitrary `S` with `IsLocalization.AtPrime S q`.

## References

* [StacksProject 0AAI](https://stacks.math.columbia.edu/tag/0AAI)
* [StacksProject 00ND](https://stacks.math.columbia.edu/tag/00ND)

## Tags

Cohen-Macaulay module, Cohen-Macaulay ring, polynomial ring, base change, depth
-/

@[expose] public section

universe u v

namespace Stacks.CohenMacaulay.PolynomialBaseChange

open TensorProduct

/-- The support of a module only depends on its isomorphism class. -/
private lemma support_eq_of_linearEquiv {A : Type*} [CommRing A] {M N : Type*} [AddCommGroup M]
    [Module A M] [AddCommGroup N] [Module A N] (Φ : M ≃ₗ[A] N) :
    Module.support A M = Module.support A N := by
  ext p
  rw [Module.mem_support_iff, Module.mem_support_iff]
  constructor
  · intro h
    exact (Module.localizedEquiv p.asIdeal.primeCompl Φ).injective.nontrivial
  · intro h
    exact (Module.localizedEquiv p.asIdeal.primeCompl Φ).symm.injective.nontrivial

/-- The dimension of the support of a module only depends on its isomorphism class. -/
private lemma supportDim_eq_of_linearEquiv {A : Type*} [CommRing A] {M N : Type*} [AddCommGroup M]
    [Module A M] [AddCommGroup N] [Module A N] (Φ : M ≃ₗ[A] N) :
    Module.supportDim A M = Module.supportDim A N :=
  Order.krullDim_eq_of_orderIso (Set.orderIsoOfEq _ _ (support_eq_of_linearEquiv Φ))

/-- Cohen–Macaulayness only depends on the isomorphism class of the module. -/
private lemma isCohenMacaulay_of_linearEquiv {A : Type*} [CommRing A] {M N : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] (Φ : M ≃ₗ[A] N)
    (hM : Module.IsCohenMacaulay A M) : Module.IsCohenMacaulay A N := by
  intro p hp
  have hp' : p ∈ Module.support A M := by rwa [support_eq_of_linearEquiv Φ]
  have h := hM p hp'
  rwa [Module.depth_eq_depth_of_linearEquiv _ (Module.localizedEquiv p.asIdeal.primeCompl Φ),
    supportDim_eq_of_linearEquiv (Module.localizedEquiv p.asIdeal.primeCompl Φ)] at h

/-- A bijective algebra map carries the multiplicative set of a prime of the source onto the
multiplicative set of the prime of the target above it. -/
private lemma algebraMapSubmonoid_primeCompl {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (hbij : Function.Bijective (algebraMap A B)) (q : Ideal B) [q.IsPrime] :
    Algebra.algebraMapSubmonoid B (q.comap (algebraMap A B)).primeCompl = q.primeCompl := by
  refine Submonoid.ext fun b => ⟨?_, ?_⟩
  · rintro ⟨a, ha, rfl⟩
    exact fun hb => ha (Ideal.mem_comap.mpr hb)
  · intro hb
    obtain ⟨a, rfl⟩ := hbij.surjective b
    exact ⟨a, fun ha => hb (Ideal.mem_comap.mp ha), rfl⟩

/-- Along a bijective algebra map, the localization of a module at a prime `q` of the target is
also its localization, as a module over the source, at the prime below `q`. -/
private lemma isLocalizedModule_restrictScalars {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (hbij : Function.Bijective (algebraMap A B)) (X : Type*) [AddCommGroup X]
    [Module A X] [Module B X] [IsScalarTower A B X] (q : Ideal B) [q.IsPrime] :
    IsLocalizedModule (q.comap (algebraMap A B)).primeCompl
      ((LocalizedModule.mkLinearMap q.primeCompl X).restrictScalars A) := by
  have :
    IsLocalizedModule (Algebra.algebraMapSubmonoid B (q.comap (algebraMap A B)).primeCompl)
      (LocalizedModule.mkLinearMap q.primeCompl X) := by
    rw [algebraMapSubmonoid_primeCompl hbij]
    infer_instance
  exact IsLocalizedModule.restrictScalars _ _

/-- Along a bijective algebra map, a prime `q` of the target lies in the support of `X` if and only
if the prime below it lies in the support of `X` over the source. -/
private lemma nontrivial_localizedModule_comap_iff {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (hbij : Function.Bijective (algebraMap A B)) (X : Type*) [AddCommGroup X]
    [Module A X] [Module B X] [IsScalarTower A B X] (q : Ideal B) [q.IsPrime] :
    Nontrivial (LocalizedModule (q.comap (algebraMap A B)).primeCompl X) ↔
      Nontrivial (LocalizedModule q.primeCompl X) := by
  have := isLocalizedModule_restrictScalars hbij X q
  have Ψ :=
    IsLocalizedModule.linearEquiv (q.comap (algebraMap A B)).primeCompl
      (LocalizedModule.mkLinearMap (q.comap (algebraMap A B)).primeCompl X)
      ((LocalizedModule.mkLinearMap q.primeCompl X).restrictScalars A)
  exact ⟨fun h => Ψ.injective.nontrivial, fun h => Ψ.symm.injective.nontrivial⟩

/-- The dimension of the support of a module is unchanged by restriction of scalars along a
bijective algebra map. -/
private lemma supportDim_eq_of_bijective_algebraMap {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (hbij : Function.Bijective (algebraMap A B)) (X : Type*) [AddCommGroup X]
    [Module A X] [Module B X] [IsScalarTower A B X] :
    Module.supportDim A X = Module.supportDim B X := by
  have hcoe : ((RingEquiv.ofBijective (algebraMap A B) hbij : A →+* B)) = algebraMap A B := rfl
  set E : PrimeSpectrum B ≃o PrimeSpectrum A :=
    PrimeSpectrum.comapEquiv (RingEquiv.ofBijective (algebraMap A B) hbij).symm with hE
  have hEapply : ∀ q : PrimeSpectrum B, E q = PrimeSpectrum.comap (algebraMap A B) q := by
    intro q
    rw [hE]
    simp only [PrimeSpectrum.comapEquiv_apply, RingEquiv.symm_symm]
    rfl
  have hmem : ∀ q : PrimeSpectrum B, q ∈ Module.support B X ↔ E q ∈ Module.support A X := by
    intro q
    rw [Module.mem_support_iff, Module.mem_support_iff, hEapply q]
    exact (nontrivial_localizedModule_comap_iff hbij X q.asIdeal).symm
  refine
    (Order.krullDim_eq_of_orderIso (α := Module.support B X) (β := Module.support A X) ?_).symm
  refine ⟨⟨fun q => ⟨E q.1, (hmem q.1).mp q.2⟩, fun p => ⟨E.symm p.1, ?_⟩, ?_, ?_⟩, ?_⟩
  · exact (hmem (E.symm p.1)).mpr (by simpa only [E.apply_symm_apply] using p.2)
  · intro q; ext1; simp
  · intro p; ext1; simp
  · intro a b
    simp only [Equiv.coe_fn_mk, ← Subtype.coe_le_coe, E.le_iff_le]

/-- The depth of the localization of a module at a prime is unchanged, along a bijective algebra
map, when computed over the source at the prime below. -/
private lemma depth_localizedModule_eq_of_bijective {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (hbij : Function.Bijective (algebraMap A B)) (X : Type*) [AddCommGroup X]
    [Module A X] [Module B X] [IsScalarTower A B X] (q : Ideal B) [q.IsPrime] :
    Module.depth (Localization.AtPrime (q.comap (algebraMap A B)))
          (IsLocalRing.maximalIdeal (Localization.AtPrime (q.comap (algebraMap A B))))
          (LocalizedModule (q.comap (algebraMap A B)).primeCompl X) =
        Module.depth (Localization.AtPrime q) (IsLocalRing.maximalIdeal (Localization.AtPrime q))
          (LocalizedModule q.primeCompl X) ∧
      Module.supportDim (Localization.AtPrime (q.comap (algebraMap A B)))
          (LocalizedModule (q.comap (algebraMap A B)).primeCompl X) =
        Module.supportDim (Localization.AtPrime q) (LocalizedModule q.primeCompl X) := by
  set p := q.comap (algebraMap A B) with hp
  set e : A ≃+* B := RingEquiv.ofBijective (algebraMap A B) hbij with he
  have hmapmon : Submonoid.map (e : A →* B) p.primeCompl = q.primeCompl :=
    algebraMapSubmonoid_primeCompl hbij q
  set E : Localization.AtPrime p ≃+* Localization.AtPrime q :=
    IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime p) (Localization.AtPrime q) e
      hmapmon with
    hEdef
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    (E : Localization.AtPrime p →+* Localization.AtPrime q).toAlgebra
  let : Module (Localization.AtPrime p) (LocalizedModule q.primeCompl X) :=
    Module.compHom _ (E : Localization.AtPrime p →+* Localization.AtPrime q)
  have htower :
    IsScalarTower (Localization.AtPrime p) (Localization.AtPrime q)
      (LocalizedModule q.primeCompl X) :=
    ⟨fun a b x => mul_smul (E a) b x⟩
  have htower2 : IsScalarTower A (Localization.AtPrime p) (LocalizedModule q.primeCompl X) := by
    refine ⟨fun a r x => ?_⟩
    have hEmap :
      E (algebraMap A (Localization.AtPrime p) a) =
        algebraMap B (Localization.AtPrime q) (algebraMap A B a) := by
      simp [hEdef, he]
    calc
      (a • r) • x = ((algebraMap A (Localization.AtPrime p) a * r)) • x := by rw [Algebra.smul_def]
      _ = (E (algebraMap A (Localization.AtPrime p) a) * E r) • x := by
        show (E (algebraMap A (Localization.AtPrime p) a * r)) • x = _
        rw [map_mul]
      _ = E (algebraMap A (Localization.AtPrime p) a) • (E r • x) := mul_smul _ _ _
      _ = a • (E r • x) := by
        rw [hEmap, IsScalarTower.algebraMap_smul, IsScalarTower.algebraMap_smul]
      _ = a • (r • x) := rfl
  have hbijE :
    Function.Surjective (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) :=
    E.surjective
  have := isLocalizedModule_restrictScalars hbij X q
  have Ψ :
    LocalizedModule p.primeCompl X ≃ₗ[Localization.AtPrime p] LocalizedModule q.primeCompl X :=
    (IsLocalizedModule.isBaseChange p.primeCompl (Localization.AtPrime p)
          (LocalizedModule.mkLinearMap p.primeCompl X)).equiv.symm.trans
      (IsLocalizedModule.isBaseChange p.primeCompl (Localization.AtPrime p)
          ((LocalizedModule.mkLinearMap q.primeCompl X).restrictScalars A)).equiv
  constructor
  · rw [Module.depth_eq_depth_of_linearEquiv _ Ψ, Module.depth_eq_depth_map_algebraMap hbijE]
    congr 1
    have :
      (E : Localization.AtPrime p →+* Localization.AtPrime q) =
        algebraMap (Localization.AtPrime p) (Localization.AtPrime q) :=
      rfl
    rw [← this]
    exact IsLocalRing.map_ringEquiv_maximalIdeal E
  · rw [supportDim_eq_of_linearEquiv Ψ]
    exact supportDim_eq_of_bijective_algebraMap E.bijective _

/-- Cohen–Macaulayness is unchanged by restriction of scalars along a bijective algebra map. -/
private lemma isCohenMacaulay_of_bijective_algebraMap {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (hbij : Function.Bijective (algebraMap A B)) {X : Type*} [AddCommGroup X]
    [Module A X] [Module B X] [IsScalarTower A B X] (hX : Module.IsCohenMacaulay A X) :
    Module.IsCohenMacaulay B X := by
  intro q hq
  have hq' : PrimeSpectrum.comap (algebraMap A B) q ∈ Module.support A X := by
    rw [Module.mem_support_iff]
    rw [Module.mem_support_iff] at hq
    exact (nontrivial_localizedModule_comap_iff hbij X q.asIdeal).mpr hq
  have h := hX _ hq'
  obtain ⟨hdepth, hdim⟩ := depth_localizedModule_eq_of_bijective hbij X q.asIdeal
  rw [← hdepth, ← hdim]
  exact h

/-- Cohen–Macaulayness is carried along a ring isomorphism `e : A ≃+* B` together with an
additive isomorphism `φ : M ≃+ N` semilinear over `e`. -/
private lemma isCohenMacaulay_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N] (φ : M ≃+ N)
    (hφ : ∀ (a : A) (m : M), φ (a • m) = e a • φ m) (hM : Module.IsCohenMacaulay A M) :
    Module.IsCohenMacaulay B N := by
  let : Algebra A B := (e : A →+* B).toAlgebra
  let : Module A N := Module.compHom N (e : A →+* B)
  have : IsScalarTower A B N := ⟨fun a b n => mul_smul (e a) b n⟩
  have Φ : M ≃ₗ[A] N := { φ with map_smul' := hφ }
  have hbij : Function.Bijective (algebraMap A B) := e.bijective
  exact isCohenMacaulay_of_bijective_algebraMap hbij (isCohenMacaulay_of_linearEquiv Φ hM)

section KeyRegularElement

/-- If `h` acts regularly on `W` and a power of `v` annihilates `W`, then `h + v` acts regularly
on `W`. -/
private lemma isSMulRegular_add_of_pow_smul_eq_zero {T W : Type*} [CommRing T] [AddCommGroup W]
    [Module T W] {h v : T} (hreg : IsSMulRegular W h) {m : ℕ} (hv : ∀ w : W, v ^ m • w = 0) :
    IsSMulRegular W (h + v) := by
  have key : ∀ w : W, (h + v) • w = 0 → w = 0 := by
    intro w hw
    rw [add_smul] at hw
    have hhv : h • w = -(v • w) := eq_neg_of_add_eq_zero_left hw
    have step : ∀ n : ℕ, h ^ n • w = (-v) ^ n • w := by
      intro n
      induction n with
      | zero => simp
      | succ n
        ih =>
        have e1 : h ^ (n + 1) • w = -(v • ((-v) ^ n • w)) := by
          rw [pow_succ, mul_smul, hhv, smul_neg, ← mul_smul, mul_comm (h ^ n) v, mul_smul, ih]
        have e2 : (-v) ^ (n + 1) • w = -(v • ((-v) ^ n • w)) := by
          rw [pow_succ, mul_smul, neg_smul, smul_neg, ← mul_smul, mul_comm ((-v) ^ n) v, mul_smul]
        rw [e1, e2]
    have hzero : h ^ m • w = 0 := by rw [step m, neg_pow, mul_smul, hv, smul_zero]
    exact (hreg.pow m) (by simpa using hzero)
  exact isSMulRegular_iff_right_eq_zero_of_smul.mpr key

/-- A polynomial of degree at most `k` whose `k`-th coefficient acts regularly on `P` acts
regularly on `P[X]`. -/
private lemma isSMulRegular_polynomialModule_of_natDegree_le {A : Type*} [CommRing A] {P : Type*}
    [AddCommGroup P] [Module A P] {h : Polynomial A} {k : ℕ} (hdeg : h.natDegree ≤ k)
    (hreg : IsSMulRegular P (h.coeff k)) : IsSMulRegular (PolynomialModule A P) h := by
  have key : ∀ w : PolynomialModule A P, h • w = 0 → w = 0 := by
    intro w hw
    by_contra hne
    have hne' : w.coeff ≠ 0 := fun hc => hne (PolynomialModule.coeff_injective (by simpa using hc))
    have hsupp : w.coeff.support.Nonempty := Finsupp.support_nonempty_iff.mpr hne'
    set d := w.coeff.support.max' hsupp with hd
    have hdmem : w.coeff d ≠ 0 := Finsupp.mem_support_iff.mp (Finset.max'_mem _ hsupp)
    have hgt : ∀ j, d < j → w.coeff j = 0 := by
      intro j hj
      refine Finsupp.notMem_support_iff.mp fun hmem => ?_
      exact absurd (Finset.le_max' _ j hmem) (by omega)
    have hcoeff : (h • w).coeff (k + d) = h.coeff k • w.coeff d := by
      rw [PolynomialModule.smul_apply]
      refine Finset.sum_eq_single_of_mem (k, d) (by simp) ?_
      rintro ⟨i, j⟩ hij hne2
      have hsum : i + j = k + d := by simpa using hij
      rcases lt_trichotomy i k with hik | hik | hik
      · rw [hgt j (by omega), smul_zero]
      · exact absurd (Prod.ext_iff.mpr ⟨hik, by omega⟩) hne2
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg hik), zero_smul]
    rw [hw] at hcoeff
    simp only [PolynomialModule.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at hcoeff
    exact hdmem (hreg (by simpa using hcoeff.symm))
  exact isSMulRegular_iff_right_eq_zero_of_smul.mpr key

/-- A polynomial all of whose coefficients lie in an ideal annihilating `P` annihilates `P[X]`. -/
private lemma smul_eq_zero_of_forall_coeff_mem {A : Type*} [CommRing A] {P : Type*}
    [AddCommGroup P] [Module A P] {J : Ideal A} (hJ : ∀ a ∈ J, ∀ p : P, a • p = 0)
    {f : Polynomial A} (hf : ∀ i, f.coeff i ∈ J) (w : PolynomialModule A P) : f • w = 0 := by
  ext n
  simp only [PolynomialModule.smul_apply, PolynomialModule.coeff_zero, Finsupp.coe_zero,
    Pi.zero_apply]
  exact Finset.sum_eq_zero fun x _ => hJ _ (hf x.1) _

/-- If every coefficient of `v` lies in `J`, every coefficient of `v ^ m` lies in `J ^ m`. -/
private lemma coeff_pow_mem_pow {A : Type*} [CommRing A] {J : Ideal A} {v : Polynomial A}
    (hv : ∀ i, v.coeff i ∈ J) : ∀ (m i : ℕ), (v ^ m).coeff i ∈ J ^ m := by
  intro m
  induction m with
  | zero =>
    intro i; simp
  | succ m ih =>
    intro i
    rw [show v ^ (m + 1) = v ^ m * v from pow_succ v m, Polynomial.coeff_mul, pow_succ]
    exact Ideal.sum_mem _ fun x _ => Ideal.mul_mem_mul (ih x.1) (hv x.2)

/-- Let `P` be an `A`-module annihilated by `J ^ m` and let `g` be a polynomial with a coefficient
`g.coeff k` acting regularly on `P` and all higher coefficients in `J`. Then `g` acts regularly on
`P[X] = ⨁_{n ≥ 0} P · X ^ n`. -/
private lemma isSMulRegular_polynomialModule_of_forall_gt_coeff_mem {A : Type*} [CommRing A]
    {P : Type*} [AddCommGroup P] [Module A P] {J : Ideal A} {m : ℕ}
    (hJ : ∀ a ∈ J ^ m, ∀ p : P, a • p = 0) {g : Polynomial A} {k : ℕ}
    (hreg : IsSMulRegular P (g.coeff k)) (hlt : ∀ i, k < i → g.coeff i ∈ J) :
    IsSMulRegular (PolynomialModule A P) g := by
  set h : Polynomial A := ∑ i ∈ Finset.range (k + 1), Polynomial.monomial i (g.coeff i) with hh
  have hcoeff : ∀ n, h.coeff n = if n ≤ k then g.coeff n else 0 := by
    intro n
    rw [hh, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' (Finset.range (k + 1)) n fun i => g.coeff i]
    simp
  have hdeg : h.natDegree ≤ k :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun n hn => by simp [hcoeff n, Nat.not_le.mpr hn]
  have hvmem : ∀ i, (g - h).coeff i ∈ J := by
    intro i
    rw [Polynomial.coeff_sub, hcoeff i]
    by_cases hik : i ≤ k
    · simp [hik]
    · simpa [hik] using hlt i (by omega)
  have hv : ∀ w : PolynomialModule A P, (g - h) ^ m • w = 0 := fun w =>
    smul_eq_zero_of_forall_coeff_mem hJ (coeff_pow_mem_pow hvmem m) w
  have hgh : IsSMulRegular (PolynomialModule A P) h :=
    isSMulRegular_polynomialModule_of_natDegree_le hdeg (by simpa [hcoeff k] using hreg)
  simpa using isSMulRegular_add_of_pow_smul_eq_zero hgh hv

/-- A maximal ideal `𝔪` of `A[X]` is not of the form `𝔭A[X]` for `𝔭 = 𝔪 ∩ A`. -/
private lemma map_C_comap_C_ne_of_isMaximal {A : Type*} [CommRing A] (𝔪 : Ideal (Polynomial A))
    [𝔪.IsMaximal] :
    Ideal.map (Polynomial.C : A →+* Polynomial A) (𝔪.comap (Polynomial.C : A →+* Polynomial A)) ≠
      𝔪 := by
  set 𝔭 : Ideal A := 𝔪.comap (Polynomial.C : A →+* Polynomial A) with hp
  have hpp : 𝔭.IsPrime := Ideal.comap_isPrime _ _
  have hptop : 𝔭 ≠ ⊤ := hpp.ne_top
  have hXnot : (Polynomial.X : Polynomial A) ∉ Ideal.map (Polynomial.C : A →+* Polynomial A) 𝔭 :=
    fun h =>
    hptop (Ideal.eq_top_of_isUnit_mem _ (by simpa using (Ideal.mem_map_C_iff.mp h) 1) isUnit_one)
  have hsupne :
    Ideal.map (Polynomial.C : A →+* Polynomial A) 𝔭 ⊔ Ideal.span {(Polynomial.X : Polynomial A)} ≠
      ⊤ := by
    intro h
    obtain ⟨u, hu, y, hy, huy⟩ :=
      Submodule.mem_sup.mp (h ▸ Submodule.mem_top (x := (1 : Polynomial A)))
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    have h0 : (1 : A) = u.coeff 0 := by
      have h1 := congrArg (fun f => Polynomial.coeff f 0) huy
      simpa [Polynomial.coeff_mul_X_zero] using h1.symm
    exact hptop (Ideal.eq_top_of_isUnit_mem _ (h0 ▸ (Ideal.mem_map_C_iff.mp hu) 0) isUnit_one)
  intro h
  have hmax : (Ideal.map (Polynomial.C : A →+* Polynomial A) 𝔭).IsMaximal := h ▸ ‹𝔪.IsMaximal›
  refine hsupne (hmax.out.2 _ (lt_of_le_of_ne le_sup_left fun hcon => hXnot ?_))
  rw [hcon]
  exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)

/-- A prime `𝔮` of `A[X]` other than `𝔭A[X]`, for `𝔭 = 𝔮 ∩ A`, contains a polynomial `g` with a
coefficient `g.coeff k ∉ 𝔭` such that `g.coeff i ∈ 𝔭` for all `i > k`. -/
private lemma exists_mem_coeff_notMem_and_forall_gt_coeff_mem {A : Type*} [CommRing A]
    (𝔮 : Ideal (Polynomial A))
    (hne :
      Ideal.map (Polynomial.C : A →+* Polynomial A) (𝔮.comap (Polynomial.C : A →+* Polynomial A)) ≠
        𝔮) :
    ∃ g ∈ 𝔮,
      ∃ k : ℕ,
        g.coeff k ∉ 𝔮.comap (Polynomial.C : A →+* Polynomial A) ∧
          ∀ i, k < i → g.coeff i ∈ 𝔮.comap (Polynomial.C : A →+* Polynomial A) := by
  classical
  set 𝔭 : Ideal A := 𝔮.comap (Polynomial.C : A →+* Polynomial A) with hp
  have hle : Ideal.map (Polynomial.C : A →+* Polynomial A) 𝔭 ≤ 𝔮 := fun q hq =>
    Ideal.polynomial_mem_ideal_of_coeff_mem_ideal 𝔮 q (Ideal.mem_map_C_iff.mp hq)
  obtain ⟨g, hg, hgn⟩ :=
    SetLike.not_le_iff_exists.mp
      (fun hsub : 𝔮 ≤ Ideal.map (Polynomial.C : A →+* Polynomial A) 𝔭 =>
        hne (le_antisymm hle hsub))
  obtain ⟨i, hi⟩ : ∃ i, g.coeff i ∉ 𝔭 := by
    by_contra hc
    exact hgn (Ideal.mem_map_C_iff.mpr (by simpa using hc))
  have hib : i ≤ g.natDegree := by
    by_contra hc
    exact
      hi
        (by
          rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; exact Submodule.zero_mem _)
  refine ⟨g, hg, Nat.findGreatest (fun j => g.coeff j ∉ 𝔭) g.natDegree, ?_, ?_⟩
  · exact Nat.findGreatest_spec (P := fun j => g.coeff j ∉ 𝔭) hib hi
  · intro j hj
    by_cases hjd : j ≤ g.natDegree
    · exact not_not.mp (Nat.findGreatest_is_greatest hj hjd)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; exact Submodule.zero_mem _

end KeyRegularElement

section FiberDimension

/-- The prime `𝔭A[X]` of `A[X]` contracts to `𝔭`. -/
private lemma comap_C_map_C {A : Type*} [CommRing A] (𝔭 : Ideal A) :
    (Ideal.map (Polynomial.C : A →+* Polynomial A) 𝔭).comap (Polynomial.C : A →+* Polynomial A) =
      𝔭 := by
  refine le_antisymm (fun a ha => ?_) fun a ha => Ideal.mem_map_of_mem _ ha
  simpa using (Ideal.mem_map_C_iff.mp ha) 0

/-- **The fibers of `Spec A[X] → Spec A` have dimension at most one.** If `𝔯 ⊆ 𝔮` are primes of
`A[X]` with the same contraction `𝔭` to `A` and `𝔯` is not the generic point `𝔭A[X]` of the fiber,
then `𝔯 = 𝔮`. -/
@[ega "IV 5.5.3" "partial"]
private lemma eq_of_le_of_comap_C_eq {A : Type*} [CommRing A] {𝔭 : Ideal A} [h𝔭 : 𝔭.IsPrime]
    {𝔯 𝔮 : Ideal (Polynomial A)} [𝔯.IsPrime] [𝔮.IsPrime]
    (h𝔯 : 𝔯.comap (Polynomial.C : A →+* Polynomial A) = 𝔭)
    (h𝔮 : 𝔮.comap (Polynomial.C : A →+* Polynomial A) = 𝔭) (hle : 𝔯 ≤ 𝔮)
    (hne : Ideal.map (Polynomial.C : A →+* Polynomial A) 𝔭 ≠ 𝔯) : 𝔯 = 𝔮 := by
  have hmapC : (Ideal.map (Polynomial.C : A →+* Polynomial A) 𝔭).IsPrime :=
    Ideal.isPrime_map_C_of_isPrime
  set p : PrimeSpectrum A := ⟨𝔭, h𝔭⟩ with hp
  have hCalg : (Polynomial.C : A →+* Polynomial A) = algebraMap A (Polynomial A) := rfl
  set F := (PrimeSpectrum.comap (algebraMap A (Polynomial A)) ⁻¹' {p}) with hF
  have hdim : Order.krullDim F ≤ 1 := by
    rw [hF, Order.krullDim_eq_of_orderIso (PrimeSpectrum.preimageOrderIsoFiber A (Polynomial A) p),
      ← ringKrullDim, ←
      ringKrullDim_eq_of_ringEquiv (polyEquivTensor A (p.asIdeal.ResidueField)).toRingEquiv]
    exact
      Ring.krullDimLE_iff.mp
        (inferInstance : Ring.KrullDimLE 1 (Polynomial p.asIdeal.ResidueField))
  have hmem :
    ∀ (I : Ideal (Polynomial A)) (_ : I.IsPrime),
      I.comap (Polynomial.C : A →+* Polynomial A) = 𝔭 → (⟨I, ‹I.IsPrime›⟩ : PrimeSpectrum _) ∈ F :=
    fun I _ hI =>
    PrimeSpectrum.ext
      (by
        rw [← hCalg]; exact hI)
  have h0 : Ideal.map (Polynomial.C : A →+* Polynomial A) 𝔭 ≤ 𝔯 :=
    Ideal.map_le_iff_le_comap.mpr (h𝔯 ▸ le_refl 𝔭)
  by_contra hne2
  set x0 : F := ⟨⟨_, hmapC⟩, hmem _ hmapC (comap_C_map_C 𝔭)⟩ with hx0
  set x1 : F := ⟨⟨𝔯, ‹𝔯.IsPrime›⟩, hmem _ ‹𝔯.IsPrime› h𝔯⟩ with hx1
  set x2 : F := ⟨⟨𝔮, ‹𝔮.IsPrime›⟩, hmem _ ‹𝔮.IsPrime› h𝔮⟩ with hx2
  have h01 : x0 < x1 := by
    rw [hx0, hx1, ← Subtype.coe_lt_coe]
    exact lt_of_le_of_ne h0 fun h => hne (congrArg PrimeSpectrum.asIdeal h)
  have h12 : x1 < x2 := by
    rw [hx1, hx2, ← Subtype.coe_lt_coe]
    exact lt_of_le_of_ne hle fun h => hne2 (congrArg PrimeSpectrum.asIdeal h)
  have hchain : ∃ l : LTSeries F, l.length = 2 := by
    refine ⟨⟨2, fun i => if i = 0 then x0 else if i = 1 then x1 else x2, ?_⟩, rfl⟩
    intro i
    fin_cases i <;> simp [h01, h12]
  have h2 : ((2 : ℕ) : WithBot ℕ∞) ≤ Order.krullDim F := Order.le_krullDim_iff.mpr hchain
  have := le_trans h2 hdim
  norm_num at this

end FiberDimension

section SystemOfParameters

/-- A module whose support has a dimension at all is nonzero. -/
private lemma nontrivial_of_supportDim_ne_bot {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] (h : Module.supportDim R M ≠ ⊥) : Nontrivial M := by
  by_contra hcon
  have : Subsingleton M := not_nontrivial_iff_subsingleton.mp hcon
  exact
    h
      (by
        rw [Module.supportDim, Module.support_eq_empty]; simp)

/-- A finite nonzero module of support dimension `0` over a Noetherian local ring is killed by a
power of the maximal ideal. -/
private theorem exists_pow_maximalIdeal_smul_eq_zero_of_supportDim_eq_zero {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] (hsupp : Module.supportDim R M = (0 : WithBot ℕ∞)) :
    ∃ m : ℕ, ∀ a ∈ IsLocalRing.maximalIdeal R ^ m, ∀ x : M, a • x = 0 := by
  have hne : Module.annihilator R M ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : M)
    have h1 : (1 : R) ∈ Module.annihilator R M := h ▸ Submodule.mem_top
    exact hx (by simpa using Module.mem_annihilator.mp h1 x)
  have hann : Module.annihilator R M ≤ IsLocalRing.maximalIdeal R :=
    IsLocalRing.le_maximalIdeal hne
  have hmax :
    (⟨IsLocalRing.maximalIdeal R, inferInstance⟩ : PrimeSpectrum R) ∈ Module.support R M := by
    rw [Module.support_eq_zeroLocus]; exact hann
  have key :
    ∀ J : Ideal R, J.IsPrime → Module.annihilator R M ≤ J → IsLocalRing.maximalIdeal R ≤ J := by
    intro J hJ hle
    have hJmem : (⟨J, hJ⟩ : PrimeSpectrum R) ∈ Module.support R M := by
      rw [Module.support_eq_zeroLocus]; exact hle
    by_contra hcon
    have hlt : (⟨J, hJ⟩ : PrimeSpectrum R) < ⟨IsLocalRing.maximalIdeal R, inferInstance⟩ :=
      lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hJ.ne_top)
        (fun h => hcon (le_of_eq (congrArg PrimeSpectrum.asIdeal h).symm))
    have hchain : ∃ l : LTSeries (Module.support R M), l.length = 1 := by
      refine ⟨⟨1, fun i => if i = 0 then ⟨_, hJmem⟩ else ⟨_, hmax⟩, ?_⟩, rfl⟩
      intro i
      fin_cases i
      simpa [← Subtype.coe_lt_coe] using hlt
    have h1 : ((1 : ℕ) : WithBot ℕ∞) ≤ Module.supportDim R M := Order.le_krullDim_iff.mpr hchain
    rw [hsupp] at h1
    norm_num at h1
  have hrad : IsLocalRing.maximalIdeal R ≤ (Module.annihilator R M).radical := by
    rw [Ideal.radical_eq_sInf]
    exact le_sInf fun J hJ => key J hJ.2 hJ.1
  obtain ⟨m, hm⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  exact ⟨m, fun a ha x => Module.mem_annihilator.mp (hm ha) x⟩

/-- Over a local ring, the depth at the maximal ideal is the supremum of lengths of regular
sequences in it. -/
private lemma depth_maximalIdeal_eq_depthSup {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*}
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] :
    Module.depth R (IsLocalRing.maximalIdeal R) M =
      Module.depthSup R (IsLocalRing.maximalIdeal R) M := by
  rw [Module.depth, Module.depthSup_eq_iSup,
    ite_eq_right (fun hc => absurd hc (Module.maximalIdeal_smul_top_ne_top _))]

/-- A finite nonzero module `M` over a Noetherian local ring satisfying
`depth_𝔪(M) = dim Supp(M) = d` admits an `M`-regular sequence `f_1, …, f_d` in `𝔪` of length
exactly `d` whose quotient `M/(f_1, …, f_d)M` is annihilated by a power of `𝔪`. -/
private theorem exists_isRegular_length_eq_and_pow_maximalIdeal_smul_eq_zero {R : Type*}
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] (d : ℕ) (hd : Module.supportDim R M = (d : WithBot ℕ∞))
    (hCM : (Module.depth R (IsLocalRing.maximalIdeal R) M : WithBot ℕ∞) = Module.supportDim R M) :
    ∃ rs : List R,
      rs.length = d ∧
        (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R) ∧
        RingTheory.Sequence.IsRegular M rs ∧
        ∃ m : ℕ,
          ∀ a ∈ IsLocalRing.maximalIdeal R ^ m,
            ∀ x : M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)), a • x = 0 := by
  have hCM' : IsCohenMacaulay R M := by
    rw [IsCohenMacaulay, ← hCM, depth_maximalIdeal_eq_depthSup]
  obtain ⟨es, hlen, hmem, hdim⟩ := cm_exists_dimDrop_list d hCM' hd
  have : Nontrivial (M ⧸ (Ideal.ofList es • (⊤ : Submodule R M))) :=
    nontrivial_of_supportDim_ne_bot
      (by
        rw [hdim]; simp)
  exact
    ⟨es, hlen, hmem,
      cohenMacaulay_dimDrop_isRegular d d le_rfl hd hCM' es hlen hmem (by simpa using hdim),
      exists_pow_maximalIdeal_smul_eq_zero_of_supportDim_eq_zero hdim⟩

end SystemOfParameters

section LocalizationTransport

/-- The coefficients of the image of a polynomial under `PolynomialModule.map`. -/
private lemma coeff_map {A : Type*} [CommRing A] {M V : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup V] [Module A V] (g : M →ₗ[A] V) (x : PolynomialModule A M) (n : ℕ) :
    (PolynomialModule.map A g x).coeff n = g (x.coeff n) :=
  rfl

/-- **Localizations compose.** If `M₁` is the localization of `M` at `T₁` and `M₂` the
localization of `M₁` at a larger submonoid `T₂`, then `M₂` is the localization of `M` at `T₂`. -/
private lemma isLocalizedModule_comp_of_le {R : Type*} [CommRing R] {T₁ T₂ : Submonoid R}
    (hT : T₁ ≤ T₂) {M M₁ M₂ : Type*} [AddCommGroup M] [Module R M] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] (f : M →ₗ[R] M₁) (g : M₁ →ₗ[R] M₂) [IsLocalizedModule T₁ f]
    [IsLocalizedModule T₂ g] : IsLocalizedModule T₂ (g ∘ₗ f)
    where
  map_units t := IsLocalizedModule.map_units g t
  surj y := by
    obtain ⟨⟨x₁, t⟩, ht⟩ := IsLocalizedModule.surj T₂ g y
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj T₁ f x₁
    refine ⟨⟨x, ⟨(s : R) * (t : R), mul_mem (hT s.2) t.2⟩⟩, ?_⟩
    simp only [Submonoid.smul_def, LinearMap.coe_comp, Function.comp_apply] at ht hs ⊢
    rw [mul_smul, ht, ← map_smul, hs]
  exists_of_eq {x₁ x₂} e := by
    simp only [LinearMap.coe_comp, Function.comp_apply] at e
    obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq (S := T₂) (f := g) e
    simp only [Submonoid.smul_def] at ht
    obtain ⟨s, hs⟩ :=
      IsLocalizedModule.exists_of_eq (S := T₁) (f := f) (x₁ := (t : R) • x₁) (x₂ := (t : R) • x₂)
        (by
          rw [map_smul, map_smul]; exact ht)
    simp only [Submonoid.smul_def] at hs
    exact
      ⟨⟨(s : R) * (t : R), mul_mem (hT s.2) t.2⟩, by
        simp only [Submonoid.smul_def]
        rw [mul_smul, mul_smul, hs]⟩

/-- **Localization commutes with `PolynomialModule`.** If `V` is the localization of `M` at a
submonoid `S` of `A`, then `V[X]` is the localization of `M[X]` at `S`, the localization being
taken coefficientwise. -/
private lemma isLocalizedModule_polynomialModule_map {A : Type*} [CommRing A] (S : Submonoid A)
    {M V : Type*} [AddCommGroup M] [Module A M] [AddCommGroup V] [Module A V] (f : M →ₗ[A] V)
    [IsLocalizedModule S f] : IsLocalizedModule S (PolynomialModule.map (R := A) A f)
    where
  map_units s := by
    rw [Module.End.isUnit_iff]
    have h := IsLocalizedModule.map_units f s
    rw [Module.End.isUnit_iff] at h
    let e : V ≃ₗ[A] V := LinearEquiv.ofBijective (algebraMap A (Module.End A V) (s : A)) h
    constructor
    · intro x y hxy
      refine PolynomialModule.coeff_injective (Finsupp.ext fun n => e.injective ?_)
      exact congrArg (fun w => PolynomialModule.coeff w n) hxy
    · intro y
      refine
        ⟨PolynomialModule.map A e.symm.toLinearMap y,
          PolynomialModule.coeff_injective (Finsupp.ext fun n => ?_)⟩
      exact e.apply_symm_apply _
  surj y := by
    induction y using PolynomialModule.induction_linear with
    | zero => exact ⟨⟨0, 1⟩, by simp⟩
    | add y₁ y₂ h₁ h₂ =>
      obtain ⟨⟨x₁, s₁⟩, e₁⟩ := h₁
      obtain ⟨⟨x₂, s₂⟩, e₂⟩ := h₂
      refine ⟨⟨(s₂ : A) • x₁ + (s₁ : A) • x₂, s₁ * s₂⟩, ?_⟩
      simp only [Submonoid.smul_def, Submonoid.coe_mul] at e₁ e₂ ⊢
      rw [smul_add, map_add, map_smul, map_smul, ← e₁, ← e₂, ← mul_smul, ← mul_smul,
        mul_comm (s₂ : A) (s₁ : A)]
    | single i m =>
      obtain ⟨⟨x, s⟩, e⟩ := IsLocalizedModule.surj S f m
      refine ⟨⟨PolynomialModule.single A i x, s⟩, ?_⟩
      simp only [Submonoid.smul_def] at e ⊢
      rw [PolynomialModule.map_single, ← e]
      exact (PolynomialModule.single_smul (R := A) i (s : A) m).symm
  exists_of_eq {x₁ x₂} e := by
    classical
    set z := x₁ - x₂ with hz
    have hz0 : PolynomialModule.map A f z = 0 := by rw [hz, map_sub, e, sub_self]
    have hall : ∀ n : ℕ, ∃ c : S, (c : A) • z.coeff n = 0 := by
      intro n
      obtain ⟨c, hc⟩ :=
        IsLocalizedModule.exists_of_eq (S := S) (f := f) (x₁ := z.coeff n) (x₂ := 0)
          (by
            rw [map_zero, ← coeff_map f z n, hz0]; rfl)
      exact ⟨c, by simpa [Submonoid.smul_def] using hc⟩
    choose c hc using hall
    refine ⟨⟨∏ n ∈ z.coeff.support, ((c n : A)), Submonoid.prod_mem _ (fun i _ => (c i).2)⟩, ?_⟩
    have key : (∏ n ∈ z.coeff.support, ((c n : A))) • z = 0 := by
      refine PolynomialModule.coeff_injective (Finsupp.ext fun n => ?_)
      show (∏ m ∈ z.coeff.support, ((c m : A))) • z.coeff n = (0 : ℕ →₀ M) n
      by_cases hn : n ∈ z.coeff.support
      · obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem (fun m => ((c m : A))) hn
        rw [hr, mul_comm, mul_smul, hc n, smul_zero]
        simp
      · rw [Finsupp.notMem_support_iff.mp hn, smul_zero]
        simp
    rw [hz, smul_sub, sub_eq_zero] at key
    simpa [Submonoid.smul_def] using key

/-- `PolynomialModule.map`, as an `A[X]`-linear map. -/
private noncomputable def polyMapₗ {A : Type*} [CommRing A] {M V : Type*} [AddCommGroup M]
    [Module A M] [AddCommGroup V] [Module A V] (f : M →ₗ[A] V) :
    PolynomialModule A M →ₗ[Polynomial A] PolynomialModule A V :=
  { PolynomialModule.map A f with
    map_smul' := fun p q => by simpa using PolynomialModule.map_smul (R' := A) f p q }

/-- `V[X]` is the localization of `M[X]` at the image in `A[X]` of a submonoid `S` of `A`, as
`A[X]`-modules. -/
private lemma isLocalizedModule_polyMapₗ {A : Type*} [CommRing A] (S : Submonoid A) {M V : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup V] [Module A V] (f : M →ₗ[A] V)
    [IsLocalizedModule S f] :
    IsLocalizedModule (Algebra.algebraMapSubmonoid (Polynomial A) S) (polyMapₗ f) := by
  have : IsLocalizedModule S ((polyMapₗ f).restrictScalars A) :=
    isLocalizedModule_polynomialModule_map S f
  exact IsLocalizedModule.of_restrictScalars S (polyMapₗ f)

/-- The constants `C s` with `s ∉ 𝔮 ∩ A` avoid `𝔮`. -/
private lemma algebraMapSubmonoid_primeCompl_le {A : Type*} [CommRing A] (𝔮 : Ideal (Polynomial A))
    [𝔮.IsPrime] [(𝔮.comap (Polynomial.C : A →+* Polynomial A)).IsPrime] :
    Algebra.algebraMapSubmonoid (Polynomial A)
        (𝔮.comap (Polynomial.C : A →+* Polynomial A)).primeCompl ≤
      𝔮.primeCompl := by
  rintro _ ⟨s, hs, rfl⟩
  exact fun h => hs (Ideal.mem_comap.mpr h)

/-- With `𝔭 = 𝔮 ∩ A` and `V = M_𝔭`, the localization of `M[X]` at a prime `𝔮` of `A[X]` is the
localization of `V[X]` at `𝔮`, as modules over `A[X]_𝔮`. -/
private noncomputable def localizedPolynomialModuleEquiv {A : Type*} [CommRing A] {M V : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup V] [Module A V] (𝔮 : Ideal (Polynomial A))
    [𝔮.IsPrime] (f : M →ₗ[A] V) [(𝔮.comap (Polynomial.C : A →+* Polynomial A)).IsPrime]
    [IsLocalizedModule (𝔮.comap (Polynomial.C : A →+* Polynomial A)).primeCompl f] :
    LocalizedModule 𝔮.primeCompl (PolynomialModule A M) ≃ₗ[Localization.AtPrime 𝔮]
      LocalizedModule 𝔮.primeCompl (PolynomialModule A V) :=
  haveI :
    IsLocalizedModule
      (Algebra.algebraMapSubmonoid (Polynomial A)
        (𝔮.comap (Polynomial.C : A →+* Polynomial A)).primeCompl)
      (polyMapₗ f) :=
    isLocalizedModule_polyMapₗ _ f
  haveI :
    IsLocalizedModule 𝔮.primeCompl
      (LocalizedModule.mkLinearMap 𝔮.primeCompl (PolynomialModule A V) ∘ₗ polyMapₗ f) :=
    isLocalizedModule_comp_of_le (algebraMapSubmonoid_primeCompl_le 𝔮) _ _
  (IsLocalizedModule.isBaseChange 𝔮.primeCompl (Localization.AtPrime 𝔮)
        (LocalizedModule.mkLinearMap 𝔮.primeCompl (PolynomialModule A M))).equiv.symm.trans
    (IsLocalizedModule.isBaseChange 𝔮.primeCompl (Localization.AtPrime 𝔮)
        (LocalizedModule.mkLinearMap 𝔮.primeCompl (PolynomialModule A V) ∘ₗ polyMapₗ f)).equiv

end LocalizationTransport

section CohenMacaulayCriterion

/-- The support dimension of a nonzero finite module over a Noetherian local ring is a natural
number. -/
private lemma exists_supportDim_eq_natCast {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (N : Type*) [AddCommGroup N] [Module R N] [Nontrivial N] :
    ∃ d : ℕ, Module.supportDim R N = (d : WithBot ℕ∞) := by
  have hbot : Module.supportDim R N ≠ ⊥ := Module.supportDim_ne_bot_of_nontrivial R N
  have hle : Module.supportDim R N ≤ ringKrullDim R := Module.supportDim_le_ringKrullDim R N
  have htop : Module.supportDim R N ≠ ⊤ := by
    intro h
    rw [h] at hle
    exact ringKrullDim_ne_top (top_le_iff.mp hle)
  obtain ⟨y, hy⟩ := WithBot.ne_bot_iff_exists.mp hbot
  have hy' : y ≠ ⊤ := fun h =>
    htop
      (by
        rw [← hy, h]; simp)
  obtain ⟨d, rfl⟩ := WithTop.ne_top_iff_exists.mp hy'
  exact
    ⟨d, by
      rw [← hy]; norm_cast⟩

/-- Let `R` be a Noetherian local ring and `N` a finite nonzero `R`-module. If `rs` is an
`N`-regular sequence in the maximal ideal whose quotient `N/rsN` has support of dimension `0`, then
`depth_𝔪(N) = dim Supp(N)`. -/
@[ega "0 16.5.7" "more general"]
private lemma depth_eq_supportDim_of_isRegular_of_supportDim_quot_eq_zero {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] {N : Type*} [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Nontrivial N] {rs : List R}
    (hmem : ∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R) (hreg : RingTheory.Sequence.IsRegular N rs)
    (hquot :
      Module.supportDim R (N ⧸ (Ideal.ofList rs • (⊤ : Submodule R N))) = (0 : WithBot ℕ∞)) :
    (Module.depth R (IsLocalRing.maximalIdeal R) N : WithBot ℕ∞) = Module.supportDim R N := by
  have hdim : Module.supportDim R N = (rs.length : WithBot ℕ∞) := by
    have h := Module.supportDim_add_length_eq_supportDim_of_isRegular rs hreg
    rw [hquot, zero_add] at h
    exact h.symm
  have hle : Module.depthSup R (IsLocalRing.maximalIdeal R) N ≤ (rs.length : ℕ∞) := by
    rw [Module.depthSup]
    refine sSup_le ?_
    rintro n ⟨ss, rfl, hmem', hreg'⟩
    have h := Module.supportDim_add_length_eq_supportDim_of_isRegular ss hreg'
    have hnt : Nontrivial (N ⧸ (Ideal.ofList ss • (⊤ : Submodule R N))) :=
      Submodule.Quotient.nontrivial_iff.mpr fun hc => hreg'.2 hc.symm
    have h0 :
      (0 : WithBot ℕ∞) ≤ Module.supportDim R (N ⧸ (Ideal.ofList ss • (⊤ : Submodule R N))) := by
      obtain ⟨y, hy⟩ :=
        WithBot.ne_bot_iff_exists.mp
          (Module.supportDim_ne_bot_of_nontrivial R (N ⧸ (Ideal.ofList ss • (⊤ : Submodule R N))))
      rw [← hy]
      exact_mod_cast (zero_le : (0 : ℕ∞) ≤ y)
    have hchain : ((ss.length : ℕ) : WithBot ℕ∞) ≤ ((rs.length : ℕ) : WithBot ℕ∞) := by
      rw [← hdim, ← h]
      calc
        ((ss.length : ℕ) : WithBot ℕ∞) = 0 + ((ss.length : ℕ) : WithBot ℕ∞) := by rw [zero_add]
        _ ≤ _ := add_le_add h0 le_rfl
    exact_mod_cast hchain
  have heq : Module.depthSup R (IsLocalRing.maximalIdeal R) N = (rs.length : ℕ∞) :=
    le_antisymm hle (Module.le_depthSup hmem hreg)
  rw [depth_maximalIdeal_eq_depthSup, heq, hdim]
  norm_cast

/-- `M[X]` is a finite `A[X]`-module when `M` is a finite `A`-module. -/
private lemma finite_polynomialModule {A : Type*} [CommRing A] (M : Type*) [AddCommGroup M]
    [Module A M] [Module.Finite A M] : Module.Finite (Polynomial A) (PolynomialModule A M) :=
  Module.Finite.equiv (PolynomialModule.polynomialTensorProductLEquivPolynomialModule A M)

/-- A constant acting regularly on `V` acts regularly on `V[X]`. -/
private lemma isSMulRegular_polynomialModule_C {A : Type*} [CommRing A] {V : Type*}
    [AddCommGroup V] [Module A V] {a : A} (h : IsSMulRegular V a) :
    IsSMulRegular (PolynomialModule A V) (Polynomial.C a) :=
  isSMulRegular_polynomialModule_of_natDegree_le (k := 0) (by simp) (by simpa using h)

end CohenMacaulayCriterion

/-- An element carrying `V` into a submodule `Q` annihilates `V ⧸ Q`. -/
private lemma smul_eq_zero_quotient {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V]
    [Module R V] {Q : Submodule R V} {a : R} (h : ∀ x : V, a • x ∈ Q) (p : V ⧸ Q) : a • p = 0 := by
  obtain ⟨x, rfl⟩ := Q.mkQ_surjective p
  exact (Submodule.Quotient.mk_eq_zero _).mpr (h x)

section PolynomialModuleQuotient

variable {A : Type*} [CommRing A] {V : Type*} [AddCommGroup V] [Module A V]

/-- Every element of `V[X]` is the sum of its homogeneous parts. -/
private lemma sum_single_coeff (x : PolynomialModule A V) :
    ∑ n ∈ x.coeff.support, PolynomialModule.single A n (x.coeff n) = x := by
  refine PolynomialModule.coeff_injective (Finsupp.ext fun n => ?_)
  rw [PolynomialModule.coeff_sum]
  simp [PolynomialModule.coeff_single, Finsupp.single_apply]

/-- A homogeneous element of `V[X]` whose coefficient lies in `JV` lies in `J[X]V[X]`. -/
private lemma single_mem_map_C_smul_top (J : Ideal A) (n : ℕ) {w : V}
    (hw : w ∈ (J • ⊤ : Submodule A V)) :
    PolynomialModule.single A n w ∈
      ((J.map (Polynomial.C : A →+* Polynomial A)) • ⊤ :
        Submodule (Polynomial A) (PolynomialModule A V)) := by
  refine Submodule.smul_induction_on hw ?_ ?_
  · intro a ha v _
    have h :
      PolynomialModule.single A n (a • v) = (Polynomial.C a) • PolynomialModule.single A n v := by
      rw [PolynomialModule.single_smul, ←
        algebraMap_smul (Polynomial A) a (PolynomialModule.single A n v)]
      rfl
    rw [h]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ ha) Submodule.mem_top
  · intro x y hx hy
    rw [PolynomialModule.single_add]
    exact Submodule.add_mem _ hx hy

/-- An element of `V[X]` all of whose coefficients lie in `JV` lies in `J[X]V[X]`. -/
private lemma mem_map_C_smul_top_of_forall_coeff_mem (J : Ideal A) {x : PolynomialModule A V}
    (hx : ∀ n, x.coeff n ∈ (J • ⊤ : Submodule A V)) :
    x ∈
      ((J.map (Polynomial.C : A →+* Polynomial A)) • ⊤ :
        Submodule (Polynomial A) (PolynomialModule A V)) := by
  rw [← sum_single_coeff x]
  exact Submodule.sum_mem _ fun n _ => single_mem_map_C_smul_top J n (hx n)

/-- The coefficients of `C a • x` are the `a`-multiples of the coefficients of `x`. -/
private lemma coeff_C_smul (a : A) (x : PolynomialModule A V) (n : ℕ) :
    ((Polynomial.C a) • x).coeff n = a • x.coeff n := by
  rw [show (Polynomial.C a) • x = a • x from algebraMap_smul (Polynomial A) a x]
  rfl

/-- **`V[X] ⧸ J[X]V[X] = (V ⧸ JV)[X]`.** Taking coefficients commutes with dividing by an ideal
of the base. -/
private noncomputable def polynomialModuleQuotEquiv (J : Ideal A) :
    (PolynomialModule A V ⧸
        ((J.map (Polynomial.C : A →+* Polynomial A)) • ⊤ :
          Submodule (Polynomial A) (PolynomialModule A V))) ≃ₗ[Polynomial A]
      PolynomialModule A (V ⧸ (J • ⊤ : Submodule A V)) := by
  set g : V →ₗ[A] (V ⧸ (J • ⊤ : Submodule A V)) := (J • (⊤ : Submodule A V)).mkQ with hg
  set F := polyMapₗ (A := A) g with hF
  have hsurj : Function.Surjective F := by
    intro y
    induction y using PolynomialModule.induction_linear with
    | zero => exact ⟨0, map_zero _⟩
    | add y₁ y₂ h₁ h₂ =>
      obtain ⟨x₁, rfl⟩ := h₁
      obtain ⟨x₂, rfl⟩ := h₂
      exact ⟨x₁ + x₂, map_add _ _ _⟩
    | single i m =>
      obtain ⟨v, rfl⟩ := (J • (⊤ : Submodule A V)).mkQ_surjective m
      exact ⟨PolynomialModule.single A i v, PolynomialModule.map_single A g i v⟩
  have hJkill : ∀ a ∈ J, ∀ p : V ⧸ (J • ⊤ : Submodule A V), a • p = 0 := fun a ha =>
    smul_eq_zero_quotient fun _ => Submodule.smul_mem_smul ha Submodule.mem_top
  have hker :
    LinearMap.ker F =
      ((J.map (Polynomial.C : A →+* Polynomial A)) • ⊤ :
        Submodule (Polynomial A) (PolynomialModule A V)) := by
    refine le_antisymm (fun x hx => ?_) (Submodule.smul_le.mpr fun a ha x _ => ?_)
    · refine mem_map_C_smul_top_of_forall_coeff_mem J fun n => ?_
      have h0 : g (x.coeff n) = 0 := by
        rw [← coeff_map g x n]
        exact congrArg (fun w => PolynomialModule.coeff w n) (LinearMap.mem_ker.mp hx)
      exact (Submodule.Quotient.mk_eq_zero _).mp h0
    · rw [LinearMap.mem_ker, map_smul]
      exact smul_eq_zero_of_forall_coeff_mem hJkill (Ideal.mem_map_C_iff.mp ha) _
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans (F.quotKerEquivOfSurjective hsurj)

/-- A `V`-regular sequence in `A` stays weakly regular on `V[X]` after applying `C`. -/
private lemma isWeaklyRegular_polynomialModule_map_C {as : List A}
    (h : RingTheory.Sequence.IsWeaklyRegular V as) :
    RingTheory.Sequence.IsWeaklyRegular (PolynomialModule A V)
      (as.map (Polynomial.C : A →+* Polynomial A)) := by
  rw [RingTheory.Sequence.isWeaklyRegular_iff] at h ⊢
  intro i hi
  have hlen : i < as.length := by simpa using hi
  rw [List.getElem_map, ← List.map_take, ← Ideal.map_ofList]
  exact
    ((polynomialModuleQuotEquiv (V := V) (Ideal.ofList (as.take i))).isSMulRegular_congr _).mpr
      (isSMulRegular_polynomialModule_C (h i hlen))

/-- An element acting invertibly on `V` acts regularly on every quotient `V ⧸ JV`. -/
private lemma isSMulRegular_quotient_smul_top_of_isUnit (J : Ideal A) {c : A}
    (hc : IsUnit (algebraMap A (Module.End A V) c)) :
    IsSMulRegular (V ⧸ (J • ⊤ : Submodule A V)) c := by
  have hbij : Function.Bijective (algebraMap A (Module.End A V) c) := by
    rw [← Module.End.isUnit_iff]; exact hc
  set e : V ≃ₗ[A] V := LinearEquiv.ofBijective (algebraMap A (Module.End A V) c) hbij with he
  have heapp : ∀ x : V, e x = c • x := fun x => rfl
  have hmap : Submodule.map (e : V →ₗ[A] V) (J • ⊤) = (J • ⊤ : Submodule A V) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  have key : ∀ x : V, c • x ∈ (J • ⊤ : Submodule A V) → x ∈ (J • ⊤ : Submodule A V) := by
    intro x hx
    rw [← heapp x, ← hmap] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    exact e.injective hxy ▸ hy
  have key2 : ∀ w : V ⧸ (J • ⊤ : Submodule A V), c • w = 0 → w = 0 := by
    intro w hw
    obtain ⟨x, rfl⟩ := (J • (⊤ : Submodule A V)).mkQ_surjective w
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hw
    exact (Submodule.Quotient.mk_eq_zero _).mpr (key x hw)
  exact isSMulRegular_iff_right_eq_zero_of_smul.mpr key2

/-- If every coefficient of `f` carries `V` into `JV`, then `f` carries `V[X]` into
`J[X]V[X]`. -/
private lemma smul_mem_map_C_smul_top (J : Ideal A) {f : Polynomial A}
    (hf : ∀ (i : ℕ) (v : V), f.coeff i • v ∈ (J • ⊤ : Submodule A V)) (x : PolynomialModule A V) :
    f • x ∈
      ((J.map (Polynomial.C : A →+* Polynomial A)) • ⊤ :
        Submodule (Polynomial A) (PolynomialModule A V)) := by
  refine mem_map_C_smul_top_of_forall_coeff_mem J fun n => ?_
  rw [PolynomialModule.smul_apply]
  exact Submodule.sum_mem _ fun y _ => hf _ _

end PolynomialModuleQuotient

section ClearDenominators

open scoped Pointwise

/-- A list of choices, one for each member of a list. -/
private lemma exists_forall₂ {α β : Type*} {l : List α} {p : α → β → Prop}
    (h : ∀ a ∈ l, ∃ b, p a b) : ∃ l' : List β, List.Forall₂ p l l' := by
  induction l with
  | nil => exact ⟨[], List.Forall₂.nil⟩
  | cons a l ih =>
    obtain ⟨b, hb⟩ := h a List.mem_cons_self
    obtain ⟨l', hl'⟩ := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    exact ⟨b :: l', List.Forall₂.cons hb hl'⟩

/-- Weak regularity only depends on a sequence up to unit multiples of its members. -/
private lemma isWeaklyRegular_of_forall₂_unit_mul {R : Type*} [CommRing R] {ss rs : List R}
    (h : List.Forall₂ (fun s r => ∃ u : Rˣ, s = (u : R) * r) ss rs) :
    ∀ {V : Type*} [AddCommGroup V] [Module R V],
      RingTheory.Sequence.IsWeaklyRegular V rs → RingTheory.Sequence.IsWeaklyRegular V ss := by
  induction h with
  | nil =>
    intro V _ _ _; simp
  | @cons s r ss' rs' hu hrest ih =>
    intro V _ _ hr
    obtain ⟨u, rfl⟩ := hu
    rw [RingTheory.Sequence.isWeaklyRegular_cons_iff] at hr ⊢
    have heq : ((u : R) * r) • (⊤ : Submodule R V) = r • (⊤ : Submodule R V) := by
      rw [← Submodule.ideal_span_singleton_smul, ← Submodule.ideal_span_singleton_smul,
        Ideal.span_singleton_mul_left_unit u.isUnit]
    refine ⟨(u.isUnit.isSMulRegular V).mul hr.1, ?_⟩
    exact ih (((Submodule.quotEquivOfEq _ _ heq).isWeaklyRegular_congr rs').mpr hr.2)

variable {A : Type*} [CommRing A] {A' : Type*} [CommRing A'] [Algebra A A'] {V : Type*}
  [AddCommGroup V] [Module A V] [Module A' V] [IsScalarTower A A' V]

/-- `IV` is stable under the scalars of the larger ring. -/
private lemma smul_mem_smul_top (I : Ideal A) (c : A') {x : V} (hx : x ∈ (I • ⊤ : Submodule A V)) :
    c • x ∈ (I • ⊤ : Submodule A V) := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha v _
    rw [smul_comm]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  · intro y z hy hz
    rw [smul_add]
    exact Submodule.add_mem _ hy hz

/-- `IV` computed over `A` contains `(IA')V` computed over `A'`, hence equals it. -/
private lemma mem_smul_top_of_mem_map_smul_top (I : Ideal A) {x : V}
    (hx : x ∈ ((I.map (algebraMap A A')) • ⊤ : Submodule A' V)) : x ∈ (I • ⊤ : Submodule A V) := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr w _
    rw [Ideal.map] at hr
    induction hr using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      rw [algebraMap_smul]
      exact Submodule.smul_mem_smul ha Submodule.mem_top
    | zero => simp
    | add y z _ _ hy hz =>
      rw [add_smul]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      rw [smul_eq_mul, mul_smul]; exact smul_mem_smul_top I c hy
  · intro y z hy hz
    exact Submodule.add_mem _ hy hz

end ClearDenominators

section SupportDimZero

/-- A module whose support is a single point has support dimension `0`. -/
private lemma supportDim_eq_zero_of_forall_mem_support_eq {R : Type*} [CommRing R] [IsLocalRing R]
    {W : Type*} [AddCommGroup W] [Module R W] [Nontrivial W]
    (h : ∀ q ∈ Module.support R W, q.asIdeal = IsLocalRing.maximalIdeal R) :
    Module.supportDim R W = 0 := by
  have hne : Module.supportDim R W ≠ ⊥ := Module.supportDim_ne_bot_of_nontrivial R W
  have : Subsingleton (Module.support R W) :=
    ⟨fun a b => Subtype.ext (PrimeSpectrum.ext (by rw [h a.1 a.2, h b.1 b.2]))⟩
  rw [Module.supportDim] at hne ⊢
  have : Nonempty (Module.support R W) := Order.krullDim_ne_bot_iff.mp hne
  exact Order.krullDim_eq_zero

/-- If `𝔮` is the only prime of `S` contained in `𝔮` and containing the annihilator of `W`, then
the localization of `W` at `𝔮` has support dimension `0`. -/
private lemma supportDim_localizedModule_eq_zero {S : Type*} [CommRing S] (𝔮 : Ideal S) [𝔮.IsPrime]
    (W : Type*) [AddCommGroup W] [Module S W] [Nontrivial (LocalizedModule 𝔮.primeCompl W)]
    (h : ∀ 𝔯 : Ideal S, 𝔯.IsPrime → 𝔯 ≤ 𝔮 → Module.annihilator S W ≤ 𝔯 → 𝔯 = 𝔮) :
    Module.supportDim (Localization.AtPrime 𝔮) (LocalizedModule 𝔮.primeCompl W) = 0 := by
  refine supportDim_eq_zero_of_forall_mem_support_eq fun 𝔫 h𝔫 => ?_
  have h𝔫p := 𝔫.2
  have hann :
    Module.annihilator (Localization.AtPrime 𝔮) (LocalizedModule 𝔮.primeCompl W) ≤ 𝔫.asIdeal :=
    Module.annihilator_le_of_mem_support h𝔫
  have hcomap :
    Module.annihilator S W ≤ 𝔫.asIdeal.comap (algebraMap S (Localization.AtPrime 𝔮)) := by
    intro a ha
    refine Ideal.mem_comap.mpr (hann (Module.mem_annihilator.mpr fun x => ?_))
    induction x using LocalizedModule.induction_on with
    | _ w s =>
      rw [algebraMap_smul, LocalizedModule.smul'_mk, Module.mem_annihilator.mp ha w]
      exact LocalizedModule.zero_mk s
  have hle : 𝔫.asIdeal.comap (algebraMap S (Localization.AtPrime 𝔮)) ≤ 𝔮 := by
    intro s hs
    by_contra hsq
    exact
      h𝔫p.ne_top
        (Ideal.eq_top_of_isUnit_mem _ hs
          (IsLocalization.map_units (Localization.AtPrime 𝔮) (⟨s, hsq⟩ : 𝔮.primeCompl)))
  have heq : 𝔫.asIdeal.comap (algebraMap S (Localization.AtPrime 𝔮)) = 𝔮 :=
    h _ (Ideal.comap_isPrime _ _) hle hcomap
  refine le_antisymm (IsLocalRing.le_maximalIdeal h𝔫p.ne_top) fun x hx => ?_
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔮.primeCompl x
  have ha : a ∈ 𝔮 :=
    (IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime 𝔮) 𝔮 a s).mp hx
  have hain :
    IsLocalization.mk' (Localization.AtPrime 𝔮) a s *
        algebraMap S (Localization.AtPrime 𝔮) (s : S) ∈
      𝔫.asIdeal := by
    rw [IsLocalization.mk'_spec]
    exact Ideal.mem_comap.mp (heq.ge ha)
  refine (h𝔫p.mem_or_mem hain).resolve_right fun hcon => ?_
  exact
    h𝔫p.ne_top
      (Ideal.eq_top_of_isUnit_mem _ hcon (IsLocalization.map_units (Localization.AtPrime 𝔮) s))

end SupportDimZero

section Descent

/-- Two lists whose members agree up to units generate the same ideal. -/
private lemma ofList_eq_of_forall₂_unit_mul {R : Type*} [CommRing R] {ss rs : List R}
    (h : List.Forall₂ (fun s r => ∃ u : Rˣ, s = (u : R) * r) ss rs) :
    Ideal.ofList ss = Ideal.ofList rs := by
  induction h with
  | nil => rfl
  | @cons s r ss' rs' hu hrest ih =>
    obtain ⟨u, rfl⟩ := hu
    rw [Ideal.ofList_cons, Ideal.ofList_cons, ih, Ideal.span_singleton_mul_left_unit u.isUnit]

/-- A finite module over a Noetherian ring whose localization at `𝔭` is nonzero and satisfies
`depth = dim Supp` admits a weakly regular sequence on `M_𝔭` consisting of elements of `𝔭`, whose
quotient is annihilated by a power of `𝔭`. -/
private theorem exists_isWeaklyRegular_mem_of_isCohenMacaulay_atPrime {A : Type*} [CommRing A]
    [IsNoetherianRing A] (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (𝔭 : Ideal A) [𝔭.IsPrime] [Nontrivial (LocalizedModule 𝔭.primeCompl M)]
    (hCM :
      (Module.depth (Localization.AtPrime 𝔭) (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭))
            (LocalizedModule 𝔭.primeCompl M) :
          WithBot ℕ∞) =
        Module.supportDim (Localization.AtPrime 𝔭) (LocalizedModule 𝔭.primeCompl M)) :
    ∃ (as : List A) (m : ℕ),
      (∀ a ∈ as, a ∈ 𝔭) ∧
        RingTheory.Sequence.IsWeaklyRegular (LocalizedModule 𝔭.primeCompl M) as ∧
        ∀ a ∈ 𝔭 ^ m,
          ∀ x : LocalizedModule 𝔭.primeCompl M,
            a • x ∈ (Ideal.ofList as • ⊤ : Submodule A (LocalizedModule 𝔭.primeCompl M)) := by
  obtain ⟨d, hd⟩ :=
    exists_supportDim_eq_natCast (R := Localization.AtPrime 𝔭) (LocalizedModule 𝔭.primeCompl M)
  obtain ⟨rs, -, hrsmem, hrsreg, mm, hmm⟩ :=
    exists_isRegular_length_eq_and_pow_maximalIdeal_smul_eq_zero d hd hCM
  have hchoice :
    ∀ r : Localization.AtPrime 𝔭,
      ∃ a : A,
        r ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) →
          a ∈ 𝔭 ∧
            ∃ u : (Localization.AtPrime 𝔭)ˣ,
              algebraMap A (Localization.AtPrime 𝔭) a = (u : Localization.AtPrime 𝔭) * r := by
    intro r
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl r
    refine
      ⟨a, fun hr =>
        ⟨(IsLocalization.AtPrime.mk'_mem_maximal_iff _ 𝔭 a s).mp hr,
          (IsLocalization.map_units (Localization.AtPrime 𝔭) s).unit, ?_⟩⟩
    rw [IsUnit.unit_spec, mul_comm]
    exact (IsLocalization.mk'_spec _ a s).symm
  choose g hg using hchoice
  have hforall₂ :
    List.Forall₂ (fun s r => ∃ u : (Localization.AtPrime 𝔭)ˣ, s = (u : Localization.AtPrime 𝔭) * r)
      ((rs.map g).map (algebraMap A (Localization.AtPrime 𝔭))) rs := by
    rw [List.map_map, List.forall₂_map_left_iff]
    exact List.forall₂_same.mpr fun r hr => (hg r (hrsmem r hr)).2
  have hIeq :
    Ideal.ofList ((rs.map g).map (algebraMap A (Localization.AtPrime 𝔭))) = Ideal.ofList rs :=
    ofList_eq_of_forall₂_unit_mul hforall₂
  refine ⟨rs.map g, mm, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
    exact (hg r (hrsmem r hr)).1
  · exact
      (RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff (S := Localization.AtPrime 𝔭)
            (LocalizedModule 𝔭.primeCompl M) (rs.map g)).mp
        (isWeaklyRegular_of_forall₂_unit_mul hforall₂ hrsreg.toIsWeaklyRegular)
  · intro a ha x
    have hmapa :
      algebraMap A (Localization.AtPrime 𝔭) a ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) ^ mm := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal 𝔭 (Localization.AtPrime 𝔭), ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ ha
    have hmem :
      a • x ∈
        (Ideal.ofList rs •
          (⊤ : Submodule (Localization.AtPrime 𝔭) (LocalizedModule 𝔭.primeCompl M))) := by
      have hzero := hmm _ hmapa (Submodule.mkQ _ x)
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, algebraMap_smul] at hzero
      exact hzero
    refine
      mem_smul_top_of_mem_map_smul_top (A' := Localization.AtPrime 𝔭) (Ideal.ofList (rs.map g)) ?_
    rw [Ideal.map_ofList, hIeq]
    exact hmem

end Descent

section OneVariable

/-- Let `𝔮` be a prime of `A[X]` lying over `𝔭`, let `V` be an `A`-module on which every `c ∉ 𝔭`
acts invertibly, and let `f_1, …, f_d ∈ 𝔭` be a weakly regular sequence on `V` whose quotient is
annihilated by `𝔭 ^ m`. Then `V[X]_𝔮` satisfies `depth = dim Supp`. -/
private theorem depth_eq_supportDim_polynomialModule_localized {A : Type*} [CommRing A]
    [IsNoetherianRing A] {q : Ideal (Polynomial A)} [q.IsPrime] {𝔭 : Ideal A} [𝔭.IsPrime]
    (h𝔭 : q.comap (Polynomial.C : A →+* Polynomial A) = 𝔭) (V : Type*) [AddCommGroup V]
    [Module A V] [Nontrivial (LocalizedModule q.primeCompl (PolynomialModule A V))]
    [Module.Finite (Localization.AtPrime q) (LocalizedModule q.primeCompl (PolynomialModule A V))]
    {as : List A} {m : ℕ} (hasmem : ∀ a ∈ as, a ∈ 𝔭)
    (hasreg : RingTheory.Sequence.IsWeaklyRegular V as)
    (hann : ∀ a ∈ 𝔭 ^ m, ∀ x : V, a • x ∈ (Ideal.ofList as • ⊤ : Submodule A V))
    (hunit : ∀ c ∉ 𝔭, IsUnit (algebraMap A (Module.End A V) c)) :
    (Module.depth (Localization.AtPrime q) (IsLocalRing.maximalIdeal (Localization.AtPrime q))
          (LocalizedModule q.primeCompl (PolynomialModule A V)) :
        WithBot ℕ∞) =
      Module.supportDim (Localization.AtPrime q)
        (LocalizedModule q.primeCompl (PolynomialModule A V)) := by
  have hJ : ∀ a ∈ 𝔭 ^ m, ∀ p : V ⧸ (Ideal.ofList as • (⊤ : Submodule A V)), a • p = 0 :=
    fun a ha => smul_eq_zero_quotient (hann a ha)
  have hcoeff :
    ∀ Q : Submodule (Polynomial A) (PolynomialModule A V),
      Ideal.ofList (as.map (Polynomial.C : A →+* Polynomial A)) •
            (⊤ : Submodule (Polynomial A) (PolynomialModule A V)) ≤
          Q →
        ∀ f : Polynomial A,
          (∀ i, f.coeff i ∈ 𝔭 ^ m) →
            f ∈ Module.annihilator (Polynomial A) (PolynomialModule A V ⧸ Q) := by
    intro Q hQ f hf
    refine Module.mem_annihilator.mpr (smul_eq_zero_quotient fun x => hQ ?_)
    rw [← Ideal.map_ofList]
    exact smul_mem_map_C_smul_top (Ideal.ofList as) (fun i v => hann _ (hf i) v) x
  have hmaple : Ideal.map (Polynomial.C : A →+* Polynomial A) 𝔭 ≤ q := by
    rw [Ideal.map_le_iff_le_comap, h𝔭]
  have hasq : ∀ b ∈ as.map (Polynomial.C : A →+* Polynomial A), b ∈ q := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact hmaple (Ideal.mem_map_of_mem _ (hasmem a ha))
  have hbs₀ :
    RingTheory.Sequence.IsWeaklyRegular (PolynomialModule A V)
      (as.map (Polynomial.C : A →+* Polynomial A)) :=
    isWeaklyRegular_polynomialModule_map_C hasreg
  obtain ⟨bs, hbsq, hbsreg, hbsann⟩ :
    ∃ bs : List (Polynomial A),
      (∀ b ∈ bs, b ∈ q) ∧
        RingTheory.Sequence.IsWeaklyRegular (PolynomialModule A V) bs ∧
        ∀ 𝔯 : Ideal (Polynomial A),
          𝔯.IsPrime →
            𝔯 ≤ q →
            Module.annihilator (Polynomial A)
                (PolynomialModule A V ⧸
                  (Ideal.ofList bs • (⊤ : Submodule (Polynomial A) (PolynomialModule A V)))) ≤
              𝔯 →
            𝔯 = q :=
    by
    by_cases hcase : Ideal.map (Polynomial.C : A →+* Polynomial A) 𝔭 = q
    · refine ⟨as.map (Polynomial.C : A →+* Polynomial A), hasq, hbs₀, ?_⟩
      intro 𝔯 h𝔯 hle hAnn
      refine le_antisymm hle fun y hy => ?_
      refine h𝔯.mem_of_pow_mem m (hAnn (hcoeff _ le_rfl (y ^ m) fun i => ?_))
      have hmem : y ^ m ∈ Ideal.map (Polynomial.C : A →+* Polynomial A) (𝔭 ^ m) := by
        rw [Ideal.map_pow, hcase]
        exact Ideal.pow_mem_pow hy m
      exact (Ideal.mem_map_C_iff.mp hmem) i
    · obtain ⟨g, hgq, k, hgk, hglt⟩ :=
        exists_mem_coeff_notMem_and_forall_gt_coeff_mem q (by rwa [h𝔭])
      rw [h𝔭] at hgk hglt
      refine ⟨as.map (Polynomial.C : A →+* Polynomial A) ++ [g], ?_, ?_, ?_⟩
      · intro b hb
        rcases List.mem_append.mp hb with h | h
        · exact hasq b h
        · rw [List.mem_singleton] at h
          exact h ▸ hgq
      · rw [RingTheory.Sequence.isWeaklyRegular_append_iff]
        refine ⟨hbs₀, ?_⟩
        rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff, ← Ideal.map_ofList]
        refine
          ((polynomialModuleQuotEquiv (V := V) (Ideal.ofList as)).isSMulRegular_congr g).mpr ?_
        exact
          isSMulRegular_polynomialModule_of_forall_gt_coeff_mem hJ
            (isSMulRegular_quotient_smul_top_of_isUnit (Ideal.ofList as) (hunit _ hgk)) hglt
      · intro 𝔯 h𝔯 hle hAnn
        have hann𝔯 : ∀ f : Polynomial A, (∀ i, f.coeff i ∈ 𝔭 ^ m) → f ∈ 𝔯 := fun f hf =>
          hAnn
            (hcoeff _
              (by
                rw [Ideal.ofList_append]; exact Submodule.smul_mono_left le_sup_left)
              f hf)
        have hg𝔯 : g ∈ 𝔯 := by
          refine hAnn (Module.mem_annihilator.mpr
            (smul_eq_zero_quotient fun x => Submodule.smul_mem_smul ?_ Submodule.mem_top))
          rw [Ideal.ofList_append]
          exact Ideal.mem_sup_right (by simp [Ideal.ofList_cons])
        have hcomap𝔯 : 𝔯.comap (Polynomial.C : A →+* Polynomial A) = 𝔭 := by
          refine le_antisymm (h𝔭 ▸ Ideal.comap_mono hle) fun a ha => ?_
          refine Ideal.mem_comap.mpr (h𝔯.mem_of_pow_mem m (hann𝔯 _ fun i => ?_))
          rw [← Polynomial.C_pow, Polynomial.coeff_C]
          rcases eq_or_ne i 0 with rfl | hi
          · simpa using Ideal.pow_mem_pow ha m
          · simp [hi]
        have hne : Ideal.map (Polynomial.C : A →+* Polynomial A) 𝔭 ≠ 𝔯 := fun hcon =>
          hgk
            ((Ideal.mem_map_C_iff.mp
                (show g ∈ Ideal.map (Polynomial.C : A →+* Polynomial A) 𝔭 from hcon ▸ hg𝔯))
              k)
        exact eq_of_le_of_comap_C_eq hcomap𝔯 h𝔭 hle hne
  have hrsmem :
    ∀ r ∈ bs.map (algebraMap (Polynomial A) (Localization.AtPrime q)),
      r ∈ IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
    intro r hr
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hr
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q (Localization.AtPrime q)]
    exact Ideal.mem_map_of_mem _ (hbsq b hb)
  have hwreg :
    RingTheory.Sequence.IsWeaklyRegular (LocalizedModule q.primeCompl (PolynomialModule A V))
      (bs.map (algebraMap (Polynomial A) (Localization.AtPrime q))) :=
    RingTheory.Sequence.IsWeaklyRegular.of_flat_of_isBaseChange
      (IsLocalizedModule.isBaseChange q.primeCompl (Localization.AtPrime q)
        (LocalizedModule.mkLinearMap q.primeCompl (PolynomialModule A V)))
      hbsreg
  have hreg := (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hrsmem).mpr hwreg
  refine depth_eq_supportDim_of_isRegular_of_supportDim_quot_eq_zero hrsmem hreg ?_
  have hlocsm :
    Submodule.localized q.primeCompl
        (Ideal.ofList bs • (⊤ : Submodule (Polynomial A) (PolynomialModule A V))) =
      Ideal.ofList (bs.map (algebraMap (Polynomial A) (Localization.AtPrime q))) •
        (⊤ :
          Submodule (Localization.AtPrime q)
            (LocalizedModule q.primeCompl (PolynomialModule A V))) := by
    rw [Submodule.localized, Submodule.localized'_smul, Submodule.localized'_top,
      Ideal.localized'_eq_map, Ideal.map_ofList]
  have Θ :
    (LocalizedModule q.primeCompl (PolynomialModule A V) ⧸
        (Ideal.ofList (bs.map (algebraMap (Polynomial A) (Localization.AtPrime q))) •
          (⊤ :
            Submodule (Localization.AtPrime q)
              (LocalizedModule q.primeCompl (PolynomialModule A V))))) ≃ₗ[Localization.AtPrime q]
      LocalizedModule q.primeCompl
        (PolynomialModule A V ⧸
          (Ideal.ofList bs • (⊤ : Submodule (Polynomial A) (PolynomialModule A V)))) :=
    (Submodule.quotEquivOfEq _ _ hlocsm.symm).trans (localizedQuotientEquiv q.primeCompl _)
  have hntq :
    Nontrivial
      (LocalizedModule q.primeCompl (PolynomialModule A V) ⧸
        (Ideal.ofList (bs.map (algebraMap (Polynomial A) (Localization.AtPrime q))) •
          (⊤ :
            Submodule (Localization.AtPrime q)
              (LocalizedModule q.primeCompl (PolynomialModule A V))))) := by
    exact Submodule.Quotient.nontrivial_iff.mpr fun hc => hreg.2 hc.symm
  have hntW := Θ.injective.nontrivial
  rw [supportDim_eq_of_linearEquiv Θ]
  exact supportDim_localizedModule_eq_zero q _ hbsann

end OneVariable

/-- If `M` is a finite Cohen–Macaulay module over a Noetherian ring `A`, then the `A[X]`-module
`M[X] = ⨁_{n ≥ 0} M · X ^ n` is Cohen–Macaulay. -/
@[ega "IV 6.11.9" "partial", ega "IV 6.3.6" "special case", ega "IV 7.5.3" "(iii), special case"]
private theorem isCohenMacaulay_polynomialModule {A : Type*} [CommRing A] [IsNoetherianRing A]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hM : Module.IsCohenMacaulay A M) :
    Module.IsCohenMacaulay (Polynomial A) (PolynomialModule A M) := by
  intro 𝔮 h𝔮
  obtain ⟨𝔭, h𝔭⟩ : ∃ 𝔭 : Ideal A, 𝔮.asIdeal.comap (Polynomial.C : A →+* Polynomial A) = 𝔭 :=
    ⟨_, rfl⟩
  have h𝔭p : 𝔭.IsPrime := h𝔭 ▸ Ideal.comap_isPrime _ _
  have hntM : Nontrivial (LocalizedModule 𝔮.asIdeal.primeCompl (PolynomialModule A M)) :=
    Module.mem_support_iff.mp h𝔮
  have hfinM : Module.Finite (Polynomial A) (PolynomialModule A M) := finite_polynomialModule M
  have hfin0 :
    Module.Finite (Localization.AtPrime 𝔮.asIdeal)
      (LocalizedModule 𝔮.asIdeal.primeCompl (PolynomialModule A M)) :=
    inferInstance
  have hloc : IsLocalizedModule 𝔭.primeCompl (LocalizedModule.mkLinearMap 𝔭.primeCompl M) :=
    inferInstance
  have h𝔭' : (𝔮.asIdeal.comap (Polynomial.C : A →+* Polynomial A)).IsPrime := h𝔭 ▸ h𝔭p
  have hloc' :
    IsLocalizedModule (𝔮.asIdeal.comap (Polynomial.C : A →+* Polynomial A)).primeCompl
      (LocalizedModule.mkLinearMap 𝔭.primeCompl M) := by
    have hpc :
      (𝔮.asIdeal.comap (Polynomial.C : A →+* Polynomial A)).primeCompl = 𝔭.primeCompl := by
      refine Submonoid.ext fun x => ?_
      show x ∉ 𝔮.asIdeal.comap (Polynomial.C : A →+* Polynomial A) ↔ x ∉ 𝔭
      rw [h𝔭]
    rw [hpc]
    exact hloc
  have Φ := localizedPolynomialModuleEquiv 𝔮.asIdeal (LocalizedModule.mkLinearMap 𝔭.primeCompl M)
  have hfin :
    Module.Finite (Localization.AtPrime 𝔮.asIdeal)
      (LocalizedModule 𝔮.asIdeal.primeCompl
        (PolynomialModule A (LocalizedModule 𝔭.primeCompl M))) :=
    Module.Finite.equiv Φ
  have hnt :
    Nontrivial
      (LocalizedModule 𝔮.asIdeal.primeCompl
        (PolynomialModule A (LocalizedModule 𝔭.primeCompl M))) :=
    Φ.injective.nontrivial
  have hntV : Nontrivial (LocalizedModule 𝔭.primeCompl M) := by
    by_contra hcon
    have : Subsingleton (LocalizedModule 𝔭.primeCompl M) := not_nontrivial_iff_subsingleton.mp hcon
    exact
      absurd
        (inferInstance :
          Subsingleton
            (LocalizedModule 𝔮.asIdeal.primeCompl
              (PolynomialModule A (LocalizedModule 𝔭.primeCompl M))))
        (not_subsingleton _)
  obtain ⟨as, m, hasmem, hasreg, hann⟩ :=
    exists_isWeaklyRegular_mem_of_isCohenMacaulay_atPrime M 𝔭
      (hM ⟨𝔭, h𝔭p⟩ (Module.mem_support_iff.mpr hntV))
  rw [Module.depth_eq_depth_of_linearEquiv _ Φ, supportDim_eq_of_linearEquiv Φ]
  exact
    depth_eq_supportDim_polynomialModule_localized h𝔭 _ hasmem hasreg hann fun c hc =>
      IsLocalizedModule.map_units (LocalizedModule.mkLinearMap 𝔭.primeCompl M)
        (⟨c, hc⟩ : 𝔭.primeCompl)

/-- Cohen–Macaulayness of `P ⊗[R] M` is carried along an algebra isomorphism `P ≃ₐ[R] S`. -/
private lemma isCohenMacaulay_tensor_of_algEquiv {R P S M : Type*} [CommRing R] [CommRing P]
    [CommRing S] [Algebra R P] [Algebra R S] [AddCommGroup M] [Module R M] (e : P ≃ₐ[R] S)
    (h : Module.IsCohenMacaulay P (P ⊗[R] M)) : Module.IsCohenMacaulay S (S ⊗[R] M) := by
  refine isCohenMacaulay_of_ringEquiv e.toRingEquiv
    (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl R M)).toAddEquiv ?_ h
  intro a x
  induction x with
  | zero => simp
  | tmul p m => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/-- The base change of a finite Cohen–Macaulay module over a Noetherian ring `A` to an
`A`-algebra `S` isomorphic to `A[X]` is Cohen–Macaulay. -/
@[ega "IV 6.11.9" "special case", ega "IV 6.3.6" "special case"]
private theorem isCohenMacaulay_of_isBaseChange_polynomial {A : Type*} [CommRing A]
    [IsNoetherianRing A] {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M] {S : Type*}
    [CommRing S] [Algebra A S] (e : Polynomial A ≃ₐ[A] S) {N : Type*} [AddCommGroup N] [Module A N]
    [Module S N] [IsScalarTower A S N] {f : M →ₗ[A] N} (hf : IsBaseChange S f)
    (hM : Module.IsCohenMacaulay A M) : Module.IsCohenMacaulay S N := by
  refine
    isCohenMacaulay_of_linearEquiv hf.equiv
      (isCohenMacaulay_tensor_of_algEquiv e
        (isCohenMacaulay_of_linearEquiv
          (PolynomialModule.polynomialTensorProductLEquivPolynomialModule A M).symm
          (isCohenMacaulay_polynomialModule M hM)))

/-- If `A` is an `R`-algebra, the base change of `M` to `A` is Cohen–Macaulay and `S` is a
polynomial ring in one variable over `A`, then the base change of `M` to `S` is Cohen–Macaulay. -/
@[ega "IV 6.11.9" "special case"]
private lemma isCohenMacaulay_tensor_of_polynomial_algEquiv {R : Type*} [CommRing R] {A : Type*}
    [CommRing A] [IsNoetherianRing A] [Algebra R A] {S : Type*} [CommRing S] [Algebra R S]
    [Algebra A S] [IsScalarTower R A S] (e : Polynomial A ≃ₐ[A] S) {M : Type*} [AddCommGroup M]
    [Module R M] [Module.Finite R M] (h : Module.IsCohenMacaulay A (A ⊗[R] M)) :
    Module.IsCohenMacaulay S (S ⊗[R] M) :=
  isCohenMacaulay_of_linearEquiv (TensorProduct.AlgebraTensorModule.cancelBaseChange R A S S M)
    (isCohenMacaulay_of_isBaseChange_polynomial e (TensorProduct.isBaseChange A (A ⊗[R] M) S) h)

/-- The base change of a finite Cohen–Macaulay module over a Noetherian ring `R` to
`MvPolynomial (Fin n) R` is Cohen–Macaulay. -/
private theorem isCohenMacaulay_tensor_mvPolynomial_fin :
    ∀ (n : ℕ) {R : Type u} [CommRing R] [IsNoetherianRing R] {M : Type v} [AddCommGroup M]
      [Module R M] [Module.Finite R M],
      Module.IsCohenMacaulay R M →
        Module.IsCohenMacaulay (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R ⊗[R] M) := by
  intro n
  induction n with
  | zero =>
    intro R _ _ M _ _ _ hM
    refine
      isCohenMacaulay_of_ringEquiv (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).symm.toRingEquiv
        (((TensorProduct.lid R M).symm.trans
            (TensorProduct.congr (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).symm.toLinearEquiv
              (LinearEquiv.refl R M))).toAddEquiv)
        ?_ hM
    intro a m
    simp [TensorProduct.smul_tmul', Algebra.smul_def]
  | succ n ih =>
    intro R _ _ M _ _ _ hM
    let e : Polynomial (MvPolynomial (Fin n) R) ≃ₐ[R] MvPolynomial (Fin (n + 1)) R :=
      (MvPolynomial.finSuccEquiv R n).symm
    let _ : Algebra (MvPolynomial (Fin n) R) (MvPolynomial (Fin (n + 1)) R) :=
      ((e : Polynomial (MvPolynomial (Fin n) R) →+* MvPolynomial (Fin (n + 1)) R).comp
          (Polynomial.C :
            MvPolynomial (Fin n) R →+* Polynomial (MvPolynomial (Fin n) R))).toAlgebra
    have _ : IsScalarTower R (MvPolynomial (Fin n) R) (MvPolynomial (Fin (n + 1)) R) := by
      refine IsScalarTower.of_algebraMap_eq fun r => ?_
      have h := e.commutes r
      simpa [RingHom.algebraMap_toAlgebra, e] using h.symm
    exact
      isCohenMacaulay_tensor_of_polynomial_algEquiv
        (AlgEquiv.ofRingEquiv (f := e.toRingEquiv) fun a => rfl) (ih hM)

/-- The base change of a finite Cohen–Macaulay module over a Noetherian ring `R` to
`MvPolynomial σ R`, for `σ` finite, is Cohen–Macaulay. -/
public theorem solution {R : Type*} [CommRing R] [IsNoetherianRing R] {σ : Type*} [Finite σ]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] {N : Type*} [AddCommGroup N]
    [Module R N] [Module (MvPolynomial σ R) N] [IsScalarTower R (MvPolynomial σ R) N]
    {f : M →ₗ[R] N} (hf : IsBaseChange (MvPolynomial σ R) f) (hM : Module.IsCohenMacaulay R M) :
    Module.IsCohenMacaulay (MvPolynomial σ R) N := by
  obtain ⟨n, ⟨eσ⟩⟩ := Finite.exists_equiv_fin σ
  refine
    isCohenMacaulay_of_linearEquiv hf.equiv
      (isCohenMacaulay_tensor_of_algEquiv (MvPolynomial.renameEquiv R eσ.symm)
        (isCohenMacaulay_tensor_mvPolynomial_fin n hM))

end Stacks.CohenMacaulay.PolynomialBaseChange

namespace Module

/-- **Cohen–Macaulayness ascends along a polynomial extension.** Let `R` be a Noetherian ring, let
`M` be a finite Cohen–Macaulay `R`-module, and let `N`, together with an `R`-linear map
`f : M →ₗ[R] N`, be the base change of `M` to the polynomial ring `S = MvPolynomial σ R` in
finitely many variables. Then `N` is a Cohen–Macaulay `S`-module. -/
@[stacks 0AAI "The base change `M ⊗_R R[x_1, …, x_n]` is presented abstractly, as an \
  `S`-module `N` with an `R`-linear `f : M →ₗ[R] N` satisfying `IsBaseChange S f` for \
  `S = MvPolynomial σ R`, as in tag 0AAG and in Mathlib's \
  `RingTheory.Sequence.IsWeaklyRegular.of_flat_of_isBaseChange`; the variables are indexed by \
  an arbitrary finite type rather than by `Fin n`; and the finiteness of `M`, which the source \
  keeps inside Definition 0AAH, is assumed explicitly. See the module docstring.",
  ega "IV 6.3.6",
  ega "IV 6.11.9" "more general"]
public theorem IsCohenMacaulay.mvPolynomial_of_isBaseChange {R : Type*} [CommRing R]
    [IsNoetherianRing R] {σ : Type*} [Finite σ] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] {N : Type*} [AddCommGroup N] [Module R N] [Module (MvPolynomial σ R) N]
    [IsScalarTower R (MvPolynomial σ R) N] {f : M →ₗ[R] N} (hf : IsBaseChange (MvPolynomial σ R) f)
    (hM : IsCohenMacaulay R M) : IsCohenMacaulay (MvPolynomial σ R) N :=
  Stacks.CohenMacaulay.PolynomialBaseChange.solution hf hM

end Module

end

namespace Stacks.CohenMacaulay.PolynomialAlgebra

open IsLocalRing RingTheory.Sequence
open Stacks.Flatness.RegularSequenceQuotient

section RingEquiv

variable {A B : Type*} [CommRing A] [CommRing B]

/-- A ring isomorphism `e : A ≃+* B` maps the `A`-regular sequences contained in an ideal `I`
onto the `B`-regular sequences contained in `Ie`. -/
private lemma image_map_setOf_isRegular (e : A ≃+* B) (I : Ideal A) :
    List.map e '' {rs : List A | (∀ r ∈ rs, r ∈ I) ∧ IsRegular A rs} =
      {ss : List B | (∀ s ∈ ss, s ∈ I.map e) ∧ IsRegular B ss} := by
  have hmem : ∀ a : A, e a ∈ I.map e ↔ a ∈ I := fun _ => by simp
  ext ss
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨rs, ⟨hI, hrs⟩, rfl⟩
    refine ⟨fun s hs => ?_, (isRegular_ringEquiv_congr e rs).mp hrs⟩
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hs
    exact (hmem r).mpr (hI r hr)
  · rintro ⟨hI, hss⟩
    have hmap : (ss.map e.symm).map e = ss := by simp [List.map_map, Function.comp_def]
    refine
      ⟨ss.map e.symm,
        ⟨fun r hr => ?_,
          (isRegular_ringEquiv_congr e _).mpr
            (by
              rw [hmap]; exact hss)⟩,
        hmap⟩
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    exact (hmem _).mp (by simpa using hI s hs)

/-- Cohen–Macaulayness of a local ring depends only on its isomorphism class. -/
public lemma isMaximalCohenMacaulay_self_congr [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    Module.IsMaximalCohenMacaulay A A ↔ Module.IsMaximalCohenMacaulay B B := by
  rw [Module.IsMaximalCohenMacaulay, Module.IsMaximalCohenMacaulay,
    Module.depth_self_eq_of_ringEquiv e, ringKrullDim_eq_of_ringEquiv e]

end RingEquiv

/-- A commutative ring is a Cohen–Macaulay module over itself exactly when all of its
localizations at primes are Cohen–Macaulay local rings. -/
private lemma isCohenMacaulay_self_iff_forall_localization (R : Type*) [CommRing R] :
    Module.IsCohenMacaulay R R ↔
      ∀ (p : Ideal R) [p.IsPrime],
        Module.IsMaximalCohenMacaulay (Localization.AtPrime p) (Localization.AtPrime p) := by
  simp only [Module.IsCohenMacaulay, Module.support_self, Set.mem_univ, forall_const,
    Module.IsMaximalCohenMacaulay, ← Module.supportDim_self_eq_ringKrullDim]
  exact ⟨fun h p _ => h ⟨p, ‹_›⟩, fun h p => h p.asIdeal⟩

/-- Every localization at a prime of a polynomial algebra in finitely many variables over a
Noetherian Cohen–Macaulay ring is a Cohen–Macaulay local ring. -/
public theorem solution {R : Type*} [CommRing R] [IsNoetherianRing R]
    (hR :
      ∀ (p : Ideal R) [p.IsPrime],
        Module.IsMaximalCohenMacaulay (Localization.AtPrime p) (Localization.AtPrime p))
    {σ : Type*} [Finite σ] (q : Ideal (MvPolynomial σ R)) [q.IsPrime] (S : Type*) [CommRing S]
    [Algebra (MvPolynomial σ R) S] [IsLocalization.AtPrime S q] [IsLocalRing S] :
    Module.IsMaximalCohenMacaulay S S :=
  have hP : Module.IsCohenMacaulay (MvPolynomial σ R) (MvPolynomial σ R) :=
    Module.IsCohenMacaulay.mvPolynomial_of_isBaseChange
      (IsBaseChange.linearMap R (MvPolynomial σ R))
      ((isCohenMacaulay_self_iff_forall_localization R).mpr hR)
  (isMaximalCohenMacaulay_self_congr
        (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) S).toRingEquiv).mp
    ((isCohenMacaulay_self_iff_forall_localization _).mp hP q)

end Stacks.CohenMacaulay.PolynomialAlgebra

/-- **A polynomial algebra over a Noetherian Cohen–Macaulay ring is Cohen–Macaulay.** Let `R` be
a Noetherian ring all of whose local rings `R_𝔭` are Cohen–Macaulay, and let `σ` be finite. Then
for every prime `𝔮` of `R[x_i : i ∈ σ]`, every localization `S` of `R[x_i : i ∈ σ]` at `𝔮` is a
Cohen–Macaulay local ring. -/
@[stacks 00ND "Cohen-Macaulayness of a Noetherian local ring is `Module.IsMaximalCohenMacaulay S S`
(Definition 00N8); that of a Noetherian ring (Definition 00NC) is spelled out as a condition on
its localizations at primes, the hypothesis at the concrete `Localization.AtPrime` and the
conclusion at an abstract `IsLocalization.AtPrime`; `R[x_1, …, x_n]` is `MvPolynomial σ R` for
finite `σ`. See the module docstring.", ega "IV 6.3.6", ega "IV 6.11.9"]
public theorem Module.IsMaximalCohenMacaulay.of_isLocalization_atPrime_mvPolynomial {R : Type*}
    [CommRing R] [IsNoetherianRing R]
    (hR :
      ∀ (p : Ideal R) [p.IsPrime],
        Module.IsMaximalCohenMacaulay (Localization.AtPrime p) (Localization.AtPrime p))
    {σ : Type*} [Finite σ] (q : Ideal (MvPolynomial σ R)) [q.IsPrime] (S : Type*) [CommRing S]
    [Algebra (MvPolynomial σ R) S] [IsLocalization.AtPrime S q] [IsLocalRing S] :
    Module.IsMaximalCohenMacaulay S S :=
  Stacks.CohenMacaulay.PolynomialAlgebra.solution hR q S

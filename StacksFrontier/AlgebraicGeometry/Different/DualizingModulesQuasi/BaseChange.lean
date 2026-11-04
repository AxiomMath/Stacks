module

public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.RingTheory.TensorProduct.Finite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.ZariskisMainTheorem
public import StacksFrontier.AlgebraicGeometry.Discriminant.TraceElement

/-!
# Base change for relative dualizing modules

A finite-open factorization of a quasi-finite algebra base changes to a finite-open
factorization of the scalar extension: the intermediate algebra becomes `A₁ ⊗[A] B'`, which is
still finite over `A₁`, and the induced map of spectra is still an open immersion. Transporting
the dual of the intermediate algebra along the base change then gives a canonical map between
the corresponding relative dualizing modules.

## Main definitions

* `Stacks.Discriminant.FiniteOpenFactorization.baseChange` is the factorization obtained by
  scalar extension, with middle algebra `A₁ ⊗[A] B'`.
* `Stacks.Discriminant.dualizingModule.baseChange` is the canonical base change map on relative
  dualizing modules.

## Main results

* `Stacks.Discriminant.FiniteOpenFactorization.baseChange_isOpenEmbedding` and
  `Stacks.Discriminant.FiniteOpenFactorization.baseChange_awayMap_bijective` are the two
  open-immersion conditions for the base-changed factorization.
* `Stacks.Discriminant.dualizingModule.baseChange_tmul` computes the base change map on pure
  tensors.

## Implementation notes

The tensor-product algebra is written `A₁ ⊗[A] B` rather than `B ⊗[A] A₁`; the two orders are
canonically isomorphic. The chosen factorization remains explicit, because independence of that
choice is the content of the following result in the source.

The away-localization condition is verified first for the distinguished elements `1 ⊗ c`, where
it follows by comparing the two localizations through the canonical base change of an away
localization; the general case is then deduced from the pointwise local data, which is where the
hypothesis-free form of the away-bijectivity criterion is needed.

## References

* [Stacks Project, Tag 0BVB](https://stacks.math.columbia.edu/tag/0BVB)
-/

@[expose] public section

open scoped TensorProduct
open Topology

universe u v w x

namespace Stacks.Discriminant

namespace FiniteOpenFactorization

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

private theorem baseChange_awayMap_bijective_tmul
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (A₁ : Type x) [CommRing A₁] [Algebra A A₁] (c : F.middle)
    (hc : Function.Bijective (Localization.awayMap
      (algebraMap F.middle B) c)) :
    letI : Algebra (A₁ ⊗[A] F.middle) (A₁ ⊗[A] B) :=
      (Algebra.TensorProduct.map (AlgHom.id A A₁)
        (IsScalarTower.toAlgHom A F.middle B)).toRingHom.toAlgebra
    Function.Bijective (Localization.awayMap
      (algebraMap (A₁ ⊗[A] F.middle) (A₁ ⊗[A] B)) ((1 : A₁) ⊗ₜ[A] c)) := by
  let C := F.middle
  let B₀ := B
  let C₁ := A₁ ⊗[A] C
  let B₁ := A₁ ⊗[A] B₀
  let _ : CommRing C := F.commRingMiddle
  let _ : Algebra A C := F.algebraMiddle
  let _ : Algebra C B₀ := F.algebraTarget
  let _ : IsScalarTower A C B₀ := F.scalarTower
  let _ : Algebra C₁ B₁ :=
    (Algebra.TensorProduct.map (AlgHom.id A A₁)
      (IsScalarTower.toAlgHom A C B₀)).toRingHom.toAlgebra
  let _ : IsScalarTower A₁ C₁ B₁ := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    show (a ⊗ₜ[A] (1 : B₀)) =
      (Algebra.TensorProduct.map (AlgHom.id A A₁)
        (IsScalarTower.toAlgHom A C B₀)) (a ⊗ₜ[A] (1 : C))
    simp [Algebra.TensorProduct.map_tmul]
  let f : C →ₐ[C] B₀ := Algebra.ofId C B₀
  let fLoc : Localization.Away c →ₐ[C] Localization.Away (algebraMap C B₀ c) :=
    Localization.awayMapₐ f c
  let e : Localization.Away c ≃ₐ[C] Localization.Away (algebraMap C B₀ c) :=
    AlgEquiv.ofBijective fLoc hc
  let EC := IsLocalization.Away.tensorProductEquivTMulRight
    (R := A) (S := A₁) c (Localization.Away c)
  let r : C₁ := (1 : A₁) ⊗ₜ[A] c
  have hdenom : algebraMap C₁ B₁ r =
      (1 : A₁) ⊗ₜ[A] algebraMap C B₀ c := by
    show (Algebra.TensorProduct.map (AlgHom.id A A₁)
      (IsScalarTower.toAlgHom A C B₀)) ((1 : A₁) ⊗ₜ[A] c) = _
    simp [Algebra.TensorProduct.map_tmul]
  let EB₀ := IsLocalization.Away.tensorProductEquivTMulRight
    (R := A) (S := A₁) (algebraMap C B₀ c)
      (Localization.Away (algebraMap C B₀ c))
  let EB : A₁ ⊗[A] Localization.Away (algebraMap C B₀ c) ≃ₐ[A₁]
      Localization.Away (algebraMap C₁ B₁ r) :=
    EB₀.trans (AlgEquiv.cast (R := A₁)
      (A := fun d : B₁ => Localization.Away d) hdenom.symm)
  let eT : A₁ ⊗[A] Localization.Away c ≃ₐ[A₁]
      A₁ ⊗[A] Localization.Away (algebraMap C B₀ c) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : A₁ ≃ₐ[A₁] A₁)
      (e.restrictScalars A)
  let E := EC.symm.trans (eT.trans EB)
  let φ := Localization.awayMap
    (algebraMap (A₁ ⊗[A] C) (A₁ ⊗[A] B₀)) ((1 : A₁) ⊗ₜ[A] c)
  have hcompat (z : A₁ ⊗[A] C) :
      φ (algebraMap (A₁ ⊗[A] C)
        (Localization.Away ((1 : A₁) ⊗ₜ[A] c)) z) =
        algebraMap B₁ (Localization.Away (algebraMap C₁ B₁ r))
          ((Algebra.TensorProduct.map (AlgHom.id A A₁)
            (IsScalarTower.toAlgHom A C B₀)) z) := by
    dsimp only [φ]
    rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
    rfl
  have hcomp : E.toRingHom.comp
      (algebraMap (A₁ ⊗[A] C) (Localization.Away ((1 : A₁) ⊗ₜ[A] c))) =
      φ.comp
          (algebraMap (A₁ ⊗[A] C)
            (Localization.Away ((1 : A₁) ⊗ₜ[A] c))) := by
    apply RingHom.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z₁ z₂ hz₁ hz₂ => simpa only [map_add] using congrArg₂ (· + ·) hz₁ hz₂
    | tmul a c' =>
        let _ : Algebra C (Localization.Away c) := inferInstance
        let _ : Algebra C (Localization.Away (algebraMap C B₀ c)) := inferInstance
        let _ : Algebra B₀ (Localization.Away (algebraMap C B₀ c)) := inferInstance
        let _ : IsScalarTower C B₀ (Localization.Away (algebraMap C B₀ c)) :=
          IsScalarTower.of_algebraMap_eq (by intro z; rfl)
        have hEC' : EC (a ⊗ₜ[A] algebraMap C (Localization.Away c) c') =
            algebraMap (A₁ ⊗[A] C)
              (Localization.Away ((1 : A₁) ⊗ₜ[A] c)) (a ⊗ₜ[A] c') :=
          IsLocalization.Away.tensorProductEquivTMulRight_tmul
            (A := C) c (Localization.Away c) a c'
        have hEC : EC.symm (algebraMap (A₁ ⊗[A] C)
            (Localization.Away ((1 : A₁) ⊗ₜ[A] c)) (a ⊗ₜ[A] c')) =
            a ⊗ₜ[A] algebraMap C (Localization.Away c) c' := by
          apply EC.injective
          rw [EC.apply_symm_apply, hEC'.symm]
        have hET : eT (a ⊗ₜ[A] algebraMap C (Localization.Away c) c') =
            a ⊗ₜ[A] algebraMap B₀
              (Localization.Away (algebraMap C B₀ c)) (algebraMap C B₀ c') := by
          calc
            eT (a ⊗ₜ[A] algebraMap C (Localization.Away c) c') =
                a ⊗ₜ[A] algebraMap C (Localization.Away (algebraMap C B₀ c)) c' := by
                  simp [eT, Algebra.TensorProduct.congr_apply,
                    Algebra.TensorProduct.map_tmul, e]
            _ = a ⊗ₜ[A] algebraMap B₀
                (Localization.Away (algebraMap C B₀ c)) (algebraMap C B₀ c') :=
                  congrArg (fun y => a ⊗ₜ[A] y)
                    (IsScalarTower.algebraMap_apply C B₀
                      (Localization.Away (algebraMap C B₀ c)) c').symm
        have hEB : EB (a ⊗ₜ[A]
            algebraMap B₀ (Localization.Away (algebraMap C B₀ c))
              (algebraMap C B₀ c')) =
            algebraMap B₁ (Localization.Away (algebraMap C₁ B₁ r))
              (a ⊗ₜ[A] algebraMap C B₀ c') := by
          have hEBraw := IsLocalization.Away.tensorProductEquivTMulRight_tmul
              (R := A) (S := A₁) (A := B₀) (algebraMap C B₀ c)
              (Localization.Away (algebraMap C B₀ c)) a (algebraMap C B₀ c')
          show (AlgEquiv.cast (R := A₁)
            (A := fun d : B₁ => Localization.Away d)
            hdenom.symm) (EB₀ (a ⊗ₜ[A]
              algebraMap B₀ (Localization.Away (algebraMap C B₀ c))
                (algebraMap C B₀ c'))) = _
          rw [hEBraw]
          cases hdenom
          rfl
        calc
          E (algebraMap (A₁ ⊗[A] C)
              (Localization.Away ((1 : A₁) ⊗ₜ[A] c)) (a ⊗ₜ[A] c')) =
              EB (eT (a ⊗ₜ[A] algebraMap C (Localization.Away c) c')) := by
                simp [E, hEC]
          _ = EB (a ⊗ₜ[A]
              algebraMap B₀ (Localization.Away (algebraMap C B₀ c))
                (algebraMap C B₀ c')) := by rw [hET]
          _ = algebraMap B₁ (Localization.Away (algebraMap C₁ B₁ r))
              (a ⊗ₜ[A] algebraMap C B₀ c') := hEB
          _ = algebraMap B₁ (Localization.Away (algebraMap C₁ B₁ r))
              ((Algebra.TensorProduct.map (AlgHom.id A A₁)
                (IsScalarTower.toAlgHom A C B₀)) (a ⊗ₜ[A] c')) := by
                rw [hdenom]
                simp [Algebra.TensorProduct.map_tmul]
          _ = φ (algebraMap (A₁ ⊗[A] C)
                (Localization.Away ((1 : A₁) ⊗ₜ[A] c)) (a ⊗ₜ[A] c')) :=
                  (hcompat (a ⊗ₜ[A] c')).symm
  have hmap : Localization.awayMap
      (algebraMap (A₁ ⊗[A] C) (A₁ ⊗[A] B₀)) ((1 : A₁) ⊗ₜ[A] c) = E.toRingHom :=
    IsLocalization.ringHom_ext (Submonoid.powers ((1 : A₁) ⊗ₜ[A] c)) hcomp.symm
  rw [hmap]
  exact E.bijective

/-- The algebra structure making `A₁ ⊗[A] B` an algebra over `A₁ ⊗[A] B'`. -/
@[instance_reducible] noncomputable def baseChangeAlgebra
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (A₁ : Type x) [CommRing A₁] [Algebra A A₁] :
    Algebra (A₁ ⊗[A] F.middle) (A₁ ⊗[A] B) :=
  (Algebra.TensorProduct.map (AlgHom.id A A₁)
    (IsScalarTower.toAlgHom A F.middle B)).toRingHom.toAlgebra

/-- Every prime of `A₁ ⊗[A] B` avoids some `1 ⊗ c` with bijective away localization map. -/
private theorem baseChange_exists_awayMap_bijective
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (A₁ : Type x) [CommRing A₁] [Algebra A A₁] :
    letI := baseChangeAlgebra F A₁
    ∀ q : PrimeSpectrum (A₁ ⊗[A] B), ∃ g : A₁ ⊗[A] F.middle,
      algebraMap (A₁ ⊗[A] F.middle) (A₁ ⊗[A] B) g ∉ q.asIdeal ∧
        Function.Bijective (Localization.awayMap
          (algebraMap (A₁ ⊗[A] F.middle) (A₁ ⊗[A] B)) g) := by
  let C := F.middle
  let C₁ := A₁ ⊗[A] C
  let B₁ := A₁ ⊗[A] B
  let _ : CommRing C := F.commRingMiddle
  let _ : Algebra A C := F.algebraMiddle
  let _ : Algebra C B := F.algebraTarget
  let _ : IsScalarTower A C B := F.scalarTower
  let _ : Algebra C₁ B₁ := baseChangeAlgebra F A₁
  let _ : Algebra B B₁ := Algebra.TensorProduct.rightAlgebra
  intro q
  let q₀ : PrimeSpectrum B := PrimeSpectrum.comap (algebraMap B B₁) q
  let p := PrimeSpectrum.comap (algebraMap C B) q₀
  have hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap C B)) := ⟨q₀, rfl⟩
  obtain ⟨_, ⟨_, ⟨c, rfl⟩, rfl⟩, hpc, hbasic⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hp
      F.isOpenEmbedding_comap.isOpen_range
  have hc : c ∉ p.asIdeal := by simpa [p] using hpc
  have hc₀ : algebraMap C B c ∉ q₀.asIdeal := by simpa [p, q₀] using hc
  have hvalue : algebraMap C₁ B₁ ((1 : A₁) ⊗ₜ[A] c) =
      algebraMap B B₁ (algebraMap C B c) := by
    show (Algebra.TensorProduct.map (AlgHom.id A A₁)
      (IsScalarTower.toAlgHom A C B)) ((1 : A₁) ⊗ₜ[A] c) = _
    show (1 : A₁) ⊗ₜ[A] algebraMap C B c =
      (1 : A₁) ⊗ₜ[A] algebraMap C B c
    rfl
  refine ⟨(1 : A₁) ⊗ₜ[A] c, ?_, ?_⟩
  · rw [hvalue]
    simpa [q₀] using hc₀
  · exact baseChange_awayMap_bijective_tmul F A₁ c
      (F.awayMap_bijective c hbasic)

/-- The base-changed factorization still induces an open embedding on prime spectra. -/
theorem baseChange_isOpenEmbedding
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (A₁ : Type x) [CommRing A₁] [Algebra A A₁] :
    letI := baseChangeAlgebra F A₁
    IsOpenEmbedding (PrimeSpectrum.comap
      (algebraMap (A₁ ⊗[A] F.middle) (A₁ ⊗[A] B))) :=
  isOpenEmbedding_comap_of_forall_exists_awayMap_bijective _
    (baseChange_exists_awayMap_bijective F A₁)

/-- Let `f : R →+* S` be a ring map such that every prime of `S` avoids `f c` for some `c : R`
with `Localization.awayMap f c` bijective. If `D(g) ⊆ Spec R` lies in the image of
`Spec S → Spec R`, then `Localization.awayMap f g` is injective. -/
theorem awayMap_injective_of_basicOpen_subset_range_of_local_data
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (g : R)
    (hg : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) ⊆
      Set.range (PrimeSpectrum.comap f))
    (H : ∀ q : PrimeSpectrum S, ∃ c : R, f c ∉ q.asIdeal ∧
      Function.Bijective (Localization.awayMap f c)) :
    Function.Injective (Localization.awayMap f g) := by
  rw [Localization.awayMap_injective_iff]
  intro a hfa
  by_contra hnot
  push Not at hnot
  let I : Ideal R := Ideal.torsionOf R R a
  have hdisj : Disjoint (I : Set R) (Submonoid.powers g : Set R) := by
    rw [Set.disjoint_left]
    intro z hzI hzpow
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hzpow
    exact hnot n ((Ideal.mem_torsionOf_iff a _).mp hzI)
  obtain ⟨p, hp, hIp, hpdisj⟩ := Ideal.exists_le_prime_disjoint I
    (Submonoid.powers g) hdisj
  have hgn : g ∉ p := fun hgp => Set.disjoint_left.mp hpdisj hgp (Submonoid.mem_powers g)
  let pSpec : PrimeSpectrum R := ⟨p, hp⟩
  obtain ⟨q, hpq⟩ := hg ((PrimeSpectrum.mem_basicOpen g pSpec).2 hgn)
  obtain ⟨c, hc, hcbij⟩ := H q
  have hcp : c ∉ p := by
    intro hcp
    apply hc
    have hmem : c ∈ (PrimeSpectrum.comap f q).asIdeal := by
      rw [hpq]
      exact hcp
    rwa [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at hmem
  have hcompat (z : R) :
      Localization.awayMap f c (algebraMap R (Localization.Away c) z) =
        algebraMap S (Localization.Away (f c)) (f z) := by
    rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
  have hzero : Localization.awayMap f c
      (algebraMap R (Localization.Away c) a) = 0 := by
    rw [hcompat, hfa, map_zero]
  have hlocalzero : algebraMap R (Localization.Away c) a = 0 :=
    hcbij.1 (by simpa using hzero)
  obtain ⟨m, hma⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers c)
      (Localization.Away c) a).mp hlocalzero
  have hmnot : (m : R) ∉ p := by
    intro hmp
    rcases (Submonoid.mem_powers_iff _ _).mp m.2 with ⟨n, hn⟩
    exact hcp (hp.mem_of_pow_mem n (hn ▸ hmp))
  have hmI : (m : R) ∈ I := by
    rw [Ideal.mem_torsionOf_iff]
    simpa [Algebra.smul_def] using hma
  exact hmnot (hIp hmI)

/-- Let `f : R →+* S` be a ring map such that every prime of `S` avoids `f c` for some `c : R`
with `Localization.awayMap f c` bijective. If `D(g) ⊆ Spec R` lies in the image of
`Spec S → Spec R`, then `Localization.awayMap f g` is bijective. -/
theorem awayMap_bijective_of_basicOpen_subset_range_of_local_data
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (H : ∀ q : PrimeSpectrum S, ∃ c : R, f c ∉ q.asIdeal ∧
      Function.Bijective (Localization.awayMap f c))
    (g : R) (hg : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum R)) ⊆
      Set.range (PrimeSpectrum.comap f)) :
    Function.Bijective (Localization.awayMap f g) := by
  set φ := Localization.awayMap f g with hφ
  let : Algebra (Localization.Away g) (Localization.Away (f g)) := φ.toAlgebra
  set A' := Localization.Away g
  set B' := Localization.Away (f g)
  have hcompat (z : R) : φ (algebraMap R A' z) = algebraMap S B' (f z) := by
    rw [hφ, Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
  have hφ_inj : Function.Injective φ :=
    awayMap_injective_of_basicOpen_subset_range_of_local_data f g hg H
  show Function.Bijective (Algebra.linearMap A' B')
  apply bijective_of_localized_maximal
  intro J hJ
  refine ⟨LocalizedModule.map_injective J.primeCompl _ hφ_inj,
    LocalizedModule.map_surjective_of_forall_exists_smul_eq _ _ fun b => ?_⟩
  have := hJ.isPrime
  have hgJ : algebraMap R A' g ∉ J := fun hc =>
    hJ.ne_top (Ideal.eq_top_of_isUnit_mem _ hc (IsLocalization.Away.algebraMap_isUnit g))
  obtain ⟨Q, hQ⟩ := hg (show (⟨J.comap (algebraMap R A'),
      Ideal.IsPrime.comap (algebraMap R A')⟩ :
      PrimeSpectrum R) ∈ PrimeSpectrum.basicOpen g from hgJ)
  obtain ⟨g', hg'Q, hg'bij⟩ := H Q
  have hg'J : algebraMap R A' g' ∉ J := fun hc =>
    hg'Q (show g' ∈ (PrimeSpectrum.comap f Q).asIdeal by rw [hQ]; exact hc)
  obtain ⟨n, x, hbeq⟩ := IsLocalization.Away.surj (f g) b
  obtain ⟨y, K, M, hy⟩ := exists_pow_mul_eq_of_awayMap_surjective f g' hg'bij.2 x
  refine ⟨algebraMap R A' g' ^ M * algebraMap R A' y,
    ⟨algebraMap R A' g' ^ K * algebraMap R A' g ^ n,
      J.primeCompl.mul_mem (pow_mem hg'J K) (pow_mem hgJ n)⟩, ?_⟩
  show φ (algebraMap R A' g' ^ K * algebraMap R A' g ^ n) * b =
    φ (algebraMap R A' g' ^ M * algebraMap R A' y)
  have hy' := congrArg (algebraMap S B') hy
  simp only [map_mul, map_pow, hcompat] at hy' ⊢
  linear_combination algebraMap S B' (f g') ^ K * hbeq + hy'

/-- The away localizations of the base-changed factorization over basic opens inside the image
are bijective. -/
theorem baseChange_awayMap_bijective
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (A₁ : Type x) [CommRing A₁] [Algebra A A₁] :
    letI := baseChangeAlgebra F A₁
    ∀ (g : A₁ ⊗[A] F.middle)
      (_ : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum (A₁ ⊗[A] F.middle))) ⊆
        Set.range (PrimeSpectrum.comap
          (algebraMap (A₁ ⊗[A] F.middle) (A₁ ⊗[A] B)))),
      Function.Bijective (Localization.awayMap
        (algebraMap (A₁ ⊗[A] F.middle) (A₁ ⊗[A] B)) g) :=
  awayMap_bijective_of_basicOpen_subset_range_of_local_data _
    (baseChange_exists_awayMap_bijective F A₁)

/-- The base change of a finite-open factorization is compatible with the scalar tower. -/
theorem baseChange_scalarTower
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (A₁ : Type x) [CommRing A₁] [Algebra A A₁] :
    letI := baseChangeAlgebra F A₁
    IsScalarTower A₁ (A₁ ⊗[A] F.middle) (A₁ ⊗[A] B) := by
  let _ := baseChangeAlgebra F A₁
  apply IsScalarTower.of_algebraMap_eq
  intro a
  show (a ⊗ₜ[A] (1 : B)) =
    (Algebra.TensorProduct.map (AlgHom.id A A₁)
      (IsScalarTower.toAlgHom A F.middle B)) (a ⊗ₜ[A] (1 : F.middle))
  simp [Algebra.TensorProduct.map_tmul]

/-- Scalar extension of a finite-open factorization. -/
noncomputable def baseChange (F : FiniteOpenFactorization.{u, v, w} A B)
    (A₁ : Type x) [CommRing A₁] [Algebra A A₁] :
    FiniteOpenFactorization.{x, max x v, max x w} A₁ (A₁ ⊗[A] B) where
  middle := A₁ ⊗[A] F.middle
  commRingMiddle := inferInstance
  algebraMiddle := inferInstance
  algebraTarget := baseChangeAlgebra F A₁
  scalarTower := baseChange_scalarTower F A₁
  finite_middle := Module.Finite.base_change A A₁ F.middle
  isOpenEmbedding_comap := baseChange_isOpenEmbedding F A₁
  awayMap_bijective := baseChange_awayMap_bijective F A₁

/-- The intermediate algebra of the base-changed factorization is the scalar extension of the
original intermediate algebra. -/
@[simp]
lemma baseChange_middle (F : FiniteOpenFactorization.{u, v, w} A B)
    (A₁ : Type x) [CommRing A₁] [Algebra A A₁] :
    (baseChange F A₁).middle = A₁ ⊗[A] F.middle := rfl

/-- A finite algebra `C` over `A` with an algebra map `C → B` is a finite-open factorization of
`B` as soon as every prime of `B` avoids the image of some `c ∈ C` at which the map of away
localizations `C_c → B_c` is bijective. -/
noncomputable def ofLocalData {C : Type w} [CommRing C] [Algebra A C] [Algebra C B]
    [IsScalarTower A C B] [Module.Finite A C]
    (H : ∀ q : PrimeSpectrum B, ∃ c : C, algebraMap C B c ∉ q.asIdeal ∧
      Function.Bijective (Localization.awayMap (algebraMap C B) c)) :
    FiniteOpenFactorization.{u, v, w} A B where
  middle := C
  commRingMiddle := inferInstance
  algebraMiddle := inferInstance
  algebraTarget := inferInstance
  scalarTower := inferInstance
  finite_middle := inferInstance
  isOpenEmbedding_comap :=
    isOpenEmbedding_comap_of_forall_exists_awayMap_bijective (algebraMap C B) H
  awayMap_bijective g hg :=
    awayMap_bijective_of_basicOpen_subset_range_of_local_data (algebraMap C B) H g hg

/-- The intermediate algebra of `ofLocalData` is the given algebra. -/
@[simp]
lemma ofLocalData_middle {C : Type w} [CommRing C] [Algebra A C] [Algebra C B]
    [IsScalarTower A C B] [Module.Finite A C]
    (H : ∀ q : PrimeSpectrum B, ∃ c : C, algebraMap C B c ∉ q.asIdeal ∧
      Function.Bijective (Localization.awayMap (algebraMap C B) c)) :
    (ofLocalData (A := A) H).middle = C := rfl

/-- The local condition of `ofLocalData` holds as soon as finitely many elements of `C` whose
images generate the unit ideal of `B` have bijective away localizations. -/
theorem forall_exists_awayMap_bijective_of_span_eq_top {C : Type w} [CommRing C]
    [Algebra C B] (s : Set C)
    (hs : Ideal.span (algebraMap C B '' s) = ⊤)
    (hb : ∀ c ∈ s, Function.Bijective (Localization.awayMap (algebraMap C B) c)) :
    ∀ q : PrimeSpectrum B, ∃ c : C, algebraMap C B c ∉ q.asIdeal ∧
      Function.Bijective (Localization.awayMap (algebraMap C B) c) := by
  intro q
  by_contra! hq
  have hle : Ideal.span (algebraMap C B '' s) ≤ q.asIdeal := by
    rw [Ideal.span_le]
    rintro _ ⟨c, hc, rfl⟩
    by_contra hnot
    exact hq c hnot (hb c hc) |>.elim
  exact q.isPrime.ne_top (top_le_iff.mp (hs ▸ hle))

end FiniteOpenFactorization

namespace dualizingModule

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

private theorem dualBaseChange_middle_smul
    {A : Type u} {C : Type w} {A₁ : Type x}
    [CommRing A] [CommRing C] [CommRing A₁] [Algebra A C] [Algebra A A₁]
    (f : Module.Dual A C) (c : C) :
    letI := algebraDualModule A C
    letI := algebraDualModule A₁ (A₁ ⊗[A] C)
    letI : Algebra C (A₁ ⊗[A] C) := Algebra.TensorProduct.rightAlgebra
    letI : Module C (Module.Dual A₁ (A₁ ⊗[A] C)) :=
      Module.compHom _ (algebraMap C (A₁ ⊗[A] C))
    (c • f).baseChange A₁ = c • f.baseChange A₁ := by
  let _ := algebraDualModule A C
  let _ := algebraDualModule A₁ (A₁ ⊗[A] C)
  let _ : Algebra C (A₁ ⊗[A] C) := Algebra.TensorProduct.rightAlgebra
  let _ : Module C (Module.Dual A₁ (A₁ ⊗[A] C)) :=
    Module.compHom _ (algebraMap C (A₁ ⊗[A] C))
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul a₁ c' =>
      show f (c * c') • a₁ =
        (f.baseChange A₁) (((1 : A₁) ⊗ₜ[A] c) * (a₁ ⊗ₜ[A] c'))
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      simp [Module.Dual.baseChange_apply_tmul]

/-- **Stacks Project, Tag 0BVB.** The canonical base change map on relative dualizing
modules, computed using a chosen finite-open factorization.  On the dual factor it extends
`φ : B' →ₗ[A] A` to the `A₁`-linear map sending `a₁ ⊗ b'` to
`a₁ * algebraMap A A₁ (φ b')`; tensoring this map with `B → A₁ ⊗[A] B` gives the displayed
map. -/
@[stacks 0BVB "the base change map"]
noncomputable def baseChange (F : FiniteOpenFactorization.{u, v, w} A B)
    (A₁ : Type x) [CommRing A₁] [Algebra A A₁] :
    letI : Algebra B (A₁ ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
    letI : Module B
        (dualizingModule (FiniteOpenFactorization.baseChange F A₁)) :=
      Module.compHom _ (algebraMap B (A₁ ⊗[A] B))
    dualizingModule F →ₗ[B]
      dualizingModule (FiniteOpenFactorization.baseChange F A₁) := by
  let F₁ := FiniteOpenFactorization.baseChange F A₁
  let C₁ := F₁.middle
  let B₁ := A₁ ⊗[A] B
  let _ := algebraDualModule A F.middle
  let _ := algebraDualModule A₁ C₁
  let : Algebra F.middle C₁ := Algebra.TensorProduct.rightAlgebra
  let : Module F.middle (Module.Dual A₁ C₁) :=
    Module.compHom _ (algebraMap F.middle C₁)
  let : Module F.middle (dualizingModule F) := TensorProduct.leftModule
  let : Module B (dualizingModule F) := by
    unfold dualizingModule
    let _ := algebraDualModule A F.middle
    let : Module B (B ⊗[F.middle] Module.Dual A F.middle) := TensorProduct.leftModule
    exact (TensorProduct.comm F.middle (Module.Dual A F.middle) B).toAddEquiv.module B
  let : Module B (Module.Dual A F.middle ⊗[F.middle] B) :=
    (TensorProduct.comm F.middle (Module.Dual A F.middle) B).toAddEquiv.module B
  let : Module C₁ B₁ := Module.compHom _ (algebraMap C₁ B₁)
  let : Algebra B B₁ := Algebra.TensorProduct.rightAlgebra
  let : Module B (dualizingModule F₁) := Module.compHom _ (algebraMap B B₁)
  let : Module C₁ (dualizingModule F₁) :=
    TensorProduct.leftModule
  let : Module F.middle (dualizingModule F₁) :=
    Module.compHom _ (algebraMap F.middle C₁)
  let dualMap : Module.Dual A F.middle →ₗ[F.middle] Module.Dual A₁ C₁ := {
    toFun := fun f => f.baseChange A₁
    map_add' := by intro f g; exact (Module.Dual.baseChange A₁).map_add f g
    map_smul' := by intro c f; exact dualBaseChange_middle_smul f c }
  let bim : Module.Dual A F.middle →ₗ[F.middle] B →ₗ[F.middle] dualizingModule F₁ := {
    toFun := fun f => {
      toFun := fun b =>
        dualizingModule.tmul F₁ (dualMap f)
          ((1 : A₁) ⊗ₜ[A] b)
      map_add' := by
        intro b b'
        change dualMap f ⊗ₜ[C₁] ((1 : A₁) ⊗ₜ[A] (b + b')) =
          dualMap f ⊗ₜ[C₁] ((1 : A₁) ⊗ₜ[A] b) +
            dualMap f ⊗ₜ[C₁] ((1 : A₁) ⊗ₜ[A] b')
        rw [TensorProduct.tmul_add, TensorProduct.tmul_add]
      map_smul' := by
        intro c b
        change dualMap f ⊗ₜ[C₁] ((1 : A₁) ⊗ₜ[A] (c • b)) =
          (algebraMap F.middle C₁ c) •
            (dualMap f ⊗ₜ[C₁] ((1 : A₁) ⊗ₜ[A] b))
        rw [show c • b = algebraMap F.middle B c * b from Algebra.smul_def _ _]
        have hC : algebraMap C₁ B₁ (algebraMap F.middle C₁ c) =
            (1 : A₁) ⊗ₜ[A] (algebraMap F.middle B) c := by
          change (Algebra.TensorProduct.map (AlgHom.id A A₁)
            (IsScalarTower.toAlgHom A F.middle B)) ((1 : A₁) ⊗ₜ[A] c) = _
          simp [Algebra.TensorProduct.map_tmul]
        have hcoeff : ((1 : A₁) ⊗ₜ[A] ((algebraMap F.middle B) c * b)) =
            algebraMap C₁ B₁ (algebraMap F.middle C₁ c) * ((1 : A₁) ⊗ₜ[A] b) := by
          calc
            (1 : A₁) ⊗ₜ[A] ((algebraMap F.middle B) c * b) =
                ((1 : A₁) ⊗ₜ[A] (algebraMap F.middle B) c) * ((1 : A₁) ⊗ₜ[A] b) := by
                  rw [Algebra.TensorProduct.tmul_mul_tmul]
                  simp
            _ = algebraMap C₁ B₁ (algebraMap F.middle C₁ c) *
                ((1 : A₁) ⊗ₜ[A] b) := by rw [hC]
        rw [hcoeff]
        change dualMap f ⊗ₜ[C₁]
            ((algebraMap F.middle C₁ c) • ((1 : A₁) ⊗ₜ[A] b)) =
          (algebraMap F.middle C₁ c) •
            (dualMap f ⊗ₜ[C₁] ((1 : A₁) ⊗ₜ[A] b))
        exact TensorProduct.tmul_smul _ _ _ }
    map_add' := by
      intro f g
      ext b
      change dualMap (f + g) ⊗ₜ[C₁] ((1 : A₁) ⊗ₜ[A] b) =
        dualMap f ⊗ₜ[C₁] ((1 : A₁) ⊗ₜ[A] b) +
          dualMap g ⊗ₜ[C₁] ((1 : A₁) ⊗ₜ[A] b)
      rw [dualMap.map_add]
      exact TensorProduct.add_tmul _ _ _
    map_smul' := by
      intro c f
      ext b
      change dualMap (c • f) ⊗ₜ[C₁] ((1 : A₁) ⊗ₜ[A] b) =
        (algebraMap F.middle C₁ c) •
          (dualMap f ⊗ₜ[C₁] ((1 : A₁) ⊗ₜ[A] b))
      rw [dualMap.map_smul]
      exact TensorProduct.smul_tmul' (R := C₁) (R' := C₁)
        (M := Module.Dual A₁ C₁) (N := B₁)
        (algebraMap F.middle C₁ c) (dualMap f) ((1 : A₁) ⊗ₜ[A] b) }
  let l : Module.Dual A F.middle ⊗[F.middle] B →ₗ[F.middle] dualizingModule F₁ :=
    TensorProduct.lift bim
  refine {
    toFun := l
    map_add' := l.map_add
    map_smul' := ?_ }
  intro b z
  induction z using TensorProduct.induction_on with
  | zero =>
      change l (b • (0 : Module.Dual A F.middle ⊗[F.middle] B)) = b • l 0
      simp
  | add x y hx hy =>
      change l (b • (x + y)) = b • l (x + y)
      calc
        l (b • (x + y)) = l (b • x + b • y) := by rw [smul_add]
        _ = l (b • x) + l (b • y) := l.map_add _ _
        _ = b • l x + b • l y := congrArg₂ (· + ·) hx hy
        _ = b • l (x + y) :=
          (smul_add b (l x) (l y)).symm.trans
            (congrArg (fun z => b • z) (l.map_add x y).symm)
  | tmul f b' =>
      change l (b • (f ⊗ₜ[F.middle] b')) = b • l (f ⊗ₜ[F.middle] b')
      have hs : b • (f ⊗ₜ[F.middle] b') = f ⊗ₜ[F.middle] (b * b') := by
        apply (TensorProduct.comm F.middle (Module.Dual A F.middle) B).toAddEquiv.injective
        change b • (b' ⊗ₜ[F.middle] f) = (b * b') ⊗ₜ[F.middle] f
        simp [TensorProduct.smul_tmul']
      rw [hs]
      change dualizingModule.tmul F₁ (dualMap f)
          ((1 : A₁) ⊗ₜ[A] (b * b')) =
        b • dualizingModule.tmul F₁ (dualMap f) ((1 : A₁) ⊗ₜ[A] b')
      change dualizingModule.tmul F₁ (dualMap f)
          ((1 : A₁) ⊗ₜ[A] (b * b')) =
        (algebraMap B B₁ b) •
          dualizingModule.tmul F₁ (dualMap f) ((1 : A₁) ⊗ₜ[A] b')
      rw [dualizingModule.smul_tmul]
      change dualMap f ⊗ₜ[C₁] ((1 : A₁) ⊗ₜ[A] (b * b')) =
        dualMap f ⊗ₜ[C₁]
          ((algebraMap B B₁ b) * ((1 : A₁) ⊗ₜ[A] b'))
      have hb : algebraMap B B₁ b = (1 : A₁) ⊗ₜ[A] b := rfl
      rw [hb, Algebra.TensorProduct.tmul_mul_tmul]
      simp only [one_mul]

/-- On a pure tensor, the relative-dualizing base change map extends the dual functional
and sends the coefficient to its scalar extension. -/
@[stacks 0BVB "pure tensor formula"]
theorem baseChange_tmul (F : FiniteOpenFactorization.{u, v, w} A B)
    (A₁ : Type x) [CommRing A₁] [Algebra A A₁]
    (f : Module.Dual A F.middle) (b : B) :
    letI : Algebra B (A₁ ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
    letI : Module B
        (dualizingModule (FiniteOpenFactorization.baseChange F A₁)) :=
      Module.compHom _ (algebraMap B (A₁ ⊗[A] B))
    baseChange F A₁ (dualizingModule.tmul F f b) =
      dualizingModule.tmul (FiniteOpenFactorization.baseChange F A₁)
        (f.baseChange A₁) (1 ⊗ₜ[A] b) :=
  rfl

/-- For a finitely presented `R`-module `M` and a flat `R`-algebra `S`, the dual
`Module.Dual S (S ⊗[R] M)` is the base change of `Module.Dual R M` along `Module.Dual.baseChange`.
-/
lemma dual_baseChange_isBaseChange_of_flat_finitePresentation
    {R : Type u} {M : Type v} {S : Type x}
    [CommRing R] [AddCommGroup M] [Module R M]
    [CommRing S] [Algebra R S] [Module.Flat R S]
    [Module.FinitePresentation R M] :
    IsBaseChange S (Module.Dual.baseChange S :
      Module.Dual R M →ₗ[R] Module.Dual S (S ⊗[R] M)) := by
  let h := Module.FinitePresentation.isBaseChange_map R M R S
  let e : S ⊗[R] Module.Dual R M ≃ₗ[S]
      Module.Dual S (S ⊗[R] M) :=
    h.equiv.trans (LinearEquiv.arrowCongr (LinearEquiv.refl S (S ⊗[R] M))
      (TensorProduct.AlgebraTensorModule.rid R S S))
  refine IsBaseChange.of_equiv e ?_
  intro f
  show e (1 ⊗ₜ[R] f) = Module.Dual.baseChange S f
  simp only [e, LinearEquiv.trans_apply, IsBaseChange.equiv_tmul, one_smul]
  ext x
  simp [Module.Dual.baseChange, LinearEquiv.arrowCongr_apply]

section FlatFinitePresentationDualBaseChange

variable {R : Type u} {M : Type v} {S : Type x}
  [CommRing R] [CommRing M] [Algebra R M]
  [CommRing S] [Algebra R S]

/-- The `S`-algebra structure on `S ⊗[R] M` through the left factor. -/
local instance : Algebra S (S ⊗[R] M) := Algebra.TensorProduct.leftAlgebra
/-- The `M`-algebra structure on `S ⊗[R] M` through the right factor. -/
local instance : Algebra M (S ⊗[R] M) := Algebra.TensorProduct.rightAlgebra
/-- The `R`-algebra structure on `S ⊗[R] M` through the left factor. -/
local instance : Algebra R (S ⊗[R] M) := Algebra.TensorProduct.leftAlgebra
/-- The scalar tower `R → M → S ⊗[R] M`. -/
local instance : IsScalarTower R M (S ⊗[R] M) := Algebra.TensorProduct.right_isScalarTower
/-- The `M`-module structure on `Module.Dual R M` given by `(m • f) x = f (m * x)`. -/
local instance : Module M (Module.Dual R M) := algebraDualModule R M
/-- The scalar tower `R → M → Module.Dual R M`. -/
local instance : IsScalarTower R M (Module.Dual R M) :=
  IsScalarTower.of_algebraMap_smul (by
    intro r f
    ext m
    change f ((algebraMap R M r) * m) = r * f m
    rw [← Algebra.smul_def]
    simp)
/-- The `S ⊗[R] M`-module structure on `Module.Dual S (S ⊗[R] M)` given by
`(t • g) x = g (t * x)`. -/
local instance : Module (S ⊗[R] M) (Module.Dual S (S ⊗[R] M)) :=
  algebraDualModule S (S ⊗[R] M)
/-- The `M`-module structure on `Module.Dual S (S ⊗[R] M)` by restriction of scalars along
`M → S ⊗[R] M`. -/
local instance : Module M (Module.Dual S (S ⊗[R] M)) :=
  Module.compHom _ (algebraMap M (S ⊗[R] M))
/-- The scalar tower `M → S ⊗[R] M → Module.Dual S (S ⊗[R] M)`. -/
local instance : IsScalarTower M (S ⊗[R] M) (Module.Dual S (S ⊗[R] M)) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
/-- The square `R → S, M → S ⊗[R] M` is a pushout, with the factors in this order. -/
local instance : Algebra.IsPushout R S M (S ⊗[R] M) := Algebra.IsPushout.symm inferInstance

/-- `Module.Dual.baseChange S` is `M`-linear: `(m • f).baseChange S = m • f.baseChange S`. -/
lemma dual_baseChange_smul (m : M) (f : Module.Dual R M) :
    Module.Dual.baseChange S (m • f) = m • Module.Dual.baseChange S f := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z z' hz hz' => simp [hz, hz']
  | tmul s m' =>
    show f (m * m') • s =
      Module.Dual.baseChange S f
        (algebraMap M (S ⊗[R] M) m * (s ⊗ₜ[R] m'))
    rw [Algebra.TensorProduct.right_algebraMap_apply,
      Algebra.TensorProduct.tmul_mul_tmul, Module.Dual.baseChange_apply_tmul]
    simp

/-- The base change map `Module.Dual R M → Module.Dual S (S ⊗[R] M)`, as an `M`-linear map. -/
def dualBaseChangeRestrictScalars :
    Module.Dual R M →ₗ[M] Module.Dual S (S ⊗[R] M) where
  toFun := Module.Dual.baseChange S
  map_add' := by intro f g; exact (Module.Dual.baseChange S).map_add f g
  map_smul' := by intro m f; exact dual_baseChange_smul m f

/-- If `Module.Dual S (S ⊗[R] M)` is the base change of `Module.Dual R M` along `R → S`, then
it is also the base change of `Module.Dual R M` along `M → S ⊗[R] M`, via
`dualBaseChangeRestrictScalars`. -/
lemma dual_baseChange_isBaseChange_overTensor_of_isBaseChange
    (h : IsBaseChange S (Module.Dual.baseChange S :
      Module.Dual R M →ₗ[R] Module.Dual S (S ⊗[R] M))) :
    IsBaseChange (S ⊗[R] M)
      (dualBaseChangeRestrictScalars (R := R) (M := M) (S := S)) := by
  let e₀ := Algebra.IsPushout.cancelBaseChange R S M (S ⊗[R] M) (Module.Dual R M)
  let eA := e₀.trans h.equiv
  let e : (S ⊗[R] M) ⊗[M] Module.Dual R M ≃ₗ[S ⊗[R] M]
      Module.Dual S (S ⊗[R] M) :=
    { eA with
      map_smul' := by
        intro c z
        induction c using TensorProduct.induction_on with
        | zero => simp
        | add c d hc hd =>
          have hc' : eA (c • z) = c • eA z := by simpa using hc
          have hd' : eA (d • z) = d • eA z := by simpa using hd
          calc
            eA ((c + d) • z) = eA (c • z + d • z) := by rw [add_smul]
            _ = eA (c • z) + eA (d • z) := eA.map_add _ _
            _ = c • eA z + d • eA z := by rw [hc', hd']
            _ = (c + d) • eA z := (add_smul _ _ _).symm
        | tmul a m =>
          induction z using TensorProduct.induction_on with
          | zero => simp
          | add x y hx hy =>
            have hx' : eA ((a ⊗ₜ[R] m) • x) = (a ⊗ₜ[R] m) • eA x := by simpa using hx
            have hy' : eA ((a ⊗ₜ[R] m) • y) = (a ⊗ₜ[R] m) • eA y := by simpa using hy
            calc
              eA ((a ⊗ₜ[R] m) • (x + y)) =
                  eA ((a ⊗ₜ[R] m) • x + (a ⊗ₜ[R] m) • y) := by rw [smul_add]
              _ = eA ((a ⊗ₜ[R] m) • x) + eA ((a ⊗ₜ[R] m) • y) := eA.map_add _ _
              _ = (a ⊗ₜ[R] m) • eA x + (a ⊗ₜ[R] m) • eA y := by rw [hx', hy']
              _ = (a ⊗ₜ[R] m) • eA (x + y) := by rw [eA.map_add, smul_add]
          | tmul n f =>
            induction n using TensorProduct.induction_on with
            | zero => simp
            | add n₁ n₂ hn₁ hn₂ =>
              calc
                eA ((a ⊗ₜ[R] m) • ((n₁ + n₂) ⊗ₜ[M] f)) =
                    eA ((a ⊗ₜ[R] m) • (n₁ ⊗ₜ[M] f) +
                      (a ⊗ₜ[R] m) • (n₂ ⊗ₜ[M] f)) := by
                        rw [TensorProduct.add_tmul, smul_add]
                _ = eA ((a ⊗ₜ[R] m) • (n₁ ⊗ₜ[M] f)) +
                    eA ((a ⊗ₜ[R] m) • (n₂ ⊗ₜ[M] f)) := eA.map_add _ _
                _ = (a ⊗ₜ[R] m) • eA (n₁ ⊗ₜ[M] f) +
                    (a ⊗ₜ[R] m) • eA (n₂ ⊗ₜ[M] f) := by
                      have h₁ : eA ((a ⊗ₜ[R] m) • (n₁ ⊗ₜ[M] f)) =
                          (a ⊗ₜ[R] m) • eA (n₁ ⊗ₜ[M] f) := by simpa using hn₁
                      have h₂ : eA ((a ⊗ₜ[R] m) • (n₂ ⊗ₜ[M] f)) =
                          (a ⊗ₜ[R] m) • eA (n₂ ⊗ₜ[M] f) := by simpa using hn₂
                      rw [h₁, h₂]
                _ = (a ⊗ₜ[R] m) • eA ((n₁ + n₂) ⊗ₜ[M] f) := by
                    simp only [TensorProduct.add_tmul, eA.map_add, smul_add]
            | tmul s' m' =>
              have e₀_tmul (b : S) (q : M) (g : Module.Dual R M) :
                  e₀ ((b ⊗ₜ[R] q) ⊗ₜ[M] g) = b ⊗ₜ[R] (q • g) := by
                calc
                  e₀ ((b ⊗ₜ[R] q) ⊗ₜ[M] g) =
                      e₀ (b • ((1 : S ⊗[R] M) ⊗ₜ[M] (q • g))) := by
                        congr 1
                        simp [TensorProduct.smul_tmul', Algebra.smul_def,
                          Algebra.TensorProduct.right_algebraMap_apply,
                          Algebra.TensorProduct.tmul_mul_tmul]
                  _ = b • e₀ ((1 : S ⊗[R] M) ⊗ₜ[M] (q • g)) := e₀.map_smul _ _
                  _ = b • (1 ⊗ₜ[R] (q • g)) := by
                        show b • (Algebra.IsPushout.cancelBaseChange R S M
                          (S ⊗[R] M) (Module.Dual R M) (1 ⊗ₜ[M] (q • g))) = _
                        rw [Algebra.IsPushout.cancelBaseChange_tmul]
                  _ = b ⊗ₜ[R] (q • g) := by simp [TensorProduct.smul_tmul']
              have eA_tmul (b : S) (q : M) (g : Module.Dual R M) :
                  eA ((b ⊗ₜ[R] q) ⊗ₜ[M] g) = b • Module.Dual.baseChange S (q • g) := by
                calc
                  eA ((b ⊗ₜ[R] q) ⊗ₜ[M] g) = h.equiv (b ⊗ₜ[R] (q • g)) := by
                    simp [eA, e₀_tmul]
                  _ = b • Module.Dual.baseChange S (q • g) := by rw [h.equiv_tmul]
              apply LinearMap.ext
              intro z
              induction z using TensorProduct.induction_on with
              | zero => simp
              | add z z' hz hz' =>
                let g₁ : Module.Dual S (S ⊗[R] M) :=
                  eA (a ⊗ₜ[R] m • (s' ⊗ₜ[R] m' ⊗ₜ[M] f))
                let g₂ : Module.Dual S (S ⊗[R] M) :=
                  (RingHom.id (S ⊗[R] M)) (a ⊗ₜ[R] m) •
                    eA (s' ⊗ₜ[R] m' ⊗ₜ[M] f)
                show g₁ (z + z') = g₂ (z + z')
                have hz : g₁ z = g₂ z := by simpa [g₁, g₂] using hz
                have hz' : g₁ z' = g₂ z' := by simpa [g₁, g₂] using hz'
                rw [g₁.map_add, g₂.map_add, hz, hz']
              | tmul b n =>
                show (eA (((a ⊗ₜ[R] m) * (s' ⊗ₜ[R] m')) ⊗ₜ[M] f))
                    (b ⊗ₜ[R] n) =
                  (eA (s' ⊗ₜ[R] m' ⊗ₜ[M] f))
                    ((a ⊗ₜ[R] m) * (b ⊗ₜ[R] n))
                rw [Algebra.TensorProduct.tmul_mul_tmul,
                  Algebra.TensorProduct.tmul_mul_tmul, eA_tmul, eA_tmul]
                simp [algebraDualModule_smul_apply,
                  Module.Dual.baseChange_apply_tmul, smul_eq_mul,
                  mul_comm, mul_left_comm] }
  exact IsBaseChange.of_equiv e (by
    intro f
    simp [e, eA, e₀, dualBaseChangeRestrictScalars,
      Algebra.IsPushout.cancelBaseChange_tmul, IsBaseChange.equiv_tmul])

/-- For a flat `R`-algebra `S` and an `R`-algebra `M` finitely presented as an `R`-module,
`Module.Dual S (S ⊗[R] M)` is the base change of `Module.Dual R M` along `M → S ⊗[R] M`, via
`dualBaseChangeRestrictScalars`. -/
lemma dual_baseChange_isBaseChange_overTensor
    [Module.Flat R S] [Module.FinitePresentation R M] :
    IsBaseChange (S ⊗[R] M)
      (dualBaseChangeRestrictScalars (R := R) (M := M) (S := S)) :=
  dual_baseChange_isBaseChange_overTensor_of_isBaseChange
    (dual_baseChange_isBaseChange_of_flat_finitePresentation (R := R) (M := M) (S := S))

end FlatFinitePresentationDualBaseChange

end dualizingModule

end Stacks.Discriminant

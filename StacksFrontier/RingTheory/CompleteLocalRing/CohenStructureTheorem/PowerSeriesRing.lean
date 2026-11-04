module

import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Sheaves.Presheaf
import StacksCore.LinearAlgebra.Matrix.CommSemiring

import StacksFrontier.RingTheory.Etale.ModuloPowers
public import StacksFrontier.RingTheory.CompleteLocalRing.CoefficientRing
public import StacksFrontier.RingTheory.CohenRing
public import StacksFrontier.RingTheory.AdicCompletion.Finiteness
public import StacksFrontier.RingTheory.AdicCompletion.Basic
public import StacksFrontier.RingTheory.KrullDimension.GoingUpGoingDown
public import StacksFrontier.RingTheory.HilbertSamuel.DimensionTheorem
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.Kaehler.SmoothRingMapsInTheNoetherianCase
public import Mathlib.RingTheory.MvPowerSeries.Ideal
public import StacksFrontier.RingTheory.AdicCompletion.LiftToComplete
import StacksFrontier.RingTheory.LocalRing.AdicCompleteRingEquiv

@[expose] public section

universe v

/-!
# The power series ring over a complete local ring

Generalities used in the proof of Stacks 032D (that a Noetherian complete local domain is finite
over a regular power series subring): the Krull dimension of a quotient by a nonzerodivisor,
ideals of definition and completeness for them, the maximal ideal of `Λ[[X_1, …, X_d]]` over a
local ring `Λ` and the bound on its number of generators, the completeness of
`Λ[[X_1, …, X_d]]` for its maximal ideal when `Λ` is a complete Noetherian local ring, and
substitution of elements of an ideal `I` into power series when the target is `I`-adically
complete.

## Main results

* `Stacks.CompleteLocalRing.RegularSubring.maximalIdeal_mvPowerSeries`
* `Stacks.CompleteLocalRing.RegularSubring.spanFinrank_maximalIdeal_mvPowerSeries_le`
* `Stacks.CompleteLocalRing.RegularSubring.isAdicComplete_maximalIdeal_powerSeries`
* `Stacks.CompleteLocalRing.RegularSubring.isAdicComplete_maximalIdeal_mvPowerSeries`
* `Stacks.CompleteLocalRing.RegularSubring.exists_eval₂Hom`

## References

* [StacksProject 032D](https://stacks.math.columbia.edu/tag/032D), Lemma 10.160.11
-/

namespace Stacks.CompleteLocalRing.RegularSubring

open IsLocalRing

/-! ### Generalities -/

/-- An element of a local ring lies in the maximal ideal exactly when its image in a local quotient
does: the quotient map is a local homomorphism. -/
theorem mk_mem_maximalIdeal_iff {A : Type*} [CommRing A] [IsLocalRing A] {J : Ideal A}
    [IsLocalRing (A ⧸ J)] {a : A} :
    Ideal.Quotient.mk J a ∈ maximalIdeal (A ⧸ J) ↔ a ∈ maximalIdeal A := by
  have := (Ideal.Quotient.mk_surjective (I := J)).isLocalHom
  rw [← maximalIdeal_comap (Ideal.Quotient.mk J), Ideal.mem_comap]

/-! ### Krull dimension of a Noetherian local ring -/

/-- **Quotienting a Noetherian local ring by a nonzerodivisor in the maximal ideal drops the Krull
dimension strictly.** By Stacks 00KW the dimension drops by exactly one, and the dimension of a
Noetherian local ring is a natural number, so the drop is strict. -/
theorem ringKrullDim_quotient_span_singleton_lt {A : Type*} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] {a : A} (ha : a ∈ nonZeroDivisors A)
    (ham : a ∈ maximalIdeal A) : ringKrullDim (A ⧸ Ideal.span {a}) < ringKrullDim A := by
  have := isLocalRing_quotient (ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top
    ((Ideal.span_singleton_le_iff_mem _).2 ham))
  obtain ⟨D, hD⟩ :=
    Stacks.RegularLocalRing.KernelRegularity.exists_natCast_eq_ringKrullDim
      (A ⧸ Ideal.span {a})
  rw [← ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors ha ham,
    hD]
  exact_mod_cast Nat.lt_succ_self D

/-! ### Ideals of definition -/

/-- In a Noetherian local ring, an ideal contained in the maximal ideal whose quotient has Krull
dimension zero contains a positive power of the maximal ideal. -/
theorem exists_pow_maximalIdeal_le {R : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (I : Ideal R) (hIle : I ≤ maximalIdeal R)
    (h0 : Ring.KrullDimLE 0 (R ⧸ I)) :
    ∃ k : ℕ, 0 < k ∧ (maximalIdeal R) ^ k ≤ I := by
  have := isLocalRing_quotient (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hIle)
  have hrad : maximalIdeal R ≤ I.radical := fun y hy => by
    obtain ⟨m, hm⟩ : IsNilpotent (Ideal.Quotient.mk I y) := by
      rw [← mem_nilradical, Ring.KrullDimLE.nilradical_eq_maximalIdeal]
      exact mk_mem_maximalIdeal_iff.2 hy
    exact ⟨m, Ideal.Quotient.eq_zero_iff_mem.1 (by rwa [map_pow])⟩
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  exact ⟨k + 1, Nat.succ_pos _, (Ideal.pow_le_pow_right (Nat.le_succ k)).trans hk⟩

/-- A complete local ring is complete for any ideal of definition, by Stacks 0319: the two ideals
have comparable powers. -/
theorem isAdicComplete_of_pow_maximalIdeal_le {R : Type*} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] (I : Ideal R) (hIle : I ≤ maximalIdeal R) {k : ℕ}
    (hk0 : 0 < k) (hk : (maximalIdeal R) ^ k ≤ I) : IsAdicComplete I R :=
  (completeness_preserved (maximalIdeal R) I hk0 one_pos hk (by simpa using hIle) R).1
    inferInstance

/-! ### The power series ring over a complete local ring -/

/-- A multivariate power series in finitely many variables whose constant coefficient vanishes
lies in the ideal generated by the variables. -/
public theorem mem_span_range_X {A : Type*} [CommRing A] :
    ∀ (n : ℕ) (φ : MvPowerSeries (Fin n) A), MvPowerSeries.constantCoeff φ = 0 →
      φ ∈ Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) A)) := by
  intro n
  induction n with
  | zero =>
    intro φ h
    have hφ : φ = 0 := by
      ext m
      rw [Subsingleton.elim m 0]
      simpa using h
    simp [hφ]
  | succ n ih =>
    intro φ h
    set e := MvPowerSeries.finSuccEquiv A n with he
    set a : MvPowerSeries (Fin n) A := PowerSeries.coeff 0 (e φ) with hadef
    have ha : MvPowerSeries.constantCoeff a = 0 := by
      have h1 := MvPowerSeries.coeff_coeff_finSuccEquiv (R := A) (n := n) φ (k := 0) (x := 0)
      rw [Finsupp.cons_zero_zero] at h1
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff]
      simpa [hadef] using
        h1.trans (by rwa [MvPowerSeries.coeff_zero_eq_constantCoeff])
    obtain ⟨q, hq⟩ : PowerSeries.X ∣ (e φ - PowerSeries.C a) := by
      rw [PowerSeries.X_dvd_iff]
      simp [hadef, ← PowerSeries.coeff_zero_eq_constantCoeff]
    have hφ : φ = e.symm (PowerSeries.C a) + MvPowerSeries.X 0 * e.symm q := by
      have h2 : e φ = PowerSeries.C a + PowerSeries.X * q := by rw [← hq]; ring
      have h3 : φ = e.symm (PowerSeries.C a + PowerSeries.X * q) := by
        rw [← h2, AlgEquiv.symm_apply_apply]
      rw [h3, map_add, map_mul]
      congr 1
      rw [he, ← MvPowerSeries.finSuccEquiv_X_zero (R := A) (n := n), AlgEquiv.symm_apply_apply]
    set T : MvPowerSeries (Fin n) A →+* MvPowerSeries (Fin (n + 1)) A :=
      ((e.symm : _ →ₐ[A] _).toRingHom).comp PowerSeries.C with hT
    have hTX : ∀ j : Fin n, T (MvPowerSeries.X j) = MvPowerSeries.X j.succ := by
      intro j
      simp only [hT, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, AlgEquiv.coe_toAlgHom]
      rw [he, ← MvPowerSeries.finSuccEquiv_X_succ (R := A) j, AlgEquiv.symm_apply_apply]
    have hle : Ideal.map T
        (Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) A)))
        ≤ Ideal.span
          (Set.range (MvPowerSeries.X : Fin (n + 1) → MvPowerSeries (Fin (n + 1)) A)) := by
      rw [Ideal.map_span]
      refine Ideal.span_le.2 ?_
      rintro y ⟨z, ⟨j, rfl⟩, rfl⟩
      exact hTX j ▸ Ideal.subset_span ⟨j.succ, rfl⟩
    rw [hφ]
    refine Ideal.add_mem _ ?_ (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨0, rfl⟩))
    exact hle (Ideal.mem_map_of_mem _ (ih a ha))

/-- A multivariate power series lies in the maximal ideal exactly when its constant coefficient
does. -/
private theorem mem_maximalIdeal_mvPowerSeries_iff {σ : Type*} {A : Type*} [CommRing A]
    [IsLocalRing A] {φ : MvPowerSeries σ A} :
    φ ∈ maximalIdeal (MvPowerSeries σ A) ↔ MvPowerSeries.constantCoeff φ ∈ maximalIdeal A := by
  simp only [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]

/-- The maximal ideal of a power series ring in finitely many variables over a local ring is
generated by the maximal ideal of the base together with the variables. This is the multivariate
`PowerSeries.maximalIdeal_eq_span_X`. -/
@[ega "0 17.1.4" "more general"]
theorem maximalIdeal_mvPowerSeries (Λ : Type*) [CommRing Λ] [IsLocalRing Λ] (d : ℕ) :
    maximalIdeal (MvPowerSeries (Fin d) Λ) =
      (maximalIdeal Λ).map (MvPowerSeries.C (σ := Fin d)) ⊔
        Ideal.span (Set.range (MvPowerSeries.X : Fin d → MvPowerSeries (Fin d) Λ)) := by
  refine le_antisymm (fun φ hφ => ?_) (sup_le ?_ (Ideal.span_le.2 ?_))
  · have hc := mem_maximalIdeal_mvPowerSeries_iff.1 hφ
    have hsplit : φ = MvPowerSeries.C (MvPowerSeries.constantCoeff φ) +
        (φ - MvPowerSeries.C (MvPowerSeries.constantCoeff φ)) := by ring
    rw [hsplit]
    exact Submodule.add_mem_sup (Ideal.mem_map_of_mem _ hc)
      (mem_span_range_X d _ (by simp))
  · refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
    rw [Ideal.mem_comap, mem_maximalIdeal_mvPowerSeries_iff]
    simpa using ha
  · rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, mem_maximalIdeal_mvPowerSeries_iff]
    simp

/-- The maximal ideal of `Λ[[X_1, …, X_d]]` is generated by `#s + d` elements, where `s`
generates the maximal ideal of `Λ`. -/
theorem spanFinrank_maximalIdeal_mvPowerSeries_le (Λ : Type*) [CommRing Λ]
    [IsLocalRing Λ] (d : ℕ) (s : Finset Λ) (hs : Ideal.span (s : Set Λ) = maximalIdeal Λ) :
    (maximalIdeal (MvPowerSeries (Fin d) Λ)).spanFinrank ≤ s.card + d := by
  have hgen : maximalIdeal (MvPowerSeries (Fin d) Λ) =
      Ideal.span ((MvPowerSeries.C (σ := Fin d) (R := Λ)) '' (s : Set Λ) ∪
        Set.range (MvPowerSeries.X : Fin d → MvPowerSeries (Fin d) Λ)) := by
    rw [maximalIdeal_mvPowerSeries, Ideal.span_union, ← hs, Ideal.map_span]
  rw [hgen]
  refine (Submodule.spanFinrank_span_le_ncard_of_finite
    ((Set.Finite.image _ s.finite_toSet).union (Set.finite_range _))).trans ?_
  refine (Set.ncard_union_le _ _).trans (add_le_add ?_ ?_)
  · exact (Set.ncard_image_le s.finite_toSet).trans (by simp)
  · rw [← Set.image_univ]
    exact (Set.ncard_image_le Set.finite_univ).trans (by simp)

/-- The Krull dimension of `Λ[[X_1, …, X_d]]` is at most `#s + d`, where `s` generates the
maximal ideal of `Λ`; this is Krull's height theorem. -/
@[ega "0 17.1.4" "more general"]
theorem ringKrullDim_mvPowerSeries_le (Λ : Type*) [CommRing Λ] [IsNoetherianRing Λ]
    [IsLocalRing Λ] (d : ℕ) (s : Finset Λ) (hs : Ideal.span (s : Set Λ) = maximalIdeal Λ) :
    ringKrullDim (MvPowerSeries (Fin d) Λ) ≤ ((s.card + d : ℕ) : WithBot ℕ∞) := by
  refine (ringKrullDim_le_spanFinrank_maximalIdeal _).trans ?_
  exact_mod_cast spanFinrank_maximalIdeal_mvPowerSeries_le Λ d s hs

section PowerSeries

open PowerSeries

/-- **A power series lies in `a·A⟦X⟧ + (X ^ n)` exactly when its coefficients below degree `n` lie
in `a`.** This describes the ideals of the second filtration of `A⟦X⟧` coefficientwise. -/
theorem mem_map_C_sup_span_X_pow_iff {A : Type*} [CommRing A] (a : Ideal A) :
    ∀ (n : ℕ) (φ : PowerSeries A),
      φ ∈ a.map (PowerSeries.C : A →+* PowerSeries A) ⊔ Ideal.span {(X : PowerSeries A) ^ n} ↔
        ∀ j < n, coeff j φ ∈ a := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro φ
    refine ⟨fun h j hj => ?_, fun h => ?_⟩
    · obtain ⟨α, hα, β, hβ, rfl⟩ := Submodule.mem_sup.1 h
      have hβj : coeff j β = 0 := (X_pow_dvd_iff.1 (Ideal.mem_span_singleton.1 hβ)) j hj
      simpa [hβj] using MvPowerSeries.coeff_mem_of_mem_map_C hα (Finsupp.single () j)
    · obtain ⟨ρ, hρ⟩ : (X : PowerSeries A) ∣ (φ - PowerSeries.C (coeff 0 φ)) := by
        rw [X_dvd_iff]; simp
      have hφ : φ = PowerSeries.C (coeff 0 φ) + X * ρ := by rw [← hρ]; ring
      have hρc : ∀ j < n, coeff j ρ ∈ a := fun j hj => by
        have hc : coeff (j + 1) φ = coeff j ρ := by rw [hφ]; simp [coeff_succ_X_mul]
        exact hc ▸ h (j + 1) (by omega)
      obtain ⟨α, hα, β, hβ, hαβ⟩ := Submodule.mem_sup.1 ((ih ρ).2 hρc)
      obtain ⟨γ, hγ⟩ := Ideal.mem_span_singleton.1 hβ
      rw [hφ, ← hαβ, mul_add, ← add_assoc]
      refine Submodule.add_mem_sup (Ideal.add_mem _
        (Ideal.mem_map_of_mem (PowerSeries.C : A →+* PowerSeries A) (h 0 n.succ_pos))
        (Ideal.mul_mem_left _ _ hα)) (Ideal.mem_span_singleton.2 ⟨γ, ?_⟩)
      rw [hγ, pow_succ]; ring

/-- The maximal ideal of a power series ring over a local ring is generated by the maximal ideal
of the base together with the variable. This is `PowerSeries.maximalIdeal_eq_span_X` over a local
rather than a field base. -/
theorem maximalIdeal_powerSeries (A : Type*) [CommRing A] [IsLocalRing A] :
    maximalIdeal (PowerSeries A) =
      (maximalIdeal A).map (PowerSeries.C : A →+* PowerSeries A) ⊔
        Ideal.span {(X : PowerSeries A)} := by
  refine le_antisymm (fun φ hφ => ?_) (sup_le ?_ ?_)
  · have hc : constantCoeff φ ∈ maximalIdeal A :=
      mem_maximalIdeal_mvPowerSeries_iff.1 hφ
    have h1 : φ - PowerSeries.C (constantCoeff φ) ∈ Ideal.span {(X : PowerSeries A)} :=
      Ideal.mem_span_singleton.2 (X_dvd_iff.2 (by simp))
    simpa using Submodule.add_mem_sup
      (Ideal.mem_map_of_mem (PowerSeries.C : A →+* PowerSeries A) hc) h1
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, PowerSeries.C, mem_maximalIdeal_mvPowerSeries_iff]
    simpa using ha
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
      mem_maximalIdeal_mvPowerSeries_iff]
    exact (PowerSeries.constantCoeff_X (R := A)).symm ▸ zero_mem _

/-- The ideals `𝔪 ^ n·A⟦X⟧ + (X ^ n)` are contained in the `n`-th power of the maximal ideal. -/
theorem le_pow_maximalIdeal_powerSeries (A : Type*) [CommRing A] [IsLocalRing A] (n : ℕ) :
    (maximalIdeal A ^ n).map (PowerSeries.C : A →+* PowerSeries A) ⊔
        Ideal.span {(X : PowerSeries A) ^ n} ≤ maximalIdeal (PowerSeries A) ^ n := by
  rw [maximalIdeal_powerSeries A, Ideal.map_pow, ← Ideal.span_singleton_pow]
  exact sup_le (Ideal.pow_right_mono le_sup_left n) (Ideal.pow_right_mono le_sup_right n)

/-- **A coefficient below degree `n` of an element of `𝔐 ^ (n + n)` lies in `𝔪 ^ m` for `m ≤ n`.**
Since `𝔐 ^ (n + n) ≤ 𝔪 ^ n·A⟦X⟧ + (X ^ n)`, a sequence that is Cauchy for the maximal ideal of
`A⟦X⟧` is Cauchy in each coefficient. -/
private theorem coeff_mem_pow_maximalIdeal (A : Type*) [CommRing A] [IsLocalRing A] {m n j : ℕ}
    (hj : j < n) (hmn : m ≤ n) {φ : PowerSeries A}
    (hφ : φ ∈ maximalIdeal (PowerSeries A) ^ (n + n)) : coeff j φ ∈ maximalIdeal A ^ m := by
  have hle : maximalIdeal (PowerSeries A) ^ (n + n) ≤
      (maximalIdeal A ^ n).map (PowerSeries.C : A →+* PowerSeries A) ⊔
        Ideal.span {(X : PowerSeries A) ^ n} := by
    rw [maximalIdeal_powerSeries A, Ideal.map_pow, ← Ideal.span_singleton_pow]
    exact Ideal.sup_pow_add_le_pow_sup_pow
  exact Ideal.pow_le_pow_right hmn ((mem_map_C_sup_span_X_pow_iff _ n φ).1 (hle hφ) j hj)

/-- **The coefficientwise limit of a Cauchy sequence of power series.** If `A` is `𝔪`-adically
precomplete and `f` is Cauchy for the maximal ideal of `A⟦X⟧`, then for each `j` the `j`-th
coefficients converge: there is `L` with `coeff j (f (n + n)) ≡ L` modulo `𝔪 ^ n` for `n > j`. -/
private theorem exists_coeff_sub_mem_pow (A : Type*) [CommRing A] [IsLocalRing A]
    [IsPrecomplete (maximalIdeal A) A] {f : ℕ → PowerSeries A}
    (hf : ∀ m n, m ≤ n → f m - f n ∈ maximalIdeal (PowerSeries A) ^ m) (j : ℕ) :
    ∃ L : A, ∀ n, j < n → coeff j (f (n + n)) - L ∈ maximalIdeal A ^ n := by
  have hcau : ∀ {p q : ℕ}, p ≤ q →
      coeff j (f ((p + j + 1) + (p + j + 1))) ≡ coeff j (f ((q + j + 1) + (q + j + 1)))
        [SMOD (maximalIdeal A ^ p • ⊤ : Submodule A A)] := fun {p q} hpq => by
    rw [SModEq.sub_mem]
    simpa using coeff_mem_pow_maximalIdeal A (m := p) (n := p + j + 1) (j := j) (by omega)
      (by omega) (hf _ _ (by omega))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := maximalIdeal A) (M := A) inferInstance
    (f := fun k => coeff j (f ((k + j + 1) + (k + j + 1)))) hcau
  refine ⟨L, fun n hjn => ?_⟩
  have h1 : coeff j (f ((n + j + 1) + (n + j + 1))) - L ∈ maximalIdeal A ^ n := by
    simpa [SModEq.sub_mem] using hL n
  have h2 : coeff j (f (n + n)) - coeff j (f ((n + j + 1) + (n + j + 1)))
      ∈ maximalIdeal A ^ n := by
    simpa using coeff_mem_pow_maximalIdeal A (m := n) (n := n) (j := j) hjn le_rfl
      (hf _ _ (by omega))
  simpa using Ideal.add_mem _ h2 h1

/-- **A power series ring over a Noetherian complete local ring is complete for its maximal
ideal.** A Cauchy sequence for the maximal ideal has a coefficientwise limit, and that limit is a
limit in `A⟦X⟧` because the two filtrations are comparable.

Not `private`: it is the completeness of the equal-characteristic Cohen interposition `Λ = κ⟦X⟧`,
needed at a field base by the callers of
`Stacks.EppTheorem.exists_isExtension_powerSeries_of_equalCharacteristic`. -/
theorem isAdicComplete_maximalIdeal_powerSeries (A : Type*) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A] :
    IsAdicComplete (maximalIdeal (PowerSeries A)) (PowerSeries A) := by
  have hprec : IsPrecomplete (maximalIdeal (PowerSeries A)) (PowerSeries A) := by
    refine ⟨fun f hf => ?_⟩
    have hf' : ∀ m n, m ≤ n → f m - f n ∈ maximalIdeal (PowerSeries A) ^ m := fun m n hmn => by
      simpa [SModEq.sub_mem] using hf hmn
    choose L hL using exists_coeff_sub_mem_pow A hf'
    refine ⟨PowerSeries.mk L, fun n => ?_⟩
    rw [SModEq.sub_mem]
    have hB : f (n + n) - PowerSeries.mk L ∈ maximalIdeal (PowerSeries A) ^ n :=
      le_pow_maximalIdeal_powerSeries A n
        ((mem_map_C_sup_span_X_pow_iff _ n _).2 fun j hj => by simpa using hL j n hj)
    simpa using Ideal.add_mem _ (hf' n (n + n) (by omega)) hB
  exact ⟨⟩

/-- The induction on the number of variables behind `isAdicComplete_maximalIdeal_mvPowerSeries`:
`Λ⟦X_0, …, X_d⟧ = (Λ⟦X_0, …, X_{d-1}⟧)⟦X_d⟧`, and each stage is again Noetherian complete local. -/
private theorem isAdicComplete_maximalIdeal_mvPowerSeries_aux :
    ∀ (d : ℕ) (Λ : Type v) [CommRing Λ] [IsNoetherianRing Λ] [IsLocalRing Λ],
      IsAdicComplete (maximalIdeal Λ) Λ →
      IsAdicComplete (maximalIdeal (MvPowerSeries (Fin d) Λ)) (MvPowerSeries (Fin d) Λ) := by
  intro d
  induction d with
  | zero =>
    intro Λ _ _ _ h
    have := h
    exact isAdicComplete_maximalIdeal_of_ringEquiv
      (MvPowerSeries.isEmptyEquiv (σ := Fin 0) (R := Λ)).symm.toRingEquiv
  | succ d ih =>
    intro Λ _ _ _ h
    have := ih Λ h
    have := isAdicComplete_maximalIdeal_powerSeries (MvPowerSeries (Fin d) Λ)
    exact isAdicComplete_maximalIdeal_of_ringEquiv
      (MvPowerSeries.finSuccEquiv Λ d).symm.toRingEquiv

end PowerSeries

/-- A power series ring in finitely many variables over a complete local ring is complete for its
maximal ideal. -/
theorem isAdicComplete_maximalIdeal_mvPowerSeries (Λ : Type*) [CommRing Λ]
    [IsNoetherianRing Λ] [IsLocalRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] (d : ℕ) :
    IsAdicComplete (maximalIdeal (MvPowerSeries (Fin d) Λ)) (MvPowerSeries (Fin d) Λ) :=
  isAdicComplete_maximalIdeal_mvPowerSeries_aux d Λ inferInstance

/-! ### Substitution into power series -/

/-- Substitution of topologically nilpotent elements: if `R` is `I`-adically complete and
`y_1, …, y_n ∈ I`, then for every ring map `f : Λ → R` there is a ring map
`Λ[[X_1, …, X_n]] → R` sending `X_i` to `y_i` and `C c` to `f c`. -/
theorem exists_eval₂Hom {Λ R : Type*} [CommRing Λ] [CommRing R] (I : Ideal R)
    [IsAdicComplete I R] {n : ℕ} (y : Fin n → R) (hy : ∀ i, y i ∈ I) (f : Λ →+* R) :
    ∃ F : MvPowerSeries (Fin n) Λ →+* R,
      (∀ i, F (MvPowerSeries.X i) = y i) ∧ ∀ c : Λ, F (MvPowerSeries.C c) = f c := by
  let _ : WithIdeal Λ := ⟨⊥⟩
  have : DiscreteTopology Λ := is_bot_adic_iff.1 rfl
  let _ : WithIdeal R := ⟨I⟩
  obtain ⟨hcs, ht2⟩ := (IsAdic.isAdicComplete_iff (I := I) rfl).1 ‹IsAdicComplete I R›
  have := hcs
  have := ht2
  have ha : MvPowerSeries.HasEval y :=
    { hpow := fun i => WithIdeal.isTopologicallyNilpotent_of_mem (hy i)
      tendsto_zero := by simp [Filter.cofinite_eq_bot] }
  set F : MvPowerSeries (Fin n) Λ →+* R :=
    MvPowerSeries.eval₂Hom (φ := f) continuous_of_discreteTopology ha with hFdef
  have hFc : ⇑F = MvPowerSeries.eval₂ f y := MvPowerSeries.coe_eval₂Hom _ _
  refine ⟨F, fun i => ?_, fun c => ?_⟩
  · rw [hFc]; exact MvPowerSeries.eval₂_X f y i
  · rw [hFc]; exact MvPowerSeries.eval₂_C f y c

end Stacks.CompleteLocalRing.RegularSubring

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.FlatFibreAtPrime
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.ProjectiveClosedFibre

/-!
# The key observation of Stacks 05IG on a fibre

Let `R → A` be a ring map, `𝔪` an ideal of `R` with `A / 𝔪 A` Noetherian, `P` a finite
`A`-module and `q` a prime of `A` containing `𝔪 A`. The module `P / 𝔪 P` has finitely many
associated primes over `A / 𝔪 A`. This file produces an element `g ∉ q` lying in every one of
them that is not contained in `q` ([Stacks, Tag 05IF]), and deduces the form in which the proof
of [Stacks, Tag 05IG] uses it: after inverting `g`, every element of `A` outside `q` acts
injectively on `P / 𝔪 P`. For `R → A` of finite type and a prime `𝔭` of `R` the same holds on
the fibre `P ⊗_R κ(𝔭)`, by passing to `R_𝔭`, where the fibre ring is of finite type over the
field `κ(𝔭)`.

## Main results

* `Stacks.WeaklyAssociatedPrimes.exists_pow_smul_mem_smul_top_of_smul_mem_smul_top`
* `Stacks.WeaklyAssociatedPrimes.exists_mul_pow_smul_mem_smul_top_of_smul_mem_smul_top`

## References

* [Stacks Project, Tag 05IF](https://stacks.math.columbia.edu/tag/05IF)
* [Stacks Project, Tag 05IG](https://stacks.math.columbia.edu/tag/05IG)
-/

@[expose] public section

open TensorProduct IsLocalRing

namespace Stacks.WeaklyAssociatedPrimes

/-- **The key observation on a Noetherian fibre.** For an ideal `𝔪` of `R` with `A / 𝔪 A`
Noetherian, a finite `A`-module `P` and a prime `q ⊇ 𝔪 A` of `A`, there is `g ∉ q` such that
every `t ∉ q` acts injectively on `P / 𝔪 P` after inverting `g`: if `t p ∈ 𝔪 P` then
`g ^ n p ∈ 𝔪 P` for some `n`. The element `g` lies in every associated prime of `P / 𝔪 P` not
contained in `q`. -/
theorem exists_pow_smul_mem_smul_top_of_smul_mem_smul_top
    {R A P : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup P] [Module A P] [Module.Finite A P] [Module R P] [IsScalarTower R A P]
    (𝔪 : Ideal R) [IsNoetherianRing (A ⧸ Ideal.map (algebraMap R A) 𝔪)] (q : Ideal A) [q.IsPrime]
    (hq : Ideal.map (algebraMap R A) 𝔪 ≤ q) :
    ∃ g : A, g ∉ q ∧ ∀ t : A, t ∉ q → ∀ p : P,
      t • p ∈ 𝔪 • (⊤ : Submodule R P) → ∃ n : ℕ, g ^ n • p ∈ 𝔪 • (⊤ : Submodule R P) := by
  classical
  set I : Ideal A := Ideal.map (algebraMap R A) 𝔪 with hI
  set Q := P ⧸ I • (⊤ : Submodule A P)
  have : Module.Finite (A ⧸ I) Q :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ I) Q
  set π : A →+* A ⧸ I := Ideal.Quotient.mk I
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  set qb : Ideal (A ⧸ I) := q.map π with hqb
  have hker : RingHom.ker π ≤ q := by rw [Ideal.mk_ker]; exact hq
  have hqbp : qb.IsPrime := Ideal.map_isPrime_of_surjective hπ hker
  have hmemq : ∀ a : A, π a ∈ qb ↔ a ∈ q := fun a => by
    rw [hqb, ← Ideal.mem_comap, Ideal.comap_map_of_surjective' π hπ, sup_eq_left.mpr hker]
  -- the bad associated primes and an element in each of them outside `qb`
  set S := {r ∈ associatedPrimes (A ⧸ I) Q | ¬ r ≤ qb}
  have hSfin : S.Finite := (associatedPrimes.finite (A ⧸ I) Q).subset fun r hr => hr.1
  have hchoose : ∀ r : S, ∃ a : A ⧸ I, a ∈ (r : Ideal (A ⧸ I)) ∧ a ∉ qb := fun r =>
    Set.not_subset.mp r.2.2
  choose a ha hanq using hchoose
  have : Fintype S := hSfin.fintype
  set gb : A ⧸ I := ∏ r : S, a r with hgb
  have hgbq : gb ∉ qb := by
    rw [hgb]
    exact fun h => (Ideal.IsPrime.prod_mem_iff (hp := hqbp)).mp h |>.elim fun r ⟨_, hr⟩ =>
      hanq r hr
  obtain ⟨g, hg⟩ := hπ gb
  refine ⟨g, fun hgq => hgbq (hg ▸ (hmemq g).mpr hgq), fun t ht p hp => ?_⟩
  -- pass to the closed fibre
  have hmemI : ∀ x : P, x ∈ 𝔪 • (⊤ : Submodule R P) ↔ x ∈ I • (⊤ : Submodule A P) :=
    fun x => mem_smul_top_iff_mem_map_smul_top (S := A) 𝔪 x
  set x : Q := Submodule.Quotient.mk p with hx
  have hsmul : ∀ (b : A) (y : P), π b • (Submodule.Quotient.mk y : Q) =
      Submodule.Quotient.mk (b • y) := fun b y => Module.Quotient.mk_smul_mk (M := P) I b y
  have htx : π t • x = 0 := by
    rw [hx, hsmul, Submodule.Quotient.mk_eq_zero, ← hmemI]
    exact hp
  -- `gb` lies in every prime minimal over the annihilator of `x`
  set C : Submodule (A ⧸ I) Q := (A ⧸ I) ∙ x with hC
  set J : Ideal (A ⧸ I) := C.annihilator with hJ
  have htJ : π t ∈ J := (Submodule.mem_annihilator_span_singleton x _).mpr htx
  have hgJ : gb ∈ J.radical := by
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro p₀ ⟨hJp, hp₀⟩
    obtain ⟨r, hr, hrp⟩ := Ideal.exists_minimalPrimes_le hJp
    apply hrp
    have hrC : r ∈ associatedPrimes (A ⧸ I) C := by
      apply Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
      simpa [hJ, Submodule.annihilator] using hr
    have hrQ : r ∈ associatedPrimes (A ⧸ I) Q :=
      associatedPrimes.subset_of_injective C.injective_subtype hrC
    by_cases hrq : r ≤ qb
    · exact absurd ((hmemq t).mp (hrq (hr.1.2 htJ))) ht
    · let r' : S := ⟨r, hrQ, hrq⟩
      exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem a (Finset.mem_univ r')) (ha r')
  obtain ⟨n, hn⟩ := hgJ
  refine ⟨n, ?_⟩
  rw [hmemI, ← Submodule.Quotient.mk_eq_zero, ← hsmul, map_pow, hg]
  exact (Submodule.mem_annihilator_span_singleton x _).mp hn

section AtPrime

attribute [local instance] moduleLocalizationLocalizedModule
  isScalarTowerLocalizationLocalizedModule Algebra.TensorProduct.rightAlgebra

/-- **The key observation at an arbitrary prime** (Stacks Tag 05IF). For `R → A` of finite type,
a finite `A`-module `P`, a prime `𝔭` of `R` and a prime `q` of `A` over `𝔭`, there is `g ∉ q`
such that every `t ∉ q` acts injectively on the fibre `P ⊗_R κ(𝔭)` after inverting `g`: if
`t p ∈ 𝔭 P` then `r g ^ n p ∈ 𝔭 P` for some `n` and some `r ∉ 𝔭`. -/
theorem exists_mul_pow_smul_mem_smul_top_of_smul_mem_smul_top
    {R A P : Type*} [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    [AddCommGroup P] [Module A P] [Module.Finite A P] [Module R P] [IsScalarTower R A P]
    (𝔭 : Ideal R) [𝔭.IsPrime] (q : Ideal A) [q.IsPrime] [q.LiesOver 𝔭] :
    ∃ g : A, g ∉ q ∧ ∀ t : A, t ∉ q → ∀ p : P, t • p ∈ 𝔭 • (⊤ : Submodule R P) →
      ∃ n : ℕ, ∃ r : R, r ∉ 𝔭 ∧ (algebraMap R A r * g ^ n) • p ∈ 𝔭 • (⊤ : Submodule R P) := by
  classical
  set T : Submonoid A := primeComplImage A 𝔭 with hT
  set R𝔭 := Localization 𝔭.primeCompl
  set A𝔭 := Localization T
  set P𝔭 := LocalizedModule T P
  have : IsNoetherianRing (A𝔭 ⧸ Ideal.map (algebraMap R𝔭 A𝔭) (maximalIdeal R𝔭)) := by
    have : Algebra.FiniteType 𝔭.ResidueField (𝔭.Fiber A) := inferInstance
    have : IsNoetherianRing (𝔭.Fiber A) :=
      Algebra.FiniteType.isNoetherianRing 𝔭.ResidueField (𝔭.Fiber A)
    exact isNoetherianRing_of_ringEquiv _ (Ideal.Fiber.algEquivQuotient 𝔭).toRingEquiv
  have hdisj : Disjoint (T : Set A) (q : Set A) := Ideal.disjoint_primeCompl_of_liesOver q 𝔭
  set q𝔭 : Ideal A𝔭 := q.map (algebraMap A A𝔭) with hq𝔭
  have : q𝔭.IsPrime := IsLocalization.AtPrime.isPrime_map_of_liesOver A 𝔭 A𝔭 q
  have hcomap : q𝔭.comap (algebraMap A A𝔭) = q :=
    IsLocalization.under_map_of_isPrime_disjoint T A𝔭 inferInstance hdisj
  obtain ⟨g', hg'q, hg'⟩ := exists_pow_smul_mem_smul_top_of_smul_mem_smul_top (P := P𝔭)
    (maximalIdeal R𝔭) q𝔭 (fibreIdeal_le_map 𝔭 q)
  obtain ⟨⟨g, σ⟩, hgσ⟩ := IsLocalization.mk'_surjective T g'
  simp only at hgσ
  subst hgσ
  have hgq : g ∉ q := by
    intro hg
    apply hg'q
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact q𝔭.mul_mem_right _ (Ideal.mem_map_of_mem _ hg)
  -- the ideal `𝔭 A_𝔭`, through which membership in `𝔪_{R_𝔭} P_𝔭` is tested
  set J : Ideal A𝔭 := Ideal.map (algebraMap A A𝔭) (Ideal.map (algebraMap R A) 𝔭) with hJ
  have hmap : Ideal.map (algebraMap R𝔭 A𝔭) (maximalIdeal R𝔭) = J := by
    rw [hJ, ← IsLocalization.AtPrime.map_eq_maximalIdeal 𝔭 R𝔭, Ideal.map_map, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  have hmemJ : ∀ z : P𝔭, z ∈ maximalIdeal R𝔭 • (⊤ : Submodule R𝔭 P𝔭) ↔
      z ∈ J • (⊤ : Submodule A𝔭 P𝔭) := fun z => by
    rw [mem_smul_top_iff_mem_map_smul_top (S := A𝔭), hmap]
  set K : Submodule A P := Ideal.map (algebraMap R A) 𝔭 • (⊤ : Submodule A P) with hK
  have hmemK : ∀ x : P, x ∈ K ↔ x ∈ 𝔭 • (⊤ : Submodule R P) := fun x =>
    (mem_smul_top_iff_mem_map_smul_top (S := A) 𝔭 x).symm
  have hmk : ∀ (a : A) (y : P), (algebraMap A A𝔭 a) • LocalizedModule.mk y (1 : T) =
      LocalizedModule.mk (a • y) 1 := fun a y => by
    rw [algebraMap_smul, LocalizedModule.smul'_mk]
  -- `𝔭 P` lands in `J P_𝔭`
  have hL1 : ∀ y ∈ K, LocalizedModule.mk y (1 : T) ∈ J • (⊤ : Submodule A𝔭 P𝔭) := by
    intro y hy
    induction hy using Submodule.smul_induction_on' with
    | smul a ha y' _ =>
        rw [← hmk]
        exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ ha) Submodule.mem_top
    | add y _ y' _ hy hy' =>
        have : LocalizedModule.mk (y + y') (1 : T) =
            LocalizedModule.mk y 1 + LocalizedModule.mk y' 1 := by
          rw [LocalizedModule.mk_add_mk, one_smul, one_smul, mul_one]
        rw [this]
        exact Submodule.add_mem _ hy hy'
  -- `J P_𝔭` pulls back into the saturation of `𝔭 P`
  have hL2 : ∀ y : P, LocalizedModule.mk y (1 : T) ∈ J • (⊤ : Submodule A𝔭 P𝔭) →
      ∃ r : R, r ∉ 𝔭 ∧ algebraMap R A r • y ∈ 𝔭 • (⊤ : Submodule R P) := by
    intro y hy
    set φ := LocalizedModule.map T K.mkQ with hφ
    have hker : J • (⊤ : Submodule A𝔭 P𝔭) ≤ LinearMap.ker φ := by
      refine Submodule.smul_le.mpr fun c hc w _ => ?_
      have hJle : J ≤ Module.annihilator A𝔭 (LocalizedModule T (P ⧸ K)) :=
        Ideal.map_le_iff_le_comap.mpr fun a ha => Module.mem_annihilator.mpr fun z => by
          induction z using LocalizedModule.induction_on with
          | h m s =>
              obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
              rw [algebraMap_smul, LocalizedModule.smul'_mk, ← Submodule.Quotient.mk_smul,
                (Submodule.Quotient.mk_eq_zero _).mpr
                  (Submodule.smul_mem_smul ha Submodule.mem_top),
                LocalizedModule.zero_mk]
      rw [LinearMap.mem_ker, map_smul]
      exact Module.mem_annihilator.mp (hJle hc) _
    have h0 := LinearMap.mem_ker.mp (hker hy)
    rw [hφ, LocalizedModule.map_mk, Submodule.mkQ_apply, ← LocalizedModule.zero_mk 1,
      LocalizedModule.mk_eq] at h0
    obtain ⟨τ, hτ⟩ := h0
    rw [one_smul, one_smul, smul_zero, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero, hmemK] at hτ
    obtain ⟨r, hr, hrτ⟩ := τ.2
    refine ⟨r, hr, ?_⟩
    have : (τ : A) • y = algebraMap R A r • y := by rw [← hrτ]
    rw [← this]
    exact hτ
  refine ⟨g, hgq, fun t ht p hp => ?_⟩
  have htq : algebraMap A A𝔭 t ∉ q𝔭 := fun h => ht (by rw [← hcomap]; exact h)
  obtain ⟨n, hn⟩ := hg' _ htq (LocalizedModule.mk p 1) (by
    rw [hmk, hmemJ]; exact hL1 _ ((hmemK _).mpr hp))
  refine ⟨n, ?_⟩
  have hgn : LocalizedModule.mk (g ^ n • p) (1 : T) ∈ J • (⊤ : Submodule A𝔭 P𝔭) := by
    rw [← hmk]
    rw [hmemJ] at hn
    have := Submodule.smul_mem _ ((algebraMap A A𝔭 (σ : A)) ^ n) hn
    rwa [smul_smul, ← mul_pow, IsLocalization.mk'_spec', ← map_pow] at this
  obtain ⟨r, hr, hrp⟩ := hL2 _ hgn
  exact ⟨r, hr, by rwa [mul_smul]⟩

end AtPrime

end Stacks.WeaklyAssociatedPrimes

end

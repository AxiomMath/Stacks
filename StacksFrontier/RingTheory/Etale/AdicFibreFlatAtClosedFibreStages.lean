module

public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Smooth.Fiber
public import StacksFrontier.RingTheory.Flat.FlatLocusAway
public import StacksFrontier.RingTheory.Smooth.AdicStageSmoothLocus
public import StacksFrontier.RingTheory.Smoothing.ArtinianFactorizationDescent
public import StacksFrontier.RingTheory.Unramified.LocusBaseChangeAtPrime

/-!
# A ring map whose adic stages are étale is étale near a prime above the ideal

Let `D → C` be a ring map of finite type with `D` Noetherian, let `J ⊆ D` be an ideal and let
`q` be a prime of `C` containing `JC`. If every stage `D / J^{n+1} → C / J^{n+1} C` is étale,
then `D → C` is étale on a principal open neighbourhood `D(s)` of `q`.

This is the commutative algebra behind the étale form of the local criterion of flatness along
a closed fibre: flatness of the stages gives flatness of `C_q` over `D` (Stacks 0523, through
`Algebra.flat_localization_atPrime_of_forall_smoothAt`); unramifiedness of the first stage gives
unramifiedness of `D → C` at `q`, the module of differentials commuting with base change
(`Algebra.isUnramifiedAt_iff_isUnramifiedAt_of_isPushout`); and a map of finite presentation
which is flat and unramified at `q` is étale at `q`, hence on some `D(s)`.

## Main results

* `Algebra.isEtaleAt_of_forall_etale_quotient_pow`: `D → C` is étale at `q`.
* `Algebra.exists_notMem_etale_localization_away_of_forall_etale_quotient_pow`: `D → C_s` is
  étale for some `s ∉ q`.
* `Algebra.exists_notMem_flat_localization_away_of_forall_flat_quotient_pow`: the flat
  analogue: if every stage is flat, `D → C_s` is flat for some `s ∉ q`.

## References

* [Stacks Project, Tag 0523](https://stacks.math.columbia.edu/tag/0523)
* [Stacks Project, Tag 00MK](https://stacks.math.columbia.edu/tag/00MK)
* [Stacks Project, Tag 08WD](https://stacks.math.columbia.edu/tag/08WD)
-/

@[expose] public section

universe u

namespace Algebra

variable {D C : Type u} [CommRing D] [CommRing C] [Algebra D C]

/-- An étale algebra is smooth at every prime: take `g = 1`. -/
theorem smoothAt_of_etale [Algebra.Etale D C] (q : Ideal C) [q.IsPrime] :
    Algebra.SmoothAt D C q :=
  ⟨1, q.ne_top_iff_one.mp ‹q.IsPrime›.ne_top, inferInstance⟩

/-- A ring map of finite presentation which is flat and unramified at a prime `q` is étale at
`q`: on a principal open `D(s₂)` where it is flat, the global criterion
`Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat` applies at the prime induced by `q`. -/
theorem isEtaleAt_of_flat_localization_of_isUnramifiedAt [IsNoetherianRing D]
    [Algebra.FiniteType D C] (q : Ideal C) [q.IsPrime]
    (hflat : Module.Flat D (Localization.AtPrime q)) [Algebra.IsUnramifiedAt D q] :
    Algebra.IsEtaleAt D q := by
  have hflat' : Module.Flat D (LocalizedModule.AtPrime q C) :=
    Module.Flat.of_linearEquiv ((IsLocalizedModule.linearEquiv q.primeCompl
      (LocalizedModule.mkLinearMap q.primeCompl C)
      (Algebra.linearMap C (Localization.AtPrime q))).restrictScalars D)
  obtain ⟨s, hs, hsflat⟩ :=
    Module.exists_away_flat_localizedModule_of_flat_atPrime (A := D) (M := C) q hflat'
  let C' := Localization.Away s
  have : Module.Flat D C' :=
    Module.Flat.of_linearEquiv ((IsLocalizedModule.linearEquiv (Submonoid.powers s)
      (Algebra.linearMap C C')
      (LocalizedModule.mkLinearMap (Submonoid.powers s) C)).restrictScalars D)
  have : Algebra.FinitePresentation D C := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have : Algebra.FinitePresentation C C' := IsLocalization.Away.finitePresentation s
  have : Algebra.FinitePresentation D C' := .trans D C C'
  have hdisj : Disjoint (Submonoid.powers s : Set C) q := by
    rw [Set.disjoint_left]
    rintro _ ⟨k, rfl⟩ hk
    exact hs (‹q.IsPrime›.mem_of_pow_mem k hk)
  let q' : Ideal C' := q.map (algebraMap C C')
  have : q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers s) C' q
    ‹_› hdisj
  have hcomap : q'.under C = q :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers s) C' ‹_› hdisj
  have hloc : IsLocalization q.primeCompl (Localization.AtPrime q') := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers s) (Localization.AtPrime q') q'
    have hM : (q'.under C).primeCompl = q.primeCompl :=
      Submonoid.ext fun x => by rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hcomap]
    change IsLocalization (q'.under C).primeCompl _ at this
    rwa [hM] at this
  let e : Localization.AtPrime q ≃ₐ[D] Localization.AtPrime q' :=
    (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q)
      (Localization.AtPrime q')).restrictScalars D
  have : Algebra.IsUnramifiedAt D q' :=
    Algebra.FormallyUnramified.of_equiv e
  have : Algebra.IsEtaleAt D q' := Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat q'
  exact Algebra.FormallyEtale.of_equiv e.symm

/-- **A ring map whose adic stages are étale is étale at a prime above the ideal.** Let `D` be
Noetherian, `D → C` of finite type, `J ⊆ D` an ideal and `q ⊇ JC` a prime of `C`. If every
`D / J^{n+1} → C / J^{n+1} C` is étale, then `D → C` is étale at `q`. -/
theorem isEtaleAt_of_forall_etale_quotient_pow [IsNoetherianRing D] [Algebra.FiniteType D C]
    (J : Ideal D) (q : Ideal C) [q.IsPrime] (hq : J.map (algebraMap D C) ≤ q)
    (h : ∀ n : ℕ, Algebra.Etale (D ⧸ J ^ (n + 1)) (C ⧸ (J ^ (n + 1)).map (algebraMap D C))) :
    Algebra.IsEtaleAt D q := by
  have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing D C
  have hflat : Module.Flat D (Localization.AtPrime q) :=
    flat_localization_atPrime_of_forall_smoothAt J q hq fun n => by
      have := isPrime_map_quotient (map_pow_succ_le hq n)
      have := h n
      exact smoothAt_of_etale _
  -- the first stage is unramified at the prime induced by `q`
  set J₁ : Ideal D := J ^ (0 + 1)
  have hJ₁ : J₁.map (algebraMap D C) ≤ q := map_pow_succ_le hq 0
  let q₁ : Ideal (C ⧸ J₁.map (algebraMap D C)) := q.map (Ideal.Quotient.mk _)
  have : q₁.IsPrime := isPrime_map_quotient hJ₁
  have : q₁.LiesOver q := by
    constructor
    rw [Ideal.under, Ideal.Quotient.algebraMap_eq, Ideal.comap_map_of_surjective _
      Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.mpr hJ₁]
  have : Algebra.IsPushout D C (D ⧸ J₁) (C ⧸ J₁.map (algebraMap D C)) :=
    Stacks.Smoothing.isPushout_quotient_idealMap D C J₁
  have : Algebra.Etale (D ⧸ J₁) (C ⧸ J₁.map (algebraMap D C)) := h 0
  have : Algebra.IsUnramifiedAt (D ⧸ J₁) q₁ := inferInstance
  have : Algebra.IsUnramifiedAt D q :=
    (isUnramifiedAt_iff_isUnramifiedAt_of_isPushout D C (D ⧸ J₁)
      (C ⧸ J₁.map (algebraMap D C)) q q₁).mpr ‹_›
  exact isEtaleAt_of_flat_localization_of_isUnramifiedAt q hflat

/-- **A ring map whose adic stages are étale is étale near a prime above the ideal.** Let `D`
be Noetherian, `D → C` of finite type, `J ⊆ D` an ideal and `q ⊇ JC` a prime of `C`. If every
`D / J^{n+1} → C / J^{n+1} C` is étale, then `D → C_s` is étale for some `s ∉ q`. -/
theorem exists_notMem_etale_localization_away_of_forall_etale_quotient_pow [IsNoetherianRing D]
    [Algebra.FiniteType D C] (J : Ideal D) (q : Ideal C) [q.IsPrime]
    (hq : J.map (algebraMap D C) ≤ q)
    (h : ∀ n : ℕ, Algebra.Etale (D ⧸ J ^ (n + 1)) (C ⧸ (J ^ (n + 1)).map (algebraMap D C))) :
    ∃ s ∉ q, Algebra.Etale D (Localization.Away s) := by
  have : Algebra.FinitePresentation D C := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have := isEtaleAt_of_forall_etale_quotient_pow J q hq h
  exact Algebra.exists_etale_of_isEtaleAt q

/-- Flatness of the quotient algebra `C / KC` over `D / K` is flatness of the module quotient
`C / K • C` over `D / K`, the form in which Stacks 0523 is stated. -/
theorem flat_quotient_smul_top_of_flat_quotient_map (K : Ideal D)
    [Module.Flat (D ⧸ K) (C ⧸ K.map (algebraMap D C))] :
    Module.Flat (D ⧸ K) (C ⧸ (K • ⊤ : Submodule D C)) := by
  let e : (C ⧸ (K • ⊤ : Submodule D C)) ≃ₗ[D] (C ⧸ K.map (algebraMap D C)) :=
    (Submodule.quotEquivOfEq _ _ (Ideal.smul_top_eq_map K)) ≪≫ₗ
      (Submodule.Quotient.restrictScalarsEquiv D _)
  exact Module.Flat.of_linearEquiv (e.extendScalarsOfSurjective Ideal.Quotient.mk_surjective)

/-- **A ring map whose adic stages are flat is flat near a prime above the ideal.** Let `D` be
Noetherian, `D → C` of finite type, `J ⊆ D` an ideal and `q ⊇ JC` a prime of `C`. If every
`D / J^{n+1} → C / J^{n+1} C` is flat, then `C_q` is flat over `D` (Stacks 0523), hence so is
`C_s` for some `s ∉ q`. -/
theorem exists_notMem_flat_localization_away_of_forall_flat_quotient_pow [IsNoetherianRing D]
    [Algebra.FiniteType D C] (J : Ideal D) (q : Ideal C) [q.IsPrime]
    (hq : J.map (algebraMap D C) ≤ q)
    (h : ∀ n : ℕ, Module.Flat (D ⧸ J ^ (n + 1)) (C ⧸ (J ^ (n + 1)).map (algebraMap D C))) :
    ∃ s ∉ q, Module.Flat D (Localization.Away s) := by
  have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing D C
  have hflat : Module.Flat D (Localization.AtPrime q) :=
    Module.Flat.of_flat_quotient_pow J C
      (fun n => have := h n; flat_quotient_smul_top_of_flat_quotient_map _) q hq
      (Localization.AtPrime q) (Algebra.linearMap C (Localization.AtPrime q))
  have hflat' : Module.Flat D (LocalizedModule.AtPrime q C) :=
    Module.Flat.of_linearEquiv ((IsLocalizedModule.linearEquiv q.primeCompl
      (LocalizedModule.mkLinearMap q.primeCompl C)
      (Algebra.linearMap C (Localization.AtPrime q))).restrictScalars D)
  obtain ⟨s, hs, hsflat⟩ :=
    Module.exists_away_flat_localizedModule_of_flat_atPrime (A := D) (M := C) q hflat'
  exact ⟨s, hs, Module.Flat.of_linearEquiv ((IsLocalizedModule.linearEquiv (Submonoid.powers s)
      (Algebra.linearMap C (Localization.Away s))
      (LocalizedModule.mkLinearMap (Submonoid.powers s) C)).restrictScalars D)⟩

end Algebra

end

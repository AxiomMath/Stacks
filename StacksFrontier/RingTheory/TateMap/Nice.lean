module

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import StacksFrontier.RingTheory.CompleteIntersection.Relative
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.EtaleLocus
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleQuasiFiniteSyntomic
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.ChartFactorization
public import StacksFrontier.RingTheory.TraceElement.TargetLocalization

/-!
# Nice charts: the trace element has vanishing annihilator

Let `A → B` be a flat quasi-finite homomorphism of Noetherian rings. Following the proof of
Proposition 0FKD, call `A → B` *nice* if the annihilator of the trace element
`τ_{B/A} ∈ ω_{B/A}` is zero. On a nice chart an isomorphism `M → ω_{B/A}` from an invertible
module is determined by the element it sends to `τ_{B/A}`, and a domain with one prime at which
`A → B` is unramified is nice as soon as `ω_{B/A}` is invertible.

## Main definitions

* `Stacks.TateMap.IsNiceChart A B`: `b • τ_{B/A} = 0` implies `b = 0`.

## Main results

* `Stacks.TateMap.IsNiceChart.linearEquiv_ext`: on a nice chart, two isomorphisms from an
  invertible module onto `ω_{B/A}` that send one element to `τ_{B/A}` are equal.
* `Stacks.TateMap.isNiceChart_of_isUnramifiedAt`: a domain which is a relative global complete
  intersection over `A` and is unramified over `A` at one prime is nice.

## References

* [Stacks Project, Tag 0FKD](https://stacks.math.columbia.edu/tag/0FKD)
-/

@[expose] public noncomputable section

universe u

namespace Stacks.TateMap

open Stacks.Discriminant Stacks.Annihilator

section Nice

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
  [IsNoetherianRing B] [Module.Flat A B] [Algebra.QuasiFinite A B]

/-- A flat quasi-finite homomorphism of Noetherian rings `A → B` is *nice* if the annihilator of
the trace element `τ_{B/A}` of `ω_{B/A}` is zero. -/
def IsNiceChart : Prop :=
  ∀ (F : FiniteOpenFactorization.{u, u, u} A B) (b : B),
    b • dualizingModule.traceElement F = 0 → b = 0

variable {A B}

omit [IsNoetherianRing B] [Algebra.QuasiFinite A B] in
/-- **Rigidity on a nice chart.** Two isomorphisms from an invertible module onto `ω_{B/A}` which
send the same element to the trace element are equal: they differ by a unit `r` with
`r • τ_{B/A} = τ_{B/A}`, and `r = 1` because `τ_{B/A}` has vanishing annihilator. -/
theorem IsNiceChart.linearEquiv_ext (h : IsNiceChart A B)
    (F : FiniteOpenFactorization.{u, u, u} A B) {M : Type*} [AddCommGroup M] [Module B M]
    [Module.Invertible B M] (e e' : M ≃ₗ[B] dualizingModule F) (m : M)
    (he : e m = dualizingModule.traceElement F) (he' : e' m = dualizingModule.traceElement F) :
    e = e' := by
  obtain ⟨r, hr⟩ := (Module.Invertible.toModuleEnd_bijective B M).2 (e.trans e'.symm).toLinearMap
  have key : ∀ x : M, e x = r • e' x := fun x ↦ by
    have hx : r • x = e'.symm (e x) := LinearMap.congr_fun hr x
    rw [← e'.map_smul, hx, LinearEquiv.apply_symm_apply]
  have hr1 : r = 1 := by
    have h0 : (r - 1) • dualizingModule.traceElement F = 0 := by
      rw [sub_smul, one_smul, sub_eq_zero]
      conv_rhs => rw [← he, key m, he']
    exact sub_eq_zero.mp (h F _ h0)
  ext x
  rw [key x, hr1, one_smul]

/-- **Niceness is preserved by localizing the chart.** If `A → B` is nice and `C` is the
localization of `B` away from an element `g`, then `A → C` is nice.

The trace element of `C` is the image of that of `B` (Tag 0BT9), so `c • τ_{C/A} = 0` with
`c = b / g^m` gives `g^j b • τ_{B/A} = 0` for some `j`, hence `g^j b = 0` and `c = 0`. -/
theorem IsNiceChart.of_isLocalizationAway [Algebra.FiniteType A B] (h : IsNiceChart A B)
    {C : Type u} [CommRing C] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsNoetherianRing C] [Module.Flat A C] [Algebra.QuasiFinite A C] (g : B)
    [IsLocalization.Away g C] : IsNiceChart A C := by
  intro G c hc
  obtain ⟨F⟩ := nonempty_finiteOpenFactorization (A := A) (B := B)
  let mk := TensorProduct.mk B C (dualizingModule F) 1
  have hl : IsLocalizedModule (Submonoid.powers g) mk := inferInstance
  let ε := localizedModule_dualizingModule_equiv g F G mk hl
  have hε : ε (mk (dualizingModule.traceElement F)) = dualizingModule.traceElement G :=
    eq_traceElement_of_isTraceElement G
      (isTraceElement_localization g F G _ hl (isTraceElement_traceElement F))
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers g) c
  have h1 : algebraMap B C b • mk (dualizingModule.traceElement F) = 0 := by
    have h2 : ε (IsLocalization.mk' C b s • mk (dualizingModule.traceElement F)) = 0 := by
      rw [map_smul, hε, hc]
    rw [LinearEquiv.map_eq_zero_iff] at h2
    rw [← IsLocalization.mk'_spec C b s, mul_comm, mul_smul, h2, smul_zero]
  have h3 : mk (b • dualizingModule.traceElement F) = mk 0 := by
    rw [map_zero, ← h1, map_smul, ← IsScalarTower.algebraMap_smul C b]
  obtain ⟨⟨t, ht⟩, hj⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers g) h3
  obtain ⟨j, rfl⟩ := ht
  rw [smul_zero, Submonoid.smul_def, smul_smul] at hj
  have hb0 : algebraMap B C b = 0 :=
    ((IsLocalization.Away.algebraMap_isUnit g).pow j).mul_right_eq_zero.mp <| by
      rw [← map_pow, ← map_mul, h F _ hj, map_zero]
  change IsLocalization.mk' C b s = 0
  rw [IsLocalization.mk'_eq_iff_eq_mul, zero_mul, hb0]

/-- **Niceness is invariant under isomorphism of the chart over the base.** -/
theorem IsNiceChart.of_algEquiv [Algebra.FiniteType A B] (h : IsNiceChart A B)
    {C : Type u} [CommRing C] [Algebra A C] [IsNoetherianRing C] [Module.Flat A C]
    [Algebra.QuasiFinite A C] (e : B ≃ₐ[A] C) : IsNiceChart A C := by
  let : Algebra B C := e.toRingHom.toAlgebra
  have : IsScalarTower A B C :=
    IsScalarTower.of_algebraMap_eq' (by ext a; exact (e.commutes a).symm)
  have : IsLocalization.Away (1 : B) C :=
    IsLocalization.away_of_isUnit_of_bijective C isUnit_one e.bijective
  exact h.of_isLocalizationAway 1

/-- **A criterion for niceness.** Let `A → B` be a flat quasi-finite homomorphism of Noetherian
rings which is a relative global complete intersection, with `B` a domain. If `A → B` is
unramified at one prime of `B`, then `A → B` is nice.

At that prime `q` the trace element generates `ω_{B/A}`, so some `s ∉ q` carries `ω_{B/A}` into
`B τ_{B/A}`. If `b • τ_{B/A} = 0` then `b s` kills the invertible module `ω_{B/A}`, hence
`b s = 0`, and `s ≠ 0` in the domain `B`. -/
theorem isNiceChart_of_isUnramifiedAt [IsDomain B] [Algebra.FiniteType A B]
    [Algebra.IsRelativeGlobalCompleteIntersection A B] (q : Ideal B) [q.IsPrime]
    [Algebra.IsUnramifiedAt A q] : IsNiceChart A B := by
  intro F b hb
  have : Module.Invertible B (dualizingModule F) :=
    dualizingModule_invertible_of_isRelativeGlobalCompleteIntersection F
  have hq : (⟨q, inferInstance⟩ : PrimeSpectrum B) ∉ PrimeSpectrum.zeroLocus
      (cokerSpanIdeal B (dualizingModule.traceElement F) : Set B) := by
    rw [zeroLocus_cokerSpanIdeal_traceElement F, Set.notMem_compl_iff]
    exact ‹Algebra.IsUnramifiedAt A q›
  rw [PrimeSpectrum.mem_zeroLocus, Set.not_subset] at hq
  obtain ⟨s, hs, hsq⟩ := hq
  have hs0 : s ≠ 0 := fun h ↦ hsq (h ▸ q.zero_mem)
  have hbs : b * s = 0 := by
    refine FaithfulSMul.eq_of_smul_eq_smul (M := B) (α := dualizingModule F) fun x ↦ ?_
    rw [zero_smul]
    have hx : s • Submodule.Quotient.mk (p := Submodule.span B
        {dualizingModule.traceElement F}) x = 0 :=
      Module.mem_annihilator.mp (by rw [← cokerSpanIdeal_def]; exact hs) _
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_span_singleton] at hx
    obtain ⟨c, hc⟩ := hx
    rw [mul_smul, ← hc, smul_comm, hb, smul_zero]
  exact (mul_eq_zero.mp hbs).resolve_right hs0

end Nice

/-! ### Generic unramifiedness -/

section Generic

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- A domain `B` over `A` is unramified at its generic point as soon as a nonzero element kills
`Ω_{B/A}`. -/
theorem isUnramifiedAt_bot_of_smul_eq_zero [IsDomain B] (c : B) (hc : c ≠ 0)
    (h : ∀ x : Ω[B⁄A], c • x = 0) : Algebra.IsUnramifiedAt A (⊥ : Ideal B) := by
  change (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum B) ∈ Algebra.unramifiedLocus A B
  rw [Algebra.unramifiedLocus_eq_compl_support, Set.mem_compl_iff, Module.notMem_support_iff,
    LocalizedModule.subsingleton_iff]
  exact fun m ↦ ⟨c, hc, h m⟩

/-- Conversely, if a domain `B` of finite type over `A` is unramified at its generic point, some
nonzero element kills `Ω_{B/A}`. -/
theorem exists_smul_eq_zero_of_isUnramifiedAt_bot [IsDomain B] [Algebra.FiniteType A B]
    [Algebra.IsUnramifiedAt A (⊥ : Ideal B)] : ∃ c : B, c ≠ 0 ∧ ∀ x : Ω[B⁄A], c • x = 0 := by
  have hmem : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum B) ∈ Algebra.unramifiedLocus A B :=
    ‹Algebra.IsUnramifiedAt A (⊥ : Ideal B)›
  rw [Algebra.unramifiedLocus_eq_compl_support, Set.mem_compl_iff, Module.support_eq_zeroLocus,
    PrimeSpectrum.mem_zeroLocus, Set.not_subset] at hmem
  obtain ⟨c, hc, hc0⟩ := hmem
  exact ⟨c, fun h ↦ hc0 (h ▸ Submodule.zero_mem _), fun x ↦ Module.mem_annihilator.mp hc x⟩

/-- In a domain essentially of finite type over `A`, unramifiedness at one prime gives
unramifiedness at the generic point: the unramified locus is open, and every nonempty open of
`Spec B` contains the generic point. -/
theorem isUnramifiedAt_bot_of_isUnramifiedAt [IsDomain B] [Algebra.EssFiniteType A B]
    (q : Ideal B) [q.IsPrime] [Algebra.IsUnramifiedAt A q] :
    Algebra.IsUnramifiedAt A (⊥ : Ideal B) := by
  have hq : (⟨q, inferInstance⟩ : PrimeSpectrum B) ∈ Algebra.unramifiedLocus A B :=
    ‹Algebra.IsUnramifiedAt A q›
  have hsp : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum B) ⤳ ⟨q, inferInstance⟩ :=
    (PrimeSpectrum.le_iff_specializes _ _).mp (show (⊥ : Ideal B) ≤ q from bot_le)
  exact hsp.mem_open Algebra.isOpen_unramifiedLocus hq

/-- A domain `B` over `A` with `B_c` formally unramified for some `c ≠ 0` is unramified at its
generic point. -/
theorem isUnramifiedAt_bot_of_formallyUnramified_away [IsDomain B] (c : B) (hc : c ≠ 0)
    [Algebra.FormallyUnramified A (Localization.Away c)] :
    Algebra.IsUnramifiedAt A (⊥ : Ideal B) :=
  Algebra.basicOpen_subset_unramifiedLocus_iff.mpr ‹_›
    (show (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum B) ∈ PrimeSpectrum.basicOpen c from hc)

/-- An element `c` of `S` killing `Ω_{S/R}` kills `Ω_{T/R}` for every localization `T` of `S`:
`Ω_{T/R}` is spanned over `T` by the differentials of elements of `S`. -/
theorem smul_kaehler_localization_eq_zero {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T] (M : Submonoid S)
    [IsLocalization M T] (c : S) (hc : ∀ x : Ω[S⁄R], c • x = 0) (x : Ω[T⁄R]) :
    algebraMap S T c • x = 0 := by
  have hx : x ∈ Submodule.span T (Set.range <|
      KaehlerDifferential.map R R S T ∘ KaehlerDifferential.D R S) := by
    rw [KaehlerDifferential.span_range_map_derivation_of_isLocalization R S T M]
    exact Submodule.mem_top
  refine Submodule.span_induction (p := fun x _ ↦ algebraMap S T c • x = 0)
    ?_ (smul_zero _) (fun _ _ _ _ h₁ h₂ ↦ by rw [smul_add, h₁, h₂, add_zero])
    (fun a _ _ h ↦ by rw [smul_comm, h, smul_zero]) hx
  rintro _ ⟨y, rfl⟩
  rw [Function.comp_apply, algebraMap_smul, ← LinearMap.map_smul, hc, map_zero]

end Generic

/-! ### Base change followed by a principal localization -/

section BaseChangeLocalization

variable {R C R' C'' C' : Type u} [CommRing R] [CommRing C] [CommRing R'] [CommRing C'']
  [CommRing C'] [Algebra R C] [Algebra R R'] [Algebra R C''] [Algebra C C''] [Algebra R' C'']
  [IsScalarTower R R' C''] [IsScalarTower R C C''] [Algebra.IsPushout R R' C C'']
  [Algebra C'' C'] [Algebra R' C'] [IsScalarTower R' C'' C'] (g : C'') [IsLocalization.Away g C']

include g in
/-- `C' = (R' ⊗_R C)_g` is flat over `R'` when `C` is flat over `R`. -/
theorem flat_baseChange_away [Module.Flat R C] : Module.Flat R' C' :=
  have : Module.Flat R' C'' :=
    Module.Flat.isBaseChange (R := R) (S := R') (M := C) C''
      (Algebra.IsPushout.out (R := R) (S := R') (R' := C) (S' := C''))
  have : Module.Flat C'' C' := IsLocalization.flat C' (Submonoid.powers g)
  Module.Flat.trans R' C'' C'

include g in
/-- `C' = (R' ⊗_R C)_g` is quasi-finite over `R'` when `C` is quasi-finite over `R`. -/
theorem quasiFinite_baseChange_away [Algebra.QuasiFinite R C] : Algebra.QuasiFinite R' C' :=
  have : Algebra.QuasiFinite R' C'' :=
    (Algebra.QuasiFinite.iff_of_algEquiv (Algebra.IsPushout.equiv R R' C C'')).mp inferInstance
  Algebra.QuasiFinite.of_isLocalization (Submonoid.powers g)

include g in
/-- `C' = (R' ⊗_R C)_g` is of finite type over `R'` when `C` is of finite type over `R`. -/
theorem finiteType_baseChange_away [Algebra.FiniteType R C] : Algebra.FiniteType R' C' :=
  have h₁ : Algebra.FiniteType R' C'' :=
    Algebra.FiniteType.equiv inferInstance (Algebra.IsPushout.equiv R R' C C'')
  have : Algebra.FinitePresentation C'' C' := IsLocalization.Away.finitePresentation g
  Algebra.FiniteType.trans h₁ inferInstance

include g in
/-- `C' = (R' ⊗_R C)_g` is a relative global complete intersection over `R'` when `C` is one over
`R`. -/
theorem isRelativeGlobalCompleteIntersection_baseChange_away
    [Algebra.IsRelativeGlobalCompleteIntersection R C] :
    Algebra.IsRelativeGlobalCompleteIntersection R' C' :=
  have : Algebra.IsPushout R C R' C'' :=
    (inferInstance : Algebra.IsPushout R R' C C'').symm
  have : Algebra.IsRelativeGlobalCompleteIntersection R' C'' :=
    Algebra.IsRelativeGlobalCompleteIntersection.baseChange R C R' C''
  Algebra.IsRelativeGlobalCompleteIntersection.of_isLocalizationAway g

include g in
/-- An element `c` of `C` killing `Ω_{C/R}` kills `Ω_{C'/R'}` for `C' = (R' ⊗_R C)_g`. -/
theorem smul_kaehler_baseChange_away_eq_zero (c : C) (hc : ∀ x : Ω[C⁄R], c • x = 0)
    (x : Ω[C'⁄R']) : algebraMap C'' C' (algebraMap C C'' c) • x = 0 := by
  have h₁ : ∀ y : Ω[C''⁄R'], algebraMap C C'' c • y = 0 := by
    intro y
    refine (KaehlerDifferential.isBaseChange R R' C C'').inductionOn
      (motive := fun y ↦ algebraMap C C'' c • y = 0) y
      (fun m ↦ ?_) (fun s n hn ↦ by rw [smul_comm, hn, smul_zero])
      (fun _ _ h₁ h₂ ↦ by rw [smul_add, h₁, h₂, add_zero])
    change algebraMap C C'' c • KaehlerDifferential.map R R' C C'' m = 0
    rw [algebraMap_smul, ← LinearMap.map_smul, hc, map_zero]
  exact smul_kaehler_localization_eq_zero (Submonoid.powers g) _ h₁ x

include g in
/-- **Generic unramifiedness after base change and a principal localization.** If the domain `C`
is unramified over `R` at one prime, `C' = (R' ⊗_R C)_g` is a domain and `C → C'` is injective,
then `C'` is unramified over `R'` at its generic point. -/
theorem isUnramifiedAt_bot_baseChange_away [IsDomain C] [Algebra.FiniteType R C] [IsDomain C']
    (hinj : Function.Injective ((algebraMap C'' C').comp (algebraMap C C'')))
    (q : Ideal C) [q.IsPrime] [Algebra.IsUnramifiedAt R q] :
    Algebra.IsUnramifiedAt R' (⊥ : Ideal C') := by
  have := isUnramifiedAt_bot_of_isUnramifiedAt (A := R) q
  obtain ⟨c, hc0, hc⟩ := exists_smul_eq_zero_of_isUnramifiedAt_bot (A := R) (B := C)
  refine isUnramifiedAt_bot_of_smul_eq_zero (algebraMap C'' C' (algebraMap C C'' c)) ?_
    (smul_kaehler_baseChange_away_eq_zero g c hc)
  rw [← RingHom.comp_apply, ← map_zero ((algebraMap C'' C').comp (algebraMap C C''))]
  exact fun h ↦ hc0 (hinj h)

end BaseChangeLocalization

section MvPolynomial

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {R C : Type u} [CommRing R] [CommRing C] [Algebra R C] [IsNoetherianRing R]
  [IsNoetherianRing C] [Module.Flat R C] [Algebra.QuasiFinite R C] [IsDomain C]
  [Algebra.FiniteType R C] [Algebra.IsRelativeGlobalCompleteIntersection R C]
  (σ : Type) [Finite σ] (g : MvPolynomial σ C)

omit [IsNoetherianRing C] in
/-- **Niceness of a localized polynomial extension.** Let `R → C` be a flat quasi-finite
relative global complete intersection of Noetherian rings with `C` a domain, unramified at one
prime. For finitely many variables `σ` and `g ≠ 0` in `C[σ]`, the localization `C[σ]_g` over
`R[σ]` is again a domain, flat, quasi-finite, of finite type, a relative global complete
intersection and unramified at its generic point, and it is nice. -/
theorem isNiceChart_localization_mvPolynomial (hg : g ≠ 0) (q : Ideal C) [q.IsPrime]
    [Algebra.IsUnramifiedAt R q] :
    ∃ (_ : IsDomain (Localization.Away g)) (_ : Module.Flat (MvPolynomial σ R)
        (Localization.Away g)) (_ : Algebra.QuasiFinite (MvPolynomial σ R) (Localization.Away g))
      (_ : Algebra.FiniteType (MvPolynomial σ R) (Localization.Away g))
      (_ : Algebra.IsRelativeGlobalCompleteIntersection (MvPolynomial σ R)
        (Localization.Away g))
      (_ : IsNoetherianRing (Localization.Away g)),
      Algebra.IsUnramifiedAt (MvPolynomial σ R) (⊥ : Ideal (Localization.Away g)) ∧
        IsNiceChart (MvPolynomial σ R) (Localization.Away g) := by
  have hdom : IsDomain (Localization.Away g) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors _
      (powers_le_nonZeroDivisors_of_noZeroDivisors hg)
  have hflat := flat_baseChange_away (R := R) (C := C) (R' := MvPolynomial σ R)
    (C' := Localization.Away g) g
  have hqf := quasiFinite_baseChange_away (R := R) (C := C) (R' := MvPolynomial σ R)
    (C' := Localization.Away g) g
  have hft := finiteType_baseChange_away (R := R) (C := C) (R' := MvPolynomial σ R)
    (C' := Localization.Away g) g
  have hci := isRelativeGlobalCompleteIntersection_baseChange_away (R := R) (C := C)
    (R' := MvPolynomial σ R) (C' := Localization.Away g) g
  have hnoeth : IsNoetherianRing (Localization.Away g) :=
    Algebra.FiniteType.isNoetherianRing (MvPolynomial σ R) _
  have hinj : Function.Injective ((algebraMap (MvPolynomial σ C) (Localization.Away g)).comp
      (algebraMap C (MvPolynomial σ C))) :=
    (IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hg)).comp
      (MvPolynomial.C_injective σ C)
  have hur := isUnramifiedAt_bot_baseChange_away (R := R) (R' := MvPolynomial σ R)
    (C' := Localization.Away g) g hinj q
  exact ⟨hdom, hflat, hqf, hft, hci, hnoeth, hur, isNiceChart_of_isUnramifiedAt ⊥⟩

end MvPolynomial

end Stacks.TateMap

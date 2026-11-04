module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Away.Lemmas
public import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.ZariskisMainTheorem
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Etale.LiftIdempotentsAndModules
public import StacksFrontier.RingTheory.Henselian.Pair
public import StacksFrontier.RingTheory.Idempotents.Lifting
public import StacksFrontier.RingTheory.ZariskiPair

@[expose] public section

/-!
# Henselian pair criteria: passage to the integral closure

For a commutative ring `A`, an ideal `I` and a finite type `A`-algebra `B` whose reduction modulo
the extended ideal splits off a finite factor, the splitting can be transported to the integral
closure of `A` in `B`. This is the first step towards the characterizations of henselian pairs.

## Main results

* `exists_integralClosure_quotient_prod_and_awayMap_bijective`: passage to the integral closure
  for a finite type algebra whose reduction splits off a finite factor.

## Implementation notes

The extension of `I` to an algebra `B` is `I.map (algebraMap A B)`.

## References

* [Stacks: Tag 09XD](https://stacks.math.columbia.edu/tag/09XD)
* [Stacks: Tag 09XI](https://stacks.math.columbia.edu/tag/09XI)
* Raynaud, *Anneaux locaux henséliens*, Chapter XI
* Gabber, *Affine analog of the proper base change theorem*, Proposition 1
-/

open Polynomial

universe u v w x

-- The product decompositions below elaborate long chains of quotient and localization
-- instances, so this file needs more recursion depth than the default.
set_option maxRecDepth 4096

section

private lemma pow_mul_pow_eq_of_pow_succ_eq_pow
    {M : Type*} [Monoid M] (a : M) (n k : ℕ)
    (h : a ^ (n + 1) = a ^ n) : a ^ n * a ^ k = a ^ n := by
  rw [← pow_add]
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      a ^ (n + (k + 1)) = a ^ (n + k) * a := by rw [Nat.add_succ, pow_succ]
      _ = a ^ n * a := by rw [ih]
      _ = a ^ n := by rw [← pow_succ, h]

private lemma isIdempotentElem_pow_of_pow_succ_eq_pow
    {M : Type*} [Monoid M] (x : M) (n : ℕ)
    (h : x ^ (n + 1) = x ^ n) : IsIdempotentElem (x ^ n) :=
  isIdempotentElem_iff.mpr (pow_mul_pow_eq_of_pow_succ_eq_pow x n n h)

private lemma quotient_pow_succ_eq_of_mul_sub_mem
    {R : Type*} [CommRing R] (I : Ideal R) (x : R) (n : ℕ)
    (h : x ^ n * (x ^ 2 - x) ∈ I) :
    (Ideal.Quotient.mk I x) ^ (n + 2) = (Ideal.Quotient.mk I x) ^ (n + 1) := by
  have hz : (Ideal.Quotient.mk I x) ^ n *
      ((Ideal.Quotient.mk I x) ^ 2 - Ideal.Quotient.mk I x) = 0 := by
    rw [← map_pow, ← map_pow, ← map_sub, ← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr h
  exact sub_eq_zero.mp (by simpa only [pow_add, pow_one, pow_two, mul_sub, mul_assoc] using hz)

private lemma isIdempotentElem_quotient_pow_of_mul_sub_mem
    {R : Type*} [CommRing R] (I : Ideal R) (x : R) (n : ℕ)
    (h : x ^ n * (x ^ 2 - x) ∈ I) :
    IsIdempotentElem ((Ideal.Quotient.mk I x) ^ (n + 1)) :=
  isIdempotentElem_pow_of_pow_succ_eq_pow _ _ (quotient_pow_succ_eq_of_mul_sub_mem I x n h)

private lemma exists_pow_mul_mem_of_mem_map_of_awayMap_bijective
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (I : Ideal R) (r : R)
    (hbij : Function.Bijective (Localization.awayMap f r))
    {x : R} (hx : f x ∈ I.map f) :
    ∃ n : ℕ, r ^ n * x ∈ I := by
  let e : Localization.Away r ≃+* Localization.Away (f r) :=
    RingEquiv.ofBijective (Localization.awayMap f r) hbij
  have hy : Submonoid.powers r ≤ (Submonoid.powers (f r)).comap f := by
    rintro a ⟨n, rfl⟩
    exact ⟨n, by simp⟩
  have hcomm : e.toRingHom.comp (algebraMap R (Localization.Away r)) =
      (algebraMap S (Localization.Away (f r))).comp f := by
    show (IsLocalization.map (Localization.Away (f r)) f hy).comp
      (algebraMap R (Localization.Away r)) =
      (algebraMap S (Localization.Away (f r))).comp f
    exact IsLocalization.map_comp hy
  have hx' : e (algebraMap R (Localization.Away r) x) ∈
      Ideal.map e.toRingHom (I.map (algebraMap R (Localization.Away r))) := by
    show (e.toRingHom.comp (algebraMap R (Localization.Away r))) x ∈
      Ideal.map e.toRingHom (I.map (algebraMap R (Localization.Away r)))
    rw [Ideal.map_map, hcomm]
    show (algebraMap S (Localization.Away (f r))) (f x) ∈
      Ideal.map ((algebraMap S (Localization.Away (f r))).comp f) I
    rw [← Ideal.map_map]
    exact Ideal.mem_map_of_mem _ hx
  obtain ⟨y, hy, heq⟩ := (Ideal.mem_map_of_equiv e _).mp hx'
  have hx'' : algebraMap R (Localization.Away r) x ∈
      I.map (algebraMap R (Localization.Away r)) := by
    convert hy using 1
    exact e.injective heq.symm
  obtain ⟨m, hm, hmem⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff
      (Submonoid.powers r) (Localization.Away r) I x).mp hx''
  obtain ⟨n, rfl⟩ := hm
  exact ⟨n, hmem⟩

private lemma exists_idempotent_quotient_pow_of_awayMap_bijective
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (I : Ideal R) (r : R)
    (hbij : Function.Bijective (Localization.awayMap f r))
    (hr : f (r ^ 2 - r) ∈ I.map f) :
    ∃ n : ℕ, IsIdempotentElem ((Ideal.Quotient.mk I r) ^ n) := by
  obtain ⟨n, hn⟩ :=
    exists_pow_mul_mem_of_mem_map_of_awayMap_bijective f I r hbij hr
  exact ⟨n + 1, isIdempotentElem_quotient_pow_of_mul_sub_mem I r n hn⟩

private noncomputable def awayMapSurjectiveIdeal
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) : Ideal R := by
  letI : Algebra R S := f.toAlgebra
  let N : Submodule R S := (Algebra.linearMap R S).range
  exact ⨅ b : S, (Ideal.torsionOf R (S ⧸ N) (Submodule.Quotient.mk b)).radical

private lemma mem_awayMapSurjectiveIdeal_iff
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (r : R) :
    r ∈ awayMapSurjectiveIdeal f ↔
      Function.Surjective (Localization.awayMap f r) := by
  let : Algebra R S := f.toAlgebra
  let N : Submodule R S := (Algebra.linearMap R S).range
  rw [Localization.awayMap_surjective_iff]
  simp only [awayMapSurjectiveIdeal, Ideal.mem_iInf, Ideal.mem_radical_iff,
    Ideal.mem_torsionOf_iff]
  constructor
  · intro h b
    obtain ⟨n, hn⟩ := h b
    have hmem : f r ^ n * b ∈ N := by
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hn
      simpa only [Algebra.smul_def, map_pow, RingHom.algebraMap_toAlgebra] using hn
    obtain ⟨c, hc⟩ := hmem
    exact ⟨c, n, by simpa only [Algebra.linearMap_apply, RingHom.algebraMap_toAlgebra]
      using hc⟩
  · intro h b
    obtain ⟨c, n, hc⟩ := h b
    refine ⟨n, ?_⟩
    have hmem : f r ^ n * b ∈ N := ⟨c, hc⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    simpa only [Algebra.smul_def, map_pow, RingHom.algebraMap_toAlgebra] using hmem

private lemma ideal_map_eq_top_of_forall_maximal_notMem
    {R T : Type*} [CommRing R] [CommRing T] (f : R →+* T) (J : Ideal R)
    (h : ∀ m : Ideal T, m.IsMaximal → ∃ r ∈ J, f r ∉ m) :
    J.map f = ⊤ := by
  by_contra htop
  obtain ⟨m, hm, hJm⟩ := Ideal.ne_top_iff_exists_maximal.mp htop
  obtain ⟨r, hr, hrm⟩ := h m hm
  exact hrm (hJm (Ideal.mem_map_of_mem f hr))

private lemma exists_mem_ideal_map_eq_one_of_isIntegral
    {R T : Type*} [CommRing R] [CommRing T] (f : R →+* T)
    (hf : f.IsIntegral) (J : Ideal R) (hJ : J.map f = ⊤) :
    ∃ r ∈ J, f r = 1 := by
  have hmap : Ideal.map f (J ⊔ RingHom.ker f) = ⊤ := by
    apply top_unique
    rw [← hJ]
    exact Ideal.map_mono le_sup_left
  have htop : J ⊔ RingHom.ker f = ⊤ :=
    (Ideal.map_eq_top_iff_of_ker_le f le_sup_right hf).mp hmap
  obtain ⟨r, hr, k, hk, hsum⟩ :=
    (Submodule.mem_sup : (1 : R) ∈ J ⊔ RingHom.ker f ↔ _).mp
      ((Ideal.eq_top_iff_one _).mp htop)
  refine ⟨r, hr, ?_⟩
  have hk0 : f k = 0 := (RingHom.mem_ker).mp hk
  have : f (r + k) = 1 := by rw [hsum, map_one]
  simpa [map_add, hk0] using this

private lemma exists_awayMap_bijective_map_eq_one_of_isIntegral
    {R S C : Type*} [CommRing R] [CommRing S] [CommRing C]
    (f : R →+* S) (hf : Function.Injective f) (π : S →+* C)
    (hπf : (π.comp f).IsIntegral)
    (hpoint : ∀ m : Ideal C, m.IsMaximal →
      ∃ r : R, Function.Bijective (Localization.awayMap f r) ∧ π (f r) ∉ m) :
    ∃ r : R, π (f r) = 1 ∧ Function.Bijective (Localization.awayMap f r) := by
  let J := awayMapSurjectiveIdeal f
  have hmap : J.map (π.comp f) = ⊤ := by
    apply ideal_map_eq_top_of_forall_maximal_notMem
    intro m hm
    obtain ⟨r, hr, hrm⟩ := hpoint m hm
    exact ⟨r, (mem_awayMapSurjectiveIdeal_iff f r).mpr hr.2, hrm⟩
  obtain ⟨r, hrJ, hr1⟩ :=
    exists_mem_ideal_map_eq_one_of_isIntegral (π.comp f) hπf J hmap
  refine ⟨r, hr1, ?_⟩
  have hsurj : Function.Surjective (Localization.awayMap f r) :=
    (mem_awayMapSurjectiveIdeal_iff f r).mp hrJ
  have hinj : Function.Injective (Localization.awayMap f r) :=
    Localization.awayMap_injective_iff.mpr (fun a ha ↦
      ⟨0, by simpa using hf (by simpa using ha)⟩)
  exact ⟨hinj, hsurj⟩

private lemma exists_awayMap_bijective_map_prod_one_zero
    {R S C₁ C₂ : Type*} [CommRing R] [CommRing S]
    [CommRing C₁] [CommRing C₂]
    (f : R →+* S) (π : S →+* C₁ × C₂)
    (hπ : Function.Surjective π) (r : R)
    (hr₁ : (π (f r)).1 = 1)
    (hrbij : Function.Bijective (Localization.awayMap f r)) :
    ∃ t : R, π (f t) = (1, 0) ∧
      Function.Bijective (Localization.awayMap f t) := by
  obtain ⟨b, hb⟩ := hπ (1, 0)
  obtain ⟨c, m, hc⟩ := Localization.awayMap_surjective_iff.mp hrbij.2 b
  refine ⟨r * c, ?_, Localization.awayMap_bijective_of_dvd f
    ⟨c, rfl⟩ hrbij⟩
  apply Prod.ext
  · have hc₁ : (π (f c)).1 = 1 := by
      calc
        (π (f c)).1 = ((π (f r)) ^ m * π b).1 := by rw [hc, map_mul, map_pow]
        _ = 1 := by simp [hb, hr₁]
    simp [map_mul, hc₁, hr₁]
  · have hc₂ : (π (f c)).2 = 0 := by
      calc
        (π (f c)).2 = ((π (f r)) ^ m * π b).2 := by rw [hc, map_mul, map_pow]
        _ = 0 := by simp [hb]
    simp [map_mul, hc₂]

private lemma ker_eq_span_one_sub_of_idempotent
    {R C : Type*} [CommRing R] [CommRing C]
    (f : R →+* C) (e : R) (_ : IsIdempotentElem e)
    (hfe : f e = 1)
    (hker : ∀ x : R, f x = 0 → e * x = 0) :
    RingHom.ker f = Ideal.span {1 - e} := by
  apply le_antisymm
  · intro x hx
    have hzero : e * x = 0 := hker x ((RingHom.mem_ker).mp hx)
    have hrepr : x = (1 - e) * x := by
      calc
        x = (1 - e) * x + e * x := by ring
        _ = (1 - e) * x := by rw [hzero, add_zero]
    rw [hrepr]
    exact Ideal.mul_mem_right x _ (Ideal.subset_span (Set.mem_singleton _))
  · apply Ideal.span_le.mpr
    intro x hx
    rcases hx with rfl
    show f (1 - e) = 0
    simp [hfe]

private lemma exists_prod_equiv_of_idempotent
    {R : Type v} {C : Type w} {D : Type x} [CommRing R] [CommRing C] [CommRing D]
    (φ : R →+* C) (ψ : R →+* D) (e : R)
    (he : IsIdempotentElem e) (hφe : φ e = 1) (hψe : ψ e = 0)
    (hφsurj : Function.Surjective φ)
    (hker : RingHom.ker φ = Ideal.span {1 - e}) :
    ∃ (T : Type v) (_ : CommRing T) (α : R ≃+* C × T) (ψ₂ : T →+* D),
      (∀ x, (φ x, ψ x) = ((α x).1, ψ₂ (α x).2)) ∧ α e = (1, 0) := by
  let J₁ : Ideal R := Ideal.span {1 - e}
  let J₂ : Ideal R := Ideal.span {e}
  let q₁ : R →+* R ⧸ J₁ := Ideal.Quotient.mk J₁
  let q₂ : R →+* R ⧸ J₂ := Ideal.Quotient.mk J₂
  have hJ₁ : RingHom.ker φ = J₁ := hker
  let β : (R ⧸ J₁) ≃+* R ⧸ RingHom.ker φ :=
    Ideal.quotientEquiv J₁ (RingHom.ker φ) (RingEquiv.refl R) (by simpa using hJ₁)
  let γ : (R ⧸ J₁) ≃+* C := β.trans (φ.quotientKerEquivOfSurjective hφsurj)
  have hγ (x : R) : γ (q₁ x) = φ x := by
    simp [γ, β, q₁]
  have hbij : Function.Bijective (q₁.prod q₂) := by
    convert RingHom.prod_bijective_of_isIdempotentElem he.one_sub he
      (by ring) (by simp [sub_mul, he.eq]) using 1
  let δ : R ≃+* (R ⧸ J₁) × (R ⧸ J₂) := RingEquiv.ofBijective (q₁.prod q₂) hbij
  let α : R ≃+* C × (R ⧸ J₂) := δ.trans (RingEquiv.prodCongr γ (RingEquiv.refl _))
  have hα (x : R) : α x = (φ x, q₂ x) := by
    apply Prod.ext
    · show γ (q₁ x) = φ x
      exact hγ x
    · rfl
  have hψJ₂ : J₂ ≤ RingHom.ker ψ := by
    apply Ideal.span_le.mpr
    intro x hx
    rcases hx with rfl
    exact (RingHom.mem_ker).mpr hψe
  let ψ₂ : R ⧸ J₂ →+* D := Ideal.Quotient.lift J₂ ψ hψJ₂
  refine ⟨R ⧸ J₂, inferInstance, α, ψ₂, ?_, ?_⟩
  · intro x
    rw [hα]
    rfl
  · rw [hα]
    exact Prod.ext hφe
      (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton e)))

private lemma exists_prod_equiv_of_awayMap_bijective
    {R : Type v} {S : Type u} {C : Type w} {D : Type x}
    [CommRing R] [CommRing S] [CommRing C] [CommRing D]
    (f : R →+* S) (I : Ideal R) (π : S →+* C × D)
    (hπsurj : Function.Surjective π)
    (hkerπ : RingHom.ker π = I.map f)
    (r : R) (hrπ : π (f r) = (1, 0))
    (hbij : Function.Bijective (Localization.awayMap f r)) :
    ∃ (T : Type v) (_ : CommRing T) (α : (R ⧸ I) ≃+* C × T) (ψ₂ : T →+* D),
      (∀ a : R, π (f a) =
        ((α (Ideal.Quotient.mk I a)).1, ψ₂ (α (Ideal.Quotient.mk I a)).2)) ∧
      ∃ g : R, α (Ideal.Quotient.mk I g) = (1, 0) ∧
        Function.Bijective (Localization.awayMap f g) := by
  have hIker : I ≤ RingHom.ker (π.comp f) := by
    intro a ha
    have hfa : f a ∈ RingHom.ker π := hkerπ.symm ▸ Ideal.mem_map_of_mem f ha
    exact (RingHom.mem_ker).mpr ((RingHom.mem_ker).mp hfa)
  let ω : R ⧸ I →+* C × D := Ideal.Quotient.lift I (π.comp f) hIker
  let φ : R ⧸ I →+* C := (RingHom.fst C D).comp ω
  let ψ : R ⧸ I →+* D := (RingHom.snd C D).comp ω
  let q : R →+* R ⧸ I := Ideal.Quotient.mk I
  have hω (a : R) : ω (q a) = π (f a) := rfl
  have hφ (a : R) : φ (q a) = (π (f a)).1 := rfl
  have hψ (a : R) : ψ (q a) = (π (f a)).2 := rfl
  have hrmem : f (r ^ 2 - r) ∈ I.map f := by
    rw [← hkerπ, RingHom.mem_ker]
    simp [map_sub, map_pow, hrπ]
  obtain ⟨n, hn⟩ :=
    exists_pow_mul_mem_of_mem_map_of_awayMap_bijective f I r hbij hrmem
  let e : R ⧸ I := (q r) ^ (n + 1)
  have hstable := quotient_pow_succ_eq_of_mul_sub_mem I r n hn
  have he : IsIdempotentElem e := isIdempotentElem_quotient_pow_of_mul_sub_mem I r n hn
  have heφ : φ e = 1 := by
    show φ ((q r) ^ (n + 1)) = 1
    rw [map_pow]
    rw [hφ]
    simp [hrπ]
  have heψ : ψ e = 0 := by
    show ψ ((q r) ^ (n + 1)) = 0
    rw [map_pow]
    rw [hψ]
    simp [hrπ]
  have hφsurj : Function.Surjective φ := by
    intro c
    obtain ⟨s, hs⟩ := hπsurj (c, 0)
    obtain ⟨a, k, ha⟩ := Localization.awayMap_surjective_iff.mp hbij.2 s
    refine ⟨q a, ?_⟩
    rw [hφ, ha, map_mul, map_pow, hs]
    simp [hrπ]
  have hker : RingHom.ker φ = Ideal.span {1 - e} := by
    apply ker_eq_span_one_sub_of_idempotent φ e he heφ
    intro z hz
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hπzero : π (f (r ^ (n + 1) * a)) = 0 := by
      have ha0 : (π (f a)).1 = 0 := by
        change φ (q a) = 0 at hz
        rw [hφ] at hz
        exact hz
      apply Prod.ext
      · simp [map_mul, map_pow, hrπ, ha0]
      · simp [map_mul, map_pow, hrπ]
    have hmem : f (r ^ (n + 1) * a) ∈ I.map f := by
      rw [← hkerπ, RingHom.mem_ker]
      exact hπzero
    obtain ⟨k, hk⟩ :=
      exists_pow_mul_mem_of_mem_map_of_awayMap_bijective f I r hbij hmem
    have hk0 : (q r) ^ k * ((q r) ^ (n + 1) * q a) = 0 := by
      show q (r ^ k * (r ^ (n + 1) * a)) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hk
    show e * q a = 0
    calc
      e * q a = ((q r) ^ (n + 1) * (q r) ^ k) * q a := by
        rw [pow_mul_pow_eq_of_pow_succ_eq_pow (q r) (n + 1) k hstable]
      _ = 0 := by simpa [mul_comm, mul_left_comm, mul_assoc] using hk0
  obtain ⟨T, hT, α, ψ₂, hcompat, heα⟩ :=
    exists_prod_equiv_of_idempotent φ ψ e he heφ heψ hφsurj hker
  refine ⟨T, hT, α, ψ₂, ?_, ?_⟩
  · intro a
    rw [← hω a]
    exact hcompat (q a)
  · refine ⟨r ^ (n + 1), ?_, ?_⟩
    · exact heα
    · exact Localization.awayMap_bijective_of_dvd f
        ⟨r ^ n, by simp [pow_succ, mul_comm]⟩ hbij

/-- Finiteness of `A / I → C₁` gives finiteness of the composite `A → B → B / IB ≃ C₁ × C₂ → C₁`. -/
private lemma finite_fst_comp_mk_comp_algebraMap
    {A : Type u} [CommRing A] (I : Ideal A)
    {B : Type v} [CommRing B] [Algebra A B]
    {C₁ : Type w} [CommRing C₁] {C₂ : Type x} [CommRing C₂]
    (e : (B ⧸ I.map (algebraMap A B)) ≃+* C₁ × C₂)
    (hfinite : ((RingHom.fst C₁ C₂).comp (e.toRingHom.comp
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B)
        Ideal.le_comap_map))).Finite) :
    (((RingHom.fst C₁ C₂).comp
      (e.toRingHom.comp (Ideal.Quotient.mk (I.map (algebraMap A B))))).comp
        (algebraMap A B)).Finite := by
  have hhom : ((RingHom.fst C₁ C₂).comp
      (e.toRingHom.comp (Ideal.Quotient.mk (I.map (algebraMap A B))))).comp (algebraMap A B) =
      ((RingHom.fst C₁ C₂).comp (e.toRingHom.comp
        (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B)
          Ideal.le_comap_map))).comp (Ideal.Quotient.mk I) := rfl
  rw [hhom]
  exact hfinite.comp
    (RingHom.Finite.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective)

private lemma exists_integralClosure_awayMap_bijective_map_prod_one_zero_of_quasiFiniteAt
    {A : Type u} {B : Type v} {C : Type w} {D : Type x}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra.FiniteType A B]
    (π : B →+* C × D) (hπ : Function.Surjective π)
    (hfin : (((RingHom.fst C D).comp π).comp (algebraMap A B)).Finite)
    (hqf : ∀ (m : Ideal C) [m.IsPrime], m.IsMaximal →
      Algebra.QuasiFiniteAt A (m.comap ((RingHom.fst C D).comp π))) :
    ∃ r : integralClosure A B,
      π (r : B) = (1, 0) ∧
        Function.Bijective (Localization.awayMap
          (integralClosure A B).val.toRingHom r) := by
  let f : integralClosure A B →+* B := (integralClosure A B).val.toRingHom
  let π₁ : B →+* C := (RingHom.fst C D).comp π
  have hπ₁f : (π₁.comp f).IsIntegral := by
    apply RingHom.IsIntegral.tower_top (f := algebraMap A (integralClosure A B))
    convert hfin.to_isIntegral using 1
    ext a
    rfl
  have hpoint (m : Ideal C) (hm : m.IsMaximal) :
      ∃ r : integralClosure A B,
        Function.Bijective (Localization.awayMap f r) ∧ π₁ (f r) ∉ m := by
    let : m.IsPrime := hm.isPrime
    let q : Ideal B := m.comap π₁
    let : q.IsPrime := Ideal.comap_isPrime _ _
    have hq : Algebra.QuasiFiniteAt A q := hqf m hm
    let : Algebra.QuasiFiniteAt A q := hq
    obtain ⟨r, hrq, hrbij⟩ :=
      Algebra.ZariskisMainProperty.of_finiteType (R := A) (S := B) q
    exact ⟨r, hrbij, by simpa [q, π₁, f, Ideal.mem_comap] using hrq⟩
  obtain ⟨r, hr₁, hrbij⟩ :=
    exists_awayMap_bijective_map_eq_one_of_isIntegral f Subtype.val_injective
      π₁ hπ₁f hpoint
  exact exists_awayMap_bijective_map_prod_one_zero f π hπ r hr₁ hrbij

private theorem exists_integralClosure_quotient_prod_and_awayMap_bijective_of_quasiFiniteAt
    {A : Type u} [CommRing A] (I : Ideal A)
    {B : Type v} [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    {C₁ : Type w} [CommRing C₁] {C₂ : Type x} [CommRing C₂]
    (e : (B ⧸ I.map (algebraMap A B)) ≃+* C₁ × C₂)
    (hfinite : ((RingHom.fst C₁ C₂).comp (e.toRingHom.comp
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B)
        Ideal.le_comap_map))).Finite)
    (hqf : ∀ (m : Ideal C₁) [m.IsPrime], m.IsMaximal →
      Algebra.QuasiFiniteAt A
        (m.comap ((RingHom.fst C₁ C₂).comp
          (e.toRingHom.comp (Ideal.Quotient.mk (I.map (algebraMap A B))))))) :
    ∃ (C₂' : Type v) (_ : CommRing C₂')
      (e' : ((integralClosure A B) ⧸
        I.map (algebraMap A (integralClosure A B))) ≃+* C₁ × C₂')
      (f₂ : C₂' →+* C₂),
      (∀ z,
        e (Ideal.quotientMap (I.map (algebraMap A B))
          ((integralClosure A B).val : integralClosure A B →+* B) (by
            rw [Ideal.map_le_iff_le_comap]
            intro a ha
            simpa using Ideal.mem_map_of_mem (algebraMap A B) ha) z) =
          ((e' z).1, f₂ (e' z).2)) ∧
      ∃ g : integralClosure A B,
        e' (Ideal.Quotient.mk (I.map (algebraMap A (integralClosure A B))) g) = (1, 0) ∧
          Function.Bijective (Localization.awayMapₐ (integralClosure A B).val g) := by
  let R := integralClosure A B
  let f : R →+* B := (integralClosure A B).val.toRingHom
  let J : Ideal B := I.map (algebraMap A B)
  let K : Ideal R := I.map (algebraMap A R)
  let π : B →+* C₁ × C₂ := e.toRingHom.comp (Ideal.Quotient.mk J)
  have hπsurj : Function.Surjective π := e.surjective.comp Ideal.Quotient.mk_surjective
  have hfinπ := finite_fst_comp_mk_comp_algebraMap I e hfinite
  have hkerπ : RingHom.ker π = K.map f := by
    have hkerπJ : RingHom.ker π = J :=
      (RingHom.ker_comp_of_injective (Ideal.Quotient.mk J) e.injective).trans Ideal.mk_ker
    rw [hkerπJ]
    show I.map (algebraMap A B) =
      (I.map (algebraMap A R)).map f
    rw [Ideal.map_map]
    rfl
  have hqfπ : ∀ (m : Ideal C₁) [m.IsPrime], m.IsMaximal →
      Algebra.QuasiFiniteAt A (m.comap ((RingHom.fst C₁ C₂).comp π)) := by
    intro m _ hm
    exact hqf m hm
  obtain ⟨r, hrπ, hrbij⟩ :=
    exists_integralClosure_awayMap_bijective_map_prod_one_zero_of_quasiFiniteAt
      π hπsurj hfinπ hqfπ
  obtain ⟨T, hT, α, ψ₂, hcompat, g, hg, hgbij⟩ :=
    exists_prod_equiv_of_awayMap_bijective f K π hπsurj hkerπ r hrπ hrbij
  refine ⟨T, hT, α, ψ₂, ?_, g, hg, ?_⟩
  · intro z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact hcompat a
  · exact hgbij

private theorem quasiFiniteAt_comap_fst_of_finite_component
    {A : Type u} {B : Type v} {C : Type w} {D : Type x}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra.FiniteType A B]
    (π : B →+* C × D) (hπsurj : Function.Surjective π)
    (hfin : (((RingHom.fst C D).comp π).comp (algebraMap A B)).Finite)
    (m : Ideal C) [m.IsPrime]
    (hker : RingHom.ker π ≤
      (m.comap (((RingHom.fst C D).comp π).comp (algebraMap A B))).map
        (algebraMap A B)) :
    Algebra.QuasiFiniteAt A (m.comap ((RingHom.fst C D).comp π)) := by
  let f : B →+* C := (RingHom.fst C D).comp π
  let a : A →+* C := f.comp (algebraMap A B)
  let : Algebra A C := a.toAlgebra
  have : Module.Finite A C := hfin
  let : Algebra.QuasiFiniteAt A m := inferInstance
  let p : Ideal A := m.under A
  have : p.IsPrime := inferInstance
  have : m.LiesOver p := ⟨rfl⟩
  obtain ⟨s, hs, huniq⟩ := Ideal.exists_not_mem_forall_mem_of_ne_of_liesOver (R := A) p m
  have hf : Function.Surjective f := by
    intro c
    obtain ⟨b, hb⟩ := hπsurj (c, 0)
    exact ⟨b, congrArg Prod.fst hb⟩
  obtain ⟨b, hb⟩ := hπsurj (s, 0)
  have hb1 : f b = s := congrArg Prod.fst hb
  let q : Ideal B := m.comap f
  have : q.IsPrime := inferInstance
  have hqb : b ∉ q := by simpa [q, Ideal.mem_comap, hb1] using hs
  have hqp : q.under A = p := by
    ext t
    show f (algebraMap A B t) ∈ m ↔ algebraMap A C t ∈ m
    rfl
  have : q.LiesOver p := ⟨hqp.symm⟩
  have hunique (q' : Ideal B) [q'.IsPrime] (hq'p : q'.LiesOver p)
      (hbq' : b ∉ q') : q' = q := by
    let : q'.LiesOver p := hq'p
    have hkerq' : RingHom.ker π ≤ q' := by
      intro x hx
      have hpmap : p.map (algebraMap A B) ≤ q' := by
        rw [Ideal.map_le_iff_le_comap]
        exact le_of_eq (q'.over_def p)
      exact hpmap (hker hx)
    have hkerfq' : RingHom.ker f ≤ q' := by
      intro x hx
      have hprod : π (x * b) = 0 := by
        apply Prod.ext
        · have hx1 : (π x).1 = 0 := (RingHom.mem_ker).mp hx
          simp [map_mul, hb, hx1]
        · simp [hb]
      have hxb : x * b ∈ q' := hkerq' ((RingHom.mem_ker).mpr hprod)
      exact (‹q'.IsPrime›.mul_mem_iff_mem_or_mem.mp hxb).resolve_right hbq'
    have : (q'.map f).IsPrime := Ideal.map_isPrime_of_surjective hf hkerfq'
    have hcomap : (q'.map f).comap f = q' :=
      (Ideal.comap_map_of_surjective f hf q').trans
        (sup_of_le_left (by simpa [RingHom.ker_eq_comap_bot] using hkerfq'))
    have hqover : (q'.map f).LiesOver p := by
      constructor
      show p = ((q'.map f).comap f).comap (algebraMap A B)
      rw [hcomap]
      exact q'.over_def p
    have hsnot : s ∉ q'.map f := by
      intro hs'
      have : b ∈ (q'.map f).comap f := by simpa [Ideal.mem_comap, hb1] using hs'
      exact hbq' (hcomap ▸ this)
    have hmq : q'.map f = m := by
      by_contra hne
      exact hsnot (huniq _ inferInstance hne inferInstance)
    rw [← hcomap, hmq]
  let Q : PrimeSpectrum B := ⟨q, inferInstance⟩
  have hopen : IsOpen (X := PrimeSpectrum.comap (algebraMap A B) ⁻¹'
      {Q.comap (algebraMap A B)}) {⟨Q, rfl⟩} := by
    have hset : ({⟨Q, rfl⟩} : Set (PrimeSpectrum.comap (algebraMap A B) ⁻¹'
        {Q.comap (algebraMap A B)})) =
        Subtype.val ⁻¹' (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum B)) := by
      ext y
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · intro hy
        rw [show y.1 = Q from congrArg Subtype.val hy]
        exact hqb
      · intro hby
        have hp' : y.1.asIdeal.under A = p := by
          have heq := congrArg PrimeSpectrum.asIdeal y.2
          exact heq.trans hqp
        have : y.1.asIdeal.LiesOver p := ⟨hp'.symm⟩
        have hqeq : y.1.asIdeal = q := hunique y.1.asIdeal ‹_› (by simpa using hby)
        exact Subtype.ext (PrimeSpectrum.ext hqeq)
    rw [hset]
    exact (PrimeSpectrum.basicOpen b).isOpen.preimage continuous_subtype_val
  exact Algebra.QuasiFiniteAt.of_isOpen_singleton_fiber (R := A) Q hopen

/-- Let `A → B` be a finite type map, let `I ⊆ A`, and suppose that `B / IB` is a product
`C₁ × C₂` for which the canonical map `A / I → C₁` is finite. If `B'` is the
integral closure of `A` in `B`, then `B' / IB'` decomposes as `C₁ × C₂'` compatibly
with `B / IB`. Moreover, there is a `g ∈ B'` whose class is `(1, 0)` and for which the
canonical map `B'_g → B_g` is an isomorphism. -/
@[stacks 09XH]
theorem exists_integralClosure_quotient_prod_and_awayMap_bijective
    {A : Type u} [CommRing A] (I : Ideal A)
    {B : Type v} [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    {C₁ : Type w} [CommRing C₁] {C₂ : Type x} [CommRing C₂]
    (e : (B ⧸ I.map (algebraMap A B)) ≃+* C₁ × C₂)
    (hfinite : ((RingHom.fst C₁ C₂).comp (e.toRingHom.comp
      (Ideal.quotientMap (I.map (algebraMap A B)) (algebraMap A B)
        Ideal.le_comap_map))).Finite) :
    ∃ (C₂' : Type v) (_ : CommRing C₂')
      (e' : ((integralClosure A B) ⧸
        I.map (algebraMap A (integralClosure A B))) ≃+* C₁ × C₂')
      (f₂ : C₂' →+* C₂),
      (∀ z,
        e (Ideal.quotientMap (I.map (algebraMap A B))
          ((integralClosure A B).val : integralClosure A B →+* B) (by
            rw [Ideal.map_le_iff_le_comap]
            intro a ha
            simpa using Ideal.mem_map_of_mem (algebraMap A B) ha) z) =
          ((e' z).1, f₂ (e' z).2)) ∧
      ∃ g : integralClosure A B,
        e' (Ideal.Quotient.mk (I.map (algebraMap A (integralClosure A B))) g) = (1, 0) ∧
          Function.Bijective (Localization.awayMapₐ (integralClosure A B).val g) := by
  let J : Ideal B := I.map (algebraMap A B)
  let π : B →+* C₁ × C₂ := e.toRingHom.comp (Ideal.Quotient.mk J)
  have hπsurj : Function.Surjective π := e.surjective.comp Ideal.Quotient.mk_surjective
  have hfinπ := finite_fst_comp_mk_comp_algebraMap I e hfinite
  have hkerπ : RingHom.ker π = J :=
    (RingHom.ker_comp_of_injective (Ideal.Quotient.mk J) e.injective).trans Ideal.mk_ker
  have hqf : ∀ (m : Ideal C₁) [m.IsPrime], m.IsMaximal →
      Algebra.QuasiFiniteAt A
        (m.comap ((RingHom.fst C₁ C₂).comp
          (e.toRingHom.comp (Ideal.Quotient.mk (I.map (algebraMap A B)))))) := by
    intro m _ _
    have hker : RingHom.ker π ≤
        (m.comap (((RingHom.fst C₁ C₂).comp π).comp (algebraMap A B))).map
          (algebraMap A B) := by
      rw [hkerπ]
      apply Ideal.map_mono
      intro a ha
      show ((RingHom.fst C₁ C₂).comp π) (algebraMap A B a) ∈ m
      have hja : algebraMap A B a ∈ J := Ideal.mem_map_of_mem _ ha
      have hzero : π (algebraMap A B a) = 0 := by
        apply (RingHom.mem_ker).mp
        rw [hkerπ]
        exact hja
      show (π (algebraMap A B a)).1 ∈ m
      rw [congrArg Prod.fst hzero]
      exact m.zero_mem
    exact quasiFiniteAt_comap_fst_of_finite_component π hπsurj hfinπ m hker
  exact exists_integralClosure_quotient_prod_and_awayMap_bijective_of_quasiFiniteAt
    I e hfinite hqf

end

end

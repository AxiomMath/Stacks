module

public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.RingHom.Flat
public import StacksFrontier.RingTheory.IntegrallyClosed.ProductOfDomains

/-!
# Normality of an equalizer of two flat ring maps out of a normal ring

Let `ρ, σ : P →+* Q` be two flat ring maps out of a normal ring `P` with finitely many minimal
primes. If their equalizer `E = {p | ρ p = σ p}` has finitely many minimal primes, then `E` is a
normal ring.

This is the ring-theoretic content of the statement that the global functions of a normal
algebraic space form a normal ring: for an affine étale chart `U` of the space whose kernel pair
`V = U ×_X U` is affine, the global functions are the equalizer of the two restriction maps
`Γ(U, 𝒪) ⇉ Γ(V, 𝒪)`, which are flat.

## Main results

* `IsNormalRing.exists_isIdempotentElem_mul_eq_zero_add_mem_nonZeroDivisors`: in a normal ring
  with finitely many minimal primes every element `s` has an idempotent `e` with `e * s = 0` and
  `s + e` a non-zero-divisor; `e` cuts out the factors on which `s` vanishes.
* `RingHom.mem_nonZeroDivisors_of_flat`: a flat ring map carries non-zero-divisors to
  non-zero-divisors.
* `IsNormalRing.eqLocus_of_flat`: the equalizer of two flat ring maps out of a normal ring is a
  normal ring.

## Implementation notes

The argument is elementwise. A non-zero-divisor `s` of `E` is a non-zero-divisor of `P`: the
idempotent `e` attached to `s` in `P` has `ρ e` and `σ e` generating the same ideal of `Q`,
namely the annihilator of `ρ s = σ s` (flatness is what controls that annihilator), so `ρ e = σ e`
and `e ∈ E`; then `e * s = 0` forces `e = 0`. A fraction `a / s` of `E` integral over `E` is then
a fraction of `P` integral over `P`, hence `a = s * b` in `P` by Stacks 034M; flatness makes
`ρ s` a non-zero-divisor of `Q`, so `ρ b = σ b`, and `b ∈ E`. Stacks 030C converts integral
closedness of the reduced ring `E` into normality.

## References

* [Stacks Project, Tag 030C](https://stacks.math.columbia.edu/tag/030C)
* [Stacks Project, Tag 034M](https://stacks.math.columbia.edu/tag/034M)
-/

@[expose] public section

open scoped nonZeroDivisors Polynomial

universe u

/-- **An idempotent cutting out the zero factors of an element.** In a normal ring `P` with
finitely many minimal primes every element `s` has an idempotent `e` with `e * s = 0` and `s + e`
a non-zero-divisor. By Stacks 030C `P` is a finite product of domains, and `e` is `1` on the
factors on which `s` vanishes and `0` on the others. -/
theorem IsNormalRing.exists_isIdempotentElem_mul_eq_zero_add_mem_nonZeroDivisors
    {P : Type u} [CommRing P] (hP : IsNormalRing P) (hmin : (minimalPrimes P).Finite) (s : P) :
    ∃ e : P, IsIdempotentElem e ∧ e * s = 0 ∧ s + e ∈ P⁰ := by
  classical
  have := hP.isReduced
  obtain ⟨n, A, _, hdom, -, ⟨φ⟩⟩ :=
    ((isIntegrallyClosed_tfae_of_finite_minimalPrimes hmin).out 1 3).mp hP
  let t : ∀ i, A i := φ s
  let ε : ∀ i, A i := fun i => if t i = 0 then 1 else 0
  refine ⟨φ.symm ε, ?_, ?_, ?_⟩
  · apply φ.injective
    rw [map_mul, RingEquiv.apply_symm_apply]
    funext i
    simp only [Pi.mul_apply, ε]
    split_ifs <;> simp
  · apply φ.injective
    rw [map_mul, RingEquiv.apply_symm_apply, map_zero]
    funext i
    simp only [Pi.mul_apply, Pi.zero_apply, ε]
    split_ifs with h
    · exact (one_mul _).trans h
    · exact zero_mul _
  · rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    apply φ.injective
    rw [map_zero]
    funext i
    have hi := congrFun (congrArg φ hy) i
    rw [map_mul, map_add, RingEquiv.apply_symm_apply, map_zero] at hi
    simp only [Pi.mul_apply, Pi.add_apply, Pi.zero_apply, ε] at hi
    have := hdom i
    have hne : t i + (if t i = 0 then 1 else 0) ≠ 0 := by
      split_ifs with h
      · simp [h]
      · simpa using h
    exact (mul_eq_zero.mp hi).resolve_right hne

/-- **A flat ring map carries non-zero-divisors to non-zero-divisors.** -/
theorem RingHom.mem_nonZeroDivisors_of_flat {P Q : Type*} [CommRing P] [CommRing Q]
    {ρ : P →+* Q} (hρ : ρ.Flat) {r : P} (hr : r ∈ P⁰) : ρ r ∈ Q⁰ := by
  let := ρ.toAlgebra
  have : Module.Flat P Q := hρ
  have hreg : IsSMulRegular Q r := Module.Flat.isSMulRegular_of_nonZeroDivisors hr
  rw [mem_nonZeroDivisors_iff_right]
  intro q hq
  apply hreg
  change ρ r * q = ρ r * 0
  rw [mul_zero, mul_comm, hq]

/-- Two idempotents annihilating `x` with `x + e` a non-zero-divisor for each are equal: each is
the generator of the annihilator of `x`. -/
private theorem eq_of_isIdempotentElem_of_mul_eq_zero {Q : Type*} [CommRing Q] {x e₁ e₂ : Q}
    (h₁ : IsIdempotentElem e₁) (h₂ : IsIdempotentElem e₂) (hx₁ : e₁ * x = 0) (hx₂ : e₂ * x = 0)
    (hr₁ : x + e₁ ∈ Q⁰) (hr₂ : x + e₂ ∈ Q⁰) : e₁ = e₂ := by
  have key : ∀ {a b : Q}, IsIdempotentElem a → b * x = 0 → x + a ∈ Q⁰ → b = b * a := by
    intro a b ha hb hr
    have h0 : (b * (1 - a)) * (x + a) = 0 := by
      have : (b * (1 - a)) * (x + a) = (b * x) * (1 - a) + b * (a - a * a) := by ring
      rw [this, hb, ha.eq, sub_self]
      ring
    have := (mem_nonZeroDivisors_iff_right.mp hr) _ h0
    rw [mul_sub, mul_one, sub_eq_zero] at this
    exact this
  rw [key h₂ hx₁ hr₂, mul_comm]
  exact (key h₁ hx₂ hr₁).symm

/-- **The equalizer of two flat ring maps out of a normal ring is normal.** Let `ρ, σ : P →+* Q`
be flat ring maps, `P` a normal ring with finitely many minimal primes, and suppose the equalizer
`E = RingHom.eqLocus ρ σ` has finitely many minimal primes. Then `E` is a normal ring. -/
theorem IsNormalRing.eqLocus_of_flat {P Q : Type u} [CommRing P] [CommRing Q]
    (ρ σ : P →+* Q) (hρ : ρ.Flat) (hσ : σ.Flat) (hP : IsNormalRing P)
    (hPmin : (minimalPrimes P).Finite) (hEmin : (minimalPrimes (ρ.eqLocus σ)).Finite) :
    IsNormalRing (ρ.eqLocus σ) := by
  classical
  set E := ρ.eqLocus σ with hEdef
  have hPred := hP.isReduced
  have hEred : IsReduced E := isReduced_of_injective E.subtype Subtype.val_injective
  -- a non-zero-divisor of `E` is one of `P`, and its image is one of `Q`
  have hnzd : ∀ s : E, s ∈ E⁰ → (s : P) ∈ P⁰ ∧ ρ s ∈ Q⁰ := by
    intro s hs
    obtain ⟨e, he, hes, hse⟩ :=
      hP.exists_isIdempotentElem_mul_eq_zero_add_mem_nonZeroDivisors hPmin (s : P)
    have hsE : ρ (s : P) = σ (s : P) := s.2
    have hρe : ρ e = σ e := by
      refine eq_of_isIdempotentElem_of_mul_eq_zero (x := ρ s) (he.map ρ) (he.map σ) ?_ ?_
        ?_ ?_
      · rw [← map_mul, hes, map_zero]
      · rw [hsE, ← map_mul, hes, map_zero]
      · rw [← map_add]; exact RingHom.mem_nonZeroDivisors_of_flat hρ hse
      · rw [hsE, ← map_add]; exact RingHom.mem_nonZeroDivisors_of_flat hσ hse
    have he0 : (⟨e, hρe⟩ : E) = 0 :=
      (mem_nonZeroDivisors_iff_right.mp hs) _ (Subtype.ext (by simpa using hes))
    have he0' : e = 0 := congrArg Subtype.val he0
    rw [he0', add_zero] at hse
    refine ⟨hse, ?_⟩
    exact RingHom.mem_nonZeroDivisors_of_flat hρ hse
  have hle : E⁰ ≤ P⁰.comap E.subtype := fun s hs => (hnzd s hs).1
  have hIC : IsIntegrallyClosed E := by
    rw [isIntegrallyClosed_iff (FractionRing E)]
    intro x hx
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective E⁰ x
    let f : FractionRing E →+* FractionRing P :=
      IsLocalization.map (FractionRing P) E.subtype hle
    have hf : f.comp (algebraMap E (FractionRing E)) =
        (algebraMap P (FractionRing P)).comp E.subtype :=
      IsLocalization.map_comp hle
    have hint : IsIntegral P (f (IsLocalization.mk' (FractionRing E) a s)) := by
      obtain ⟨p, hpm, hp⟩ := hx
      refine ⟨p.map E.subtype, hpm.map _, ?_⟩
      rw [Polynomial.eval₂_map, ← hf, ← Polynomial.hom_eval₂, hp, map_zero]
    obtain ⟨b, hb⟩ := (isIntegrallyClosed_iff (FractionRing P)).mp hP.isIntegrallyClosed hint
    have hfx : f (IsLocalization.mk' (FractionRing E) a s) =
        IsLocalization.mk' (FractionRing P) (a : P) ⟨(s : P), hle s.2⟩ :=
      IsLocalization.map_mk' _ _ _
    rw [hfx, IsLocalization.eq_mk'_iff_mul_eq] at hb
    have hbs : b * (s : P) = a := IsFractionRing.injective P (FractionRing P) (by rwa [map_mul])
    have hbE : ρ b = σ b := by
      have h1 : ρ b * ρ s = σ b * ρ s := by
        rw [← map_mul, hbs, show ρ (s : P) = σ (s : P) from s.1.2, ← map_mul, hbs]
        exact a.2
      have h2 : (ρ b - σ b) * ρ s = 0 := by rw [sub_mul, h1, sub_self]
      exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff_right.mp (hnzd s.1 s.2).2) _ h2)
    refine ⟨⟨b, hbE⟩, ?_⟩
    rw [IsLocalization.eq_mk'_iff_mul_eq, ← map_mul]
    congr 1
    exact Subtype.ext hbs
  have h := ((isIntegrallyClosed_tfae_of_finite_minimalPrimes hEmin).out 1 2).mpr hIC
  exact isNormalRing_iff.mpr h

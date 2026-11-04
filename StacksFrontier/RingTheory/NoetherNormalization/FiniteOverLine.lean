module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Algebras finite over a polynomial ring in one variable meet every hypersurface `h = 0`

Let `k` be a field and `R` a `k`-algebra which is finite over `k[t]` for an element `t ∈ R`, that
is `k[X] → R`, `X ↦ t`, is finite. If `P ⊂ R` is a prime with `dim R/P ≥ 1`, then `k[X] → R/P` is
injective: its kernel is a prime of `k[X]`, and if it were a nonzero prime it would be maximal,
`R/P` would be a domain integral over the field `k[X]/ker`, hence a field, of dimension `0`. So
`R/P` is integral over `k[X]` and lying over provides, for every monic `h ∈ k[X]` of positive
degree, a prime of `R` containing `P` and `h(t)`.

Geometrically: every irreducible component of positive dimension of `Spec R` maps onto `𝔸¹_k`,
so it meets the zero locus of `h(t)`. This is the reason a finite relative Noether normalization
`t : U → 𝔸¹_W` of a family of curves gives divisors `t⁻¹(V(h))` meeting every component of every
geometric fibre, as used for the Gysin map of `R² g_!` in the reduction of the weight bound of
Weil II ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main results

* `Polynomial.ker_aeval_quotient_eq_bot_of_finite`: `k[X] → R/P` is injective.
* `Polynomial.exists_isPrime_le_aeval_mem_of_finite`: a prime above `P` contains `h(t)`.
-/

@[expose] public section

open Polynomial

namespace Polynomial

variable {k R : Type*} [Field k] [CommRing R] [Algebra k R] {t : R}

/-- If `k[X] → R`, `X ↦ t`, is finite, then `k[X] → R/P` is integral. -/
private theorem isIntegral_quotient_mk_comp_aeval (hfin : (aeval t : k[X] →ₐ[k] R).Finite)
    (P : Ideal R) :
    ((Ideal.Quotient.mk P).comp (aeval t : k[X] →ₐ[k] R).toRingHom).IsIntegral :=
  (RingHom.Finite.comp (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective)
    hfin).to_isIntegral

/-- If `k[X] → R`, `X ↦ t`, is finite and `P` is a prime of `R` with `dim R/P ≥ 1`, the induced
map `k[X] → R/P` is injective: a nonzero prime kernel would be maximal and make `R/P` a field. -/
theorem ker_aeval_quotient_eq_bot_of_finite (hfin : (aeval t : k[X] →ₐ[k] R).Finite)
    (P : Ideal R) [P.IsPrime] (hdim : 1 ≤ ringKrullDim (R ⧸ P)) :
    RingHom.ker ((Ideal.Quotient.mk P).comp (aeval t : k[X] →ₐ[k] R).toRingHom) = ⊥ := by
  set φ : k[X] →+* R ⧸ P := (Ideal.Quotient.mk P).comp (aeval t : k[X] →ₐ[k] R).toRingHom
  by_contra hne
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hmax : (RingHom.ker φ).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
  -- `R/P` is integral over the field `k[X]/ker φ`
  let ψ : k[X] ⧸ RingHom.ker φ →+* R ⧸ P := RingHom.kerLift φ
  have hψint : ψ.IsIntegral := by
    intro x
    obtain ⟨p, hp, hpx⟩ := isIntegral_quotient_mk_comp_aeval hfin P x
    refine ⟨p.map (Ideal.Quotient.mk (RingHom.ker φ)), hp.map _, ?_⟩
    rwa [eval₂_map, show ψ.comp (Ideal.Quotient.mk _) = φ from
      RingHom.ext fun _ => RingHom.kerLift_mk φ _]
  let := ψ.toAlgebra
  have : Algebra.IsIntegral (k[X] ⧸ RingHom.ker φ) (R ⧸ P) := ⟨hψint⟩
  have hfield : IsField (R ⧸ P) :=
    isField_of_isIntegral_of_isField' (R := k[X] ⧸ RingHom.ker φ) (S := R ⧸ P)
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient (RingHom.ker φ)).1 hmax)
  rw [ringKrullDim_eq_zero_of_isField hfield] at hdim
  exact absurd hdim (by decide)

/-- **A finite algebra over `k[t]` meets every hypersurface `h(t) = 0` above every prime of
positive coheight**: if `k[X] → R`, `X ↦ t`, is finite, `P` is a prime of `R` with
`dim R/P ≥ 1` and `h ∈ k[X]` is monic of positive degree, there is a prime `Q ⊇ P` of `R`
containing `h(t)`. -/
theorem exists_isPrime_le_aeval_mem_of_finite (hfin : (aeval t : k[X] →ₐ[k] R).Finite)
    (P : Ideal R) [P.IsPrime] (hdim : 1 ≤ ringKrullDim (R ⧸ P)) {h : k[X]} (_hh : h.Monic)
    (hdeg : 0 < h.natDegree) : ∃ Q : Ideal R, Q.IsPrime ∧ P ≤ Q ∧ aeval t h ∈ Q := by
  set φ : k[X] →+* R ⧸ P := (Ideal.Quotient.mk P).comp (aeval t : k[X] →ₐ[k] R).toRingHom
  -- a maximal ideal of `k[X]` containing `h`
  have hspan : Ideal.span {h} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact fun hu => absurd (natDegree_eq_zero_of_isUnit hu) hdeg.ne'
  obtain ⟨m, hm, hhm⟩ := Ideal.exists_le_maximal _ hspan
  let := φ.toAlgebra
  have : Algebra.IsIntegral k[X] (R ⧸ P) := ⟨isIntegral_quotient_mk_comp_aeval hfin P⟩
  obtain ⟨Q', -, hQ', hQ'm⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := R ⧸ P) m ⊥
    (by
      rw [Ideal.comap_bot_of_injective]
      · exact bot_le
      · exact (RingHom.injective_iff_ker_eq_bot _).2
          (ker_aeval_quotient_eq_bot_of_finite hfin P hdim))
  refine ⟨Q'.comap (Ideal.Quotient.mk P), Ideal.comap_isPrime _ _, fun x hx => ?_, ?_⟩
  · rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx]
    exact Q'.zero_mem
  · rw [Ideal.mem_comap]
    exact (hQ'm ▸ hhm (Ideal.mem_span_singleton_self h) : h ∈ Q'.comap (algebraMap k[X] (R ⧸ P)))

end Polynomial

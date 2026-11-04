module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Spectrum.Prime.Polynomial
public import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

/-!
# The image in `Spec R` of a standard open of `Spec R[x]`

Let `R` be a ring. The structure map `Spec(R[x]) → Spec(R)`, induced by the inclusion
`C : R → R[x]`, is open, and the image of a standard open is a quasi-compact open. Both claims come
from one computation: a prime `p ⊂ R` lies in the image of `D(f)`, `f ∈ R[x]`, if and only if the
fibre `R[x]_f ⊗_R κ(p) = κ(p)[x]_f̄` is nonzero, i.e. if and only if `f` does not map to `0` in
`κ(p)[x]`, i.e. if and only if some coefficient of `f` avoids `p`. So for `f = a_d x^d + … + a_0`
the image of `D(f)` is `D(a_d) ∪ … ∪ D(a_0)`: a *finite* union of standard opens, hence a
quasi-compact open, and hence — the standard opens being a basis of `Spec(R[x])` — the map is open.

## Main results

* `Polynomial.image_comap_C_basicOpen_eq_biUnion_basicOpen_coeffs`, Stacks 00FB (second part): the
  image of the standard open `D(f) ⊆ Spec(R[x])` in `Spec(R)` is the union of the standard opens
  `D(a)` of the coefficients `a` of `f`.

## Implementation notes

The first claim of the source, that `Spec(R[x]) → Spec(R)` is open, is already in Mathlib as
`Polynomial.isOpenMap_comap_C` (and `AlgebraicGeometry.Polynomial.isOpenMap_comap_C`, which carries
the tag as its first part), so the covering set of this tag is that declaration together with the
one stated here. The equality stated here implies that one, standard opens forming a basis.

The second claim is stated as the explicit finite union the source computes, not as
`IsCompact (comap C '' basicOpen f)`. The latter is a degenerate instance of "a continuous image of
a quasi-compact set is quasi-compact" (`IsCompact.image` and `PrimeSpectrum.isCompact_basicOpen`),
true for every ring map and using nothing about `R[x]`; the mathematics of the source's second
claim is the finite union, from which quasi-compactness (`Set.Finite.isCompact_biUnion`) and
openness (`PrimeSpectrum.isOpen_basicOpen`) both follow at once.

The union is indexed by `f.coeffs`, the finset of *nonzero* coefficients of `f`; since `D(0) = ∅`
this is the source's union over all of `a_0, …, a_d`. Mathlib's
`Polynomial.image_comap_C_basicOpen` describes the same image as
`(zeroLocus (Set.range f.coeff))ᶜ`, a form in which the finiteness that makes the image
quasi-compact, the point of the source's second claim, is not visible.

Faithfulness. (1) Both `R` and `f` occur on either side of the equality, so no hypothesis is idle;
no further hypothesis is imposed on `R`. (2) The base is the source's: the map is `comap C` along
`R → R[x]`, the coefficients are elements of `R`, and the standard opens on the right are opens of
`Spec R`. (3) The source's canonical map `Spec(R[x]) → Spec(R)` is pinned as
`PrimeSpectrum.comap Polynomial.C`, and its image on `D(f)` is pinned by an equality rather than
asserted to be some quasi-compact open. (4) The instantiation is not degenerate: over `R = ℤ`, the
image of `D(2x + 3)` is `D(2) ∪ D(3) = Spec ℤ` while the image of `D(2)` is the proper open `D(2)`,
so the right hand side genuinely varies with `f`, and the statement is not an instance of a general
fact about arbitrary ring maps.

## References

* [Stacks Project, Tag 00FB](https://stacks.math.columbia.edu/tag/00FB)
-/

@[expose] public section

open PrimeSpectrum

namespace Polynomial

/-- **Stacks 00FB**, second part. Let `R` be a ring and `f ∈ R[x]`. The image of the standard open
`D(f) ⊆ Spec(R[x])` under the map `Spec(R[x]) → Spec(R)` is the union of the standard opens `D(a)`,
`a` running over the coefficients of `f`; in particular it is a quasi-compact open. -/
@[stacks 00FB "Second part"]
public theorem image_comap_C_basicOpen_eq_biUnion_basicOpen_coeffs {R : Type*} [CommRing R]
    (f : R[X]) :
    PrimeSpectrum.comap (C : R →+* R[X]) '' (basicOpen f : Set (PrimeSpectrum R[X])) =
      ⋃ a ∈ f.coeffs, (basicOpen a : Set (PrimeSpectrum R)) := by
  ext p
  simp only [mem_image_comap_C_basicOpen, Set.mem_iUnion, SetLike.mem_coe, mem_basicOpen,
    exists_prop, mem_coeffs_iff]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨_, ⟨i, mem_support_iff.2 fun h ↦ hi (h ▸ p.asIdeal.zero_mem), rfl⟩, hi⟩
  · rintro ⟨_, ⟨i, -, rfl⟩, hi⟩
    exact ⟨i, hi⟩

end Polynomial

end

/-!
# Prime ideals of a polynomial ring over a principal ideal domain

Let `R` be a principal ideal domain and `P` a prime ideal of `R[X]`. We classify `P` by its
contraction `P ∩ R`:

* if `P ∩ R = 0`, then `P = 0` or `P = (f)` with `f` irreducible; this holds over any unique
  factorization domain (`Polynomial.eq_bot_or_eq_span_irreducible_of_comap_C_eq_bot`);
* if `P ∩ R ≠ 0`, then `P ∩ R = (π)` for a prime `π`
  (`Polynomial.exists_prime_comap_C_eq_span`), and for any surjection `ψ : R → k` onto a field
  with kernel `(π)`, either `P = (π)` or `P = (π, f)` with `f` monic and irreducible modulo `ψ`
  (`Polynomial.eq_span_C_or_eq_span_C_monic`).

These are the common core of Stacks Tags 00EZ and 00F0.
-/

@[expose] public section

namespace Polynomial

open Ideal

variable {R : Type*} [CommRing R]

/-- The ideal `(C p)` of `R[X]` is the extension of `(p)` along `C`. -/
private theorem span_singleton_C_eq_map_C (p : R) : span {C p} = (span {p}).map C := by
  rw [map_span, Set.image_singleton]

/-- Irreducibility modulo `C p` is irreducibility of the coefficientwise reduction modulo `p`. -/
private theorem irreducible_mk_span_C_iff (p : R) (f : R[X]) :
    Irreducible (Ideal.Quotient.mk (span {C p}) f) ↔
      Irreducible (f.map (Ideal.Quotient.mk (span {p}))) := by
  rw [span_singleton_C_eq_map_C,
    ← MulEquiv.irreducible_iff (polynomialQuotientEquivQuotientPolynomial (span {p})).symm,
    polynomialQuotientEquivQuotientPolynomial_symm_mk]

/-- The preimage of `(φ f)` under a surjection `φ` with kernel `(c)` is `(c, f)`. -/
private theorem comap_span_singleton_eq_span_pair {S : Type*} [CommRing S] (φ : R[X] →+* S)
    (hφ : Function.Surjective φ) {c : R[X]} (hker : RingHom.ker φ = span {c}) (f : R[X]) :
    comap φ (span {φ f}) = span {c, f} := by
  rw [← Set.image_singleton, ← map_span, comap_map_of_surjective _ hφ,
    ← RingHom.ker_eq_comap_bot, hker, span_insert, sup_comm]

/-- A nonzero prime ideal of `R[X]`, for `R` a unique factorization domain, meeting `R` only in
`0`, is generated by one irreducible polynomial. -/
theorem eq_bot_or_eq_span_irreducible_of_comap_C_eq_bot [IsDomain R] [UniqueFactorizationMonoid R]
    (P : Ideal R[X]) [hP : P.IsPrime] (h : P.comap C = ⊥) :
    P = ⊥ ∨ ∃ f : R[X], Irreducible f ∧ P = span {f} := by
  refine or_iff_not_imp_left.2 fun hbot ↦ ?_
  obtain ⟨f, hfP, hf⟩ := hP.exists_mem_prime_of_ne_bot hbot
  refine ⟨f, hf.irreducible, ?_⟩
  let K := FractionRing R
  let := Polynomial.algebra R K
  have := Polynomial.isLocalization (nonZeroDivisors R) K
  have hdisj : Disjoint ((nonZeroDivisors R).map C : Set R[X]) P := by
    refine Set.disjoint_left.2 fun _ ⟨c, hc, hcx⟩ hx ↦ nonZeroDivisors.ne_zero hc ?_
    rwa [← hcx, SetLike.mem_coe, ← mem_comap, h, mem_bot] at hx
  have hf' : (span {f}).IsPrime := (span_singleton_prime hf.ne_zero).2 hf
  have hsub : span {f} ≤ P := (span_singleton_le_iff_mem P).2 hfP
  have hdisj' := hdisj.mono_right (SetLike.coe_subset_coe.2 hsub)
  have hPK := IsLocalization.isPrime_of_isPrime_disjoint _ K[X] P hP hdisj
  have hfK := IsLocalization.isPrime_of_isPrime_disjoint _ K[X] _ hf' hdisj'
  have hfK_ne : (span {f}).map (algebraMap R[X] K[X]) ≠ ⊥ := by
    intro h0
    have h1 : algebraMap R[X] K[X] f = 0 := by
      rw [← mem_bot, ← h0]
      exact mem_map_of_mem _ (mem_span_singleton_self f)
    refine hf.ne_zero
      ((IsLocalization.to_map_eq_zero_iff (M := (nonZeroDivisors R).map C) K[X] ?_).1 h1)
    rintro _ ⟨c, hc, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (C_ne_zero.2 (nonZeroDivisors.ne_zero hc))
  have heq := ((IsPrime.to_maximal_ideal hfK_ne).eq_of_le hPK.ne_top (map_mono hsub)).symm
  rw [← IsLocalization.under_map_of_isPrime_disjoint _ K[X] hP hdisj, heq,
    IsLocalization.under_map_of_isPrime_disjoint _ K[X] hf' hdisj']

/-- A prime ideal of `R[X]`, for `R` a principal ideal domain, meeting `R` in a nonzero ideal
contracts to the ideal generated by a prime element of `R`. -/
theorem exists_prime_comap_C_eq_span [IsPrincipalIdealRing R]
    (P : Ideal R[X]) [P.IsPrime] (h : P.comap C ≠ ⊥) :
    ∃ π : R, Prime π ∧ P.comap C = span {π} :=
  ⟨Submodule.IsPrincipal.generator (P.comap C),
    Submodule.IsPrincipal.prime_generator_of_isPrime _ h,
    (Submodule.IsPrincipal.span_singleton_generator _).symm⟩

/-- Let `ψ : R → k` be a surjection onto a field with kernel `(π)`, and `P` a prime of `R[X]`
containing `π`. Then `P = (π)`, or `P = (π, f)` for a monic `f` whose reduction by `ψ` is
irreducible. -/
theorem eq_span_C_or_eq_span_C_monic {k : Type*} [Field k] (ψ : R →+* k)
    (hψ : Function.Surjective ψ) {π : R} (hker : RingHom.ker ψ = span {π})
    (P : Ideal R[X]) [hP : P.IsPrime] (hπ : C π ∈ P) :
    P = span {C π} ∨ ∃ f : R[X], f.Monic ∧ Irreducible (f.map ψ) ∧ P = span {C π, f} := by
  set φ := mapRingHom ψ
  have hφ : Function.Surjective φ := (coe_mapRingHom ψ).symm ▸ map_surjective ψ hψ
  have hkerφ : RingHom.ker φ = span {C π} := by
    rw [ker_mapRingHom, hker, ← span_singleton_C_eq_map_C]
  have hkerP : RingHom.ker φ ≤ P := by rwa [hkerφ, span_singleton_le_iff_mem]
  have hPeq : P = (P.map φ).comap φ := by
    rw [comap_map_of_surjective _ hφ, ← RingHom.ker_eq_comap_bot, sup_eq_left.2 hkerP]
  have := map_isPrime_of_surjective hφ hkerP
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (P.map φ)).principal
  rw [submodule_span_eq] at hg
  by_cases hg0 : g = 0
  · left
    rw [hPeq, hg, hg0, span_singleton_eq_bot.2 rfl, ← RingHom.ker_eq_comap_bot, hkerφ]
  right
  set g' := g * C (leadingCoeff g)⁻¹
  have hg'm : g'.Monic := monic_mul_leadingCoeff_inv hg0
  have hg' : P.map φ = span {g'} := by
    rw [hg, span_singleton_mul_right_unit
      (isUnit_C.2 (isUnit_iff_ne_zero.2 (inv_ne_zero (leadingCoeff_ne_zero.2 hg0))))]
  obtain ⟨f, hf, -, hfm⟩ := lifts_and_natDegree_eq_and_monic (mem_lifts_of_surjective hψ g') hg'm
  have hprime : Prime g' := (span_singleton_prime hg'm.ne_zero).1 (hg' ▸ inferInstance)
  refine ⟨f, hfm, hf ▸ hprime.irreducible, ?_⟩
  rw [hPeq, hg', ← hf]
  exact comap_span_singleton_eq_span_pair φ hφ hkerφ f

/-- Every prime ideal of `R[X]` over a principal ideal domain is zero, generated by an
irreducible polynomial, or generated by an irreducible constant and a polynomial irreducible
modulo that constant. -/
theorem eq_bot_or_eq_span_or_eq_span_pair_of_isPrime [IsDomain R] [IsPrincipalIdealRing R]
    (P : Ideal R[X]) (hP : P.IsPrime) :
    P = ⊥ ∨ (∃ f : R[X], Irreducible f ∧ P = span {f}) ∨
      (∃ (p : R) (f : R[X]), Irreducible p ∧
        Irreducible (Ideal.Quotient.mk (span {C p}) f) ∧ P = span {C p, f}) := by
  by_cases h : P.comap C = ⊥
  · exact (eq_bot_or_eq_span_irreducible_of_comap_C_eq_bot P h).imp_right Or.inl
  obtain ⟨π, hπ, hPπ⟩ := exists_prime_comap_C_eq_span P h
  have : (span {π}).IsPrime := (span_singleton_prime hπ.ne_zero).2 hπ
  have : (span {π}).IsMaximal :=
    IsPrime.to_maximal_ideal (span_singleton_eq_bot.not.2 hπ.ne_zero)
  let := Ideal.Quotient.field (span {π})
  have hCπ : C π ∈ P := by
    rw [← mem_comap, hPπ]
    exact mem_span_singleton_self π
  rcases eq_span_C_or_eq_span_C_monic (k := R ⧸ span {π}) (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective mk_ker P hCπ with hP | ⟨f, -, hf, hP⟩
  · exact Or.inr (Or.inl ⟨C π, (prime_C_iff.2 hπ).irreducible, hP⟩)
  refine Or.inr (Or.inr ⟨π, f, hπ.irreducible, ?_, hP⟩)
  exact (irreducible_mk_span_C_iff π f).2 hf

/-- Converse of `eq_bot_or_eq_span_or_eq_span_pair_of_isPrime`: the listed ideals are prime. -/
theorem isPrime_of_eq_bot_or_eq_span_or_eq_span_pair [IsDomain R] [IsPrincipalIdealRing R]
    (P : Ideal R[X])
    (h : P = ⊥ ∨ (∃ f : R[X], Irreducible f ∧ P = span {f}) ∨
      (∃ (p : R) (f : R[X]), Irreducible p ∧
        Irreducible (Ideal.Quotient.mk (span {C p}) f) ∧ P = span {C p, f})) :
    P.IsPrime := by
  rcases h with rfl | ⟨f, hf, rfl⟩ | ⟨p, f, hp, hf, rfl⟩
  · exact isPrime_bot
  · exact (span_singleton_prime hf.ne_zero).2
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp hf)
  · have : (span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp
    let := Ideal.Quotient.field (span {p})
    set ψ : R[X] →+* (R ⧸ span {p})[X] := mapRingHom (Ideal.Quotient.mk _) with hψdef
    have hψ : Function.Surjective ψ := map_surjective _ Ideal.Quotient.mk_surjective
    have hker : RingHom.ker ψ = span {C p} := by
      rw [hψdef, ker_mapRingHom, mk_ker, span_singleton_C_eq_map_C]
    have : (span {ψ f}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible ((irreducible_mk_span_C_iff p f).1 hf)
    rw [← comap_span_singleton_eq_span_pair ψ hψ hker f]
    exact (comap_isMaximal_of_surjective ψ hψ).isPrime

/-- The second and third shapes of `eq_bot_or_eq_span_or_eq_span_pair_of_isPrime` never give the
same ideal. The first shape differs from both, since their generators are nonzero. -/
theorem span_singleton_ne_span_pair [IsDomain R] {g : R[X]} {p : R} {f : R[X]}
    (hg : Irreducible g) (hp : Irreducible p)
    (hf : Irreducible (Ideal.Quotient.mk (span {C p}) f)) :
    span {g} ≠ span {C p, f} := by
  intro h
  have hgp : g ∣ C p := mem_span_singleton.mp (h ▸ subset_span (by simp))
  have hg0 : g = C (g.coeff 0) := by
    refine eq_C_of_natDegree_eq_zero (Nat.le_zero.mp ?_)
    simpa using natDegree_le_of_dvd hgp (C_ne_zero.mpr hp.ne_zero)
  have hcp : g.coeff 0 ∣ p := by
    rw [hg0, C_dvd_iff_dvd_coeff] at hgp
    simpa using hgp 0
  have hcu : ¬ IsUnit (g.coeff 0) := fun hu => hg.not_isUnit (hg0 ▸ hu.map C)
  obtain ⟨d, hd⟩ := hcp
  have hdu : IsUnit d := (hp.isUnit_or_isUnit hd).resolve_left hcu
  have hpc : p ∣ g.coeff 0 := by
    rw [hd]
    exact (associated_mul_unit_right _ _ hdu).symm.dvd
  have hpg : C p ∣ g := by
    rw [hg0]
    exact _root_.map_dvd C hpc
  have hfg : f ∈ span {g} := h ▸ subset_span (by simp)
  have hf0 : f ∈ span {C p} := span_singleton_le_span_singleton.mpr hpg hfg
  exact hf.ne_zero (Ideal.Quotient.eq_zero_iff_mem.mpr hf0)

/-- **Stacks 00F0**, both directions: the prime ideals of `R[X]`, for `R` a principal ideal
domain. The tag is the case `R = k[x]` for a field `k`. -/
@[stacks 00F0 "for `R[X]` over any principal ideal domain `R`; the tag is the case `R = k[x]`"]
theorem isPrime_iff_eq_bot_or_eq_span_or_eq_span_pair [IsDomain R] [IsPrincipalIdealRing R]
    (P : Ideal R[X]) :
    P.IsPrime ↔ P = ⊥ ∨ (∃ f : R[X], Irreducible f ∧ P = span {f}) ∨
      (∃ (p : R) (f : R[X]), Irreducible p ∧
        Irreducible (Ideal.Quotient.mk (span {C p}) f) ∧ P = span {C p, f}) :=
  ⟨eq_bot_or_eq_span_or_eq_span_pair_of_isPrime P, isPrime_of_eq_bot_or_eq_span_or_eq_span_pair P⟩

end Polynomial

end

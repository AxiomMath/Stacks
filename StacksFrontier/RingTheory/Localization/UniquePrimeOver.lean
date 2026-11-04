module
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.RingTheory.Radical.NatInt
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
# Localizing below a unique prime lying over a given prime

Let `R → S` be a ring map and `p ⊂ R` a prime. Suppose there is a unique prime `q ⊂ S`
lying over `p`, and suppose that either going up holds for `R → S`, or going down holds
for `R → S` and there is at most one prime of `S` above every prime of `R`. Then
`S_p = S_q`.

## Conventions

The ring map `R → S` is carried by `[Algebra R S]`. Uniqueness of the prime over `p` is
the hypothesis `huniq`. Going up is supplied as an explicit proposition, there being no
general going-up predicate available; going down is `Algebra.HasGoingDown R S` together
with injectivity of contraction along `R → S` on primes. The conclusion `S_p = S_q` is
expressed by saying that `S_p`, the localization of `S` at the image of `R ∖ p`, is
*also* a localization of `S` at the complement of `q`.

## Main results

* `localization_eq_of_unique_prime_over`: under these hypotheses, the localization of `S` at the
  image of `R ∖ p` is a localization of `S` at the complement of `q`.
-/

@[expose] public section

open scoped Pointwise

/-- If `p` is a prime of `R` with a unique prime `q` of `S` lying over it, and `R → S`
satisfies going up (or going down together with injectivity of contraction on primes),
then the localization of `S` at the image of `R ∖ p` is also a localization of `S` at
the complement of `q`; that is, `S_p = S_q`. -/
@[stacks 00EA]
theorem localization_eq_of_unique_prime_over
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (huniq : ∀ q' : Ideal S, q'.IsPrime → q'.LiesOver p → q' = q)
    (h2 :
      (∀ (p₁ p₂ : Ideal R) (q₁ : Ideal S), p₁.IsPrime → p₂.IsPrime → q₁.IsPrime →
          p₁ ≤ p₂ → q₁.under R = p₁ →
            ∃ q₂ : Ideal S, q₂.IsPrime ∧ q₁ ≤ q₂ ∧ q₂.under R = p₂) ∨
      (Algebra.HasGoingDown R S ∧
        ∀ (q₁ q₂ : Ideal S), q₁.IsPrime → q₂.IsPrime →
          q₁.under R = q₂.under R → q₁ = q₂)) :
    IsLocalization q.primeCompl
      (Localization (Algebra.algebraMapSubmonoid S p.primeCompl)) := by
  have key : ∀ q' : Ideal S, q'.IsPrime → q'.under R ≤ p → q' ≤ q := by
    intro q' hq'p hsub
    have hp'p : (q'.under R).IsPrime := inferInstance
    rcases h2 with hgu | ⟨hgd, hone⟩
    · obtain ⟨q₂, hq₂p, hq'le, hq₂over⟩ :=
        hgu (q'.under R) p q' hp'p ‹p.IsPrime› hq'p hsub rfl
      exact huniq q₂ hq₂p ⟨hq₂over.symm⟩ ▸ hq'le
    · obtain ⟨P, hPle, hPp, hPover⟩ :=
        Ideal.exists_ideal_le_liesOver_of_le (p := q'.under R) (q := p) q hsub
      exact hone P q' hPp hq'p (P.over_def (q'.under R)).symm ▸ hPle
  have h_le : Algebra.algebraMapSubmonoid S p.primeCompl ≤ q.primeCompl := fun _ hx =>
    Set.disjoint_left.mp (Ideal.disjoint_primeCompl_of_liesOver (C := S) (p := p) (𝔓 := q)) hx
  have h_units : ∀ r ∈ q.primeCompl,
      IsUnit (algebraMap S (Localization (Algebra.algebraMapSubmonoid S p.primeCompl)) r) := by
    intro n hn
    by_contra hnu
    have hne :
        (Ideal.span {algebraMap S (Localization (Algebra.algebraMapSubmonoid S p.primeCompl)) n}
          : Ideal _) ≠ ⊤ := by
      rw [Ne, Ideal.span_singleton_eq_top]; exact hnu
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have : m.IsPrime := hm.isPrime
    set q' : Ideal S :=
      Ideal.comap (algebraMap S (Localization (Algebra.algebraMapSubmonoid S p.primeCompl))) m
      with hq'def
    have hq'p : q'.IsPrime := inferInstance
    have hn_in : n ∈ q' :=
      hle (Ideal.subset_span (Set.mem_singleton _))
    have hsub : q'.under R ≤ p := by
      intro r hr
      by_contra hrp
      have hMmem :
          algebraMap R S r ∈ Algebra.algebraMapSubmonoid S p.primeCompl := ⟨r, hrp, rfl⟩
      have hunit :
          IsUnit (algebraMap S (Localization (Algebra.algebraMapSubmonoid S p.primeCompl))
            (algebraMap R S r)) :=
        IsLocalization.map_units _ ⟨algebraMap R S r, hMmem⟩
      have hmem :
          algebraMap S (Localization (Algebra.algebraMapSubmonoid S p.primeCompl))
            (algebraMap R S r) ∈ m := hr
      exact hm.ne_top (Ideal.eq_top_of_isUnit_mem m hmem hunit)
    exact hn (key q' hq'p hsub hn_in)
  exact IsLocalization.of_le (M := Algebra.algebraMapSubmonoid S p.primeCompl)
    q.primeCompl h_le h_units


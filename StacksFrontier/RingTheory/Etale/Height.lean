module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.Unramified.LocalStructure
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Étale ring maps preserve heights of primes

Let `f : A →+* B` be an étale ring map and let `q` be a prime ideal of `B` lying over the prime
ideal `p` of `A`. This file shows that `p` and `q` have the same height, equivalently that the
localizations `A_p` and `B_q` have the same Krull dimension (Stacks Tag 07QP).

## Main results

* `Ideal.height_le_height_of_liesOver_of_hasGoingDown`: the going-down inequality
  `p.height ≤ q.height`, which needs only that `A → B` satisfies going down (in particular
  whenever `B` is flat over `A`).
* `Ideal.height_le_height_of_liesOver_of_etale`: the reverse inequality `q.height ≤ p.height`,
  which uses that a fibre of an étale map contains no strict inclusion of primes.
* `RingHom.Etale.height_eq_height` and `RingHom.Etale.ringKrullDim_localization_atPrime_eq`:
  the two equivalent forms of Stacks Tag 07QP.

## Implementation notes

Both inequalities read heights as order heights in the prime spectrum, via
`PrimeSpectrum.height_eq_orderHeight`. The going-down inequality then lifts a chain of primes of
`A` to a chain of primes of `B` with `Ideal.exists_ltSeries_of_hasGoingDown`, and the reverse
inequality pushes a chain of primes of `B` forward along `PrimeSpectrum.comap`, staying strict
because an étale algebra is quasi-finite, so `Algebra.QuasiFinite.eq_of_le_of_under_eq` forbids
strict inclusions inside a fibre.

Only quasi-finiteness enters the second inequality; the more general statement for
`Algebra.QuasiFiniteAt` is Stacks 00QF, `Ideal.height_le_height_of_liesOver_of_quasiFiniteAt`,
which is not used here so that this file depends on Mathlib alone.
-/

/-- The going-down inequality: if the prime `q` of `B` lies over the prime `p` of `A` and
`A → B` satisfies going down (for instance if `B` is flat over `A`), then `p.height ≤ q.height`. -/
theorem Ideal.height_le_height_of_liesOver_of_hasGoingDown {A B : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [Algebra.HasGoingDown A B] (p : Ideal A) (q : Ideal B)
    [hp : p.IsPrime] [hq : q.IsPrime] [q.LiesOver p] : p.height ≤ q.height := by
  rw [(⟨p, hp⟩ : PrimeSpectrum A).height_eq_orderHeight,
      (⟨q, hq⟩ : PrimeSpectrum B).height_eq_orderHeight]
  apply Order.height_le
  intro s hs
  have : q.LiesOver s.last.asIdeal := by rwa [hs]
  obtain ⟨t, hlen, hlast, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown s q
  exact hlen ▸ Order.length_le_height hlast.le

/-- The étale-specific inequality: if `A → B` is étale and the prime `q` of `B` lies over the
prime `p` of `A`, then `q.height ≤ p.height`. -/
theorem Ideal.height_le_height_of_liesOver_of_etale {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.Etale A B] (p : Ideal A) (q : Ideal B) [hp : p.IsPrime]
    [hq : q.IsPrime] [q.LiesOver p] : q.height ≤ p.height := by
  rw [(⟨q, hq⟩ : PrimeSpectrum B).height_eq_orderHeight,
      (⟨p, hp⟩ : PrimeSpectrum A).height_eq_orderHeight]
  apply Order.height_le
  intro s hs
  have hstep : ∀ i : Fin s.length, PrimeSpectrum.comap (algebraMap A B) (s.toFun i.castSucc) <
      PrimeSpectrum.comap (algebraMap A B) (s.toFun i.succ) := fun i => by
    have hlt : s.toFun i.castSucc < s.toFun i.succ := s.step i
    exact lt_of_le_of_ne (Ideal.comap_mono hlt.le) fun heq => hlt.ne <| PrimeSpectrum.ext <|
      Algebra.QuasiFinite.eq_of_le_of_under_eq (R := A) _ _ hlt.le
        (congrArg PrimeSpectrum.asIdeal heq)
  let t : LTSeries (PrimeSpectrum A) :=
    ⟨s.length, fun i => PrimeSpectrum.comap (algebraMap A B) (s.toFun i), hstep⟩
  have hlast : t.last = (⟨p, hp⟩ : PrimeSpectrum A) := PrimeSpectrum.ext <|
    (congrArg (fun x : PrimeSpectrum B => (x.comap (algebraMap A B)).asIdeal) hs).trans
      (Ideal.LiesOver.over (p := p) (P := q)).symm
  exact Order.length_le_height hlast.le

/-- Equivalent formulation of Stacks Tag 07QP in terms of heights: for an étale ring map
`f : A →+* B`, if `q` is a prime of `B` lying over the prime `p` of `A`, then the height of `q`
in `B` equals the height of `p` in `A`. -/
theorem RingHom.Etale.height_eq_height {A B : Type*} [CommRing A] [CommRing B] {f : A →+* B}
    (hf : f.Etale) (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] (hlo : p = q.comap f) :
    p.height = q.height := by
  let := f.toAlgebra
  have : Algebra.Etale A B := hf
  have : Algebra.HasGoingDown A B := Algebra.HasGoingDown.of_flat
  have : q.LiesOver p := ⟨hlo⟩
  exact le_antisymm (Ideal.height_le_height_of_liesOver_of_hasGoingDown p q)
    (Ideal.height_le_height_of_liesOver_of_etale p q)

/-- Stacks Tag 07QP. For an étale ring map `f : A →+* B`, if `q` is a prime of `B` lying over the
prime `p` of `A`, then the Krull dimensions of the localizations `A_p` and `B_q` agree. -/
@[stacks 07QP, ega "IV 17.6.4" "affine/ring case", ega "IV 6.1.3" "special case"]
theorem RingHom.Etale.ringKrullDim_localization_atPrime_eq {A B : Type*} [CommRing A] [CommRing B]
    {f : A →+* B} (hf : f.Etale) (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime]
    (hlo : p = q.comap f) :
    ringKrullDim (Localization.AtPrime p) = ringKrullDim (Localization.AtPrime q) := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p),
      IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q),
      RingHom.Etale.height_eq_height hf p q hlo]

attribute [stacks 0AGY "Lemma 07QP of the section: for an étale ring map `A → B` and a prime
`𝔮 ⊂ B` lying over `𝔭 ⊂ A`, `dim A_𝔭 = dim B_𝔮`."]
  RingHom.Etale.ringKrullDim_localization_atPrime_eq

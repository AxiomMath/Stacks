module

public import Mathlib.RingTheory.Etale.Locus
public import StacksCore.Tactic.StacksAttribute

/-!
# Étale ring maps and étaleness at a prime

[Stacks, Tag 00U1] calls a ring map `R → S` *étale* if it is of finite presentation and the naive
cotangent complex `NL_{S/R}` is quasi-isomorphic to zero, that is, `H_1(NL_{S/R}) = 0` and
`Ω_{S/R} = 0`; and it calls `R → S` *étale at a prime* `q ⊂ S` if `R → S_g` is étale for some
`g ∈ S` with `g ∉ q`.

Mathlib's `Algebra.Etale R S` is formal étaleness together with finite presentation, and
`Algebra.FormallyEtale R S` is by definition `Ω[S⁄R] = 0` together with
`H1Cotangent R S = H_1(NL_{S/R}) = 0`. So `Algebra.Etale` is the first half of Definition 00U1
literally; `Algebra.etale_iff_finitePresentation_and_naiveCotangent` spells this out.

The second half is `Algebra.EtaleAtPrime R q`. Mathlib's `Algebra.IsEtaleAt R q` is formal
étaleness of the stalk `S_q`, a different notion; the two agree when `S` is finitely presented
over `R` (`Algebra.etaleAtPrime_iff_isEtaleAt`), and étaleness at `q` in the source's sense
always implies `Algebra.IsEtaleAt R q` (`Algebra.EtaleAtPrime.isEtaleAt`).

## Main definitions

* `Algebra.EtaleAtPrime`: `R → S` is étale at the prime `q`.

## Main results

* `Algebra.etale_iff_finitePresentation_and_naiveCotangent`: `R → S` is étale if and only if it is
  of finite presentation, `H_1(NL_{S/R}) = 0` and `Ω_{S/R} = 0`.
* `Algebra.etaleAtPrime_iff_isEtaleAt`: for `S` finitely presented over `R`, étaleness at `q` is
  formal étaleness of `S_q` over `R`.

## References

* [Stacks Project, Tag 00U1](https://stacks.math.columbia.edu/tag/00U1)
-/

@[expose] public section

namespace Algebra

variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- A ring map `R → S` is *étale at a prime* `q ⊂ S` if there is a `g ∈ S`, `g ∉ q`, such that
`R → S_g` is étale. Here `S_g` is `Localization.Away g`, an `R`-algebra through `R → S → S_g`. -/
@[stacks 00U1 "Second half of the definition: étale at a prime `q`, stated verbatim as
`∃ g ∉ q, Algebra.Etale R (Localization.Away g)`. Mathlib's `Algebra.IsEtaleAt` is formal
étaleness of `S_q` and agrees with this notion for `S` of finite presentation over `R`
(`Algebra.etaleAtPrime_iff_isEtaleAt`)."]
def EtaleAtPrime (q : Ideal S) : Prop :=
  ∃ g ∉ q, Algebra.Etale R (Localization.Away g)

variable (S) in
/-- A ring map `R → S` is étale if and only if it is of finite presentation and the naive
cotangent complex `NL_{S/R}` is quasi-isomorphic to zero, that is, `H_1(NL_{S/R}) = 0` and
`Ω_{S/R} = 0`. -/
@[stacks 00U1 "First half of the definition: étale ring maps. `Algebra.Etale R S` is
`Algebra.FormallyEtale R S` (which is `Ω[S⁄R] = 0` together with `H1Cotangent R S = 0`, the first
homology of the naive cotangent complex) plus `Algebra.FinitePresentation R S`; this is the
source's definition literally."]
theorem etale_iff_finitePresentation_and_naiveCotangent :
    Algebra.Etale R S ↔ Algebra.FinitePresentation R S ∧
      Subsingleton (Algebra.H1Cotangent R S) ∧ Subsingleton Ω[S⁄R] := by
  rw [Algebra.etale_iff, Algebra.formallyEtale_iff]
  tauto

variable {R}

/-- If `R → S` is étale at a prime `q`, then the stalk `S_q` is formally étale over `R`. -/
theorem EtaleAtPrime.isEtaleAt {q : Ideal S} [q.IsPrime] (h : EtaleAtPrime R q) :
    Algebra.IsEtaleAt R q := by
  obtain ⟨g, hg, hE⟩ := h
  have hsub := Algebra.basicOpen_subset_etaleLocus_iff (R := R) (A := S) (f := g) |>.mpr
    hE.formallyEtale
  exact hsub (show (⟨q, ‹_›⟩ : PrimeSpectrum S) ∈ PrimeSpectrum.basicOpen g from hg)

/-- For `S` of finite presentation over `R`, `R → S` is étale at a prime `q` if and only if the
stalk `S_q` is formally étale over `R`. -/
theorem etaleAtPrime_iff_isEtaleAt [Algebra.FinitePresentation R S] (q : Ideal S) [q.IsPrime] :
    EtaleAtPrime R q ↔ Algebra.IsEtaleAt R q :=
  ⟨EtaleAtPrime.isEtaleAt, fun _ ↦ Algebra.exists_etale_of_isEtaleAt q⟩

end Algebra

module

public import StacksFrontier.RingTheory.GeometricallyRegular.Defs
public import StacksFrontier.RingTheory.Smoothing.SingularIdeals

/-!
# The local smoothing situation and resolvable factorizations

Fix a Noetherian ring `R`, an `R`-algebra `A` of finite presentation, an `R`-algebra map
`A → Λ` and a prime ideal `q ⊂ Λ`. The ideal attached to these data is
`𝔥_A = √(H_{A/R} Λ)`, the radical of the extension to `Λ` of the singular ideal of `A`
over `R`.

Such a chain *can be resolved* at `q` if it factors as `A → B → Λ` with `B` of finite
presentation over `R` and `𝔥_A ⊆ 𝔥_B ⊄ q`; the factorization is then called a *resolution*.
The two local tricks of this section — spreading out a resolution of the localized chain, and
resolving in dimension zero — are the lemmas in
`StacksFrontier.RingTheory.Smoothing.SpreadingOutResolutions` and
`StacksFrontier.RingTheory.Smoothing.ZeroDimensionalResolution`.

## Main definitions

* `Stacks.Smoothing.CanBeResolved`: the chain `R → A → Λ ⊃ q` can be resolved.
* `Stacks.Smoothing.CanBeResolvedInPositiveCharacteristic`: the statement of Lemma 07FJ — every
  such chain over a field of characteristic `p > 0`, with `Λ` Noetherian and geometrically
  regular and `q` minimal over `𝔥_A`, can be resolved at `q`.
* `Stacks.Smoothing.LocalSmoothingSituation`: the standing data of the section — the rings, the
  algebra maps, the finiteness hypotheses and the chosen prime.
* `Stacks.Smoothing.LocalSmoothingSituation.radicalSingularIdealExtension`: the ideal `𝔥_A`.
* `Stacks.Smoothing.LocalSmoothingSituation.IsResolvableAfterLocalizing`: the localized chain
  `R_p → A_p → Λ_q ⊃ q Λ_q` can be resolved, where `p = R ∩ q`.

## Implementation notes

The displayed chain `R → A → Λ` is three algebra structures together with an
`IsScalarTower R A Λ`; the unbundled predicate `CanBeResolved` therefore applies verbatim to
localized and quotient chains, which is how it is used.

`CanBeResolved` puts the resolving algebra in `Type (max u v w)`, and
`IsResolvableAfterLocalizing` quantifies over models of the three localizations in the
universes of `R`, `A` and `Λ` respectively. No universe is lost: a model of each localization
exists in its own universe (take `Localization`), and `CanBeResolved` is invariant under
`R`-algebra isomorphism of the resolving algebra, which may always be chosen as a quotient of
a polynomial ring on finitely many variables.

## References

* [Stacks Project, Tag 07F7](https://stacks.math.columbia.edu/tag/07F7)
-/

@[expose] public section

namespace Stacks.Smoothing

universe u v w

/-- A chain `R → A → Λ` *can be resolved* at the prime `q ⊂ Λ` if there is a factorization
`A → B → Λ` with `B` of finite presentation over `R` and `𝔥_A ⊆ 𝔥_B ⊄ q`, where
`𝔥_C = √(H_{C/R} Λ)` is the radical of the extension to `Λ` of the singular ideal of `C`.
This is the definition following Situation 07F7. -/
def CanBeResolved (R : Type u) (A : Type v) (Λ : Type w) [CommRing R] [CommRing A]
    [CommRing Λ] [Algebra R A] [Algebra A Λ] [Algebra R Λ] [IsScalarTower R A Λ]
    (q : Ideal Λ) : Prop :=
  ∃ (B : Type (max u v w)) (_ : CommRing B) (_ : Algebra R B) (_ : Algebra A B)
      (_ : Algebra B Λ),
    IsScalarTower R A B ∧ IsScalarTower A B Λ ∧ IsScalarTower R B Λ ∧
    Algebra.FinitePresentation R B ∧
    (Ideal.map (algebraMap A Λ) (singularIdeal R A)).radical ≤
      (Ideal.map (algebraMap B Λ) (singularIdeal R B)).radical ∧
    ¬ (Ideal.map (algebraMap B Λ) (singularIdeal R B)).radical ≤ q

/-- The statement of Lemma `07FJ`: in the local smoothing situation `k → A → Λ ⊃ q` of `07F7`
over a field `k` of characteristic `p > 0`, with `Λ` Noetherian and geometrically regular over
`k` and `q` minimal over `𝔥_A = √(H_{A/k} Λ)`, the chain can be resolved at `q`.

The statement is named because the proof of Lemma `07FJ` is long enough to be spread over many
modules, each of which states its own contribution towards this one; and because Popescu's
theorem (Tag 07GC) is a Noetherian induction whose inductive step is exactly this. It is proved
as `Stacks.Smoothing.canBeResolvedInPositiveCharacteristic`. -/
def CanBeResolvedInPositiveCharacteristic : Prop :=
  ∀ (k A Λ : Type u) [Field k] [CommRing A] [CommRing Λ]
    [Algebra k A] [Algebra k Λ] [Algebra A Λ] [IsScalarTower k A Λ]
    [Algebra.FinitePresentation k A] [IsNoetherianRing Λ]
    [Algebra.IsGeometricallyRegular k Λ] (p : ℕ) [CharP k p], 0 < p →
    ∀ (q : Ideal Λ) [q.IsPrime],
      q ∈ (Ideal.map (algebraMap A Λ) (singularIdeal k A)).radical.minimalPrimes →
      CanBeResolved k A Λ q

/-- The standing data of Stacks 07F7: a Noetherian ring `R`, an `R`-algebra `A` of finite
presentation, an `R`-algebra map `A → Λ`, and a prime ideal `q ⊂ Λ`. -/
-- Stacks 07F7 is a situation tag: it fixes this set-up and the notation `𝔥_A`, and asserts
-- nothing. It is deliberately not formalized as a tag,
-- so this structure carries no `@[stacks 07F7]`.
structure LocalSmoothingSituation where
  /-- The Noetherian base ring. -/
  R : Type u
  /-- The algebra of finite presentation over the base. -/
  A : Type v
  /-- The target of the algebra map from `A`. -/
  Λ : Type w
  /-- The commutative-ring structure on `R`. -/
  [commRingR : CommRing R]
  /-- The commutative-ring structure on `A`. -/
  [commRingA : CommRing A]
  /-- The commutative-ring structure on `Λ`. -/
  [commRingΛ : CommRing Λ]
  /-- The `R`-algebra structure on `A`. -/
  [algebraRA : Algebra R A]
  /-- The `R`-algebra structure on `Λ`. -/
  [algebraRΛ : Algebra R Λ]
  /-- The given algebra map `A → Λ`. -/
  [algebraAΛ : Algebra A Λ]
  /-- The map `R → Λ` is the composite of the displayed maps. -/
  [isScalarTower : IsScalarTower R A Λ]
  /-- The base ring is Noetherian. -/
  [noetherianR : IsNoetherianRing R]
  /-- The algebra `A` is of finite presentation over `R`. -/
  [finitePresentation : Algebra.FinitePresentation R A]
  /-- The chosen prime ideal of `Λ`. -/
  q : Ideal Λ
  /-- The chosen ideal is prime. -/
  [isPrimeQ : q.IsPrime]

attribute [instance] LocalSmoothingSituation.commRingR LocalSmoothingSituation.commRingA
  LocalSmoothingSituation.commRingΛ LocalSmoothingSituation.algebraRA
  LocalSmoothingSituation.algebraRΛ LocalSmoothingSituation.algebraAΛ
  LocalSmoothingSituation.isScalarTower LocalSmoothingSituation.noetherianR
  LocalSmoothingSituation.finitePresentation LocalSmoothingSituation.isPrimeQ

namespace LocalSmoothingSituation

variable (S : LocalSmoothingSituation.{u, v, w})

/-- The ideal `𝔥_A = √(H_{A/R} Λ)` of the local smoothing situation. -/
noncomputable def radicalSingularIdealExtension : Ideal S.Λ :=
  (Ideal.map (algebraMap S.A S.Λ) (singularIdeal S.R S.A)).radical

/-- The prime `p = R ∩ q` of the base ring. -/
def basePrime : Ideal S.R := S.q.comap (algebraMap S.R S.Λ)

/-- The ideal `p = R ∩ q` is prime. -/
instance : S.basePrime.IsPrime := Ideal.comap_isPrime _ _

/-- The chain of the local smoothing situation can be resolved at its prime. -/
abbrev CanBeResolved : Prop := Stacks.Smoothing.CanBeResolved S.R S.A S.Λ S.q

/-- The localized chain `R_p → A_p → Λ_q ⊃ q Λ_q` can be resolved, where `p = R ∩ q`. The
three localizations are taken to be arbitrary compatible models, so the predicate does not
depend on a choice; the compatibility of the displayed arrows is recorded by the scalar-tower
hypotheses. -/
def IsResolvableAfterLocalizing : Prop :=
  ∃ (Rp : Type u) (_ : CommRing Rp) (_ : Algebra S.R Rp)
      (_ : IsLocalization S.basePrime.primeCompl Rp),
    ∃ (Ap : Type v) (_ : CommRing Ap) (_ : Algebra S.A Ap)
        (_ : Algebra S.R Ap) (_ : Algebra Rp Ap)
        (_ : IsLocalization (S.basePrime.primeCompl.map (algebraMap S.R S.A)) Ap)
        (_ : IsScalarTower S.R S.A Ap) (_ : IsScalarTower S.R Rp Ap),
      ∃ (Λq : Type w) (_ : CommRing Λq) (_ : Algebra S.Λ Λq)
          (_ : Algebra S.A Λq) (_ : Algebra Rp Λq) (_ : Algebra Ap Λq)
          (_ : IsLocalization S.q.primeCompl Λq)
          (_ : IsScalarTower S.A S.Λ Λq) (_ : IsScalarTower S.A Ap Λq)
          (_ : IsScalarTower Rp Ap Λq),
        Stacks.Smoothing.CanBeResolved Rp Ap Λq (Ideal.map (algebraMap S.Λ Λq) S.q)

end LocalSmoothingSituation

end Stacks.Smoothing

end

module

public import StacksFrontier.RingTheory.Flat.DevissagePrimeDataLocalize
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Reducing the dévissage obligation of Stacks 05I7 to the étale neighbourhood of Stacks 05I1

`StacksFrontier.AlgebraicGeometry.Flatness.FinitePresentationStalk05I7` proves Stacks 05I7 granted
`Stacks.Flatness.ExistsSpreadOutCompleteDevissage`: after a flat local base change `R → R'` and a
flat extension `A → A'` of finite presentation over `R'`, the spread-out module `A' ⊗[A] N`
carries a complete dévissage over the maximal ideal of `R'` with prime data over a prime `q'`
contracting to `q`, and its localization at `q'` is flat over `R'`.

That obligation is stated with `R'` *local* and `A'` of finite presentation *over `R'`*, which is
not the shape Stacks 05I1 produces: 05I1 produces an elementary étale neighbourhood `R → R₁`,
whose source is not local, an algebra `A₁` over it and a complete dévissage *at* a prime `q₁` of
`A₁`, over the prime below `q₁` rather than over a maximal ideal.

This file closes that gap. `Stacks.Flatness.ExistsEtaleNeighborhoodCompleteDevissage` records the
05I1-shaped input, and
`Stacks.Flatness.existsSpreadOutCompleteDevissage_of_existsEtaleNeighborhoodCompleteDevissage`
derives the obligation from it, taking
```
  R' = (R₁)_{p₁},   A' = (A₁)_{p₁},   q' = q₁A',
```
where `p₁` is the prime of `R₁` below `q₁`. The four things that have to be produced are

* finite presentation of `A'` over `R'`
  (`Stacks.Flatness.finitePresentation_localization_algebraMapSubmonoid`), the finite-presentation
  analogue of `Stacks.Flatness.finiteType_of_isLocalization`;
* locality of `R → R'`
  (`Stacks.Flatness.isLocalHom_algebraMap_localization_of_comap_eq`), for which the one input is
  that `p₁` contracts to the maximal ideal of `R`; flatness of `R'` over `R` is then the
  composite of the flat `R → R₁` with a localization;
* primality of `q'` and the identity `q = q'.comap (algebraMap A A')`
  (`Stacks.Flatness.isPrime_map_algebraMap` and
  `Stacks.Flatness.comap_map_algebraMap_eq_of_comap_eq`), both instances of the prime
  correspondence for a localization missing the inverted set;
* flatness over `R'` of the localization of `A' ⊗[A] N` at `q'`
  (`Stacks.Flatness.flat_localizedModule_of_isLocalization`), which is the one clause needing a
  transport of modules: `A'_{q'}` is the localization of `A₁` at `q₁`
  (`IsLocalization.isLocalization_isLocalization_atPrime_isLocalization`), so the localization of
  `A' ⊗[A] N` at `q'` is the base change of `N` to that ring, hence the localization of
  `A₁ ⊗[A] N` at `q₁`, and flatness over `R'` is flatness over `R₁` by
  `Module.flat_iff_of_isLocalization`.

The dévissage clause itself is produced by
`Module.CompleteDevissage.devissage_clause_of_primeData` below, from
`Module.CompleteDevissage.localizeAtPrime` and
`Module.CompleteDevissage.PrimeData.localize` together with three pieces of bookkeeping: a
dévissage over `p₁R'` is one over the maximal ideal of `R'` because those ideals are equal
(`Module.CompleteDevissage.exists_primeData_of_eq`), a dévissage transports along an equivalence
of the module being dévissaged because only `initialEquiv` mentions it
(`Module.CompleteDevissage.ofLinearEquiv` and
`Module.CompleteDevissage.PrimeData.ofLinearEquiv`), and the localization of a base change is the
base change along the localized algebra
(`Stacks.Flatness.localizedBaseChangeEquiv`). What 05I1 itself produces, a
`Module.NonemptyCompleteDevissageAt`, feeds in through
`Module.CompleteDevissage.devissage_clause_of_nonemptyCompleteDevissageAt`.

## The strength of the hypothesis: the reduction is lateral

`Stacks.Flatness.ExistsEtaleNeighborhoodCompleteDevissage` is **logically equivalent** to
`Stacks.Flatness.ExistsSpreadOutCompleteDevissage`, and both implications are proved here:
`Stacks.Flatness.existsEtaleNeighborhoodCompleteDevissage_iff`. The converse direction takes the
étale neighbourhood to be the local ring itself, the one point needing an argument being that the
prime below `q'` contracts to the maximal ideal of `R`, which the prime data forces
(`Module.CompleteDevissage.PrimeData.under_eq`) together with locality of `R → R'`.

So this reduction **buys no logical strength**: the 05I7 statement obtained here,
`AlgebraicGeometry.finitePresentation_stalk_of_existsEtaleNeighborhoodCompleteDevissage`, is
neither stronger nor weaker than
`AlgebraicGeometry.finitePresentation_stalk_of_existsSpreadOutCompleteDevissage`. What it buys is
the *shape* of the remaining obligation: it no longer mentions a local base, a maximal ideal, or
finite presentation over a local ring, none of which the construction of Stacks 05HR and 05I1
comes with, so that construction can discharge it without any further localization bookkeeping.

The clauses which remain open in `Stacks.Flatness.ExistsEtaleNeighborhoodCompleteDevissage`, and
are not addressed here, are the existence of the elementary étale neighbourhood with its
dévissage — the mathematical content of Stacks 05I1 — and flatness of the localization of
`A₁ ⊗[A] N` at `q₁` over `R₁`, which is the flat-base-change consequence of the flatness
hypothesis on `N` and which is already a clause of the obligation being replaced.

## Main definitions

* `Stacks.Flatness.ExistsEtaleNeighborhoodCompleteDevissage`: the 05I1-shaped input — a flat
  extension `R → R₁` of the local base, an algebra `A₁` of finite presentation over `R₁` and flat
  over `A`, a prime `q₁` over `q` whose contraction to `R` is the maximal ideal, flatness of the
  localization of `A₁ ⊗[A] N` at `q₁`, and a complete dévissage over the prime below `q₁` with
  prime data over `q₁`.

## Main results

* `Module.CompleteDevissage.devissage_clause_of_primeData` and
  `Module.CompleteDevissage.devissage_clause_of_nonemptyCompleteDevissageAt`: the dévissage clause
  of `Stacks.Flatness.ExistsSpreadOutCompleteDevissage`, verbatim, from a dévissage over the
  prime below `q₁` and from the output of 05I1 respectively.
* `Stacks.Flatness.existsSpreadOutCompleteDevissage_of_existsEtaleNeighborhoodCompleteDevissage`:
  the obligation of `StacksFrontier.AlgebraicGeometry.Flatness.FinitePresentationStalk05I7`, derived
  from the 05I1-shaped input.
* `Stacks.Flatness.existsEtaleNeighborhoodCompleteDevissage_iff`: the two obligations are
  equivalent, so the reduction is lateral.
* `AlgebraicGeometry.finitePresentation_stalk_of_existsEtaleNeighborhoodCompleteDevissage`:
  Stacks 05I7 granted that input.

## References

* [Stacks Project, Tag 05I7](https://stacks.math.columbia.edu/tag/05I7)
* [Stacks Project, Tag 05I5](https://stacks.math.columbia.edu/tag/05I5)
* [Stacks Project, Tag 05I4](https://stacks.math.columbia.edu/tag/05I4)
* [Stacks Project, Tag 05I1](https://stacks.math.columbia.edu/tag/05I1)
* [Stacks Project, Tag 05HR](https://stacks.math.columbia.edu/tag/05HR)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Stacks.Flatness

/-! ### The four clauses of the obligation other than the dévissage -/

/-- **Finite presentation of an algebra survives a localization of the base.**

This is the finite-presentation analogue of `Stacks.Flatness.finiteType_of_isLocalization`, and
like it, it is restricted to a single universe: the localized algebra is identified with the base
change `(Localization P) ⊗[R] S`, which is of finite presentation over `Localization P` because
`S` is of finite presentation over `R`. -/
@[ega "IV 21.15.9" "partial"]
instance finitePresentation_localization_algebraMapSubmonoid {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S] (P : Submonoid R) :
    Algebra.FinitePresentation (Localization P)
      (Localization (Algebra.algebraMapSubmonoid S P)) :=
  have : Algebra.IsPushout R (Localization P) S
      (Localization (Algebra.algebraMapSubmonoid S P)) :=
    .symm <| Algebra.isPushout_of_isLocalization P _ _ _
  .equiv (Algebra.IsPushout.equiv R (Localization P) S _)

/-- **A localization of a ring at a prime contracting to the maximal ideal is a local extension.**

If `p` is a prime of an `R`-algebra `R₁` whose contraction to a local ring `R` is the maximal
ideal, then `R → (R₁)_p` is a local homomorphism: an element of the maximal ideal of `R` lands in
`p`, hence in the maximal ideal of the localization. -/
@[ega "I 8.1.1" "(i) ⇒ (ii)", ega "IV 1.3.10" "partial"]
theorem isLocalHom_algebraMap_localization_of_comap_eq {R R₁ : Type u} [CommRing R] [CommRing R₁]
    [IsLocalRing R] [Algebra R R₁] (p : Ideal R₁) [p.IsPrime]
    (hp : p.comap (algebraMap R R₁) = IsLocalRing.maximalIdeal R) :
    IsLocalHom (algebraMap R (Localization p.primeCompl)) := by
  refine ((IsLocalRing.local_hom_TFAE (algebraMap R (Localization p.primeCompl))).out 4 1).mp ?_
  intro x hx
  rw [← hp] at hx
  change algebraMap R (Localization p.primeCompl) x
    ∈ IsLocalRing.maximalIdeal (Localization p.primeCompl)
  rw [IsScalarTower.algebraMap_apply R R₁ (Localization p.primeCompl)]
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ p _).mpr hx

/-- **The image of a prime over `r` in the localization at `r` is prime.** The inverted set misses
the prime, by `Stacks.Flatness.disjoint_algebraMapSubmonoid_of_comap_eq`. -/
theorem isPrime_map_algebraMap {R C C' : Type u} [CommRing R] [CommRing C] [CommRing C']
    [Algebra R C] [Algebra C C'] {r : Ideal R} [r.IsPrime] {p : Ideal C} [p.IsPrime]
    [IsLocalization (Algebra.algebraMapSubmonoid C r.primeCompl) C']
    (hp : p.comap (algebraMap R C) = r) : (Ideal.map (algebraMap C C') p).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint
    (Algebra.algebraMapSubmonoid C r.primeCompl) C' p ‹_›
    (disjoint_algebraMapSubmonoid_of_comap_eq hp)

/-- **The contraction of the image of a prime over `r` to a subalgebra is the contraction of the
prime.**

Here `A → C` is any algebra map, `p` is a prime of `C` contracting to a prime `r` of `R` in the
base, and `C'` is the localization of `C` at `r`. The contraction of `pC'` to `A` is computed in
two steps, through `C`, where `Stacks.Flatness.disjoint_algebraMapSubmonoid_of_comap_eq` and
`IsLocalization.under_map_of_isPrime_disjoint` return `p` itself.

With `A = R` this is the statement that `pC'` still lies over `r`; the extra generality is what
the clause `q = q'.comap (algebraMap A A')` of
`Stacks.Flatness.ExistsSpreadOutCompleteDevissage` asks for. -/
theorem comap_map_algebraMap_eq_of_comap_eq {R A C C' : Type u} [CommRing R] [CommRing A]
    [CommRing C] [CommRing C'] [Algebra R C] [Algebra A C] [Algebra C C'] [Algebra A C']
    [IsScalarTower A C C'] {r : Ideal R} [r.IsPrime] {p : Ideal C} [p.IsPrime]
    [IsLocalization (Algebra.algebraMapSubmonoid C r.primeCompl) C']
    (hp : p.comap (algebraMap R C) = r) :
    (Ideal.map (algebraMap C C') p).comap (algebraMap A C') = p.comap (algebraMap A C) := by
  have hu : (Ideal.map (algebraMap C C') p).comap (algebraMap C C') = p :=
    IsLocalization.under_map_of_isPrime_disjoint
      (Algebra.algebraMapSubmonoid C r.primeCompl) C' ‹_›
      (disjoint_algebraMapSubmonoid_of_comap_eq hp)
  rw [IsScalarTower.algebraMap_eq A C C', ← Ideal.comap_comap, hu]

/-- **Flatness of a module at a prime survives localizing the base at the prime below it.**

Let `A → A₁` be an algebra map, `R₁` a ring acting on `A₁`, `p` a prime of `R₁` and `q₁` a prime
of `A₁`. Write `R'` for a localization of `R₁` at `p` and `A'` for a localization of `A₁` at `p`,
and let `q'` be a prime of `A'` contracting to `q₁`. If the localization of `A₁ ⊗[A] N` at `q₁`
is flat over `R₁`, then the localization of `A' ⊗[A] N` at `q'` is flat over `R'`.

The proof identifies the two modules. The ring `A'_{q'}` is the localization of `A₁` at `q₁`
(`IsLocalization.isLocalization_isLocalization_atPrime_isLocalization`). Both
`A' ⊗[A] N` localized at `q'` and `A₁ ⊗[A] N` localized at `q₁` are therefore base changes of `N`
to that ring: the first by composing the base change to `A'` with the localization at `q'`
(`IsBaseChange.comp`), the second after cancelling the base change to `A₁`
(`IsBaseChange.of_comp`). Flatness then transfers along the resulting equivalence, and flatness
over `R'` is flatness over `R₁` by `Module.flat_iff_of_isLocalization`. -/
theorem flat_localizedModule_of_isLocalization {A A₁ A' R₁ R' N : Type u} [CommRing A]
    [CommRing A₁] [CommRing A'] [CommRing R₁] [CommRing R'] [Algebra A A₁] [Algebra A₁ A']
    [Algebra A A'] [IsScalarTower A A₁ A'] [Algebra R₁ A₁] [Algebra R₁ R'] [Algebra R₁ A']
    [Algebra R' A'] [IsScalarTower R₁ R' A'] [IsScalarTower R₁ A₁ A'] [AddCommGroup N]
    [Module A N] (p : Ideal R₁) [p.IsPrime] [IsLocalization p.primeCompl R']
    [IsLocalization (Algebra.algebraMapSubmonoid A₁ p.primeCompl) A'] (q₁ : Ideal A₁)
    [q₁.IsPrime] (q' : Ideal A') [q'.IsPrime] (hq' : q'.comap (algebraMap A₁ A') = q₁)
    (hflat : Module.Flat R₁ (LocalizedModule q₁.primeCompl (A₁ ⊗[A] N))) :
    Module.Flat R' (LocalizedModule q'.primeCompl (A' ⊗[A] N)) := by
  have hC : IsLocalization q₁.primeCompl (Localization q'.primeCompl) :=
    hq' ▸ IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid A₁ p.primeCompl) (Localization q'.primeCompl) q'
  have hA' : IsBaseChange A' (TensorProduct.mk A A' N 1) := TensorProduct.isBaseChange A N A'
  have hq'bc : IsBaseChange (Localization q'.primeCompl)
      (LocalizedModule.mkLinearMap q'.primeCompl (A' ⊗[A] N)) :=
    IsLocalizedModule.isBaseChange q'.primeCompl (Localization q'.primeCompl) _
  have hA₁ : IsBaseChange A₁ (TensorProduct.mk A A₁ N 1) := TensorProduct.isBaseChange A N A₁
  obtain ⟨g, hgl⟩ : ∃ g : (A₁ ⊗[A] N) →ₗ[A₁] LocalizedModule q'.primeCompl (A' ⊗[A] N),
      IsLocalizedModule q₁.primeCompl g := by
    refine ⟨hA₁.lift (((LocalizedModule.mkLinearMap q'.primeCompl
      (A' ⊗[A] N)).restrictScalars A).comp (TensorProduct.mk A A' N 1)), ?_⟩
    refine (isLocalizedModule_iff_isBaseChange q₁.primeCompl (Localization q'.primeCompl) _).mpr
      (hA₁.of_comp ?_)
    rw [hA₁.lift_comp]
    exact hA'.comp hq'bc
  have e : LocalizedModule q₁.primeCompl (A₁ ⊗[A] N) ≃ₗ[A₁]
      LocalizedModule q'.primeCompl (A' ⊗[A] N) :=
    IsLocalizedModule.linearEquiv q₁.primeCompl
      (LocalizedModule.mkLinearMap q₁.primeCompl (A₁ ⊗[A] N)) g
  have hR₁ : Module.Flat R₁ (LocalizedModule q'.primeCompl (A' ⊗[A] N)) :=
    Module.Flat.of_linearEquiv (e.symm.restrictScalars R₁)
  exact (Module.flat_iff_of_isLocalization R' p.primeCompl
    (LocalizedModule q'.primeCompl (A' ⊗[A] N))).mpr hR₁

/-- **The localization of a base change is the base change along the localized algebra**, so that
the module shape `A' ⊗[A] N` demanded by `Stacks.Flatness.ExistsSpreadOutCompleteDevissage` is the
shape `Module.CompleteDevissage.localizeAtPrime` produces. -/
noncomputable def localizedBaseChangeEquiv (A A₁ : Type u) [CommRing A] [CommRing A₁]
    [Algebra A A₁] (N : Type u) [AddCommGroup N] [Module A N] (P : Submonoid A₁) :
    LocalizedModule P (A₁ ⊗[A] N) ≃ₗ[Localization P] (Localization P) ⊗[A] N :=
  (IsLocalizedModule.isBaseChange P (Localization P)
      (LocalizedModule.mkLinearMap P (A₁ ⊗[A] N))).equiv.symm ≪≫ₗ
    TensorProduct.AlgebraTensorModule.cancelBaseChange A A₁ (Localization P) (Localization P) N

end Stacks.Flatness

namespace Module.CompleteDevissage

/-! ### Bookkeeping for the dévissage clause -/

variable {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.FiniteType R S] [AddCommGroup N] [Module S N] [Module.Finite S N]

/-- **A dévissage with prime data over `r` is one over any ideal equal to `r`.** This is what
turns the dévissage over `rR_r` that `Module.CompleteDevissage.localizeAtPrime` produces into one
over `IsLocalRing.maximalIdeal R_r`, which is what
`Stacks.Flatness.ExistsSpreadOutCompleteDevissage` asks for.

The equality is eliminated by `subst` rather than by rewriting: the goal mentions `r` both in the
type of the dévissage and in the instance argument `[r.IsPrime]`, and rewriting under the latter
makes no progress. -/
theorem exists_primeData_of_eq {r r' : Ideal R} [r.IsPrime] [r'.IsPrime] (h : r = r')
    {q : Ideal S} {D : CompleteDevissage R S N r} (pd : D.PrimeData q) :
    ∃ D' : CompleteDevissage R S N r', Nonempty (D'.PrimeData q) := by
  subst h
  exact ⟨D, ⟨pd⟩⟩

/-- **Transporting a dévissage along an equivalence of the module being dévissaged.** Only
`initialEquiv` mentions that module, so every other field is carried over unchanged. -/
noncomputable def ofLinearEquiv {r : Ideal R} [r.IsPrime] {N₂ : Type w} [AddCommGroup N₂]
    [Module S N₂] [Module.Finite S N₂] (D : CompleteDevissage R S N r) (e : N₂ ≃ₗ[S] N) :
    CompleteDevissage R S N₂ r :=
  { D with initialEquiv := e.trans D.initialEquiv }

/-- **The prime data of a transported dévissage is the prime data of the original one**: the stage
primes and all nine conditions of `Module.CompleteDevissage.PrimeData` mention only the stage
algebras and the maps between them, never the module. -/
def PrimeData.ofLinearEquiv {r : Ideal R} [r.IsPrime] {N₂ : Type w} [AddCommGroup N₂]
    [Module S N₂] [Module.Finite S N₂] {D : CompleteDevissage R S N r} {q : Ideal S}
    (pd : D.PrimeData q) (e : N₂ ≃ₗ[S] N) : (D.ofLinearEquiv e).PrimeData q where
  lowerPrime := pd.lowerPrime
  lowerPrime_isPrime := pd.lowerPrime_isPrime
  lowerPrime_under := pd.lowerPrime_under
  upperPrime := pd.upperPrime
  upperPrime_isPrime := pd.upperPrime_isPrime
  upperPrime_under := pd.upperPrime_under
  upperPrime_unique := pd.upperPrime_unique
  initial_under := pd.initial_under
  transition_under := pd.transition_under

/-- **The dévissage clause of `Stacks.Flatness.ExistsSpreadOutCompleteDevissage`, verbatim, from
a dévissage over the prime below `q₁`.**

Given a complete dévissage of the spread-out module `A₁ ⊗[A] N` over the prime of `R₁` below
`q₁`, with prime data over `q₁`, localizing the base at that prime gives a local ring,
`Module.CompleteDevissage.localizeAtPrime` carries the dévissage to it and
`Module.CompleteDevissage.PrimeData.localize` carries the nine stage-prime conditions across. The
dévissage so obtained is over the image of the base prime, which is the maximal ideal of the
localized base, and is of the localization of `A₁ ⊗[A] N`, which is the base change of `N` to the
localized algebra. -/
theorem devissage_clause_of_primeData (A R₁ A₁ N : Type u) [CommRing A] [CommRing R₁]
    [CommRing A₁] [AddCommGroup N] [Module A N] [Module.Finite A N] [Algebra A A₁]
    [Algebra R₁ A₁] [Algebra.FiniteType R₁ A₁] (q₁ : Ideal A₁) [q₁.IsPrime]
    (D : CompleteDevissage R₁ A₁ (A₁ ⊗[A] N) (q₁.under R₁)) (pd : D.PrimeData q₁) :
    ∃ D' : CompleteDevissage (Localization (q₁.under R₁).primeCompl)
        (Localization (Algebra.algebraMapSubmonoid A₁ (q₁.under R₁).primeCompl))
        (Localization (Algebra.algebraMapSubmonoid A₁ (q₁.under R₁).primeCompl) ⊗[A] N)
        (IsLocalRing.maximalIdeal (Localization (q₁.under R₁).primeCompl)),
      Nonempty (D'.PrimeData (Ideal.map (algebraMap A₁
        (Localization (Algebra.algebraMapSubmonoid A₁ (q₁.under R₁).primeCompl))) q₁)) :=
  exists_primeData_of_eq
    (IsLocalization.AtPrime.map_eq_maximalIdeal (q₁.under R₁)
      (Localization (q₁.under R₁).primeCompl))
    (pd.localize.ofLinearEquiv
      (Stacks.Flatness.localizedBaseChangeEquiv A A₁ N
        (Algebra.algebraMapSubmonoid A₁ (q₁.under R₁).primeCompl)).symm)

/-- **The dévissage clause of `Stacks.Flatness.ExistsSpreadOutCompleteDevissage`, verbatim, from
the output of Stacks 05I1.**

A complete dévissage *at* `q₁` carries the prime data of its underlying dévissage
(`Module.NonemptyCompleteDevissageAt.primeData`), so this is
`Module.CompleteDevissage.devissage_clause_of_primeData` applied to it. The three fields of
`Module.NonemptyCompleteDevissageAt` that `Module.CompleteDevissage.PrimeData` drops are not
used. -/
theorem devissage_clause_of_nonemptyCompleteDevissageAt (A R₁ A₁ N : Type u) [CommRing A]
    [CommRing R₁] [CommRing A₁] [AddCommGroup N] [Module A N] [Module.Finite A N] [Algebra A A₁]
    [Algebra R₁ A₁] [Algebra.FiniteType R₁ A₁] (q₁ : Ideal A₁) [q₁.IsPrime]
    (E : NonemptyCompleteDevissageAt R₁ A₁ (A₁ ⊗[A] N) q₁) :
    ∃ D : CompleteDevissage (Localization (q₁.under R₁).primeCompl)
        (Localization (Algebra.algebraMapSubmonoid A₁ (q₁.under R₁).primeCompl))
        (Localization (Algebra.algebraMapSubmonoid A₁ (q₁.under R₁).primeCompl) ⊗[A] N)
        (IsLocalRing.maximalIdeal (Localization (q₁.under R₁).primeCompl)),
      Nonempty (D.PrimeData (Ideal.map (algebraMap A₁
        (Localization (Algebra.algebraMapSubmonoid A₁ (q₁.under R₁).primeCompl))) q₁)) :=
  devissage_clause_of_primeData A R₁ A₁ N q₁ E.toCompleteDevissage E.primeData

end Module.CompleteDevissage

namespace Stacks.Flatness

/-! ### The 05I1-shaped input and the obligation -/

/-- **The local-algebra form of Stacks 05I1, in the shape that construction produces it.**

Let `R` be a local ring, `A` an `R`-algebra of finite presentation, `q` a prime of `A` over the
maximal ideal of `R` and `N` a finite `A`-module whose localization at `q` is flat over `R`. The
assertion is that there is a flat extension `R → R₁` of the base — not local, and with no finite
presentation asked of it — an algebra `A₁` of finite presentation over `R₁` and flat over `A`, and
a prime `q₁` of `A₁` lying over `q` and over a prime of `R₁` contracting to the maximal ideal of
`R`, such that `A₁ ⊗[A] N` localized at `q₁` is flat over `R₁` and carries a complete dévissage
over the prime below `q₁`, with prime data over `q₁`.

This is the output of Proposition Stacks 05I1 applied to the elementary étale neighbourhood of
Stacks 05HR, weakened in the dévissage clause exactly as
`Stacks.Flatness.ExistsSpreadOutCompleteDevissage` weakens it: a plain
`Module.CompleteDevissage` with `Module.CompleteDevissage.PrimeData`, not a
`Module.NonemptyCompleteDevissageAt`. The output of 05I1 supplies it through
`Module.NonemptyCompleteDevissageAt.primeData`.

It is **logically equivalent** to `Stacks.Flatness.ExistsSpreadOutCompleteDevissage`
(`Stacks.Flatness.existsEtaleNeighborhoodCompleteDevissage_iff`); what it gains is its shape. -/
def ExistsEtaleNeighborhoodCompleteDevissage : Prop :=
  ∀ (R A : Type u) [CommRing R] [CommRing A] [IsLocalRing R] [Algebra R A]
    [Algebra.FinitePresentation R A] (q : Ideal A) [q.IsPrime],
    q.comap (algebraMap R A) = IsLocalRing.maximalIdeal R →
    ∀ (N : Type u) [AddCommGroup N] [Module A N] [Module.Finite A N] [Module R N]
      [IsScalarTower R A N], Module.Flat R (LocalizedModule q.primeCompl N) →
      ∃ (R₁ : Type u) (_ : CommRing R₁) (_ : Algebra R R₁) (_ : Module.Flat R R₁)
        (A₁ : Type u) (_ : CommRing A₁) (_ : Algebra R₁ A₁)
        (_ : Algebra.FinitePresentation R₁ A₁) (_ : Algebra A A₁) (_ : Module.Flat A A₁)
        (q₁ : Ideal A₁) (_ : q₁.IsPrime),
        q₁.comap (algebraMap A A₁) = q ∧
          (q₁.under R₁).comap (algebraMap R R₁) = IsLocalRing.maximalIdeal R ∧
            Module.Flat R₁ (LocalizedModule q₁.primeCompl (A₁ ⊗[A] N)) ∧
              ∃ D : Module.CompleteDevissage R₁ A₁ (A₁ ⊗[A] N) (q₁.under R₁),
                Nonempty (D.PrimeData q₁)

/-- **The spreading out of a complete dévissage over a local base follows from the étale
neighbourhood of Stacks 05I1.**

Given the 05I1-shaped input, take `R'` to be the localization of `R₁` at the prime `p₁` below
`q₁`, `A'` the localization of `A₁` at `p₁` and `q'` the image of `q₁` in `A'`. Then `R'` is
local, `R → R'` is flat and local because `p₁` contracts to the maximal ideal of `R`, `A'` is of
finite presentation over `R'` and flat over `A`, `q'` is a prime contracting to `q`, the
localization of `A' ⊗[A] N` at `q'` is flat over `R'`, and the dévissage at `q₁` localizes to one
over the maximal ideal of `R'` with prime data over `q'`.

So `Stacks.Flatness.ExistsSpreadOutCompleteDevissage` — the obligation left open by
`StacksFrontier.AlgebraicGeometry.Flatness.FinitePresentationStalk05I7` — is reduced to the
existence of the elementary étale neighbourhood together with its dévissage. -/
theorem existsSpreadOutCompleteDevissage_of_existsEtaleNeighborhoodCompleteDevissage
    (H : ExistsEtaleNeighborhoodCompleteDevissage.{u}) :
    ExistsSpreadOutCompleteDevissage.{u} := by
  intro R A _ _ _ _ _ q _ hq N _ _ _ _ _ hflat
  obtain ⟨R₁, _, _, _, A₁, _, _, _, _, _, q₁, _, hq₁, hp₁, hflat₁, D, ⟨pd⟩⟩ := H R A q hq N hflat
  have hq'p : (Ideal.map (algebraMap A₁
      (Localization (Algebra.algebraMapSubmonoid A₁ (q₁.under R₁).primeCompl))) q₁).IsPrime :=
    isPrime_map_algebraMap (r := q₁.under R₁) rfl
  refine ⟨Localization (q₁.under R₁).primeCompl, inferInstance, inferInstance, inferInstance,
    isLocalHom_algebraMap_localization_of_comap_eq _ hp₁, inferInstance,
    Localization (Algebra.algebraMapSubmonoid A₁ (q₁.under R₁).primeCompl), inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, _, hq'p, ?_, ?_, ?_⟩
  · rw [comap_map_algebraMap_eq_of_comap_eq (A := A) (r := q₁.under R₁) rfl, hq₁]
  · exact flat_localizedModule_of_isLocalization (q₁.under R₁) q₁ _
      (comap_map_algebraMap_eq_of_comap_eq (A := A₁) (r := q₁.under R₁) rfl) hflat₁
  · exact Module.CompleteDevissage.devissage_clause_of_primeData A R₁ A₁ N q₁ D pd

/-- **The converse: the 05I1-shaped input follows from the obligation it replaces.**

Take the étale neighbourhood to be the local ring `R'` itself. The one clause that is not already
a clause of `Stacks.Flatness.ExistsSpreadOutCompleteDevissage` is that the prime below `q'`
contracts to the maximal ideal of `R`: the prime data forces `q'` to lie over the maximal ideal of
`R'` (`Module.CompleteDevissage.PrimeData.under_eq`), and `R → R'` is a local homomorphism.

Together with
`Stacks.Flatness.existsSpreadOutCompleteDevissage_of_existsEtaleNeighborhoodCompleteDevissage`
this makes the two obligations **logically equivalent**: the reduction performed in this file is
lateral, and buys no logical strength. What it buys is that the hypothesis no longer mentions a
local base, a maximal ideal, or finite presentation over a local ring, which are what the output
of Stacks 05I1 does not come with. -/
theorem existsEtaleNeighborhoodCompleteDevissage_of_existsSpreadOutCompleteDevissage
    (H : ExistsSpreadOutCompleteDevissage.{u}) :
    ExistsEtaleNeighborhoodCompleteDevissage.{u} := by
  intro R A _ _ _ _ _ q _ hq N _ _ _ _ _ hflat
  obtain ⟨R', _, _, _, _, _, A', _, _, _, _, _, q', _, hqq', hflat', D, ⟨pd⟩⟩ :=
    H R A q hq N hflat
  have hunder : q'.under R' = IsLocalRing.maximalIdeal R' := pd.under_eq
  refine ⟨R', inferInstance, inferInstance, inferInstance, A', inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, q', inferInstance, hqq'.symm, ?_, hflat', ?_⟩
  · rw [hunder]
    exact IsLocalRing.maximalIdeal_comap (algebraMap R R')
  · exact Module.CompleteDevissage.exists_primeData_of_eq hunder.symm pd

/-- **The 05I1-shaped obligation and the one it replaces are logically equivalent.** -/
theorem existsEtaleNeighborhoodCompleteDevissage_iff :
    ExistsEtaleNeighborhoodCompleteDevissage.{u} ↔ ExistsSpreadOutCompleteDevissage.{u} :=
  ⟨existsSpreadOutCompleteDevissage_of_existsEtaleNeighborhoodCompleteDevissage,
    existsEtaleNeighborhoodCompleteDevissage_of_existsSpreadOutCompleteDevissage⟩

end Stacks.Flatness

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 05I7, granted the elementary étale neighbourhood of Tag 05I1.** A
quasi-coherent module of finite type which is flat over the base at a point has a finitely
presented stalk at that point.

This is `AlgebraicGeometry.finitePresentation_stalk_of_existsSpreadOutCompleteDevissage` with its
dévissage obligation discharged from
`Stacks.Flatness.ExistsEtaleNeighborhoodCompleteDevissage`, so that what remains open is the
existence of the étale neighbourhood and its dévissage in the shape Stacks 05I1 produces, with no
local base and no maximal ideal.

The two hypotheses are equivalent
(`Stacks.Flatness.existsEtaleNeighborhoodCompleteDevissage_iff`), so this statement is neither
stronger nor weaker than
`AlgebraicGeometry.finitePresentation_stalk_of_existsSpreadOutCompleteDevissage`; it is recorded
only because its hypothesis is in the shape the construction of Stacks 05HR and 05I1 produces. -/
theorem finitePresentation_stalk_of_existsEtaleNeighborhoodCompleteDevissage
    (H : Stacks.Flatness.ExistsEtaleNeighborhoodCompleteDevissage.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (x : X)
    (hflat : IsFlatOverAt f.toLRSHom.toShHom F x) :
    letI : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    Module.FinitePresentation (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
  finitePresentation_stalk_of_existsSpreadOutCompleteDevissage
    (Stacks.Flatness.existsSpreadOutCompleteDevissage_of_existsEtaleNeighborhoodCompleteDevissage
      H) f F x hflat

end AlgebraicGeometry

end

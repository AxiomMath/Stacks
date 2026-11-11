module

import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Smooth.Locus
import Mathlib.Tactic.ENatToNat

public import StacksFrontier.RingTheory.FormallySmooth.Field
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Smoothness and separability of field extensions

This file relates smoothness of algebras to separability of field extensions.

* Stacks 07ND, formal-smoothness form. Let `R → S` be a finite type map of domains, let `K` and
  `L` be the fraction fields of `R` and `S`, and let `L` carry the induced `K`-algebra structure.
  Then `S_{(0)} = L` is formally smooth over `R` if and only if `L/K` is separable. Stacks 07ND
  itself, with smoothness at `(0)` in the sense of Definition 00TB, is
  `Algebra.smoothAt_bot_iff_isSeparableExtension` in `StacksFrontier.RingTheory.Smooth.GenericPoint`,
  derived from this one.
* Stacks 037X. Let `K/k` be a finitely generated field extension. Then `K/k` is separable if and
  only if some smooth `k`-subalgebra of `K` has `K` as its fraction field, if and only if `K` is a
  localization of a smooth `k`-algebra.

Smoothness at the generic point is strictly weaker than smoothness: for `R = ℚ` and the cuspidal
curve `S = ℚ[x, y]/(y² - x³)` the fraction field is `ℚ(y/x)`, separable over `ℚ`, so `R → S` is
smooth at `(0)`, while `R → S` is not smooth at the cusp `(x, y)`. In characteristic `p` the
condition is a real one: for `K = 𝐅_p(t)` and `S = K[x]/(x^p - t)` the extension `L = K(t^{1/p})`
is purely inseparable and `K → S` is smooth nowhere.

## Main results

* `Algebra.isSmoothAt_bot_iff_isSeparableExtension`: the formal-smoothness form of Stacks 07ND,
  with Mathlib's `Algebra.IsSmoothAt R (⊥ : Ideal S)` (formal smoothness of `S_{(0)} = L` over
  `R`) in place of Definition 00TB; Stacks 07ND proper is
  `Algebra.smoothAt_bot_iff_isSeparableExtension` (`StacksFrontier.RingTheory.Smooth.GenericPoint`).
* `Algebra.IsSeparableExtension.tfae_exists_smooth`: Stacks 037X, for a finitely generated field
  extension `K/k`, separability of `K/k`, the existence of a smooth `k`-subalgebra of `K` having
  `K` as its fraction field, and the existence of a smooth `k`-algebra having `K` as a
  localization, are all equivalent.

## Implementation notes

### Smoothness at the generic point

Smoothness at a prime `𝔮` in the sense of Definition 00TB is `Algebra.SmoothAt R S 𝔮`: some
`g ∉ 𝔮` has `S_g` smooth, hence of finite presentation, over `R`. Mathlib's
`Algebra.IsSmoothAt R 𝔮` is only formal smoothness of `S_𝔮` over `R`; the first implies the second
(`Algebra.isSmoothAt_of_smoothAt`), and the two agree once some `S_g`, `g ∉ 𝔮`, is of finite
presentation over `R` (Lemma 00TA, `Algebra.IsSmoothAt.exists_notMem_smooth`). For `𝔮 = (0)` such
a `g` exists by generic finite presentation (Lemma 00FG,
`GenericFinitePresentation.generic_finite_presentation`), which is where `Algebra.FiniteType R S`
and the injectivity of `R → S` are used. So Lemma 07ND is first proved for `Algebra.IsSmoothAt`
(`Algebra.isSmoothAt_bot_iff_isSeparableExtension`) and then transported to Definition 00TB
(`Algebra.smoothAt_bot_iff_isSeparableExtension`, in `StacksFrontier.RingTheory.Smooth.GenericPoint`);
the converse direction of the source's proof makes the same reduction to finite presentation via
Lemma 00FG.

Any model of the local ring computes `Algebra.IsSmoothAt`, a localization being determined up to
a canonical isomorphism of `S`-algebras. At `𝔮 = (0)` on a domain the local ring is the fraction
field: the multiplicative complement of the prime `(0)` is the set of nonzero divisors
(`Ideal.primeCompl_bot`), so a fraction field of `S` *is* a localization of `S` at `(0)`. Both
sides of Lemma 07ND are therefore statements about the single extension `L`, and the proof is the
two-step chain

`R → L` formally smooth `↔` `K → L` formally smooth `↔` `L/K` separable.

The first step is formal smoothness passing along the localization `R → K` in both directions:
`K` is formally étale over `R`, being a localization of it, and restricting scalars along a
formally étale map neither creates nor destroys formal smoothness. That is Lemma 00T4, in the form
`Algebra.FormallyEtale.of_isLocalization` together with
`Algebra.FormallySmooth.iff_restrictScalars`. The second step is Lemma 0321, formal smoothness
equals separability for field extensions. The Stacks project argues instead through geometric
reducedness (Lemmas 00TT, 04KN, 030W, 00TV and 00TG); identifying `S_{(0)}` with `L` first removes
the base change `S ⊗_R K`, the passage to a nonzero `g ∈ S`, and the reduction to finite
presentation (Lemma 00FG).

For the formal-smoothness form two hypotheses of Lemma 07ND are not used, both because Lemma 0321
is an equivalence for an arbitrary field extension. `Algebra.FiniteType R S` is not needed there:
finite generation of `L/K` plays no role once separability is characterized by formal smoothness
rather than by the existence of a separating transcendence basis; it is used for Definition 00TB,
through Lemma 00FG. `IsDomain R` is not needed either, being implied by `IsFractionRing R K` with
`K` a field. Both are kept, matching the statement of Stacks 07ND.

The fraction fields are abstract: `K` and `L` are any fields with `IsFractionRing R K` and
`IsFractionRing S L`, rather than the models `FractionRing R` and `FractionRing S`, and the
extension `L/K` is the `Algebra K L` instance made compatible with the two towers by
`IsScalarTower R K L` and `IsScalarTower R S L`; since two ring maps `K → L` agreeing on `R`
agree (`IsLocalization.ringHom_ext`), `IsScalarTower R K L` determines it. The injectivity of
`R → S` in Stacks 07ND is not a separate hypothesis: `algebraMap R L` is injective, being a ring
map of fields after the localization map of a domain at its nonzero divisors, and it equals
`(algebraMap S L).comp (algebraMap R S)` by `IsScalarTower R S L`, so `algebraMap R S` is
injective; conversely injectivity is what lets `IsFractionRing.lift` build the `K`-algebra
structure on `L`.

Separability of the possibly transcendental extension `L/K` is `Algebra.IsSeparableExtension`,
Definition 030O (2) — every subextension of `L/K` finitely generated over `K` is separably
generated — and not Mathlib's `Algebra.IsSeparable`, which is separability of an *algebraic*
extension and would exclude the generic point of a positive-dimensional variety.

### Separable extensions as localizations of smooth algebras

Choose a finite type `k`-subalgebra `A ⊆ K` whose fraction field is `K` and apply Lemma 07ND to
`k → A`. Since `k` is its own fraction field and the local ring of `A` at `(0)` is `K`, that lemma
reads

`K` is formally smooth over `k` `↔` `K/k` is separable,

and this is the single equivalence both halves of Lemma 037X are proved through. Given
separability it produces, at `A` the subalgebra generated by a finite set of elements whose
localization is `K`, a nonzero `g ∈ A` with `A_g` smooth over `k` (Lemma 00TA,
`Algebra.IsSmoothAt.exists_notMem_smooth`, which needs `A` of finite presentation over `k`; over a
field that is finite type, `Algebra.FinitePresentation.of_finiteType`). Realizing `A_g` as the
subalgebra `A[1/g] ⊆ K`, whose fraction field is again `K`, gives the second item, and inverting
all nonzerodivisors gives the third. Conversely, if `K` is a localization of a smooth `k`-algebra
`R`, then `R` is formally smooth over `k` and `K` is formally smooth over `R`, a localization being
formally smooth, so `K` is formally smooth over `k` and the equivalence returns separability. For a
finitely generated extension this equivalence is a special case of Lemma 0321,
`Algebra.FormallySmooth.iff_isSeparableExtension`; it is derived here from Lemma 07ND, following
the Stacks project.

The cycle is proved as `1 → 2 → 3 → 1`. The step `2 → 3` is bookkeeping, a fraction field being
the localization at the nonzerodivisors; the step `3 → 1` uses from the third item only that `K`
is formally smooth over `k`. That the chosen subalgebra has `K` as its fraction field is an
instance of a general fact: a localization of a domain which happens to be a field is its fraction
field. Mathlib has this only for a subalgebra of a ring's own fraction field
(`Localization.subalgebra.instIsFractionRingSubtypeMemSubalgebra`), so it is proved here.

Stacks 037X states a two-term equivalence, separability against "`K` is the localization of a
smooth `k`-algebra"; three terms are stated here because that phrase has two readings and neither
implies the other on its own. The literal reading is the third item: some smooth `k`-algebra `R`,
related to `K` by nothing more than a `k`-algebra map exhibiting `K` as `S⁻¹R`. The reading the
proof produces, and the one needed where the lemma is applied ("there exists a smooth
`k'`-algebra `B` such that `K'` is the fraction field of `B`"), is the second item: the smooth
algebra is a `k`-subalgebra of `K` and the localization is at all nonzerodivisors, that is
`K = Frac R`. Taken as an implication from separability the second item is the stronger statement,
taken as a hypothesis the third is, so both are recorded.

Smoothness is Mathlib's `Algebra.Smooth`, formal smoothness together with finite presentation.
"Finitely generated field extension" is `Algebra.EssFiniteType k K`, Mathlib's spelling of finite
generation for field extensions (`IntermediateField.essFiniteType_iff`), taken as an instance
hypothesis. It is needed only for the implications out of separability, and there it cannot be
dropped: `K = k(x₁, x₂, …)` is separable over `k` but is not a localization of any finite
presentation `k`-algebra. In the third item the smooth algebra is quantified in the universe of
`K`, as an existential over types must fix a universe; no generality is lost for the implications
out of separability, where the witness is a subalgebra of `K`.

## References

* [Stacks 07ND](https://stacks.math.columbia.edu/tag/07ND)
  (`algebra-lemma-smooth-at-generic-point`), smoothness at the generic point.
* [Stacks 037X](https://stacks.math.columbia.edu/tag/037X)
  (`algebra-lemma-localization-smooth-separable`).
* [Stacks 0321](https://stacks.math.columbia.edu/tag/0321), formally smooth equals separable for
  field extensions.
* [Stacks 00T4](https://stacks.math.columbia.edu/tag/00T4), formal smoothness and localization.
* [Stacks 030O](https://stacks.math.columbia.edu/tag/030O), separability of a field extension.
* [Stacks 00TB](https://stacks.math.columbia.edu/tag/00TB), smoothness at a prime.
* [Stacks 00TA](https://stacks.math.columbia.edu/tag/00TA), the smooth locus is open.

## Tags

smooth ring map, generic point, fraction field, separable field extension
-/

@[expose] public section

universe v

@[expose] public section

namespace Stacks.Smooth.GenericPointSeparability

/-- The prime `(0)` of a domain `S` has the nonzero divisors as its multiplicative complement, so
a fraction ring of `S` is a localization of `S` at `(0)`. -/
private theorem isLocalization_atPrime_bot (S L : Type*) [CommRing S] [CommRing L] [IsDomain S]
    [Algebra S L] [IsFractionRing S L] : IsLocalization.AtPrime L (⊥ : Ideal S) :=
  show IsLocalization (⊥ : Ideal S).primeCompl L from
    Ideal.primeCompl_bot (α := S) ▸ ‹IsFractionRing S L›

/-- Smoothness of an `R`-algebra `S` at a prime `p` may be read off any model `Sₚ` of the local
ring: a localization is unique up to a canonical `S`-algebra isomorphism, and formal smoothness
transports along it. -/
private theorem isSmoothAt_iff_formallySmooth (R : Type*) {S : Type*} (Sₚ : Type*) [CommRing R]
    [CommRing S] [CommRing Sₚ] [Algebra R S] [Algebra S Sₚ] [Algebra R Sₚ] [IsScalarTower R S Sₚ]
    (p : Ideal S) [p.IsPrime] [IsLocalization.AtPrime Sₚ p] :
    Algebra.IsSmoothAt R p ↔ Algebra.FormallySmooth R Sₚ :=
  Algebra.FormallySmooth.iff_of_equiv
    ((IsLocalization.algEquiv p.primeCompl _ Sₚ).restrictScalars R)

/-- **Stacks 07ND.** For a finite type map `R → S` of domains with fraction fields `K` and `L`,
`S` is smooth over `R` at `(0)` if and only if `L/K` is separable. The hypotheses `IsDomain R` and
`Algebra.FiniteType R S` are not used; see the implementation notes. -/
@[nolint unusedArguments]
public theorem solution (R S K L : Type*)
    [CommRing R] [CommRing S] [Field K] [Field L] [IsDomain R] [IsDomain S]
    [Algebra R S] [Algebra.FiniteType R S] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] [Algebra R L] [Algebra K L]
    [IsScalarTower R S L] [IsScalarTower R K L] :
    Algebra.IsSmoothAt R (⊥ : Ideal S) ↔ Algebra.IsSeparableExtension K L :=
  have := isLocalization_atPrime_bot S L
  have : Algebra.FormallyEtale R K := .of_isLocalization (nonZeroDivisors R)
  (isSmoothAt_iff_formallySmooth R L (⊥ : Ideal S)).trans
    (Algebra.FormallySmooth.iff_restrictScalars.trans
      (Algebra.FormallySmooth.iff_isSeparableExtension K L))

end Stacks.Smooth.GenericPointSeparability

end

@[expose] public section

/-- **Formal smoothness at the generic point is separability of the fraction field extension.**
Let `R → S` be a finite type map of domains, let `K` and `L` be the fraction fields of `R` and `S`,
and let `L` be a `K`-algebra compatibly with both towers — which forces `R → S` to be injective.
Then `S_{(0)} = L` is formally smooth over `R` (Mathlib's `Algebra.IsSmoothAt R (⊥ : Ideal S)`)
if and only if `L/K` is separable.

This is the formal-smoothness form of Stacks 07ND: `Algebra.IsSmoothAt` is not Definition 00TB,
which also asks for finite presentation of some `S_g`, `g ≠ 0`. The statement with Definition 00TB
is `Algebra.smoothAt_bot_iff_isSeparableExtension`. -/
public theorem Algebra.isSmoothAt_bot_iff_isSeparableExtension (R S K L : Type*)
    [CommRing R] [CommRing S] [Field K] [Field L] [IsDomain R] [IsDomain S]
    [Algebra R S] [Algebra.FiniteType R S] [Algebra R K] [IsFractionRing R K]
    [Algebra S L] [IsFractionRing S L] [Algebra R L] [Algebra K L]
    [IsScalarTower R S L] [IsScalarTower R K L] :
    Algebra.IsSmoothAt R (⊥ : Ideal S) ↔ Algebra.IsSeparableExtension K L :=
    by apply Stacks.Smooth.GenericPointSeparability.solution

end

@[expose] public section

namespace Stacks.Smooth.SeparableLocalization

variable (k K : Type*) [Field k] [Field K] [Algebra k K]

/-- A localization of a domain which happens to be a field is a fraction field of that domain:
`0` is not among the inverted elements, so they are nonzerodivisors, and every element of the
localization is a quotient of two elements of the domain. -/
private theorem isFractionRing_of_isLocalization (A L : Type*) [CommRing A] [IsDomain A] [Field L]
    [Algebra A L] (S : Submonoid A) [IsLocalization S L] : IsFractionRing A L := by
  have hS : S ≤ nonZeroDivisors A := le_nonZeroDivisors_of_noZeroDivisors
    fun h ↦ not_subsingleton L (IsLocalization.subsingleton (M := S) h)
  have : FaithfulSMul A L :=
    (faithfulSMul_iff_algebraMap_injective A L).2 (IsLocalization.injective L hS)
  refine IsFractionRing.of_field A L fun z ↦ ?_
  obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.surj S z
  exact ⟨x, y, by rw [eq_div_iff (IsLocalization.map_units L y).ne_zero, hxy]⟩

/-- The `k`-subalgebra of `K` generated by a finite set of elements whose localization is `K` has
`K` as its fraction field. -/
private theorem isFractionRing_essFiniteType_subalgebra [Algebra.EssFiniteType k K] :
    IsFractionRing ↥(Algebra.EssFiniteType.subalgebra k K) K :=
  isFractionRing_of_isLocalization _ K (Algebra.EssFiniteType.submonoid k K)

/-- A fraction field `K` of a domain `A` is the localization of `A` at the prime `(0)`, so `A` is
smooth over `k` at `(0)` exactly when `K` is formally smooth over `k`. -/
private theorem isSmoothAt_bot_iff_formallySmooth (A : Subalgebra k K) [IsFractionRing ↥A K] :
    Algebra.IsSmoothAt k (⊥ : Ideal ↥A) ↔ Algebra.FormallySmooth k K :=
  have := GenericPointSeparability.isLocalization_atPrime_bot ↥A K
  GenericPointSeparability.isSmoothAt_iff_formallySmooth k K (⊥ : Ideal ↥A)

/-- **Lemma 07ND for a finitely generated field extension.** `K/k` is separable if and only if `K`
is formally smooth over `k`: apply Lemma 07ND to `k` and a finite type `k`-subalgebra of `K` with
fraction field `K`, the fraction field of the base field `k` being `k` itself. -/
private theorem formallySmooth_iff_isSeparableExtension [Algebra.EssFiniteType k K] :
    Algebra.FormallySmooth k K ↔ Algebra.IsSeparableExtension k K :=
  have := isFractionRing_essFiniteType_subalgebra k K
  (isSmoothAt_bot_iff_formallySmooth k K (Algebra.EssFiniteType.subalgebra k K)).symm.trans
    (Algebra.isSmoothAt_bot_iff_isSeparableExtension k _ k K)

/-- Inverting a nonzero `g` in a `k`-subalgebra `A` of `K` with fraction field `K`: if the
localization `A_g` is smooth over `k`, then `A[1/g]` is a smooth `k`-subalgebra of `K`, again with
fraction field `K`. -/
private theorem exists_smooth_subalgebra_of_smooth_away (A : Subalgebra k K)
    [IsFractionRing ↥A K] (g : ↥A) (hg : g ≠ 0)
    [Algebra.Smooth k (Localization.Away g)] :
    ∃ R : Subalgebra k K, Algebra.Smooth k ↥R ∧ IsFractionRing ↥R K :=
  let B := Localization.subalgebra K (Submonoid.powers g)
    (Submonoid.powers_le.2 (mem_nonZeroDivisors_of_ne_zero hg))
  ⟨B.restrictScalars k,
    Algebra.Smooth.of_equiv
      ((IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g) ↥B).restrictScalars k),
    inferInstanceAs (IsFractionRing ↥B K)⟩

/-- A formally smooth field extension `K/k` with a finite type `k`-subalgebra `A ⊆ K` having
fraction field `K` is the fraction field of a *smooth* `k`-subalgebra: `A` is smooth over `k` at
the generic point, hence some `A[1/g]` is smooth over `k`. -/
private theorem exists_smooth_subalgebra (A : Subalgebra k K) [Algebra.FiniteType k ↥A]
    [IsFractionRing ↥A K] [Algebra.FormallySmooth k K] :
    ∃ R : Subalgebra k K, Algebra.Smooth k ↥R ∧ IsFractionRing ↥R K := by
  have : Algebra.FinitePresentation k ↥A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have : Algebra.IsSmoothAt k (⊥ : Ideal ↥A) := (isSmoothAt_bot_iff_formallySmooth k K A).2 ‹_›
  obtain ⟨g, hg, _⟩ := Algebra.IsSmoothAt.exists_notMem_smooth k (⊥ : Ideal ↥A)
  exact exists_smooth_subalgebra_of_smooth_away k K A g (by simpa using hg)

/-- **Stacks 037X.** For a finitely generated field extension `K/k` the following are
equivalent: `K/k` is separable; some smooth `k`-subalgebra of `K` has `K` as its fraction field;
some smooth `k`-algebra has `K` as a localization. -/
public theorem solution (k : Type*) (K : Type v) [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] :
    List.TFAE
      [Algebra.IsSeparableExtension k K,
        ∃ R : Subalgebra k K, Algebra.Smooth k R ∧ IsFractionRing R K,
        ∃ (R : Type v) (_ : CommRing R) (_ : Algebra k R) (_ : Algebra R K)
          (_ : IsScalarTower k R K) (S : Submonoid R),
          Algebra.Smooth k R ∧ IsLocalization S K] := by
  tfae_have 1 → 2 := fun hsep ↦
    have := (formallySmooth_iff_isSeparableExtension k K).2 hsep
    have := isFractionRing_essFiniteType_subalgebra k K
    exists_smooth_subalgebra k K (Algebra.EssFiniteType.subalgebra k K)
  tfae_have 2 → 3 := fun ⟨R, hsm, hfr⟩ ↦
    ⟨↥R, inferInstance, inferInstance, inferInstance, inferInstance, nonZeroDivisors ↥R, hsm, hfr⟩
  tfae_have 3 → 1 := fun ⟨R, _, _, _, _, S, hsm, _⟩ ↦
    have := hsm.formallySmooth
    have := Algebra.FormallySmooth.of_isLocalization (Rₘ := K) S
    (formallySmooth_iff_isSeparableExtension k K).1 (Algebra.FormallySmooth.comp k R K)
  tfae_finish

end Stacks.Smooth.SeparableLocalization

end

@[expose] public section

/-- **A finitely generated field extension is separable if and only if it is the localization of a
smooth algebra.** For a finitely generated field extension `K/k` the following are equivalent:
`K/k` is separable; some smooth `k`-subalgebra of `K` has `K` as its fraction field; some smooth
`k`-algebra has `K` as a localization. -/
@[stacks 037X, sga "1 II 5.7" "partial"]
public theorem Algebra.IsSeparableExtension.tfae_exists_smooth
    (k : Type*) (K : Type v) [Field k] [Field K] [Algebra k K] [Algebra.EssFiniteType k K] :
    List.TFAE
      [Algebra.IsSeparableExtension k K,
        ∃ R : Subalgebra k K, Algebra.Smooth k R ∧ IsFractionRing R K,
        ∃ (R : Type v) (_ : CommRing R) (_ : Algebra k R) (_ : Algebra R K)
          (_ : IsScalarTower k R K) (S : Submonoid R),
          Algebra.Smooth k R ∧ IsLocalization S K] :=
            by apply Stacks.Smooth.SeparableLocalization.solution

end

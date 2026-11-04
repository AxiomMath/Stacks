module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import StacksFrontier.RingTheory.Localization.InjectiveOfLocalization
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import StacksFrontier.FieldTheory.Separable.Defs
public import StacksFrontier.RingTheory.DiscreteValuationRing.Solution
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent
public import StacksFrontier.RingTheory.GeometricallyNormal.Separable
public import StacksFrontier.RingTheory.Nagata.Defs
public import StacksFrontier.RingTheory.Nagata.Japanese
public import StacksFrontier.RingTheory.Nagata.JapaneseCriteria

@[expose] public section

universe u

/-!
# Universally Japanese and Nagata descend along a principal open cover

Proof of `isUniversallyJapaneseRing_and_isNagataRing_of_localizationSpan`: let `t ⊆ R` generate
the unit ideal and let `Rₚ g` be a localization of `R` away from `g` for every `g ∈ t`. If every
`Rₚ g` is universally Japanese then so is `R`, and if every `Rₚ g` is a Nagata ring then so
is `R`.

Both descents are the source's, and both end in the descent of N-2 along a principal open cover,
Tag 032H, taken over the nonzero images of `t`. For the first, let `S` be a domain of finite type
over `R`. In a localization of `S` away from the image of a `g ∈ t` the element `g` has become
invertible, so that localization is a domain of finite type over `Rₚ g` and hence N-2 by the
hypothesis on `Rₚ g`; this is `isJapaneseRing_of_isUnit_of_finiteType`, and Tag 032H then makes
`S` N-2, which is the universally Japanese condition for `R`.

For the second, Noetherianity of `R` descends from the `Rₚ g` because an ideal of `R` is finitely
generated as soon as its extensions to the localizations are. For a prime `p ⊆ R` and a `g ∈ t`
outside `p` the ideal `p Rₚ g` is prime, so `Rₚ g ⧸ p Rₚ g` is a domain, and it is the
localization of `R ⧸ p` away from the image of `g` (`isLocalizationAway_quotient`); it is
therefore N-2 by the Nagata hypothesis on `Rₚ g`, and Tag 032H over `R ⧸ p` makes `R ⧸ p` itself
N-2.

## Main results

* `Stacks.Nagata.PrincipalOpenDescent.solution`: the proof of
  `isUniversallyJapaneseRing_and_isNagataRing_of_localizationSpan`.

## Implementation notes

The images in `S`, respectively in `R ⧸ p`, of the elements of `t` need not be nonzero, while Tag
032H asks its localizations to be domains, which an away-localization at `0` is not. Both descents
are therefore taken over the nonzero images, whose span is again the unit ideal
(`span_range_sdiff_singleton_zero_eq_top`). That set of images is written as a `Set.range` over
`t` rather than as `algebraMap R S '' t`: the two are the same set (`Set.image_eq_range`), and in
the range form an element of the cover destructs to an element of `t`, which is the index the
hypotheses on the localizations are stated over.

The `Rₚ g`-algebra structure carrying the first part is `IsLocalization.Away.lift`, for which the
localization map has to be a unit on `g`; that unit is the hypothesis of
`isJapaneseRing_of_isUnit_of_finiteType`, which therefore mentions neither `S` nor a tower over
it. Inside it, the scalar tower `R → Rₚ g → S_s` is `IsLocalization.Away.lift_eq` and finite type
over `Rₚ g` follows from finite type over `R` by
`Algebra.FiniteType.of_restrictScalars_finiteType`. The second part builds no algebra structure:
`IsLocalization` for a quotient of a localization is already an instance in Mathlib
(`IsLocalization.instQuotientIdealAlgebraMapSubmonoidMapRingHomAlgebraMap`), and only its
submonoid has to be recognized as the powers of the image of `g` (`Submonoid.map_powers`).

The descent of Noetherianity, Tag 00EO (6), is proved here as
`isNoetherianRing_of_localizationSpan` for an arbitrary spanning set and arbitrary models of the
localizations, the form the descent of Tag 032H is stated in: Mathlib's
`AlgebraicGeometry.isNoetherianRing_of_away` is the same descent for a `Finset` and for the model
`Localization.Away`. It is deduced from `Ideal.fg_of_localizationSpan`, finite generation of an
ideal being what the cover has to see.

## References

* [Stacks Project, Tag 032V](https://stacks.math.columbia.edu/tag/032V)
* [Stacks Project, Tag 032H](https://stacks.math.columbia.edu/tag/032H)
* [Stacks Project, Tag 00EO](https://stacks.math.columbia.edu/tag/00EO)
-/

@[expose] public section



namespace Stacks.Nagata.PrincipalOpenDescent

/-- Noetherianity descends along a principal open cover: if `t ⊆ R` generates the unit ideal and
every localization of `R` away from an element of `t` is Noetherian, then `R` is Noetherian.

This is Tag 00EO (6) for an arbitrary spanning set and arbitrary models of the localizations;
Mathlib's `AlgebraicGeometry.isNoetherianRing_of_away` is the case of a `Finset` and of the model
`Localization.Away`. -/
private theorem isNoetherianRing_of_localizationSpan {R : Type u} [CommRing R] (t : Set R)
    (ht : Ideal.span t = ⊤) (Rₚ : ∀ _ : t, Type u) [∀ g, CommRing (Rₚ g)]
    [∀ g, Algebra R (Rₚ g)] [∀ g, IsLocalization.Away g.val (Rₚ g)]
    (H : ∀ g, IsNoetherianRing (Rₚ g)) : IsNoetherianRing R := by
  rw [isNoetherianRing_iff_ideal_fg]
  intro I
  refine Ideal.fg_of_localizationSpan t ht fun g => ?_
  have := H g
  have : IsNoetherianRing (Localization.Away g.val) :=
    isNoetherianRing_of_ringEquiv (Rₚ g)
      (IsLocalization.algEquiv (Submonoid.powers g.val) (Rₚ g)
        (Localization.Away g.val)).toRingEquiv
  exact (isNoetherianRing_iff_ideal_fg _).mp ‹_› _

/-- The nonzero images in `S` of a family generating the unit ideal of `R` generate the unit ideal
of `S`. The family of images is indexed by `t` itself, so that each of them comes with the element
of `t` it is the image of. -/
private theorem span_range_sdiff_singleton_zero_eq_top {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] {t : Set R} (ht : Ideal.span t = ⊤) :
    Ideal.span (Set.range (fun g : t => algebraMap R S g.val) \ {0}) = ⊤ := by
  have h : Ideal.span (Set.range (fun g : t => algebraMap R S g.val) \ {0})
      = Ideal.span (Set.range (fun g : t => algebraMap R S g.val)) :=
    Submodule.span_sdiff_singleton_zero ..
  rw [h, ← Set.image_eq_range, ← Ideal.map_span, ht, Ideal.map_top]

/-- **A domain `T` of finite type over `R` in which `g` becomes invertible is N-2 as soon as the
localization `Rₚ` of `R` away from `g` is universally Japanese.** Inverting `g` makes `T` an
algebra over `Rₚ`, and `T` is of finite type over `Rₚ` because it is of finite type over `R`; so
the hypothesis on `Rₚ` applies to `T`. -/
private theorem isJapaneseRing_of_isUnit_of_finiteType {R Rₚ T : Type u} [CommRing R]
    [CommRing Rₚ] [CommRing T] [IsDomain T] [Algebra R Rₚ] [Algebra R T]
    [Algebra.FiniteType R T] (g : R) [IsLocalization.Away g Rₚ]
    (H : IsUniversallyJapaneseRing Rₚ) (hg : IsUnit (algebraMap R T g)) : IsJapaneseRing T := by
  let : Algebra Rₚ T := (IsLocalization.Away.lift (S := Rₚ) g hg).toAlgebra
  have : IsScalarTower R Rₚ T :=
    IsScalarTower.of_algebraMap_eq fun r => (IsLocalization.Away.lift_eq _ hg r).symm
  have : Algebra.FiniteType Rₚ T := Algebra.FiniteType.of_restrictScalars_finiteType R Rₚ T
  exact H.japanese T

/-- **The quotient of a localization away from `g` by the extension of an ideal `p` of `R` is the
localization of `R ⧸ p` away from the image of `g`.** Localization commutes with the quotient, and
the image of the powers of `g` is the set of powers of the image of `g`. -/
private theorem isLocalizationAway_quotient {R Rₚ : Type u} [CommRing R] [CommRing Rₚ]
    [Algebra R Rₚ] (g : R) [IsLocalization.Away g Rₚ] (p : Ideal R) :
    IsLocalization.Away (algebraMap R (R ⧸ p) g) (Rₚ ⧸ Ideal.map (algebraMap R Rₚ) p) := by
  have hm : Algebra.algebraMapSubmonoid (R ⧸ p) (Submonoid.powers g)
      = Submonoid.powers (algebraMap R (R ⧸ p) g) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
  show IsLocalization (Submonoid.powers (algebraMap R (R ⧸ p) g)) _
  rw [← hm]
  infer_instance

/-- **A ring covered by universally Japanese principal opens is universally Japanese.** Part (1)
of Tag 032V. -/
private theorem isUniversallyJapaneseRing_of_localizationSpan {R : Type u} [CommRing R]
    (t : Set R) (ht : Ideal.span t = ⊤) (Rₚ : ∀ _ : t, Type u) [∀ g, CommRing (Rₚ g)]
    [∀ g, Algebra R (Rₚ g)] [∀ g, IsLocalization.Away g.val (Rₚ g)]
    (H : ∀ g, IsUniversallyJapaneseRing (Rₚ g)) : IsUniversallyJapaneseRing R := by
  refine { japanese := fun S _ _ _ _ => ?_ }
  have hdom : ∀ s : (Set.range (fun g : t => algebraMap R S g.val) \ {0} : Set S),
      IsDomain (Localization.Away s.val) :=
    fun s => IsLocalization.Away.isDomain _ (by simpa using s.2.2)
  refine (isN1_and_isJapaneseRing_of_localizationSpan _
    (span_range_sdiff_singleton_zero_eq_top ht) (Rₚ := fun s => Localization.Away s.val)).2 ?_
  rintro ⟨s, ⟨g, rfl⟩, -⟩
  exact isJapaneseRing_of_isUnit_of_finiteType g.val (H g)
    (by rw [IsScalarTower.algebraMap_apply R S (Localization.Away (algebraMap R S g.val))]
        exact IsLocalization.Away.algebraMap_isUnit _)

/-- **A ring covered by Nagata principal opens is a Nagata ring.** Part (2) of Tag 032V. -/
private theorem isNagataRing_of_localizationSpan {R : Type u} [CommRing R]
    (t : Set R) (ht : Ideal.span t = ⊤) (Rₚ : ∀ _ : t, Type u) [∀ g, CommRing (Rₚ g)]
    [∀ g, Algebra R (Rₚ g)] [∀ g, IsLocalization.Away g.val (Rₚ g)]
    (H : ∀ g, IsNagataRing (Rₚ g)) : IsNagataRing R := by
  refine ⟨isNoetherianRing_of_localizationSpan t ht Rₚ fun g => (H g).1, fun p hp => ?_⟩
  -- Every element of the cover of `R ⧸ p` is the image of an element of `t` outside `p`.
  have hpre : ∀ s : (Set.range (fun g : t => algebraMap R (R ⧸ p) g.val) \ {0} : Set (R ⧸ p)),
      ∃ g : t, algebraMap R (R ⧸ p) g.val = s.val ∧ g.val ∉ p := by
    rintro ⟨s, ⟨g, rfl⟩, hs⟩
    exact ⟨g, rfl, fun hmem => hs (by
      simpa [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] using hmem)⟩
  choose g hg hgp using hpre
  -- `p Rₚ (g s)` is prime, so `Rₚ (g s) ⧸ p Rₚ (g s)` is a domain, and it is the localization of
  -- `R ⧸ p` away from `s`.
  have hq : ∀ s, (Ideal.map (algebraMap R (Rₚ (g s))) p).IsPrime := fun s =>
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (g s).val) _ p hp
      ((Ideal.disjoint_powers_iff_notMem_of_isPrime _).2 (hgp s))
  have hloc : ∀ s, IsLocalization.Away s.val
      (Rₚ (g s) ⧸ Ideal.map (algebraMap R (Rₚ (g s))) p) := fun s => by
    rw [← hg s]
    exact isLocalizationAway_quotient (g s).val p
  exact (isN1_and_isJapaneseRing_of_localizationSpan _
    (span_range_sdiff_singleton_zero_eq_top ht)
    (Rₚ := fun s => Rₚ (g s) ⧸ Ideal.map (algebraMap R (Rₚ (g s))) p)).2 fun s => (H (g s)).2 _

/-- **Universally Japanese and Nagata descend along a principal open cover.** Proof of Tag 032V:
for a finite-type domain `S` over `R` the nonzero images of `t` generate the unit ideal of `S` and
the corresponding `S_s` are domains of finite type over the `Rₚ g`, hence N-2, so `S` is N-2 by
Tag 032H; and for a prime `p ⊆ R` the rings `Rₚ g ⧸ p Rₚ g` are the localizations of `R ⧸ p` at
the images of `g`, hence N-2, so `R ⧸ p` is N-2 by Tag 032H, `R` being Noetherian by the descent
of Tag 00EO. -/
public theorem solution {R : Type u}
    [CommRing R] (t : Set R) (ht : Ideal.span t = ⊤) (Rₚ : ∀ _ : t, Type u)
    [∀ g, CommRing (Rₚ g)] [∀ g, Algebra R (Rₚ g)] [∀ g, IsLocalization.Away g.val (Rₚ g)] :
    ((∀ g, IsUniversallyJapaneseRing (Rₚ g)) → IsUniversallyJapaneseRing R) ∧
      ((∀ g, IsNagataRing (Rₚ g)) → IsNagataRing R) :=
  ⟨isUniversallyJapaneseRing_of_localizationSpan t ht Rₚ,
    isNagataRing_of_localizationSpan t ht Rₚ⟩

end Stacks.Nagata.PrincipalOpenDescent

end

/-!
# Universally Japanese and Nagata descend along a principal open cover

Let `R` be a ring and let `t ⊆ R` be a set of elements generating the unit ideal, so that the
principal opens `D(g)`, `g ∈ t`, cover `Spec R`. Both conditions of Definition 032R descend from
this cover to `R`: if every localization `R_g` is universally Japanese then so is `R`, and if
every `R_g` is a Nagata ring then so is `R`.

The two descents run over the same cover but by different routes. For the first, a finite-type
domain `S` over `R` receives the images of the `g` as a family generating its own unit ideal, and
`S_g` is of finite type over `R_g`, so N-2 for the `S_g` comes from the hypothesis and N-2 for `S`
from the descent of the Japanese condition, Tag 032H. For the second, Noetherianity of `R`
descends from the `R_g` (Tag 00EO), and for a prime `p ⊆ R` the localizations of `R ⧸ p` at the
images of the `g` are the `R_g ⧸ p R_g`, N-2 by hypothesis, so `R ⧸ p` is N-2 again by Tag 032H.

## Main results

* `isUniversallyJapaneseRing_and_isNagataRing_of_localizationSpan`: the two descent statements,
  the universally Japanese one as the first conjunct and the Nagata one as the second.

## Implementation notes

The two statements of the source are the two conjuncts of one theorem, each with its own hypothesis
family: universally Japanese for every `R_g` gives it for `R`, and Nagata for every `R_g` gives it
for `R`. Neither part is weakened by the other, and a caller selects the one it wants with `.1` or
`.2`. This follows the sibling descent statement `isN1_and_isJapaneseRing_of_localizationSpan` of
Tag 032H, whose shape the hypotheses here copy.

The source lists finitely many `f₁, …, f_n`; the statement takes an arbitrary set `t` with
`Ideal.span t = ⊤`, the spelling of Mathlib's `Module.Finite.of_localizationSpan`. This is the
same hypothesis: a set spanning the unit ideal has a finite subset that already spans it, and the
hypothesis on the localizations is inherited by that subset. The localizations are abstract — an
`R`-algebra `Rₚ g` with `IsLocalization.Away g (Rₚ g)` rather than the model `Localization.Away g`
— so that a caller's own localizations apply without transport.

`R` and the `Rₚ g` share the universe `u`, because `IsUniversallyJapaneseRing` and `IsNagataRing`
quantify over the finite-type domains, respectively the prime quotients, of a ring in that ring's
own universe (see 032R and 032F). Nothing is excluded: `Localization.Away g` lies in the universe
of `R`.

No hypothesis of Noetherianity, reducedness or domain-hood is imposed on `R` or on the `Rₚ g`,
the source imposing none, and none is needed: Noetherianity of `R` in the second part is a
consequence of the hypothesis rather than an assumption, and the rings that the two predicates
test for N-2 — finite-type domains over `R`, and prime quotients of `R` — are domains for free.

Faithfulness, point by point.
1. No hypothesis is dead: `Ideal.span t = ⊤` is the source's "generate the unit ideal", and it
   is what makes the descent true — one non-unit `g` with `R_g` Nagata says nothing about `R`;
   `IsLocalization.Away g.val (Rₚ g)` is the source's `R_{f_i}`; and each conjunct consumes
   its own family of hypotheses on those localizations, neither being used by the other.
2. The scalars and base are the source's: `IsUniversallyJapaneseRing (Rₚ g)` and
   `IsNagataRing (Rₚ g)` are conditions on `Rₚ g` as a ring in its own right, the finiteness
   inside them being of integral closures over the finite-type domains over `Rₚ g`, respectively
   over the prime quotients of `Rₚ g`; the conclusions are the same conditions on `R`, read over
   `R`, and nothing is asserted over a fraction field or over one ring on behalf of another.
3. The canonical map is pinned, not merely assumed to exist: `IsLocalization.Away g.val (Rₚ g)`
   says that `algebraMap R (Rₚ g)` is the localization of `R` at the powers of `g`, so `Rₚ g` is
   the source's `R_{f_i}` and not an arbitrary `R`-algebra with the two properties.
4. The instantiation is not degenerate: `R = ℤ` with `t = {2, 3}` (which spans `⊤`, as `3 - 2 = 1`)
   and `Rₚ` the two away-localizations satisfies both hypothesis families, `ℤ` being a Nagata ring
   and universally Japanese and both conditions passing to localizations (Tag 032U); and the
   implications have content, `t = {1}` with `Rₚ _ = R` showing that the conclusions are exactly
   as strong as the hypotheses in the trivial cover.

## References

* [Stacks Project, Tag 032V](https://stacks.math.columbia.edu/tag/032V)
* [Stacks Project, Tag 032R](https://stacks.math.columbia.edu/tag/032R)
* [Stacks Project, Tag 032H](https://stacks.math.columbia.edu/tag/032H)
-/

@[expose] public section



/-- **Universally Japanese and Nagata descend along a principal open cover.** Let `t ⊆ R`
generate the unit ideal and for `g ∈ t` let `Rₚ g` be a localization of `R` away from `g`. If
every `Rₚ g` is universally Japanese then so is `R`, and if every `Rₚ g` is a Nagata ring then so
is `R`.

The source states the two parts for finitely many `f₁, …, f_n`; they are the two conjuncts
here, and an arbitrary spanning set is the same hypothesis. -/
@[stacks 032V]
public theorem isUniversallyJapaneseRing_and_isNagataRing_of_localizationSpan {R : Type u}
    [CommRing R] (t : Set R) (ht : Ideal.span t = ⊤) (Rₚ : ∀ _ : t, Type u)
    [∀ g, CommRing (Rₚ g)] [∀ g, Algebra R (Rₚ g)] [∀ g, IsLocalization.Away g.val (Rₚ g)] :
    ((∀ g, IsUniversallyJapaneseRing (Rₚ g)) → IsUniversallyJapaneseRing R) ∧
      ((∀ g, IsNagataRing (Rₚ g)) → IsNagataRing R) :=
  Stacks.Nagata.PrincipalOpenDescent.solution t ht Rₚ

end

/-!
# Nagata descent along an extension of discrete valuation rings

Let `A → B` be an extension of discrete valuation rings, inducing a separable extension `K → L`
of their fraction fields. If `B` is a Nagata ring, then `A` is a Nagata ring.

## Main results

* `IsNagataRing.of_isSeparable_fractionRing`: the Nagata property descends from `B` to `A` when
  their fraction-field extension is separable.

## Implementation notes

The fraction fields are kept abstract. The two scalar-tower assumptions say that the inclusion
`A → B` and the extension `K → L` induce the same map from `A` to `L`; in particular, this encodes
the source's inclusions without choosing concrete fraction-field models. The source's term
"extension of discrete valuation rings" is `IsDiscreteValuationRing.IsExtension`.

Three of the private helpers below duplicate `private` helpers of neighbouring modules
(`injective_of_isLocalization_of_injective` of
`StacksFrontier.RingTheory.Localization.InjectiveOfLocalization`,
`isJapaneseRing_of_isField` of `Nagata.Examples` and
`module_finite_integralClosure_of_isJapaneseRing` of `Nagata.JapaneseCriteria`); being private
there, they are not available to importers.

## References

* [Stacks Project, Tag 0GLS](https://stacks.math.columbia.edu/tag/0GLS)
-/

@[expose] public section

open scoped TensorProduct

/-- A field is N-2: a finite extension of its fraction field is finite-dimensional over it, so
the integral closure is the whole extension. -/
private theorem isJapaneseRing_of_isField (F : Type u) [CommRing F] [IsDomain F]
    (hF : IsField F) : IsJapaneseRing F := by
  refine { finite := fun E _ _ _ _ _ => ?_ }
  have : Module.Finite F (FractionRing F) :=
    Module.Finite.equiv (IsLocalization.atUnits F (nonZeroDivisors F) fun x hx =>
      isUnit_iff_exists_inv.2 (hF.mul_inv_cancel (nonZeroDivisors.ne_zero hx))).toLinearEquiv
  have : Module.Finite F E := Module.Finite.trans (FractionRing F) E
  have : Algebra.IsIntegral F E := Algebra.IsIntegral.of_finite F E
  rw [integralClosure_eq_top_iff.2 this]
  exact Module.Finite.equiv (Subalgebra.topEquiv (R := F) (A := E)).symm.toLinearEquiv

/-- An N-2 discrete valuation ring is a Nagata ring: its only primes are `⊥`, whose quotient is
the ring itself, and the maximal ideal, whose quotient is a field. -/
private theorem isNagataRing_of_isJapaneseRing (A : Type u) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (hA : IsJapaneseRing A) : IsNagataRing A := by
  refine ⟨inferInstance, fun p hp => ?_⟩
  by_cases hp0 : p = ⊥
  · subst p
    exact IsJapaneseRing.of_ringEquiv (RingEquiv.quotientBot A).symm hA
  · have : p.IsMaximal := IsPrime.to_maximal_ideal hp0
    exact isJapaneseRing_of_isField _
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient p).mp inferInstance)

open Stacks.GeometricallyReduced.Separability in
/-- **The finiteness statement carrying Tag 0GLS.** For a finite purely inseparable extension
`K₁/K`, the integral closure of `A` in `K₁` is a finite `A`-module. The compositum `K₁ ⊗[K] L` is
a field because `L/K` is separable and `K₁/K` purely inseparable; the integral closure of `B` in
it is finite because `B` is N-2, and `B ⊗[A] integralClosure A K₁` embeds into that finite
`B`-module, so faithful flatness of `A → B` descends the finiteness to `A`. -/
private theorem finite_integralClosure_of_separable_fraction_extension
    (A B K L : Type u) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Algebra A B]
    [IsDiscreteValuationRing.IsExtension A B] [Field K] [Field L] [Algebra A K]
    [IsFractionRing A K] [Algebra B L] [IsFractionRing B L] [Algebra A L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    (hB : IsJapaneseRing B) (hsep : Algebra.IsSeparableExtension K L)
    (K₁ : Type u) [Field K₁] [Algebra A K₁] [Algebra K K₁] [IsScalarTower A K K₁]
    [FiniteDimensional K K₁] [IsPurelyInseparable K K₁] :
    Module.Finite A (integralClosure A K₁) := by
  have : Algebra.IsSeparableExtension K L := hsep
  have : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let T := K₁ ⊗[K] L
  let : Field T :=
    (isField_tensorProduct_of_isSeparableExtension_of_isPurelyInseparable K L K₁).toField
  let ψ₀ : B ⊗[A] K →ₐ[B] L :=
    Algebra.TensorProduct.lift (Algebra.ofId B L) (IsScalarTower.toAlgHom A K L)
      fun _ _ => Commute.all _ _
  have hψ₀ : Function.Injective ψ₀ :=
    injective_of_isLocalization_of_injective
      (M := Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) ψ₀.toRingHom
      ψ₀.commutes (IsLocalization.injective L le_rfl)
  let φ : K ⊗[A] B →ₐ[K] L :=
    Algebra.TensorProduct.lift (Algebra.ofId K L)
      (IsScalarTower.toAlgHom A B L) fun _ _ => Commute.all _ _
  have hφ : Function.Injective φ := by
    have heq : ∀ x, ψ₀ (Algebra.TensorProduct.comm A K B x) = φ x := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul k b => simp [φ, ψ₀, mul_comm]
      | add x y hx hy => simp [hx, hy]
    intro x y hxy
    apply (Algebra.TensorProduct.comm A K B).injective
    apply hψ₀
    simpa only [heq] using hxy
  let e : K₁ ⊗[A] B ≃ₐ[K₁] K₁ ⊗[K] (K ⊗[A] B) :=
    (Algebra.TensorProduct.cancelBaseChange A K K₁ K₁ B).symm
  let μ : K₁ ⊗[K] (K ⊗[A] B) →ₗ[K₁] T :=
    LinearMap.baseChange K₁ φ.toLinearMap
  have hμ : Function.Injective μ := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap φ.toLinearMap hφ
  let : Algebra L T := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower A L T := IsScalarTower.to₁₃₄ A K L T
  let : Algebra B T := RingHom.toAlgebra ((algebraMap L T).comp (algebraMap B L))
  have : IsScalarTower B L T := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A B T := IsScalarTower.to₁₂₄ A B L T
  have : IsScalarTower A K₁ T := .of_algebraMap_eq fun a => by
    simp [T, IsScalarTower.algebraMap_apply A K K₁]
  let θ₀ : B ⊗[A] K₁ →ₐ[B] T :=
    Algebra.TensorProduct.lift (Algebra.ofId B T) (IsScalarTower.toAlgHom A K₁ T)
      fun _ _ => Commute.all _ _
  have hθ₀ : Function.Injective θ₀ := by
    have heq : ∀ x, θ₀ x = μ (e (Algebra.TensorProduct.comm A B K₁ x)) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul b k =>
          simp [θ₀, μ, e, φ, T, IsScalarTower.algebraMap_apply B L T,
            Algebra.TensorProduct.right_algebraMap_apply, mul_comm]
      | add x y hx hy => simp [hx, hy]
    intro x y hxy
    apply (Algebra.TensorProduct.comm A B K₁).injective
    apply e.injective
    apply hμ
    simpa only [← heq] using hxy
  let A₁ := integralClosure A K₁
  let ν : B ⊗[A] A₁ →ₗ[B] B ⊗[A] K₁ :=
    LinearMap.baseChange B (Subalgebra.val A₁).toLinearMap
  have hν : Function.Injective ν := by
    simp [ν, LinearMap.baseChange_eq_ltensor]
  have hmem : ∀ z : B ⊗[A] A₁, θ₀ (ν z) ∈ integralClosure B T := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b a =>
        have ha : IsIntegral B
            (Algebra.TensorProduct.includeLeft (R := K) (A := K₁) (B := L) (a : K₁)) :=
          (a.2.map (IsScalarTower.toAlgHom A K₁ T)).tower_top
        simpa [ν, θ₀, T] using
          Subalgebra.mul_mem (integralClosure B T) (Subalgebra.algebraMap_mem _ b) ha
    | add x y hx hy => simpa only [map_add] using Subalgebra.add_mem _ hx hy
  have hTfin : Module.Finite B (integralClosure B T) := by
    have : Module.Finite L T :=
      Module.Finite.equiv (Algebra.TensorProduct.commRight K L K₁).toLinearEquiv
    exact module_finite_integralClosure_of_isJapaneseRing hB L T
  let θ : B ⊗[A] A₁ →ₗ[B] integralClosure B T :=
    { toFun := fun z => ⟨θ₀ (ν z), hmem z⟩
      map_add' := fun x y => Subtype.ext (by simp)
      map_smul' := fun b x => Subtype.ext (by simp) }
  have : Module.Finite B (B ⊗[A] A₁) :=
    Module.Finite.of_injective θ fun x y hxy => hν (hθ₀ (Subtype.ext_iff.mp hxy))
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B

namespace IsNagataRing

/-- Let `A → B` be an extension of discrete valuation rings, and let `K → L` be the induced
extension of their fraction fields. If `B` is Nagata and `L/K` is separable, then `A` is
Nagata. -/
@[stacks 0GLS]
theorem of_isSeparable_fractionRing
    (A B K L : Type u) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Algebra A B]
    [IsDiscreteValuationRing.IsExtension A B]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L] [Algebra A L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    (hB : IsNagataRing B) (hsep : Algebra.IsSeparableExtension K L) :
    IsNagataRing A := by
  apply isNagataRing_of_isJapaneseRing A
  rw [isJapaneseRing_iff_finite_integralClosure_isPurelyInseparable]
  intro K₁ _ _ _ _ _ _
  let e : FractionRing A ≃ₐ[A] K := FractionRing.algEquiv A K
  let : Algebra K K₁ :=
    RingHom.toAlgebra ((algebraMap (FractionRing A) K₁).comp e.symm.toRingHom)
  have : IsScalarTower A K K₁ := .of_algebraMap_eq fun a => by
    show algebraMap A K₁ a = algebraMap (FractionRing A) K₁ (e.symm (algebraMap A K a))
    rw [e.symm.commutes]
    exact IsScalarTower.algebraMap_apply A (FractionRing A) K₁ a
  have : FiniteDimensional K K₁ := by
    show Module.Finite K K₁
    rw [← RingHom.finite_algebraMap]
    exact (RingHom.finite_algebraMap.mpr inferInstance).comp
      (RingEquiv.finite e.symm.toRingEquiv)
  have : IsPurelyInseparable K K₁ := by
    obtain ⟨q, hq⟩ := ExpChar.exists (FractionRing A)
    let : Algebra (FractionRing A) K := e.toRingHom.toAlgebra
    have : ExpChar K q := expChar_of_injective_algebraMap e.injective q
    rw [isPurelyInseparable_iff_pow_mem K q]
    intro x
    obtain ⟨n, y, hy⟩ := IsPurelyInseparable.pow_mem (FractionRing A) q x
    refine ⟨n, e y, ?_⟩
    show algebraMap (FractionRing A) K₁ (e.symm (e y)) = x ^ q ^ n
    simpa using hy
  have : (⊥ : Ideal B).IsPrime := Ideal.isPrime_bot
  exact finite_integralClosure_of_separable_fraction_extension A B K L
    (IsJapaneseRing.of_ringEquiv (RingEquiv.quotientBot B) (hB.2 ⊥)) hsep K₁

end IsNagataRing

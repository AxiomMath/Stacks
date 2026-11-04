module

import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.PowerSeries.Ideal

public import StacksFrontier.RingTheory.PowerSeries.IntegrallyClosed
public import StacksFrontier.RingTheory.Nagata.Basic
public import StacksFrontier.RingTheory.Nagata.Tate
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u

/-!
# N-2 ascends to the power series ring over a Noetherian domain

Let `R` be a Noetherian N-2 (Japanese) domain: the integral closure of `R` in every finite
extension of `K = Frac R` is a finite `R`-module. This file proves that the formal power series
ring `R⟦X⟧` is again N-2.

The argument is the source's. Write `R'` for the integral closure of `R` in `K`. Taking `L = K`
in the N-2 hypothesis makes `R'` a finite `R`-module, so `R'` is a Noetherian domain, integrally
closed, and with `K` again as its fraction field. Being integral over `R` with that same fraction
field, `R'` is itself N-2. Now `R'` is a Noetherian normal domain, the element `X` generates a
prime ideal of `R'⟦X⟧` with quotient `R'`, and `R'⟦X⟧` is `X`-adically complete, so Tate's
theorem makes `R'⟦X⟧` N-2. Finally `R'⟦X⟧` is a finite extension of `R⟦X⟧`, because `R'` is one
of `R`, and N-2 descends along a finite extension of domains with Noetherian base.

## Main results

* `Stacks.Nagata.PowerSeriesAscent.solution`: the proof of `PowerSeries.isJapaneseRing`, Tag 032Q.

## Implementation notes

Three steps of the argument are lemmas of the general theory that neither Mathlib nor this
development records, and they are proved here as private helpers.

* `module_finite_powerSeries`: if `B` is a finite `A`-module then `B⟦X⟧` is a finite `A⟦X⟧`-module.
  The source states it for the finite ring extension `R ⊆ R'`; it holds for any module-finite
  algebra, with the same proof. Generators `s₁, …, s_n` of `B` over `A` are again generators of
  `B⟦X⟧` over `A⟦X⟧`: each coefficient of a given `f ∈ B⟦X⟧` is an `A`-combination of the `sᵢ`,
  a choice made separately for each coefficient with no coherence required, and collecting the
  `i`-th coefficients into a power series `gᵢ ∈ A⟦X⟧` gives `f = ∑ᵢ gᵢ • sᵢ`.

* `module_finite_integralClosure_of_isIntegral`: in a tower `R → S → L` with `S` integral over
  `R`, the integral closures of `R` and of `S` in `L` have the same elements, so `R`-finiteness
  of the former gives `S`-finiteness of the latter. This is what makes N-2 pass from `R` to a
  domain integral over it with the same fraction field (`isJapaneseRing_of_isIntegral`, which the
  source applies only to `R'`).

* `span_X_eq_ker_constantCoeff`: `(X) = ker (constantCoeff)` in `R⟦X⟧`, whence
  `R⟦X⟧ ⧸ (X) ≃+* R`. Mathlib proves this equality inside `PowerSeries.span_X_isPrime` without
  naming it; here it identifies the quotient that Tate's theorem is applied to, in
  `isJapaneseRing_powerSeries`.

Tag 0306, the Noetherianity of `R⟦X⟧`, is Mathlib's instance `PowerSeries.instIsNoetherianRing`,
and Tag 0BI0, the normality of `R'⟦X⟧`, is the instance `PowerSeries.instIsIntegrallyClosed`;
both are used through instance resolution rather than by name. Tag 032K is
`isN2_of_finite_of_isN2` of `StacksFrontier.RingTheory.Nagata.Basic`, whose `IsN2_032k` is by
definition the `IsJapaneseRing` of Tag 032F.

## References

* [Stacks Project, Tag 032Q](https://stacks.math.columbia.edu/tag/032Q)
-/

@[expose] public section



namespace Stacks.Nagata.PowerSeriesAscent

open PowerSeries

section Coefficients

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- Scaling a constant power series `C b` by `g : A⟦X⟧` scales `b` by each coefficient of `g`. -/
private theorem coeff_smul_C (g : A⟦X⟧) (b : B) (k : ℕ) :
    coeff k (g • (C b : B⟦X⟧)) = coeff k g • b := by
  rw [Algebra.smul_def, algebraMap_apply'' (A := B) g, coeff_mul_C, coeff_map, Algebra.smul_def]

/-- If `B` is a finite `A`-module, then `B⟦X⟧` is a finite `A⟦X⟧`-module: generators of `B`
over `A` are again generators of `B⟦X⟧` over `A⟦X⟧`, the coefficients of a power series being
free to be chosen one at a time. -/
theorem module_finite_powerSeries [Module.Finite A B] : Module.Finite A⟦X⟧ B⟦X⟧ := by
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := B)
  refine Module.finite_def.mpr (Submodule.fg_def.mpr ⟨Set.range fun i => (C (s i) : B⟦X⟧),
    Set.finite_range _, eq_top_iff.mpr fun f _ => ?_⟩)
  have hcoeff : ∀ k : ℕ, ∃ c : Fin n → A, ∑ i, c i • s i = coeff k f := fun k =>
    (Submodule.mem_span_range_iff_exists_fun A).mp (by rw [hs]; trivial)
  choose c hc using hcoeff
  have hf : f = ∑ i, (mk fun k => c k i) • (C (s i) : B⟦X⟧) := by
    ext k
    rw [map_sum, ← hc k]
    simp only [coeff_smul_C, coeff_mk]
  rw [hf]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end Coefficients

/-- In a tower `R → S → L` with `S` integral over `R`, the integral closures of `R` and of `S`
in `L` have the same elements; so if the first is a finite `R`-module, the second is a finite
`S`-module. -/
private theorem module_finite_integralClosure_of_isIntegral {R S L : Type*} [CommRing R]
    [CommRing S] [CommRing L] [Algebra R S] [Algebra R L] [Algebra S L] [IsScalarTower R S L]
    [Algebra.IsIntegral R S] (h : Module.Finite R (integralClosure R L)) :
    Module.Finite S (integralClosure S L) := by
  have : Module.Finite R ↥(integralClosure S L) :=
    Module.Finite.of_surjective
      ({ toFun := fun z : ↥(integralClosure R L) => (⟨z, z.2.tower_top⟩ : ↥(integralClosure S L))
         map_add' := fun _ _ => rfl
         map_smul' := fun _ _ => rfl } : ↥(integralClosure R L) →ₗ[R] ↥(integralClosure S L))
      fun z => ⟨⟨z, isIntegral_trans (z : L) z.2⟩, rfl⟩
  exact Module.Finite.of_restrictScalars_finite R S _

/-- N-2 passes from a domain `R` to a domain `S` that is integral over `R` and has the same
field of fractions `K`. -/
private theorem isJapaneseRing_of_isIntegral {R S : Type u} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] [Algebra R S] [Algebra.IsIntegral R S] (K : Type u) [Field K]
    [Algebra R K] [Algebra S K] [IsScalarTower R S K] [IsFractionRing R K] [IsFractionRing S K]
    (hR : IsJapaneseRing R) : IsJapaneseRing S := by
  have : IsFractionRing R (FractionRing S) :=
    IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors R)
      ((FractionRing.algEquiv S K).restrictScalars R).symm
  refine { finite := fun L _ _ _ _ _ => ?_ }
  let : Algebra R L := ((algebraMap S L).comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R S L := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R (FractionRing S) L := .of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R S (FractionRing S) r,
      ← IsScalarTower.algebraMap_apply S (FractionRing S) L,
      IsScalarTower.algebraMap_apply R S L]
  exact module_finite_integralClosure_of_isIntegral
    (isN2_apply_of_isFractionRing R (fun L _ _ _ _ _ => hR.finite L) (FractionRing S) L)

/-- The ideal `(X)` of `R⟦X⟧` is the kernel of `constantCoeff`. Mathlib proves this inside
`PowerSeries.span_X_isPrime` without naming it. -/
private theorem span_X_eq_ker_constantCoeff {R : Type*} [CommRing R] :
    Ideal.span {(X : R⟦X⟧)} = RingHom.ker (constantCoeff (R := R)) := by
  ext f
  simp [RingHom.mem_ker, Ideal.mem_span_singleton, X_dvd_iff]

/-- **Tate's theorem at the variable of a power series ring.** If `R` is a Noetherian normal
N-2 domain, then `R⟦X⟧` is N-2: it is a Noetherian normal domain, `X` generates a prime ideal
with quotient `R`, and `R⟦X⟧` is `X`-adically complete. -/
@[ega "0 23.1.3" "A = R[[T]], x = T"]
private theorem isJapaneseRing_powerSeries {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] (hR : IsJapaneseRing R) : IsJapaneseRing R⟦X⟧ :=
  have : (Ideal.span {(X : R⟦X⟧)}).IsPrime := span_X_isPrime
  IsJapaneseRing.of_quotient_span_singleton X (IsJapaneseRing.of_ringEquiv
    ((Ideal.quotEquivOfEq span_X_eq_ker_constantCoeff).trans
      (RingHom.quotientKerEquivOfSurjective constantCoeff_surj)).symm hR)

/-- **N-2 ascends to `R⟦X⟧`.** If `R` is a Noetherian N-2 domain, then `R⟦X⟧` is N-2: the
integral closure `R'` of `R` in `Frac R` is a Noetherian normal N-2 domain finite over `R`, so
`R'⟦X⟧` is N-2 by Tate's theorem and finite over `R⟦X⟧`, and N-2 descends along that finite
extension. -/
public theorem solution {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (hR : IsJapaneseRing R) : IsJapaneseRing R⟦X⟧ := by
  -- `R'`, the integral closure of `R` in `K = Frac R`, is a Noetherian normal domain, finite
  -- over `R` and with the same fraction field, hence N-2.
  have hfin : Module.Finite R ↥(integralClosure R (FractionRing R)) :=
    hR.finite (FractionRing R)
  have : IsNoetherianRing ↥(integralClosure R (FractionRing R)) := IsNoetherianRing.of_finite R _
  have : IsIntegrallyClosed ↥(integralClosure R (FractionRing R)) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (K := FractionRing R) (L := FractionRing R)
  have : IsFractionRing ↥(integralClosure R (FractionRing R)) (FractionRing R) :=
    isFractionRing_integralClosure R (FractionRing R) (FractionRing R)
  -- Tate's theorem makes `R'⟦X⟧` N-2, and `R'⟦X⟧` is a finite extension of `R⟦X⟧`.
  refine { finite := fun L _ _ _ _ _ => ?_ }
  exact isN2_of_finite_of_isN2 R⟦X⟧ (↥(integralClosure R (FractionRing R)))⟦X⟧
    (PowerSeries.map_injective _ (FaithfulSMul.algebraMap_injective R _))
    module_finite_powerSeries
    (fun L _ _ _ _ _ =>
      (isJapaneseRing_powerSeries
        (isJapaneseRing_of_isIntegral (FractionRing R) hR)).finite L) L

end Stacks.Nagata.PowerSeriesAscent

end

/-!
# The power series ring over a Noetherian N-2 domain is N-2

Let `R` be a Noetherian domain which is N-2 (Japanese): the integral closure of `R` in every
finite extension of its fraction field is a finite `R`-module. Then the ring `R⟦X⟧` of formal
power series in one variable over `R` is again a Noetherian N-2 domain.

The N-2 condition on `R⟦X⟧` is the content. Writing `R'` for the integral closure of `R` in
`Frac R`, the hypothesis makes `R'` finite over `R`, hence `R'⟦X⟧` finite over `R⟦X⟧`. Since
`R'` is a Noetherian normal domain, `R'⟦X⟧` is one as well (Tag 0BI0), and the element
`X ∈ R'⟦X⟧` has `R'⟦X⟧` complete with respect to it and quotient `R'⟦X⟧/X R'⟦X⟧ ≅ R'` a domain
and N-2, so `R'⟦X⟧` is N-2 (Tag 032P). Being N-2 descends along a finite extension of domains
`R⟦X⟧ ⊆ R'⟦X⟧` with Noetherian base (Tag 032K), so `R⟦X⟧` is N-2.

## Main results

* `PowerSeries.isJapaneseRing`: `R⟦X⟧` is N-2 when `R` is a Noetherian N-2 domain.

## Implementation notes

The source's conclusion `R[[x]]` is Noetherian, a domain, and N-2 is a conjunction of three
assertions, and the first two are already Mathlib instances holding under strictly weaker
hypotheses: `PowerSeries.instIsNoetherianRing` (the source's Tag 0306) and
`PowerSeries.instIsDomain`. Only the third is stated. The other two are not merely omitted but
used: `IsJapaneseRing R⟦X⟧` is a statement about a domain, so `PowerSeries.instIsDomain` is what
makes the conclusion typecheck, and the conjunction is recovered from the three by
`inferInstance` together with this theorem. This follows the neighbouring statement
`PowerSeries.instIsIntegrallyClosed` for Tag 0BI0, whose conclusion is a conjunction of the same
shape.

N-2 is spelled `IsJapaneseRing` of Tag 032F, a class with a single field `finite`. The hypothesis
on `R` is nevertheless an explicit argument rather than an instance binder, because the statement
is about an arbitrary N-2 domain, and so the result is a theorem rather than an instance; the name
is the conclusion's, in the `PowerSeries` namespace, matching `Polynomial.isNoetherianRing` and
`PowerSeries.instIsNoetherianRing`. Since `IsJapaneseRing` quantifies over test extensions in the
universe of its argument, `R` and `R⟦X⟧` lie in a single universe `u`, and no generality is lost
(see Tag 032F).

Faithfulness.
1. Every hypothesis is used: `IsDomain R` and `IsJapaneseRing R` are the source's "a domain, and
   N-2", and `IsNoetherianRing R` is used twice by the conclusion's proof — for Noetherianity of
   `R⟦X⟧`, and through Tag 0BI0 for normality of `R'⟦X⟧`; the lemma is not stated for a general
   N-2 domain because that is not the source's claim and the route has no substitute for the
   ascending chain condition.
2. The base is the source's: `R⟦X⟧ = PowerSeries R` is the one-variable power series ring over
   `R`, and the finiteness asserted by the conclusion is of the integral closure of `R⟦X⟧`, as a
   module over `R⟦X⟧` — not over `R`, and not of the integral closure of `R`.
3. Where the source names a canonical map the statement pins it: unfolding `IsJapaneseRing`, the
   fraction field of `R⟦X⟧` is `FractionRing R⟦X⟧` with its canonical algebra map, and a test
   extension `L` carries `IsScalarTower R⟦X⟧ (FractionRing R⟦X⟧) L`, so `R⟦X⟧` acts on `L` along
   the composite of the localization map with the structure map — existence of some algebra
   structure is not enough.
4. The instantiation is not degenerate: `R = ℤ` is a Noetherian N-2 domain that is not a field
   (its integral closure in a number field is the ring of integers, finite over `ℤ`), so the
   theorem says the two-dimensional ring `ℤ⟦X⟧` is N-2, and applies again to `ℤ⟦X⟧` itself.

## References

* [Stacks Project, Tag 032Q](https://stacks.math.columbia.edu/tag/032Q)
* [Stacks Project, Tag 032F](https://stacks.math.columbia.edu/tag/032F)
-/

@[expose] public section



namespace PowerSeries

/-- **Tag 032Q.** If `R` is a Noetherian N-2 (Japanese) domain, then so is the formal power
series ring `R⟦X⟧`: the integral closure of `R⟦X⟧` in every finite extension of `Frac R⟦X⟧` is
a finite `R⟦X⟧`-module.

Together with `PowerSeries.instIsNoetherianRing` and `PowerSeries.instIsDomain` this says that
`R⟦X⟧` is a Noetherian N-2 domain. -/
@[stacks 032Q, ega "0 23.1.4" "case r = 1"]
public theorem isJapaneseRing {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (hR : IsJapaneseRing R) : IsJapaneseRing R⟦X⟧ :=
      by apply Stacks.Nagata.PowerSeriesAscent.solution ; assumption

end PowerSeries

end

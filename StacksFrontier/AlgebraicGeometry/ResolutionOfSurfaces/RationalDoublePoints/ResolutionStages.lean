module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Ideal.Height
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.Properties.RegularLocus
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupChain
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.Situation
public import StacksFrontier.RingTheory.Serre.Criterion
public import StacksCore.Tactic.StacksAttribute

/-!
# The stages of a resolution of a rational double point

Let `A` be a two-dimensional local normal Nagata domain which defines a rational singularity,
whose completion is normal, and which is Gorenstein. The source resolves `Spec A` by a finite
sequence of blowups in singular closed points, every member of which is again normal with
finitely many singular points of the same kind. This file proves those conditions at the first
member `Spec A` of such a sequence.

The input is Serre's criterion: a normal Noetherian local ring of dimension two is regular at
every prime other than its maximal ideal, because such a prime has height at most one. So the
singular locus of `Spec A` is at most the closed point, and the local ring there is `A` itself.

## Main results

* `AlgebraicGeometry.isRegularLocalRing_stalk_spec_iff` compares regularity of the local ring of
  `Spec R` at a prime with regularity of the localization of `R` there.
* `AlgebraicGeometry.height_le_one_of_ne_maximalIdeal`: in a local ring of Krull dimension two a
  prime other than the maximal ideal has height at most one.
* `AlgebraicGeometry.singularLocus_spec_subset_closedPoint`: the singular locus of the spectrum
  of a two-dimensional normal Noetherian local domain is contained in the closed point.
* `AlgebraicGeometry.isRegular_spec_of_isRegularLocalRing`: the spectrum of a regular local ring
  is a regular scheme.
* `AlgebraicGeometry.isNormal_and_finite_singularLocus_and_exists_situation`: the conditions the
  source imposes on every member of its sequence, verified at `Spec A`.

## Implementation notes

"Of the same type" is read as: the local ring at a singular point is isomorphic to the ring of a
`AlgebraicGeometry.RationalDoublePointSituation`, the standing situation of Tag 0BGC. An
isomorphism of rings is used rather than an equality of types, so that the situation can be
built from `A` itself and no property has to be transported.

What this file does not contain is the sequence of blowups and the regularity of its last
member. The termination half of the source's argument for those is in
`StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.FormalArcs.Termination`, where Tag 0BG2 and
Tag 0BG3 are composed: over a complete two-dimensional normal local base, a sequence of blowups
at closed points whose exceptional divisors are cut out by the successive transforms of one
element of the local ring at the initial centre has a stage whose centre is a regular point.

The computation with the quadratic form of the singularity that occupies Section 54.12 of the
source, which is what feeds that composition, is now largely in place. The graded dimensions are
`AlgebraicGeometry.BlowUpDualizing.finrank_gradedPiece_eq` of
`RationalDoublePoints/GradedDimensions.lean`; the case I and case II dichotomy and the good
coordinate are in `RationalDoublePoints/{GoodCoordinate,CaseDichotomy}.lean`; the identification
of the exceptional curve with the zero scheme of the quadratic form is proved at the level of
relations, as `AlgebraicGeometry.gradedRelationIdeal_eq_span_quadraticFormPoly` of
`RationalDoublePoints/FormPolynomial.lean`, together with its dehomogenization at a good
coordinate; and a good coordinate is shown to be a superficial element of the maximal ideal,
which is the algebraic form of the source's assertion that it cuts the exceptional divisor out.

What remains absent is the ring of the affine blowup chart itself — the left hand side of the
source's `A[𝔪/x₁]/x₁ ≅ κ[y₂, y₃]/(q(1, y₂, y₃))` — together with the step from a good coordinate
to the singular point of the blowup lying in the chart it determines, the description of the
dualizing sheaf of the blowup which makes the singularities of a blowup Gorenstein again, and the
base change of the sequence to the spectrum of the completion, which is where the source applies
Tag 0BG3.

Governing all of it is the embedding dimension `dim_κ(𝔪/𝔪²) = 3`, which every result of
Section 54.12 named above needs, each of
`AlgebraicGeometry.exists_generators_and_quadraticRelation`,
`AlgebraicGeometry.BlowUpDualizing.finrank_gradedPiece_eq_two_mul_add_one` and the results of
`RationalDoublePoints/{FormPolynomial,GradedRelations}.lean` taking it, or the `2n + 1` it
produces, in a binder. **It is now proved**, as `AlgebraicGeometry.BlowUpDualizing`
`.finrank_cotangentSpace_eq_three_of_dualizingNormalization` of
`RationalDoublePoints/EmbeddingDimensionGorenstein.lean`, which carries one hypothesis: a
dualizing module `ω_X` on the blowup of `Spec(A)` in the maximal ideal, normalized relative to
`A` in the sense of Remark 0B4R. The three results above that take the embedding dimension in a
binder are discharged by applying them to it, which is one step at the call site, and the same
file records why that one hypothesis remains — the *existence* of a normalized `ω_X` is not
constructed in this development, only its uniqueness up to isomorphism.

The route is not the source's. The source reads `deg 𝒪_E(1) = 2` off `ω_E = 𝒪_E(-1)`, and gets
`ω_X ≅ 𝒪_X` from clause (3) of Tag 0B64, whose one input — the global generation of `ω_X|_E` of
Tag 0B5H — is equivalent to that clause and still blocked behind Tag 0E32. The route taken
instead never trivializes `ω_X`: Riemann–Roch for `𝒪_E(-1)` turns `dim_κ H¹(E, 𝒪_E(-1)) ≤ 1`
into `dim_κ(𝔪/𝔪²) ≤ 3`, duality on `E` over `κ` at the invertible `𝒪_E(-1)` turns that bound
into `dim_κ H⁰(E, ω_X|_E) ≤ 1`, and the latter is the Gorenstein hypothesis: `Γ(X, ω_X) ≅ ω_A ≅ A`
is a cyclic `A`-module by Tag 0BBU, it surjects onto `Γ(E, ω_X|_E)` by the restriction sequence
together with `H¹(X, ω_X(1)) = 0`, and `Γ(E, 𝒪_E) = κ`. The identification of `ω_E = H¹(a(ω_X))`
with the dualizing sheaf of `E` over `κ` that the duality step needs is
formalized as `AlgebraicGeometry`
`.BlowUpDualizing.nonempty_exceptionalDualizingModule_iso_dualizingSheafOverField` of
`Duality/ExceptionalDualizingSheafIdentification.lean`. What is unconditional for `A` not regular,
with no dualizing module at all, remains the inequality `dim_κ(𝔪ⁿ/𝔪ⁿ⁺¹) ≥ 2n + 1`,
`AlgebraicGeometry.BlowUpDualizing.two_mul_add_one_le_finrank_gradedPiece`.

## References

* [Stacks Project, Tag 0BGE](https://stacks.math.columbia.edu/tag/0BGE)
* [Stacks Project, Tag 0BGC](https://stacks.math.columbia.edu/tag/0BGC)
* [Stacks Project, Tag 0BGB](https://stacks.math.columbia.edu/tag/0BGB)
* [Stacks Project, Tag 031S](https://stacks.math.columbia.edu/tag/031S)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

/-- The local ring of `Spec R` at a prime is regular exactly when the localization of `R` at
that prime is regular. -/
public theorem isRegularLocalRing_stalk_spec_iff (R : Type u) [CommRing R]
    (p : PrimeSpectrum R) :
    IsRegularLocalRing ((Spec (.of R)).presheaf.stalk p) ↔
      IsRegularLocalRing (Localization.AtPrime p.asIdeal) := by
  let : p.asIdeal.IsPrime := p.2
  let e := (Spec.stalkIso (.of R) p).commRingCatIsoToRingEquiv
  exact ⟨fun _ => .of_ringEquiv e, fun _ => .of_ringEquiv e.symm⟩

/-- **Property `(R_1)`.** In a normal Noetherian ring the localization at a prime of height at
most one is a regular local ring. This is one half of Serre's criterion, Tag 031S. -/
public theorem isRegularLocalRing_localization_of_isNormalRing {R : Type u} [CommRing R]
    [IsNoetherianRing R] (hR : IsNormalRing R) (p : Ideal R) [p.IsPrime] (hp : p.height ≤ 1) :
    IsRegularLocalRing (Localization.AtPrime p) :=
  (isDomain_and_isIntegrallyClosed_atPrime_iff_isRegularLocalRing_and_min_two_le_depth.mp
    hR).1 p hp

/-- In a local ring of Krull dimension two, a prime ideal other than the maximal ideal has
height at most one. -/
public theorem height_le_one_of_ne_maximalIdeal {R : Type u} [CommRing R] [IsLocalRing R]
    (hdim : ringKrullDim R = 2) (p : Ideal R) [p.IsPrime] (hp : p ≠ maximalIdeal R) :
    p.height ≤ 1 := by
  have hmax : (maximalIdeal R).height = 2 := by
    have h : ((maximalIdeal R).height : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) := by
      rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hdim]
      norm_num
    exact WithBot.coe_injective h
  have hlt : p < maximalIdeal R :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal_of_isPrime p) hp
  have hle : p.height + 1 ≤ 2 := by
    rw [← hmax]
    exact Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have hne : p.height ≠ ⊤ := fun htop => by simp [htop] at hle
  have hlt2 : p.height < 2 := (ENat.add_one_le_iff hne).mp hle
  have htwo : (2 : ℕ∞) = 1 + 1 := by norm_num
  rw [htwo] at hlt2
  exact (ENat.lt_add_one_iff (by simp)).mp hlt2

/-- A prime of `A` whose localization is regular is not in the singular locus of `Spec A`. -/
private theorem notMem_singularLocus_spec_of_isRegularLocalRing_localization (A : Type u)
    [CommRing A] (p : PrimeSpectrum A)
    (h : ∀ [p.asIdeal.IsPrime], IsRegularLocalRing (Localization.AtPrime p.asIdeal)) :
    p ∉ singularLocus (Spec (.of A)) :=
  fun hp => hp ((isRegularLocalRing_stalk_spec_iff A p).mpr h)

/-- The singular locus of the spectrum of a two-dimensional normal Noetherian local domain is
contained in the closed point: every other prime has height at most one, where normality makes
the local ring regular. -/
public theorem singularLocus_spec_subset_closedPoint (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [IsNormalDomain A] (hdim : ringKrullDim A = 2) :
    singularLocus (Spec (.of A)) ⊆ {closedPoint A} := by
  intro p hp
  by_contra hne
  have hp' : p.asIdeal ≠ maximalIdeal A := fun h => hne (PrimeSpectrum.ext h)
  exact notMem_singularLocus_spec_of_isRegularLocalRing_localization A p
    (isRegularLocalRing_localization_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed A)
      p.asIdeal (height_le_one_of_ne_maximalIdeal hdim p.asIdeal hp')) hp

/-- The singular locus of the spectrum of a two-dimensional normal Noetherian local domain is
finite. -/
public theorem finite_singularLocus_spec (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [IsNormalDomain A] (hdim : ringKrullDim A = 2) :
    (singularLocus (Spec (.of A))).Finite :=
  Set.Finite.subset (Set.finite_singleton _) (singularLocus_spec_subset_closedPoint A hdim)

/-- The spectrum of a regular local ring is a regular scheme: the local ring at a prime is the
localization there, and a regular local ring is a regular ring. -/
public theorem isRegular_spec_of_isRegularLocalRing (A : Type u) [CommRing A] [IsLocalRing A]
    [IsRegularLocalRing A] : IsRegular (Spec (.of A)) := by
  have hreg : IsRegularRing A :=
    ((IsLocalRing.isRegularRing_tfae (R := A)).out 1 3).mp
      (inferInstance : IsRegularLocalRing A)
  refine isRegular_of_singularLocus_eq_empty _ (Set.eq_empty_iff_forall_notMem.mpr fun p => ?_)
  exact notMem_singularLocus_spec_of_isRegularLocalRing_localization A p
    (IsRegularRing.isRegularLocalRing_localization p.asIdeal)

/-- **The first member of the sequence of Tag 0BGE.** Let `A` be a two-dimensional local normal
Nagata domain which defines a rational singularity, whose completion is normal, and which is
Gorenstein. Then `Spec A`, the first member of the source's sequence of blowups, is normal and has
only finitely many singular points; when `A` is regular the empty sequence of blowups already has a
regular last member; and the local ring at each singular point of `Spec A` is again a
two-dimensional local normal Nagata domain defining a rational singularity, with normal completion,
Gorenstein and not regular — the standing situation of Tag 0BGC. -/
public theorem isNormal_and_finite_singularLocus_and_exists_situation
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
    (hnagata : IsNagataRing A) (hdim : ringKrullDim A = 2)
    (hrational : DefinesRationalSingularity A)
    (hcompletion : IsNormalDomain (AdicCompletion (maximalIdeal A) A))
    (hgorenstein : letI : IsNoetherianRing A := hnagata.isNoetherianRing
      Dualizing.IsGorensteinLocalRing A) :
    IsNormal (Spec (.of A)) ∧ (singularLocus (Spec (.of A))).Finite ∧
      (IsRegularLocalRing A → ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)),
        Stacks.ResolutionOfSurfaces.PointBlowupChain (Spec (.of A))
          (singularLocus (Spec (.of A))) Y f ∧ IsRegular Y) ∧
      ∀ x ∈ singularLocus (Spec (.of A)), ∃ S : RationalDoublePointSituation.{u},
        Nonempty (S.A ≃+* (Spec (.of A)).presheaf.stalk x) := by
  let : IsNoetherianRing A := hnagata.isNoetherianRing
  refine ⟨isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed A),
    finite_singularLocus_spec A hdim,
    fun _ => ⟨Spec (.of A), 𝟙 _, .refl, isRegular_spec_of_isRegularLocalRing A⟩, ?_⟩
  intro x hx
  obtain rfl : x = closedPoint A := singularLocus_spec_subset_closedPoint A hdim hx
  have he : A ≃+* (Spec (.of A)).presheaf.stalk (closedPoint A) :=
    (stalkClosedPointIso (.of A)).commRingCatIsoToRingEquiv.symm
  have hnotreg : ¬ IsRegularLocalRing A := fun _ => hx (.of_ringEquiv he)
  exact ⟨{ A := A
           nagata := hnagata
           dimension_two := hdim
           definesRationalSingularity := hrational
           completion_normalDomain := hcompletion
           gorenstein := hgorenstein
           not_isRegularLocalRing := hnotreg }, ⟨he⟩⟩

end AlgebraicGeometry

end

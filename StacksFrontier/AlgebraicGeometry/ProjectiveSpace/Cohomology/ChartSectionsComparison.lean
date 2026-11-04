module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistGradedPieces
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.WeightSplittingNaturality
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.LaurentGradedPiece

/-!
# The monomial charts are the sections of `𝒪(d)` on the standard opens, naturally

Let `R` be a commutative ring, let `P = R[T₀, …, Tₙ]` carry its grading by total degree, and for a
finite set `s` of coordinates let `D₊(∏_{i ∈ s} Tᵢ)` be the corresponding standard open of
`ℙⁿ_R = Proj P`. This file identifies the module of sections of the twisting sheaf `𝒪(d)` over
that standard open with the free `R`-module `Stacks.ProjectiveSpace.Cohomology.twistChart` on the
degree-`d` Laurent monomials that are regular outside `s`, and shows that the identification is
**natural in `s`**: for `s ⊆ t` the restriction map of `𝒪(d)` becomes the inclusion of monomial
charts `twistChart R n d s ≤ twistChart R n d t`.

`StacksFrontier/AlgebraicGeometry/ProjectiveSpace/Cohomology/LaurentGradedPiece.lean` identifies the
sections with the monomial chart for a single `s`, by way of
`Stacks.ProjectiveSpace.Cohomology.twistSections`, the degree-`d` graded piece of the localization
`P[1/∏_{i ∈ s} Tᵢ]`; what is added here is the comparison of the two vocabularies in which that
graded piece is described — `Stacks.ProjectiveCohomology.awayGrading` and
`Stacks.GradedLocalization.gradedPiece` — and the naturality square. Together they make the
combinatorial Čech complex of
`StacksFrontier/AlgebraicGeometry/ProjectiveSpace/Cohomology/LaurentCharts.lean`, whose terms are the
monomial charts and whose differentials are built from the chart inclusions, the Čech complex of
the standard cover of `ℙⁿ_R` for `𝒪(d)`, which is what [Stacks, Tag 01XT] computes with.

## Main definitions

* `Stacks.ProjectiveSpace.Cohomology.chartSheafSections` — the sections of `𝒪(d)` over the
  standard open `D₊(∏_{i ∈ s} Tᵢ)`.
* `Stacks.ProjectiveSpace.Cohomology.chartSectionsAddEquiv` — those sections, as the degree-`d`
  graded piece `twistSections R n d s` of `P[1/∏_{i ∈ s} Tᵢ]`.
* `Stacks.ProjectiveSpace.Cohomology.chartSectionsAddEquivTwistChart` — those sections, as the
  monomial chart `twistChart R n d s`.
* `Stacks.ProjectiveSpace.Cohomology.chartLocalizedMap` — the localization map
  `P[1/∏_{i ∈ s} Tᵢ] → P[1/∏_{i ∈ t} Tᵢ]` of [Stacks, Tag 01M4] between two chart denominators,
  which `chartLocalizedLinearMap` repackages as an `R`-linear map.

## Main results

* `Stacks.ProjectiveSpace.Cohomology.mem_awayGrading_iff_mem_twistSections` — the two descriptions
  of the degree-`d` part of `P[1/∏_{i ∈ s} Tᵢ]` agree.
* `Stacks.ProjectiveSpace.Cohomology.chartLocalizedMap_mk` — **the localization map on a single
  fraction**: it multiplies the numerator by the power of `∏_{i ∈ t \ s} Tᵢ` needed to raise the
  denominator.
* `Stacks.ProjectiveSpace.Cohomology.chartLocalizedMap_laurentFrac` — hence it sends each Laurent
  monomial of the smaller chart to the same Laurent monomial of the larger one.
* `Stacks.ProjectiveSpace.Cohomology.coe_chartSectionsAddEquiv_map_homOfLE` — the restriction map
  of `𝒪(d)` between two standard opens is that localization map.
* `Stacks.ProjectiveSpace.Cohomology.chartSectionsAddEquivTwistChart_map_homOfLE` — **the
  naturality of the monomial model**: through the identification of sections with monomial charts
  the restriction map of `𝒪(d)` is the inclusion `twistChart R n d s ≤ twistChart R n d t`.

## Implementation notes

**Three homonyms.** `Stacks.ProjectiveSpace.Cohomology.twistSections` (used here) is an
`R`-submodule of a localization, `Stacks.ProjectiveCohomology.twistSections` is a presheaf and
`Stacks.ProjectiveSpace.TwistSections.twistSections` is a module of sheaf sections; all three are
qualified in full below.

**Why the localization map is reproved to be `R`-linear.** The map supplied by
`AlgebraicGeometry.ProjectiveSpectrum.moduleRestrictionMaps` is semilinear over the map of
degree-zero localizations, so the only scalars it is visibly linear over are the polynomials. The
`R`-linearity needed to compare two monomial bases is read off from the description of the map on a
single fraction, `chartLocalizedMap_mk`, rather than from a scalar-tower instance.

**Why a power of the smaller denominator acts invertibly.** `chartLocalizedMap_mk` is proved by
clearing the denominator: a power of `∏_{i ∈ s} Tᵢ` turns both sides into the same fraction over
`1`, and since `∏_{i ∈ t} Tᵢ` is a multiple of `∏_{i ∈ s} Tᵢ`, multiplication by that power is
injective on `P[1/∏_{i ∈ t} Tᵢ]` — `LocalizedModule.divBy` is its inverse.

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj CategoryTheory TopologicalSpace
  Opposite

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.ProjectiveSpace.Cohomology

variable {R : Type u} [CommRing R] {n : ℕ} {d : ℤ}

/-! ### The inclusion of standard opens -/

/-- The denominator of a larger chart factors through that of a smaller one: for `s ⊆ t`,
`∏_{i ∈ t} Tᵢ = (∏_{i ∈ s} Tᵢ) · (∏_{i ∈ t \ s} Tᵢ)`. -/
theorem chartDenom_mul_sdiff (R : Type u) [CommRing R] (n : ℕ) (s t : Finset (Fin (n + 1)))
    (hst : s ⊆ t) :
    chartDenom R n t = chartDenom R n s * chartDenom R n (t \ s) := by
  rw [chartDenom, chartDenom, chartDenom, ← Finset.prod_sdiff hst, mul_comm]

/-- Inverting more coordinates cuts out a smaller standard open: for `s ⊆ t` the chart `t` is
contained in the chart `s`. -/
theorem basicOpen_chartDenom_le (R : Type u) [CommRing R] (n : ℕ) (s t : Finset (Fin (n + 1)))
    (hst : s ⊆ t) :
    ProjectiveSpectrum.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (chartDenom R n t)
      ≤ ProjectiveSpectrum.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (chartDenom R n s) := by
  rw [chartDenom_mul_sdiff R n s t hst]
  exact ProjectiveSpectrum.basicOpen_mul_le_left _ _ _

/-! ### The two descriptions of the degree-`d` part of the localization -/

/-- **The vocabulary bridge.** The degree-`d` part of `R[T₀, …, Tₙ][1/∏_{i ∈ s} Tᵢ]` described as
the single fractions with homogeneous numerator of the right degree
(`Stacks.ProjectiveCohomology.awayGrading`) is the one described as a graded piece of a graded
localization (`Stacks.ProjectiveSpace.Cohomology.twistSections`). Both are the sections of `𝒪(d)`
over `D₊(∏_{i ∈ s} Tᵢ)` by [Stacks, Tag 01M6]; the two spellings arise from the two routes through
the degree-zero localization of the shifted module. -/
theorem mem_awayGrading_iff_mem_twistSections (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)
    (s : Finset (Fin (n + 1)))
    (y : LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R)) :
    y ∈ Stacks.ProjectiveCohomology.awayGrading
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
          (chartDenom_mem_homogeneousSubmodule n s) d
      ↔ y ∈ twistSections R n d s :=
  ((Stacks.ProjectiveCohomology.mem_degreeZeroLocalization_twistGrading_iff
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (chartDenom_mem_homogeneousSubmodule n s) d y).symm.trans
    (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeZeroLocalization_twistGrading_eq
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (chartDenom_mem_homogeneousSubmodule n s) d y)).trans mem_twistSections.symm

/-- The bridge of `mem_awayGrading_iff_mem_twistSections`, as an isomorphism of additive groups:
the two subgroups have the same elements, so the identity of the ambient localization matches
them. -/
def awayGradingAddEquivTwistSections (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)
    (s : Finset (Fin (n + 1))) :
    Stacks.ProjectiveCohomology.awayGrading
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (chartDenom_mem_homogeneousSubmodule n s) d ≃+ twistSections R n d s where
  toFun z := ⟨z.1, (mem_awayGrading_iff_mem_twistSections R n d s z.1).1 z.2⟩
  invFun y := ⟨y.1, (mem_awayGrading_iff_mem_twistSections R n d s y.1).2 y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-! ### The sections of a twist over a standard open, as a monomial chart -/

/-- The module of sections of `𝒪(d)` over the standard open `D₊(∏_{i ∈ s} Tᵢ)` of `ℙⁿ_R`. -/
abbrev chartSheafSections (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (s : Finset (Fin (n + 1))) :=
  (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d).val.obj
    (op (ProjectiveSpectrum.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (chartDenom R n s)))

/-- **The sections of `𝒪(d)` over a standard open are the degree-`d` graded piece of a single
localization.** For a nonempty `s` the denominator `∏_{i ∈ s} Tᵢ` has positive degree, so
[Stacks, Tag 01M6] applies. -/
def chartSectionsAddEquiv (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (s : Finset (Fin (n + 1)))
    (hs : s.Nonempty) : chartSheafSections R n d s ≃+ twistSections R n d s :=
  (Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (chartDenom_mem_homogeneousSubmodule n s) (Finset.card_pos.2 hs) d).trans
    (awayGradingAddEquivTwistSections R n d s)

/-- The fraction representing a section is the one produced by
`Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading`: the bridge of
`awayGradingAddEquivTwistSections` does not move elements of the localization. -/
theorem coe_chartSectionsAddEquiv (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)
    (s : Finset (Fin (n + 1))) (hs : s.Nonempty) (x : chartSheafSections R n d s) :
    ((chartSectionsAddEquiv R n d s hs x :
        LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R)))
      = (Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
          (chartDenom_mem_homogeneousSubmodule n s) (Finset.card_pos.2 hs) d x :
            LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R)) := rfl

/-- **The monomial chart is the module of sections.** The sections of `𝒪(d)` over
`D₊(∏_{i ∈ s} Tᵢ)` are the free `R`-module on the degree-`d` Laurent monomials that are regular
outside `s`. -/
def chartSectionsAddEquivTwistChart (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)
    (s : Finset (Fin (n + 1))) (hs : s.Nonempty) :
    chartSheafSections R n d s ≃+ twistChart R n d (↑s : Set (Fin (n + 1))) :=
  (chartSectionsAddEquiv R n d s hs).trans
    (twistChartEquivTwistSections R n d s).symm.toAddEquiv

/-! ### The localization map between two chart denominators -/

/-- The compatible pair of restriction maps of [Stacks, Tag 01M4] attached to the inclusion
`D₊(∏_{i ∈ t} Tᵢ) ⊆ D₊(∏_{i ∈ s} Tᵢ)` of standard opens. -/
def chartRestrictionMaps (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (s t : Finset (Fin (n + 1)))
    (hs : s.Nonempty) (hst : s ⊆ t) :=
  ProjectiveSpectrum.moduleRestrictionMaps
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (twistGrading (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d)
    (chartDenom R n s) (chartDenom R n t)
    ⟨s.card, Finset.card_pos.2 hs, chartDenom_mem_homogeneousSubmodule n s⟩
    ⟨t.card, Finset.card_pos.2 (hs.mono hst), chartDenom_mem_homogeneousSubmodule n t⟩
    (basicOpen_chartDenom_le R n s t hst)

/-- The localization map `R[T₀, …, Tₙ][1/∏_{i ∈ s} Tᵢ] → R[T₀, …, Tₙ][1/∏_{i ∈ t} Tᵢ]` induced by
the identity of the polynomial ring. -/
def chartLocalizedMap (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (s t : Finset (Fin (n + 1)))
    (hs : s.Nonempty) (hst : s ⊆ t)
    (z : LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R)) :
    LocalizedModule.Away (chartDenom R n t) (MvPolynomial (Fin (n + 1)) R) :=
  (chartRestrictionMaps R n d s t hs hst).localizedMap z

/-- The localization map is linear over the polynomial ring. -/
theorem chartLocalizedMap_smul_poly (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)
    (s t : Finset (Fin (n + 1))) (hs : s.Nonempty) (hst : s ⊆ t)
    (c : MvPolynomial (Fin (n + 1)) R)
    (z : LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R)) :
    chartLocalizedMap R n d s t hs hst (c • z) = c • chartLocalizedMap R n d s t hs hst z := by
  simp only [chartLocalizedMap]
  exact LinearMap.CompatibleSMul.map_smul _ c z

/-- The localization map is the identity on polynomials, that is on the fractions with denominator
`1`. -/
theorem chartLocalizedMap_mk_one (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)
    (s t : Finset (Fin (n + 1))) (hs : s.Nonempty) (hst : s ⊆ t)
    (m : MvPolynomial (Fin (n + 1)) R) :
    chartLocalizedMap R n d s t hs hst (LocalizedModule.mk m 1) = LocalizedModule.mk m 1 :=
  (chartRestrictionMaps R n d s t hs hst).map_mk m

/-- The localization map is additive. -/
theorem chartLocalizedMap_add (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)
    (s t : Finset (Fin (n + 1))) (hs : s.Nonempty) (hst : s ⊆ t)
    (z w : LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R)) :
    chartLocalizedMap R n d s t hs hst (z + w)
      = chartLocalizedMap R n d s t hs hst z + chartLocalizedMap R n d s t hs hst w :=
  map_add (chartRestrictionMaps R n d s t hs hst).localizedMap z w

/-- The `N`-th power of a larger chart denominator splits off that of a smaller one. -/
private theorem chartDenom_pow_eq_mul_sdiff (R : Type u) [CommRing R] (n : ℕ)
    (s t : Finset (Fin (n + 1))) (hst : s ⊆ t) (N : ℕ) :
    chartDenom R n t ^ N = chartDenom R n s ^ N * chartDenom R n (t \ s) ^ N := by
  rw [chartDenom_mul_sdiff R n s t hst, mul_pow]

/-- Multiplication by a power of the inverted element is injective on a localization away from it:
`LocalizedModule.divBy` undoes it. -/
theorem chartDenom_pow_smul_injective_self (R : Type u) [CommRing R] (n : ℕ)
    (t : Finset (Fin (n + 1))) (N : ℕ) :
    Function.Injective fun z : LocalizedModule.Away (chartDenom R n t)
        (MvPolynomial (Fin (n + 1)) R) => chartDenom R n t ^ N • z := by
  refine Function.LeftInverse.injective
    (g := LocalizedModule.divBy (chartPow R n t N)) fun z => ?_
  have h := LocalizedModule.divBy_mul_by (chartPow R n t N) z
  rwa [Module.algebraMap_end_apply] at h

/-- **A power of the smaller chart denominator acts invertibly on the larger chart.** For `s ⊆ t`
the denominator `∏_{i ∈ t} Tᵢ` is a multiple of `∏_{i ∈ s} Tᵢ`, so multiplication by a power of
the latter is injective on `R[T₀, …, Tₙ][1/∏_{i ∈ t} Tᵢ]`. -/
theorem chartDenom_pow_smul_injective (R : Type u) [CommRing R] (n : ℕ)
    (s t : Finset (Fin (n + 1))) (hst : s ⊆ t) (N : ℕ) :
    Function.Injective fun z : LocalizedModule.Away (chartDenom R n t)
        (MvPolynomial (Fin (n + 1)) R) => chartDenom R n s ^ N • z := by
  intro z₁ z₂ h
  have h' : chartDenom R n s ^ N • z₁ = chartDenom R n s ^ N • z₂ := h
  refine chartDenom_pow_smul_injective_self R n t N ?_
  show chartDenom R n t ^ N • z₁ = chartDenom R n t ^ N • z₂
  rw [chartDenom_pow_eq_mul_sdiff R n s t hst, mul_comm, mul_smul, mul_smul, h']

/-- **The localization map on a single fraction.** Raising the denominator from
`(∏_{i ∈ s} Tᵢ) ^ N` to `(∏_{i ∈ t} Tᵢ) ^ N` multiplies the numerator by
`(∏_{i ∈ t \ s} Tᵢ) ^ N`. Both sides become the fraction `x / 1` after multiplication by
`(∏_{i ∈ s} Tᵢ) ^ N`, which is injective by `chartDenom_pow_smul_injective`. -/
theorem chartLocalizedMap_mk (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)
    (s t : Finset (Fin (n + 1))) (hs : s.Nonempty) (hst : s ⊆ t)
    (x : MvPolynomial (Fin (n + 1)) R) (N : ℕ) :
    chartLocalizedMap R n d s t hs hst (LocalizedModule.mk x (chartPow R n s N))
      = LocalizedModule.mk (x * chartDenom R n (t \ s) ^ N) (chartPow R n t N) := by
  have hsrc : chartDenom R n s ^ N • chartLocalizedMap R n d s t hs hst
        (LocalizedModule.mk x (chartPow R n s N))
      = (LocalizedModule.mk x 1 :
          LocalizedModule.Away (chartDenom R n t) (MvPolynomial (Fin (n + 1)) R)) :=
    ((chartLocalizedMap_smul_poly R n d s t hs hst _ _).symm.trans
      (congrArg (chartLocalizedMap R n d s t hs hst)
        (Stacks.ProjectiveCohomology.pow_smul_mk_pow (chartDenom R n s) x N))).trans
      (chartLocalizedMap_mk_one R n d s t hs hst x)
  have htgt : chartDenom R n s ^ N •
        (LocalizedModule.mk (x * chartDenom R n (t \ s) ^ N) (chartPow R n t N) :
          LocalizedModule.Away (chartDenom R n t) (MvPolynomial (Fin (n + 1)) R))
      = LocalizedModule.mk x 1 := by
    rw [LocalizedModule.smul'_mk]
    have harith : chartDenom R n s ^ N • (x * chartDenom R n (t \ s) ^ N)
        = (chartPow R n t N) • x := by
      show chartDenom R n s ^ N * (x * chartDenom R n (t \ s) ^ N) = chartDenom R n t ^ N * x
      rw [chartDenom_pow_eq_mul_sdiff R n s t hst]
      ring
    rw [harith, LocalizedModule.mk_cancel]
  exact chartDenom_pow_smul_injective R n s t hst N (hsrc.trans htgt.symm)

/-- The localization map is linear over the coefficient ring: every element of the source is a
fraction, and on fractions the formula of `chartLocalizedMap_mk` is visibly `R`-linear. -/
theorem chartLocalizedMap_smul (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)
    (s t : Finset (Fin (n + 1))) (hs : s.Nonempty) (hst : s ⊆ t) (r : R)
    (z : LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R)) :
    chartLocalizedMap R n d s t hs hst (r • z) = r • chartLocalizedMap R n d s t hs hst z := by
  induction z using LocalizedModule.induction_on with
  | h x u =>
    obtain ⟨N, hN⟩ := u.2
    obtain rfl : u = chartPow R n s N := Subtype.ext hN.symm
    rw [LocalizedModule.smul'_mk, chartLocalizedMap_mk, chartLocalizedMap_mk,
      LocalizedModule.smul'_mk, smul_mul_assoc]

/-- The localization map between two chart denominators, as a map of `R`-modules. -/
def chartLocalizedLinearMap (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)
    (s t : Finset (Fin (n + 1))) (hs : s.Nonempty) (hst : s ⊆ t) :
    LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R) →ₗ[R]
      LocalizedModule.Away (chartDenom R n t) (MvPolynomial (Fin (n + 1)) R) where
  toFun := chartLocalizedMap R n d s t hs hst
  map_add' := chartLocalizedMap_add R n d s t hs hst
  map_smul' := chartLocalizedMap_smul R n d s t hs hst

/-! ### The localization map on Laurent monomials -/

/-- **The exponent bookkeeping of raising a denominator.** Writing a Laurent monomial `e` over
`(∏_{i ∈ t} Tᵢ) ^ N` instead of `(∏_{i ∈ s} Tᵢ) ^ N` multiplies its numerator by
`(∏_{i ∈ t \ s} Tᵢ) ^ N`: the exponent vectors add. Outside `s` the exponents of `e` are
nonnegative, so no truncation occurs. -/
theorem numExp_add_shiftExp_sdiff {s t : Finset (Fin (n + 1))} (hst : s ⊆ t)
    {e : Fin (n + 1) → ℤ} (hout : ∀ i ∉ s, 0 ≤ e i) (N : ℕ) :
    numExp s e N + shiftExp n (t \ s) N = numExp t e N := by
  classical
  refine Finsupp.ext fun i => ?_
  rw [Finsupp.add_apply, numExp_apply, numExp_apply, shiftExp_apply]
  by_cases his : i ∈ s
  · simp [his, hst his]
  · have := hout i his
    by_cases hit : i ∈ t <;> simp [his, hit]
    omega

/-- **The localization map fixes Laurent monomials.** A degree-`d` Laurent monomial regular outside
`s` is also regular outside the larger `t`, and the localization map carries the one fraction
representing it to the other. -/
theorem chartLocalizedMap_laurentFrac (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)
    (s t : Finset (Fin (n + 1))) (hs : s.Nonempty) (hst : s ⊆ t) {e : Fin (n + 1) → ℤ}
    (he : e ∈ laurentMonomials n d (↑s : Set (Fin (n + 1)))) :
    chartLocalizedMap R n d s t hs hst (laurentFrac R n s e) = laurentFrac R n t e := by
  have houts : ∀ i ∉ s, 0 ≤ e i := fun i hi => he.2 i (by simpa using hi)
  have houtt : ∀ i ∉ t, 0 ≤ e i := fun i hi => houts i fun h => hi (hst h)
  have hint : ∀ i ∈ t, 0 ≤ e i + (clearDen t e : ℤ) := le_add_clearDen t e
  have hins : ∀ i ∈ s, 0 ≤ e i + (clearDen t e : ℤ) := fun i hi => hint i (hst hi)
  rw [laurentFrac_eq_mk (R := R) houts hins, laurentFrac_eq_mk (R := R) houtt hint,
    chartLocalizedMap_mk]
  congr 1
  rw [chartDenom_pow, MvPolynomial.monomial_mul_monomial, one_mul,
    numExp_add_shiftExp_sdiff hst houts]

/-! ### Naturality in the standard open -/

/-- **The restriction map of `𝒪(d)` is the localization map.** Restricting a section from
`D₊(∏_{i ∈ s} Tᵢ)` to the smaller `D₊(∏_{i ∈ t} Tᵢ)` and reading it as a fraction is the same as
reading it as a fraction and applying the localization map of [Stacks, Tag 01M4]. -/
theorem coe_chartSectionsAddEquiv_map_homOfLE (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)
    (s t : Finset (Fin (n + 1))) (hs : s.Nonempty) (hst : s ⊆ t)
    (x : chartSheafSections R n d s) :
    ((chartSectionsAddEquiv R n d t (hs.mono hst)
        (((twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d).val.map
          (homOfLE (basicOpen_chartDenom_le R n s t hst)).op).hom x) :
        LocalizedModule.Away (chartDenom R n t) (MvPolynomial (Fin (n + 1)) R)))
      = chartLocalizedMap R n d s t hs hst
          ((chartSectionsAddEquiv R n d s hs x :
            LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R))) :=
  Stacks.ProjectiveCohomology.coe_sectionsTwistEquivAwayGrading_map_homOfLE
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (chartDenom_mem_homogeneousSubmodule n s) (Finset.card_pos.2 hs)
    (chartDenom_mem_homogeneousSubmodule n t) (Finset.card_pos.2 (hs.mono hst))
    (basicOpen_chartDenom_le R n s t hst) d x

/-- The identification of the monomial chart with the module of sections, unfolded: restrict the
support and read off the coordinates in the monomial basis. -/
theorem coe_twistChartEquivTwistSections_apply (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)
    (s : Finset (Fin (n + 1))) (w : twistChart R n d (↑s : Set (Fin (n + 1)))) :
    twistChartEquivTwistSections R n d s w
      = (twistSectionsBasis R n d s).repr.symm
          (Finsupp.supportedEquivFinsupp (M := R) (R := R)
            (laurentMonomials n d (↑s : Set (Fin (n + 1)))) w) := rfl

/-- The inverse identification, unfolded: take the coordinates in the monomial basis and extend
them by zero. -/
theorem coe_twistChartEquivTwistSections_symm_apply (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)
    (s : Finset (Fin (n + 1))) (y : twistSections R n d s) :
    (((twistChartEquivTwistSections R n d s).symm y :
        twistChart R n d (↑s : Set (Fin (n + 1)))) : (Fin (n + 1) → ℤ) →₀ R)
      = (((Finsupp.supportedEquivFinsupp (M := R) (R := R)
          (laurentMonomials n d (↑s : Set (Fin (n + 1))))).symm
            ((twistSectionsBasis R n d s).repr y)) : (Fin (n + 1) → ℤ) →₀ R) := rfl

/-- A basis vector of the monomial chart — the indicator of a single allowed Laurent exponent
vector — is the corresponding Laurent monomial of the localization. -/
theorem coe_twistChartEquivTwistSections_single (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)
    (s : Finset (Fin (n + 1))) {e : Fin (n + 1) → ℤ}
    (he : e ∈ laurentMonomials n d (↑s : Set (Fin (n + 1))))
    (w : twistChart R n d (↑s : Set (Fin (n + 1))))
    (hw : (w : (Fin (n + 1) → ℤ) →₀ R) = Finsupp.single e 1) :
    ((twistChartEquivTwistSections R n d s w :
        LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R)))
      = laurentFrac R n s e := by
  have hw' : w = (Finsupp.supportedEquivFinsupp (M := R) (R := R)
      (laurentMonomials n d (↑s : Set (Fin (n + 1))))).symm
        (Finsupp.single (⟨e, he⟩ : laurentMonomials n d (↑s : Set (Fin (n + 1)))) 1) :=
    Subtype.ext (by rw [hw, Finsupp.supportedEquivFinsupp_symm_single])
  rw [coe_twistChartEquivTwistSections_apply, hw', LinearEquiv.apply_symm_apply,
    Module.Basis.repr_symm_single_one]
  simp only [twistSectionsBasis, Module.Basis.coe_mk]

/-- Conversely, a monomial basis vector of the module of sections comes from the indicator of its
Laurent exponent vector. -/
theorem coe_twistChartEquivTwistSections_symm_basis (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)
    (s : Finset (Fin (n + 1))) (e : laurentMonomials n d (↑s : Set (Fin (n + 1)))) :
    (((twistChartEquivTwistSections R n d s).symm (twistSectionsBasis R n d s e) :
        twistChart R n d (↑s : Set (Fin (n + 1)))) : (Fin (n + 1) → ℤ) →₀ R)
      = Finsupp.single (e : Fin (n + 1) → ℤ) 1 := by
  rw [coe_twistChartEquivTwistSections_symm_apply, Module.Basis.repr_self,
    Finsupp.supportedEquivFinsupp_symm_single]

/-- **The inclusion of monomial charts is the localization map.** Transporting an element of the
chart `s` into the chart `t` and reading it as a fraction over `∏_{i ∈ t} Tᵢ` is the same as
reading it over `∏_{i ∈ s} Tᵢ` and applying the localization map. Both sides are `R`-linear, so it
suffices to check this on the monomial basis, where it is
`chartLocalizedMap_laurentFrac`. -/
theorem coe_twistChartEquivTwistSections_inclusion (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)
    (s t : Finset (Fin (n + 1))) (hs : s.Nonempty) (hst : s ⊆ t) (z : twistSections R n d s) :
    ((twistChartEquivTwistSections R n d t
        (Submodule.inclusion (twistChart_mono (R := R) (d := d) (Finset.coe_subset.2 hst))
          ((twistChartEquivTwistSections R n d s).symm z)) :
        LocalizedModule.Away (chartDenom R n t) (MvPolynomial (Fin (n + 1)) R)))
      = chartLocalizedMap R n d s t hs hst
          (z : LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R)) := by
  have key :
      ((twistSections R n d t).subtype.comp
          ((twistChartEquivTwistSections R n d t).toLinearMap.comp
            ((Submodule.inclusion (twistChart_mono (R := R) (d := d)
                (Finset.coe_subset.2 hst))).comp
              (twistChartEquivTwistSections R n d s).symm.toLinearMap)))
        = (chartLocalizedLinearMap R n d s t hs hst).comp (twistSections R n d s).subtype := by
    refine (twistSectionsBasis R n d s).ext fun e => ?_
    have hw : ((Submodule.inclusion (twistChart_mono (R := R) (d := d)
            (Finset.coe_subset.2 hst))
          ((twistChartEquivTwistSections R n d s).symm (twistSectionsBasis R n d s e)) :
          twistChart R n d (↑t : Set (Fin (n + 1)))) : (Fin (n + 1) → ℤ) →₀ R)
        = Finsupp.single (e : Fin (n + 1) → ℤ) 1 := by
      rw [Submodule.coe_inclusion, coe_twistChartEquivTwistSections_symm_basis]
    have hb : ((twistSectionsBasis R n d s e : twistSections R n d s) :
        LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R))
        = laurentFrac R n s (e : Fin (n + 1) → ℤ) := by
      simp only [twistSectionsBasis, Module.Basis.coe_mk]
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
      chartLocalizedLinearMap, LinearMap.coe_mk, AddHom.coe_mk]
    rw [coe_twistChartEquivTwistSections_single R n d t
      (laurentMonomials_mono (Finset.coe_subset.2 hst) e.2) _ hw, hb,
      chartLocalizedMap_laurentFrac R n d s t hs hst e.2]
  exact DFunLike.congr_fun key z

/-- **The monomial model of the sections of `𝒪(d)` is natural in the standard open.** For
`s ⊆ t` the restriction map of `𝒪(d)` from `D₊(∏_{i ∈ s} Tᵢ)` to `D₊(∏_{i ∈ t} Tᵢ)` becomes,
through the identification of sections with monomial charts, the inclusion of submodules
`twistChart R n d s ≤ twistChart R n d t`. With
`Stacks.ProjectiveSpace.Cohomology.chartSectionsAddEquivTwistChart` this is the statement that the
combinatorial complex built from the monomial charts is the Čech complex of the standard cover of
`ℙⁿ_R` for `𝒪(d)`. -/
theorem chartSectionsAddEquivTwistChart_map_homOfLE (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)
    (s t : Finset (Fin (n + 1))) (hs : s.Nonempty) (hst : s ⊆ t)
    (x : chartSheafSections R n d s) :
    chartSectionsAddEquivTwistChart R n d t (hs.mono hst)
        (((twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d).val.map
          (homOfLE (basicOpen_chartDenom_le R n s t hst)).op).hom x)
      = Submodule.inclusion (twistChart_mono (R := R) (d := d) (Finset.coe_subset.2 hst))
          (chartSectionsAddEquivTwistChart R n d s hs x) := by
  have hA : chartSectionsAddEquiv R n d t (hs.mono hst)
        (((twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d).val.map
          (homOfLE (basicOpen_chartDenom_le R n s t hst)).op).hom x)
      = twistChartEquivTwistSections R n d t
          (Submodule.inclusion (twistChart_mono (R := R) (d := d) (Finset.coe_subset.2 hst))
            ((twistChartEquivTwistSections R n d s).symm
              (chartSectionsAddEquiv R n d s hs x))) :=
    Subtype.ext ((coe_chartSectionsAddEquiv_map_homOfLE R n d s t hs hst x).trans
      (coe_twistChartEquivTwistSections_inclusion R n d s t hs hst
        (chartSectionsAddEquiv R n d s hs x)).symm)
  exact (congrArg (fun y : twistSections R n d t =>
      (twistChartEquivTwistSections R n d t).symm y) hA).trans
    ((twistChartEquivTwistSections R n d t).symm_apply_apply _)

end Stacks.ProjectiveSpace.Cohomology

end

module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.CechComparison.OverlapChart

/-!
# Restriction to the overlap is the inclusion of monomial charts

The Čech differential `Stacks.ProjectiveSpace.Cohomology.lineCechDiff` of the standard two-chart
cover of `ℙ¹_R` is built from the submodule inclusions
`twistChart R 1 d {i} ≤ twistChart R 1 d Set.univ` of the monomial charts. For that complex to be
the Čech complex of the twisting sheaf it is not enough that its three objects be the sections of
`𝒪(d)` over `D₊(X₀)`, `D₊(X₁)` and `D₊(X₀X₁)` — the inclusions must be the restriction maps.

This file settles the chart half of that: under the identification of `twistChart R 1 d {0}` with
the functions on `D₊(X₀)` (`twistChartSingletonChartRingEquiv`, i.e. division by `X₀^d`) and of
`twistChart R 1 d Set.univ` with the functions on `D₊(X₀X₁)` (`twistChartUnivEquivLaurent`
followed by `overlapAlgEquivLaurent`, again division by `X₀^d`), the submodule inclusion **is**
restriction of functions from the chart to the overlap. Both charts are trivialized on the same
generator `X₀^d` — `Stacks.ProjectiveSpace.TwistSections.twistSectionsOverlapEquivAway` uses the
factorization `X₀X₁ = X₀ · X₁`, whose distinguished variable is `X₀` — which is why no twist by a
unit intervenes.

Concretely: a degree-`d` Laurent monomial regular away from `X₀` has nonnegative exponent at `X₁`,
so dividing it by `X₀^d` gives a polynomial in `X₁/X₀`; the inclusion into the overlap chart
corresponds to the inclusion `R[t] ↪ R[t, t⁻¹]`, which is what
`isLocalizationAway_overlapParam` makes restriction of functions be.

## Main definitions

* `Stacks.ProjectiveSpace.CechComparison.twistChartInclusion` — the inclusion
  `twistChart R 1 d {0} ≤ twistChart R 1 d Set.univ`, as an `R`-linear map.

## Main results

* `Stacks.ProjectiveSpace.CechComparison.twistChartUnivEquivLaurent_single` and
  `twistChartSingletonEquiv_single` — the two monomial identifications on a single monomial.
* `Stacks.ProjectiveSpace.CechComparison.overlapAlgEquivLaurent_overlapRestrict` — restriction of
  functions from `D₊(X₀)` to `D₊(X₀X₁)` is the inclusion `R[t] ↪ R[t, t⁻¹]`.
* `Stacks.ProjectiveSpace.CechComparison.twistChartUnivEquivLaurent_twistChartInclusion` — **the
  restriction-map compatibility.** The inclusion of the chart `{0}` into the overlap chart is
  restriction of functions.

## Implementation notes

The three `_single` lemmas all have the same shape, because the two monomial identifications and
`Stacks.ProjectiveSpace.TwistSections.twistChartSingletonEquiv` are built from the same three
steps: `Finsupp.supportedEquivFinsupp`, `Finsupp.domLCongr` along a reindexing of the monomials,
and `AddMonoidAlgebra.coeffLinearEquiv`. Each is proved by computing the first step on a single
monomial (`supportedEquivFinsupp_single`) and then rewriting; the last step is definitional.

The compatibility itself is then an identity of `R`-linear maps, checked on the single monomials
by `Finsupp.induction_linear` after transporting along `Finsupp.supportedEquivFinsupp`.

No `@[stacks]` attribute is attached: the computation of the cohomology of `𝒪(d)` on `ℙⁿ` is tag
01XT, whose covering set also needs the comparison of Čech with derived cohomology, tag 01XD.

## References

* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open HomogeneousLocalization MvPolynomial Stacks.ProjectiveSpace.Cohomology
open Stacks.ProjectiveSpace.TwistSections Stacks.SymmetricAway

universe u

namespace Stacks.ProjectiveSpace.CechComparison

attribute [local instance] MvPolynomial.gradedAlgebra uniqueNeZeroFinTwo
attribute [local instance] isLocalizationAway_overlapParam

variable {R : Type u} [CommRing R]

/-- A single monomial, read in the finitely supported functions on its index set. -/
theorem supportedEquivFinsupp_single {α : Type*} {s : Set α} {e : α} (he : e ∈ s) (r : R) :
    Finsupp.supportedEquivFinsupp (R := R) (M := R) s
        ⟨Finsupp.single e r, Finsupp.single_mem_supported R r he⟩ = Finsupp.single ⟨e, he⟩ r :=
  (Finsupp.supportedEquivFinsupp (R := R) (M := R) s).eq_symm_apply.mp
    (Subtype.ext (Finsupp.supportedEquivFinsupp_symm_single _ ⟨e, he⟩ r).symm)

/-- The three-step identification of a chart with a polynomial ring, on a single monomial. -/
private theorem supportedEquivFinsupp_trans_domLCongr_coeffLinearEquiv_symm_single
    {α β : Type*} {s : Set α} (f : s ≃ β) {e : α} (he : e ∈ s) (r : R) :
    ((Finsupp.supportedEquivFinsupp (R := R) (M := R) s).trans
      ((Finsupp.domLCongr f).trans (AddMonoidAlgebra.coeffLinearEquiv R).symm))
        ⟨Finsupp.single e r, Finsupp.single_mem_supported R r he⟩
      = (AddMonoidAlgebra.coeffLinearEquiv R).symm (Finsupp.single (f ⟨e, he⟩) r) := by
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, supportedEquivFinsupp_single he r,
    Finsupp.domLCongr_single]

/-- **The overlap chart of `ℙ¹` on a single monomial.** The degree-`d` Laurent monomial with
exponent `a` at `T₁` is the Laurent monomial `t^a`. -/
theorem twistChartUnivEquivLaurent_single {d : ℤ} {e : Fin 2 → ℤ}
    (he : e ∈ laurentMonomials 1 d (Set.univ : Set (Fin 2))) (r : R) :
    twistChartUnivEquivLaurent R d ⟨Finsupp.single e r, single_mem_twistChart he r⟩
      = LaurentPolynomial.C r * LaurentPolynomial.T (e 1) := by
  refine (supportedEquivFinsupp_trans_domLCongr_coeffLinearEquiv_symm_single
    (laurentMonomialsUnivFinTwoEquiv d) he r).trans ?_
  rw [← LaurentPolynomial.single_eq_C_mul_T]
  rfl

/-- **A chart of `ℙⁿ` on a single monomial.** The Laurent monomial `e` regular away from `Tᵢ` is
the polynomial monomial `Stacks.ProjectiveSpace.TwistSections.laurentMonomialRestrict` in the
remaining variables. -/
theorem twistChartSingletonEquiv_single {n : ℕ} {d : ℤ} {i : Fin (n + 1)} {e : Fin (n + 1) → ℤ}
    (he : e ∈ laurentMonomials n d ({i} : Set (Fin (n + 1)))) (r : R) :
    twistChartSingletonEquiv R n d i ⟨Finsupp.single e r, single_mem_twistChart he r⟩
      = MvPolynomial.monomial (laurentMonomialRestrict d i ⟨e, he⟩) r :=
  (supportedEquivFinsupp_trans_domLCongr_coeffLinearEquiv_symm_single
    (laurentMonomialsSingletonEquiv n d i) he r).trans rfl

/-- The identification of a chart of `ℙ¹` with the affine line factors through the monomial
description of that chart. -/
theorem chartRingAlgEquivPolynomial_twistChartSingletonChartRingEquiv (d : ℤ)
    (x : twistChart R 1 d ({0} : Set (Fin 2))) :
    chartRingAlgEquivPolynomial R (twistChartSingletonChartRingEquiv R 1 d 0 x)
      = MvPolynomial.uniqueAlgEquiv R {j : Fin 2 // j ≠ (0 : Fin 2)}
          (twistChartSingletonEquiv R 1 d 0 x) := by
  have h : twistChartSingletonChartRingEquiv R 1 d 0 x
      = chartAlgEquiv (R := R) (0 : Fin 2) (twistChartSingletonEquiv R 1 d 0 x) := rfl
  rw [h, chartRingAlgEquivPolynomial, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]

/-- **Restriction of functions from the chart `D₊(X₀)` of the projective line to the overlap
`D₊(X₀X₁)` is the inclusion `R[t] ↪ R[t, t⁻¹]`.** This is the characterizing property of the
localization isomorphism `overlapAlgEquivLaurent`. -/
theorem overlapAlgEquivLaurent_overlapRestrict (x : chartRing R (0 : Fin 2)) :
    overlapAlgEquivLaurent R (overlapRestrict R x) =
      Polynomial.toLaurent (chartRingAlgEquivPolynomial R x) := by
  change overlapRingEquivLaurent R (algebraMap (chartRing R (0 : Fin 2)) (overlapRing R) x) = _
  rw [overlapRingEquivLaurent, IsLocalization.ringEquivOfRingEquiv_eq,
    LaurentPolynomial.algebraMap_eq_toLaurent, AlgEquiv.coe_toRingEquiv]

/-- The restriction of a degree-`d` Laurent section from the chart `D₊(X₀)` of the projective line
to the overlap `D₊(X₀X₁)`: a monomial regular away from `X₀` is in particular a monomial. -/
def twistChartInclusion (R : Type u) [CommRing R] (d : ℤ) :
    twistChart R 1 d ({0} : Set (Fin 2)) →ₗ[R] twistChart R 1 d (Set.univ : Set (Fin 2)) :=
  Submodule.inclusion (twistChart_mono (Set.subset_univ _))

/-- The exponent of a degree-`d` Laurent monomial of `ℙ¹` regular away from `X₀`, at the other
variable, is nonnegative. -/
theorem toNat_exponent_one {d : ℤ} {e : Fin 2 → ℤ}
    (he : e ∈ laurentMonomials 1 d ({0} : Set (Fin 2))) : ((e 1).toNat : ℤ) = e 1 :=
  Int.toNat_of_nonneg ((mem_laurentMonomials.1 he).2 1 (by decide))

/-- **The monomial carried by a degree-`d` Laurent monomial of `ℙ¹` regular away from `X₀`.** Its
single exponent is the exponent of the Laurent monomial at `X₁`. -/
theorem laurentMonomialRestrict_default {d : ℤ} {e : Fin 2 → ℤ}
    (he : e ∈ laurentMonomials 1 d ({0} : Set (Fin 2))) :
    ((laurentMonomialRestrict d (0 : Fin 2) ⟨e, he⟩
        (default : {j : Fin 2 // j ≠ (0 : Fin 2)}) : ℕ) : ℤ) = e 1 := by
  rw [laurentMonomialRestrict_apply]
  exact toNat_exponent_one he

/-- A chart of the projective line is the free `R`-module on its monomials. This is
`Finsupp.supportedEquivFinsupp` with `Stacks.ProjectiveSpace.Cohomology.twistChart` rather than
`Finsupp.supported` as its source, so that terms built from it carry the type the lemmas about
the chart are stated at. -/
def twistChartSingletonFinsuppEquiv (R : Type u) [CommRing R] (d : ℤ) (i : Fin 2) :
    twistChart R 1 d ({i} : Set (Fin 2)) ≃ₗ[R]
      (↥(laurentMonomials 1 d ({i} : Set (Fin 2))) →₀ R) :=
  Finsupp.supportedEquivFinsupp _

/-- A single monomial of a chart of the projective line. -/
theorem twistChartSingletonFinsuppEquiv_symm_single (d : ℤ) (i : Fin 2)
    (a : laurentMonomials 1 d ({i} : Set (Fin 2))) (r : R) :
    (twistChartSingletonFinsuppEquiv R d i).symm (Finsupp.single a r)
      = ⟨Finsupp.single a.1 r, single_mem_twistChart a.2 r⟩ :=
  Subtype.ext (Finsupp.supportedEquivFinsupp_symm_single _ a r)

/-- **The restriction-map compatibility for the standard chart `D₊(X₀)` of the projective line, on
a single monomial.** -/
theorem twistChartUnivEquivLaurent_twistChartInclusion_single (d : ℤ) {e : Fin 2 → ℤ}
    (he : e ∈ laurentMonomials 1 d ({0} : Set (Fin 2))) (r : R) :
    twistChartUnivEquivLaurent R d
        (twistChartInclusion R d ⟨Finsupp.single e r, single_mem_twistChart he r⟩)
      = overlapAlgEquivLaurent R (overlapRestrict R
          (twistChartSingletonChartRingEquiv R 1 d 0
            ⟨Finsupp.single e r, single_mem_twistChart he r⟩)) := by
  rw [overlapAlgEquivLaurent_overlapRestrict,
    chartRingAlgEquivPolynomial_twistChartSingletonChartRingEquiv,
    twistChartSingletonEquiv_single he r, MvPolynomial.uniqueAlgEquiv_monomial,
    ← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.toLaurent_C_mul_X_pow,
    laurentMonomialRestrict_default he]
  exact twistChartUnivEquivLaurent_single (laurentMonomials_mono (Set.subset_univ _) he) r

/-- **The restriction-map compatibility for the standard chart `D₊(X₀)` of the projective line.**
The submodule inclusion of the monomial chart `twistChart R 1 d {0}` into the overlap chart
`twistChart R 1 d Set.univ`, which is one leg of
`Stacks.ProjectiveSpace.Cohomology.lineCechDiff`, is restriction of functions from `D₊(X₀)` to
`D₊(X₀X₁)` read through the trivializations of `𝒪(d)` on the two opens by `X₀^d`. -/
theorem twistChartUnivEquivLaurent_twistChartInclusion (d : ℤ)
    (x : twistChart R 1 d ({0} : Set (Fin 2))) :
    twistChartUnivEquivLaurent R d (twistChartInclusion R d x)
      = overlapAlgEquivLaurent R
          (overlapRestrict R (twistChartSingletonChartRingEquiv R 1 d 0 x)) := by
  obtain ⟨y, rfl⟩ := (twistChartSingletonFinsuppEquiv R d 0).symm.surjective x
  induction y using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single a r =>
      rw [twistChartSingletonFinsuppEquiv_symm_single]
      exact twistChartUnivEquivLaurent_twistChartInclusion_single d a.2 r

end Stacks.ProjectiveSpace.CechComparison

end

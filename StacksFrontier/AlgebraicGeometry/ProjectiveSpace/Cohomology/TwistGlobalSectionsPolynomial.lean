module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.PolynomialChartFractions
public import StacksFrontier.AlgebraicGeometry.ProjTwistSectionRing.Statement
public import StacksFrontier.AlgebraicGeometry.ProjStalkGlobalSections.TwistTrivialization

/-!
# `Γ(ℙⁿ_R, 𝒪(k)) = (R[T₀, …, Tₙ])_k`, through the canonical section map

Let `R` be a commutative ring, let `P = R[T₀, …, Tₙ]` carry its grading by total degree, so that
`ℙⁿ_R = Proj P`, and let `k ≥ 0`. [Stacks, Tag 01MP] attaches to a homogeneous element `a` of
degree `k` the global section `a / 1` of `𝒪(k)`,
`degreeSection`. This file proves that for the
polynomial ring that map is **bijective**:

$$ (R[T_0, \ldots, T_n])_k \xrightarrow{\ \sim\ } \Gamma(\mathbf{P}^n_R, \mathcal{O}(k)). $$

[Stacks, Tag 01XT] already computes `H⁰(ℙⁿ_R, 𝒪(k))` as an abstract `R`-module — that is
`Stacks.ProjectiveSpace.Cohomology.twistCohomologyIsoHomogeneous`, built from the Čech complex of
the standard cover — but it says nothing about *which* map realizes the identification, and an
injection between free modules of equal finite rank need not be onto. What is proved here is the
statement about the canonical map, which is what the multiplicative structure of
[Stacks, Tag 01MP] is carried by.

## The proof

The source's own argument, in the monomial model of
`StacksFrontier/AlgebraicGeometry/ProjectiveSpace/Cohomology/ChartSectionsComparison.lean`. A global
section `σ` of `𝒪(k)` restricts on the standard open `D₊(∏_{i ∈ s} Tᵢ)` to a Laurent polynomial
of total degree `k` regular outside `s`, and the identification is natural in `s`, so all those
Laurent polynomials are *one* element `v` of the free module on all Laurent exponent vectors. It
lies in the chart of every singleton `{i}`, hence in their intersection, which in nonnegative
degree is the polynomial chart; so `v` is a homogeneous polynomial `a` of degree `k`, and `a / 1`
and `σ` have the same restriction to every `D₊(Tᵢ)`. Those opens cover, so `σ = degreeSection a`.
Injectivity is the same computation read backwards: `a / 1 = b / 1` in `P[1/T₀]` gives
`T₀^N (a - b) = 0`, and `T₀` is a nonzerodivisor.

## Main definitions

* `Stacks.ProjectiveSpace.Cohomology.twistRes`, `.chartElt` and `.chartFraction`: the restriction
  of a global section of `𝒪(d)` to a standard chart, read respectively as a section, as a
  monomial chart element and as a fraction.

## Main results

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.eq_of_restrict_twistingSheaf_eq`: a global section
  of `𝒪(d)` on `Proj(S)` is determined by its restrictions to an open cover.
* `Stacks.ProjectiveSpace.Cohomology.coe_chartElt_eq`: **the monomial chart element of a global
  section does not depend on the chart.**
* `Stacks.ProjectiveSpace.Cohomology.chartFraction_degreeSection`: the canonical section of a
  homogeneous polynomial `a` is `a / 1` on every chart.
* `Stacks.ProjectiveSpace.Cohomology.injective_degreeSection` and
  `Stacks.ProjectiveSpace.Cohomology.surjective_degreeSection`.
* `Stacks.ProjectiveSpace.Cohomology.bijective_degreeSection_mvPolynomial`: **the canonical map
  `(R[T₀, …, Tₙ])_k ⟶ Γ(ℙⁿ_R, 𝒪(k))` is bijective.**

## Implementation notes

**Why the restriction maps are packaged as `twistRes`, `chartElt` and `chartFraction`.** Written
out, the restriction of a section of the twisting sheaf is
`(twistingSheaf 𝒜 d).val.map (homOfLE le_top).op σ` with `𝒜` the polynomial grading spelled in
full; a `rewrite` whose motive has to abstract that term does not terminate inside the default
heartbeat budget. Named, every step below is a `congrArg` or a `rewrite` at a one-symbol head.
The same consideration puts `eq_of_restrict_twistingSheaf_eq` in the general `Proj` setting with
`𝒜` a variable: specialized to the polynomial grading its proof runs out of budget, and
abstractly it costs nothing.

`Stacks.ProjectiveSpace.Cohomology.exists_mem_basicOpen_chartDenom_singleton` is stated before the
two transparency attributes of this file take effect. Under
`attribute [local instance_reducible] ProjectiveSpectrum.top` the coercion of the scheme
`AlgebraicGeometry.Proj 𝒜` to its carrier — which is what
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.exists_X_notMem_asHomogeneousIdeal` is stated
over — is expensive to unify with the homogeneous spectrum; outside their scope it is immediate.

**There are two `degreeSection`s in the library**, one in the `ProjTwistSections` namespace and
one in `AlgebraicGeometry.ProjectiveSpectrum.Proj`, with the same body and the same type. The one
used here is the `ProjTwistSections` one, because that is the one
`Stacks.AlgebraicGeometry.ProjTwistSectionRing.sectionsRingHom` — the ring map of
[Stacks, Tag 01MP] — is assembled from. The other is definitionally equal to it.

## What is not claimed

No `stacks` attribute is attached. [Stacks, Tag 01MP] asserts that the degreewise section maps
assemble into a graded ring homomorphism, which is proved as
`Stacks.AlgebraicGeometry.ProjTwistSectionRing.globalSectionsRingMap`; it does not assert that the
homomorphism is bijective for any particular graded ring. [Stacks, Tag 01XT] computes
`H^q(ℙⁿ_R, 𝒪(d))` as `R`-modules, and the whole content of this file is about which map does so.
The bijectivity for the polynomial ring is used by the source inside the proofs of
[Stacks, Tag 01YS] and [Stacks, Tag 089Z] without being stated as a lemma of its own.

## References

* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

section Separated

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Type u} {σ : Type u} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℤ)

/-- **A global section of `𝒪(d)` on `Proj(S)` is determined by its restrictions to an open
cover.** -/
theorem eq_of_restrict_twistingSheaf_eq {ι : Type*} (U : ι → Opens (ProjectiveSpectrum.top 𝒜))
    (hcover : ∀ x : ProjectiveSpectrum.top 𝒜, ∃ j, x ∈ U j)
    {a b : (twistingSheaf 𝒜 d).val.obj (op ⊤)}
    (h : ∀ j, (twistingSheaf 𝒜 d).val.map (homOfLE (le_top : U j ≤ ⊤)).op a
        = (twistingSheaf 𝒜 d).val.map (homOfLE (le_top : U j ≤ ⊤)).op b) : a = b := by
  apply (associatedModuleSheafSectionsEquiv 𝒜 (twistGrading (S := S) 𝒜 d) ⊤).injective
  apply Subtype.ext
  funext x
  obtain ⟨j, hj⟩ := hcover x.1
  have e (c : (twistingSheaf 𝒜 d).val.obj (op ⊤)) :=
    associatedModuleSheaf_restrict_apply (𝒜 := 𝒜) (𝒨 := twistGrading (S := S) 𝒜 d)
      (homOfLE (le_top : U j ≤ ⊤)) c ⟨x.1, hj⟩
  exact (e a).symm.trans ((congrArg (fun t => (associatedModuleSheafSectionsEquiv 𝒜
    (twistGrading (S := S) 𝒜 d) (U j) t).1 ⟨x.1, hj⟩) (h j)).trans (e b))

end Separated

end AlgebraicGeometry.ProjectiveSpectrum.Proj

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections

namespace Stacks.ProjectiveSpace.Cohomology

/-- The chart denominator of a singleton is the corresponding variable. -/
theorem chartDenom_singleton (R : Type u) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :
    chartDenom R n {i} = MvPolynomial.X i := by
  simp [chartDenom]

/-- **The standard coordinate charts cover `ℙⁿ_R`**: at every point of
`Proj R[T₀, …, Tₙ]` some variable lies outside the homogeneous prime. -/
theorem exists_mem_basicOpen_chartDenom_singleton (R : Type u) [CommRing R] (n : ℕ)
    (x : ProjectiveSpectrum.top (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) :
    ∃ i : Fin (n + 1), x ∈ ProjectiveSpectrum.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (chartDenom R n {i}) := by
  obtain ⟨i, hi⟩ :=
    ProjStalkGlobalSections.exists_X_notMem_asHomogeneousIdeal R n x
  exact ⟨i, by rw [chartDenom_singleton]; exact hi⟩

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)

/-- The global sections of `𝒪(d)` on `ℙⁿ_R`. -/
abbrev twistTopSections :=
  (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d).val.obj (op ⊤)

/-- The restriction of a global section of `𝒪(d)` to the standard open `D₊(∏_{i ∈ s} Tᵢ)`. -/
def twistRes (s : Finset (Fin (n + 1))) (σ : twistTopSections R n d) :
    chartSheafSections R n d s :=
  (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d).val.map
    (homOfLE le_top).op σ

/-- The monomial chart element of the restriction of a global section of `𝒪(d)` to
`D₊(∏_{i ∈ s} Tᵢ)`. -/
def chartElt (s : Finset (Fin (n + 1))) (hs : s.Nonempty) (σ : twistTopSections R n d) :
    twistChart R n d (↑s : Set (Fin (n + 1))) :=
  chartSectionsAddEquivTwistChart R n d s hs (twistRes R n d s σ)

/-- The fraction representing the restriction of a global section of `𝒪(d)` to
`D₊(∏_{i ∈ s} Tᵢ)`. -/
def chartFraction (s : Finset (Fin (n + 1))) (hs : s.Nonempty) (σ : twistTopSections R n d) :
    LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R) :=
  (chartSectionsAddEquiv R n d s hs (twistRes R n d s σ) : _)

variable {R n d}

/-- The chart element and the chart fraction describe the same restriction. -/
theorem chartFraction_eq (s : Finset (Fin (n + 1))) (hs : s.Nonempty)
    (σ : twistTopSections R n d) :
    chartFraction R n d s hs σ
      = ((twistChartEquivTwistSections R n d s (chartElt R n d s hs σ) :
          twistSections R n d s) :
        LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R)) := by
  rw [chartElt, chartSectionsAddEquivTwistChart, AddEquiv.trans_apply]
  exact congrArg Subtype.val
    ((twistChartEquivTwistSections R n d s).apply_symm_apply _).symm

/-- A global section of `𝒪(d)` is determined on a standard chart by its chart fraction. -/
theorem twistRes_injective (s : Finset (Fin (n + 1))) (hs : s.Nonempty)
    {σ τ : twistTopSections R n d} (h : chartFraction R n d s hs σ = chartFraction R n d s hs τ) :
    twistRes R n d s σ = twistRes R n d s τ :=
  (chartSectionsAddEquiv R n d s hs).injective (Subtype.ext h)

/-- **The monomial chart element of a global section does not depend on the chart**: for
`s ⊆ t` the two chart elements have the same Laurent coefficients. -/
theorem coe_chartElt_eq (s t : Finset (Fin (n + 1))) (hs : s.Nonempty) (ht : t.Nonempty)
    (hst : s ⊆ t) (σ : twistTopSections R n d) :
    ((chartElt R n d t ht σ :
        twistChart R n d (↑t : Set (Fin (n + 1)))) : (Fin (n + 1) → ℤ) →₀ R)
      = ((chartElt R n d s hs σ :
        twistChart R n d (↑s : Set (Fin (n + 1)))) : (Fin (n + 1) → ℤ) →₀ R) :=
  congrArg Subtype.val
    (chartSectionsAddEquivTwistChart_map_homOfLE R n d s t hs hst (twistRes R n d s σ))

/-- **A global section of `𝒪(d)` on `ℙⁿ_R` is determined by its restrictions to the standard
coordinate charts `D₊(Tᵢ)`**, which cover `ℙⁿ_R`. -/
theorem eq_of_twistRes_singleton_eq {σ τ : twistTopSections R n d}
    (h : ∀ i : Fin (n + 1), twistRes R n d {i} σ = twistRes R n d {i} τ) : σ = τ :=
  eq_of_restrict_twistingSheaf_eq (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d
    (fun i : Fin (n + 1) => ProjectiveSpectrum.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (chartDenom R n {i}))
    (exists_mem_basicOpen_chartDenom_singleton R n) h

/-! ### The canonical section map in nonnegative degrees -/

/-- **The canonical global section of a homogeneous polynomial is the fraction `a / 1` on every
standard chart.** -/
theorem chartFraction_degreeSection (R : Type u) [CommRing R] (n k : ℕ)
    (s : Finset (Fin (n + 1))) (hs : s.Nonempty)
    (a : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R k) :
    chartFraction R n (k : ℤ) s hs
        (degreeSection
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) k a)
      = LocalizedModule.mk (a : MvPolynomial (Fin (n + 1)) R) 1 := by
  have h := degreeZeroToGlobalSections_basicOpen
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (twistGrading (S := MvPolynomial (Fin (n + 1)) R)
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (k : ℤ))
    (chartDenom_mem_homogeneousSubmodule n s) (Finset.card_pos.2 hs)
    ⟨(a : MvPolynomial (Fin (n + 1)) R),
      ProjTwistSections.mem_twistGrading_zero _ a⟩
  refine (congrArg Subtype.val h).trans ?_
  congr 1

/-- **A power of a variable is a nonzerodivisor on a polynomial ring.** -/
theorem eq_of_X_pow_mul_eq {σ : Type*} (R : Type u) [CommRing R] (i : σ) (N : ℕ)
    {f g : MvPolynomial σ R}
    (h : MvPolynomial.X i ^ N * f = MvPolynomial.X i ^ N * g) : f = g := by
  have hz : MvPolynomial.X i ^ N * (f - g) = 0 := by rw [mul_sub, h, sub_self]
  have hfg : f - g = 0 := by
    refine MvPolynomial.ext _ _ fun m => ?_
    have h2 := congrArg (MvPolynomial.coeff (Finsupp.single i N + m)) hz
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial_mul, one_mul,
      MvPolynomial.coeff_zero] at h2
    rw [h2, MvPolynomial.coeff_zero]
  exact sub_eq_zero.mp hfg

/-- **The canonical map `(R[T₀, …, Tₙ])_k ⟶ Γ(ℙⁿ_R, 𝒪(k))` is injective.** -/
theorem injective_degreeSection (R : Type u) [CommRing R] (n k : ℕ) :
    Function.Injective (degreeSection
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) k) := by
  have hs : ({0} : Finset (Fin (n + 1))).Nonempty := ⟨0, Finset.mem_singleton_self 0⟩
  intro a b hab
  have h := congrArg (chartFraction R n (k : ℤ) {0} hs) hab
  rw [chartFraction_degreeSection, chartFraction_degreeSection] at h
  obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp h
  obtain ⟨N, hN⟩ := u.2
  refine Subtype.ext (eq_of_X_pow_mul_eq R 0 N ?_)
  have hu' : (u : MvPolynomial (Fin (n + 1)) R) * (a : MvPolynomial (Fin (n + 1)) R)
      = (u : MvPolynomial (Fin (n + 1)) R) * (b : MvPolynomial (Fin (n + 1)) R) := by
    simpa [Submonoid.smul_def, smul_eq_mul] using hu
  have hN' : chartDenom R n {0} ^ N = (u : MvPolynomial (Fin (n + 1)) R) := hN
  rw [← chartDenom_singleton R n 0, hN']
  exact hu'

/-- **The canonical map `(R[T₀, …, Tₙ])_k ⟶ Γ(ℙⁿ_R, 𝒪(k))` is surjective.** -/
theorem surjective_degreeSection (R : Type u) [CommRing R] (n k : ℕ) :
    Function.Surjective (degreeSection
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) k) := by
  intro σ
  have hsi : ∀ i : Fin (n + 1), ({i} : Finset (Fin (n + 1))).Nonempty :=
    fun i => ⟨i, Finset.mem_singleton_self i⟩
  have huniv : (Finset.univ : Finset (Fin (n + 1))).Nonempty := ⟨0, Finset.mem_univ 0⟩
  have hcoe : ∀ i : Fin (n + 1),
      (chartElt R n (k : ℤ) Finset.univ huniv σ : (Fin (n + 1) → ℤ) →₀ R)
        = ((chartElt R n (k : ℤ) {i} (hsi i) σ) : (Fin (n + 1) → ℤ) →₀ R) :=
    fun i => coe_chartElt_eq {i} Finset.univ (hsi i) huniv (Finset.subset_univ _) σ
  have hchart : ∀ i : Fin (n + 1),
      ((chartElt R n (k : ℤ) Finset.univ huniv σ) : (Fin (n + 1) → ℤ) →₀ R)
        ∈ twistChart R n (k : ℤ) (↑({i} : Finset (Fin (n + 1))) : Set (Fin (n + 1))) :=
    fun i => (hcoe i).symm ▸ (chartElt R n (k : ℤ) {i} (hsi i) σ).2
  have hv0 : ((chartElt R n (k : ℤ) Finset.univ huniv σ) : (Fin (n + 1) → ℤ) →₀ R)
      ∈ twistChart R n (k : ℤ) (∅ : Set (Fin (n + 1))) := by
    rw [← twistChart_iInf_singleton_of_nonneg R n (Int.natCast_nonneg k)]
    refine Submodule.mem_iInf _ |>.2 fun i => ?_
    have hi := hchart i
    rwa [Finset.coe_singleton] at hi
  obtain ⟨a, ha⟩ := exists_homogeneous_coe_twistChartEquivTwistSections R n k hv0
  refine ⟨a, eq_of_twistRes_singleton_eq fun i => twistRes_injective {i} (hsi i) ?_⟩
  rw [chartFraction_degreeSection, chartFraction_eq]
  have hce : chartElt R n (k : ℤ) {i} (hsi i) σ =
      ⟨((chartElt R n (k : ℤ) Finset.univ huniv σ) : (Fin (n + 1) → ℤ) →₀ R), hchart i⟩ :=
    Subtype.ext (hcoe i).symm
  rw [hce, ha {i} (hchart i)]

/-- **`Γ(ℙⁿ_R, 𝒪(k)) = (R[T₀, …, Tₙ])_k` through the canonical section map of
[Stacks, Tag 01MP]**, for every `n ≥ 0` and every `k ≥ 0`. -/
theorem bijective_degreeSection_mvPolynomial (R : Type u) [CommRing R] (n k : ℕ) :
    Function.Bijective (degreeSection
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) k) :=
  ⟨injective_degreeSection R n k, surjective_degreeSection R n k⟩

end Stacks.ProjectiveSpace.Cohomology

end

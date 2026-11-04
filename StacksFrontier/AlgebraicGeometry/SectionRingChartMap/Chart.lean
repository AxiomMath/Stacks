module

public import StacksFrontier.AlgebraicGeometry.SectionRingChartMap.Multiplicative
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DegreeZeroLocalizationArbitraryDegree
public import StacksFrontier.AlgebraicGeometry.ProjF1DegreeOneChart.Basic

/-!
# The chart `X_a ⟶ Proj Γ_*(X, L)` of Stacks Tag 01PZ

Let `X` be a scheme, `L` an invertible `𝒪_X`-module and `a` a global section of `L ^⊗ d` for some
`d > 0`, that is a homogeneous element of degree `d` of the graded section ring
`Γ_*(X, L) = ⨁_{n ≥ 0} Γ(X, L ^⊗ n)` of Stacks Tag 01CV. This file builds the morphism

`X_a ⟶ Proj Γ_*(X, L)`

landing in the chart `D₊(a)`, which is the local piece out of which the canonical morphism
`X ⟶ Proj Γ_*(X, 𝓛)` of Stacks Tag 01PZ is glued.

Two known results do all the work and this file only has to supply the ring map between them.

* `Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.chartHomEquiv` is the bijection between the
  morphisms `Y ⟶ Proj 𝒜` whose preimage of `D₊(r)` is everything and the ring homomorphisms out
  of `HomogeneousLocalization.Away 𝒜 r`, for `r` homogeneous of any positive degree. So the
  morphism *is* the ring map.
* `Stacks.SheafOfModules.homogeneousLocalizationLiftOfDegree` builds such a ring homomorphism out
  of a family `e : ℕ → Γ_*(X, L) →+ Γ(X, X_a)` indexed by the exponent of the denominator,
  provided the family is compatible with multiplying numerator and denominator by `a`, sends `1`
  to `1`, and is multiplicative.

## Main definitions

* `Stacks.SectionRingChartMap.chartFamily`: **the family of numerator maps**,
  `e n z = (a · z)_{d (n+1)} / a^{n+1}`, the ratio produced by
  `StacksFrontier/AlgebraicGeometry/SectionRingChartMap/Division.lean` at the *shifted* exponent.
* `Stacks.SectionRingChartMap.chartRingMap`: **the chart ring map**, a ring homomorphism
  `Γ_*(X, L)₍a₎ = HomogeneousLocalization.Away (grading L) a → Γ(X, V)` for any open `V ≤ X_a`.
* `Stacks.SectionRingChartMap.chartHom`: **the chart morphism** `X_a ⟶ Proj Γ_*(X, L)`, together
  with `Stacks.SectionRingChartMap.chartHom_preimage_basicOpen`, which says it lands in `D₊(a)`.

## Main results

* `Stacks.SectionRingChartMap.chartFamily_one`, `chartFamily_pow_mul`, `chartFamily_mul`: the
  three hypotheses of the lift, for this family.
* `Stacks.SectionRingChartMap.chartRingMap_mk`: **the value of the chart ring map on a
  fraction** `x / aⁿ` with `x` homogeneous of degree `n d`: it is the ratio `(a x) / a^{n+1}`.
* `Stacks.SectionRingChartMap.chartHomEquiv_chartHom`: the chart morphism induces the chart ring
  map, which by `Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.eq_of_chartHomEquiv_eq` determines
  it uniquely among morphisms landing in `D₊(a)`.

## The exponent shift

The lift consumes the family at the exponent **zero** as well, and division by `a⁰` is not
division: the zeroth power `Stacks.SectionExtension.powSec L a 0` is the unit of the section ring,
whose nonvanishing open is not known to be all of `X` (see the "What is not done" of
`StacksFrontier/AlgebraicGeometry/SectionExtension/Powers.lean`). The family is therefore defined
with a uniform shift,

`e n z = (a · z) / a^{n+1}`,

whose denominator exponent is positive for every `n`. On a numerator `x` of degree `n d` this is
the same element as `x / aⁿ` — multiplying numerator and denominator of a fraction by `a` does not
change it — and the exponent-zero member stops being special: `e 0 1` is `a / a¹`, which is
`Stacks.SectionRingChartMap.numMapR_of_self`, and the other two hypotheses are the
positive-exponent identities of `SectionRingChartMap/Multiplicative.lean` applied to `a · z`
rather than to `z`.

No degree-zero reading of a section as a function is needed, and in particular neither
`Stacks.SectionRingGeometric.tensorUnitHomAddEquiv` nor
`AlgebraicGeometry.SheafOfModules.unitIso` is brought in.

## References

* [Stacks Project, Tag 01PZ](https://stacks.math.columbia.edu/tag/01PZ)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01NA](https://stacks.math.columbia.edu/tag/01NA)

## What is not done

**The glued morphism `X ⟶ Proj Γ_*(X, L)` is not constructed**, so Stacks Tag 01PZ is not proved
and **no `@[stacks]` attribute is attached here**: what is built is one chart of it. Gluing needs
the charts to agree on the overlaps `X_a ⊓ X_b = X_{ab}`, whose chart dictionary is
`StacksFrontier/AlgebraicGeometry/SectionRingProjOverlap/Basic.lean`, and the cover of `X` by the
`X_a` for `a` of positive degree, which is ampleness; neither is used here. Nothing is claimed
about the chart ring map being an isomorphism either: the criteria
`Stacks.SheafOfModules.homogeneousLocalizationLiftOfDegree_injective` and
`..._surjective` are available and not invoked, and bijectivity is not needed to produce the
morphism.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections mul sectionRing)
open Stacks.SectionProduct (globalSection)
open Stacks.SectionExtension (powSec)
open Stacks.AmpleFiniteAvoidance (nvOpen grading)

universe u

namespace Stacks.SectionRingChartMap

section Monoidal

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
  {d : ℕ} (a : powSections L d) {V : X.Opens}

/-! ### The family of numerator maps -/

/-- **The family of numerator maps of the chart at `a`.** Its `n`-th member sends a ring element
`z` to the ratio of the degree-`d (n+1)` component of `a · z` by `a^{n+1}`, on `V`.

The exponent is shifted by one so that every denominator is a *positive* power of `a` and every
member is an honest division; on a numerator homogeneous of degree `n d` the value is the same as
the ratio of `z` by `aⁿ`, which is what makes this the family the degree-zero localization asks
for. -/
public noncomputable def chartFamily (hV : V ≤ nvOpen L a) (n : ℕ) :
    sectionRing L →+ Γ(X, V) :=
  (numMapR L a hV (n + 1) (Nat.le_add_left 1 n)).comp
    (AddMonoidHom.mulLeft (DirectSum.of (powSections L) d a))

/-- The `n`-th member of `Stacks.SectionRingChartMap.chartFamily` at `z` is `numMapR` applied to
`a · z`. -/
public theorem chartFamily_apply (hV : V ≤ nvOpen L a) (n : ℕ) (z : sectionRing L) :
    chartFamily L a hV n z
      = numMapR L a hV (n + 1) (Nat.le_add_left 1 n)
          (DirectSum.of (powSections L) d a * z) := rfl

/-- **The family is the division of `SectionRingChartMap/Division.lean`.** If `a · z` is the
homogeneous element named by a section `t` of `L ^⊗ (d (n+1))`, then the `n`-th member of the
family at `z` is the ratio `t / a^{n+1}` of `Stacks.SectionRingChartMap.numMap`. This is what
makes the chart ring map the geometric ratio rather than a formal construction. -/
public theorem chartFamily_eq_numMap (hV : V ≤ nvOpen L a) (n : ℕ) (z : sectionRing L)
    (t : powSections L (d * (n + 1)))
    (ht : DirectSum.of (powSections L) (d * (n + 1)) t
      = DirectSum.of (powSections L) d a * z) :
    chartFamily L a hV n z
      = numMap L a hV (n + 1) (Nat.le_add_left 1 n) (globalSection X _ t) := by
  rw [chartFamily_apply, ← ht, numMapR_of]

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- The degree of a product of homogeneous elements: the only degree arithmetic in this file, an
arithmetic of the *index* of `Stacks.AmpleFiniteAvoidance.grading`, whose values are additive
subgroups of one and the same ring, so it is a rewrite inside a proposition and transports
nothing. -/
private theorem mul_mem_grading {i j k : ℕ} (h : k = i + j) {x y : sectionRing L}
    (hx : x ∈ grading L i) (hy : y ∈ grading L j) : x * y ∈ grading L k :=
  h ▸ SetLike.mul_mem_graded hx hy

/-- **The unit law.** `e 0 1` is the ratio of `a` by `a¹`, which is `1`. -/
public theorem chartFamily_one (hV : V ≤ nvOpen L a) : chartFamily L a hV 0 1 = 1 := by
  show numMapR L a hV 1 (Nat.le_add_left 1 0)
    (DirectSum.of (powSections L) d a * 1) = 1
  rw [mul_one, numMapR_of_self]

/-- **The compatibility with multiplying numerator and denominator by a power of `a`.** -/
public theorem chartFamily_pow_mul (hV : V ≤ nvOpen L a) (n k : ℕ) (x : sectionRing L)
    (hx : x ∈ grading L (n * d)) :
    chartFamily L a hV (n + k) (DirectSum.of (powSections L) d a ^ k * x)
      = chartFamily L a hV n x := by
  have hfx : DirectSum.of (powSections L) d a * x ∈ grading L (d * (n + 1)) :=
    mul_mem_grading L (by ring) (Stacks.ExternalGrading.of_mem_summand d a) hx
  show numMapR L a hV (n + k + 1) (Nat.le_add_left 1 (n + k))
      (DirectSum.of (powSections L) d a *
        (DirectSum.of (powSections L) d a ^ k * x))
    = numMapR L a hV (n + 1) (Nat.le_add_left 1 n) (DirectSum.of (powSections L) d a * x)
  rw [mul_left_comm]
  exact numMapR_pow_mul' L a hV (n + 1) k (n + k + 1) (by omega) (Nat.le_add_left 1 n)
    (Nat.le_add_left 1 (n + k)) hfx

/-- **Multiplicativity.** The product of the two shifted ratios carries one factor of `a` too
many, and `Stacks.SectionRingChartMap.numMapR_of_mul` removes it. -/
public theorem chartFamily_mul (hV : V ≤ nvOpen L a) (n m : ℕ) (x y : sectionRing L)
    (hx : x ∈ grading L (n * d)) (hy : y ∈ grading L (m * d)) :
    chartFamily L a hV (n + m) (x * y)
      = chartFamily L a hV n x * chartFamily L a hV m y := by
  have hfx : DirectSum.of (powSections L) d a * x ∈ grading L (d * (n + 1)) :=
    mul_mem_grading L (by ring) (Stacks.ExternalGrading.of_mem_summand d a) hx
  have hfy : DirectSum.of (powSections L) d a * y ∈ grading L (d * (m + 1)) :=
    mul_mem_grading L (by ring) (Stacks.ExternalGrading.of_mem_summand d a) hy
  have hfxy : DirectSum.of (powSections L) d a * (x * y) ∈ grading L (d * (n + m + 1)) :=
    mul_mem_grading L (by ring) (Stacks.ExternalGrading.of_mem_summand d a)
      (mul_mem_grading L (k := (n + m) * d) (by ring) hx hy)
  show numMapR L a hV (n + m + 1) (Nat.le_add_left 1 (n + m))
      (DirectSum.of (powSections L) d a * (x * y))
    = numMapR L a hV (n + 1) (Nat.le_add_left 1 n) (DirectSum.of (powSections L) d a * x)
      * numMapR L a hV (m + 1) (Nat.le_add_left 1 m) (DirectSum.of (powSections L) d a * y)
  calc numMapR L a hV (n + m + 1) (Nat.le_add_left 1 (n + m))
          (DirectSum.of (powSections L) d a * (x * y))
      = numMapR L a hV (n + m + 1 + 1) (Nat.le_add_left 1 (n + m + 1))
          (DirectSum.of (powSections L) d a *
            (DirectSum.of (powSections L) d a * (x * y))) :=
        (numMapR_of_mul L a hV (n + m + 1) (Nat.le_add_left 1 (n + m))
          (Nat.le_add_left 1 (n + m + 1)) hfxy).symm
    _ = numMapR L a hV (n + m + 1 + 1) (Nat.le_add_left 1 (n + m + 1))
          ((DirectSum.of (powSections L) d a * x) *
            (DirectSum.of (powSections L) d a * y)) := by
        rw [show DirectSum.of (powSections L) d a *
              (DirectSum.of (powSections L) d a * (x * y))
            = (DirectSum.of (powSections L) d a * x) *
              (DirectSum.of (powSections L) d a * y) from by ring]
    _ = _ :=
        numMapR_mul' L a hV (n + 1) (m + 1) (n + m + 1 + 1) (by omega) (Nat.le_add_left 1 n)
          (Nat.le_add_left 1 m) (Nat.le_add_left 1 (n + m + 1)) hfx hfy

/-! ### The chart ring map -/

/-- **The chart ring map at `a`.** A ring homomorphism out of the degree-zero part
`Γ_*(X, L)₍a₎ = HomogeneousLocalization.Away (grading L) a` of the localization of the section
ring at `a`, to the functions on any open `V ≤ X_a`. On the fraction `x / aⁿ` it is the ratio
`(a x) / a^{n+1}` (`Stacks.SectionRingChartMap.chartRingMap_mk`), which is the geometric ratio
`x / aⁿ` on `V`.

This is the map out of which the morphism `X_a ⟶ Proj Γ_*(X, L)` of Stacks Tag 01PZ is produced
by `Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.chartHomEquiv`. -/
public noncomputable def chartRingMap (hV : V ≤ nvOpen L a) :
    HomogeneousLocalization.Away (grading L) (DirectSum.of (powSections L) d a) →+* Γ(X, V) :=
  Stacks.SheafOfModules.homogeneousLocalizationLiftOfDegree (grading L)
    (Stacks.ExternalGrading.of_mem_summand d a) (chartFamily L a hV)
    (chartFamily_pow_mul L a hV) (chartFamily_one L a hV) (chartFamily_mul L a hV)

/-- **The value of the chart ring map on a fraction.** -/
public theorem chartRingMap_mk (hV : V ≤ nvOpen L a) (n : ℕ) (x : sectionRing L)
    (hx : x ∈ grading L (n • d)) :
    chartRingMap L a hV
        (HomogeneousLocalization.Away.mk (grading L)
          (Stacks.ExternalGrading.of_mem_summand d a) n x hx)
      = chartFamily L a hV n x :=
  Stacks.SheafOfModules.homogeneousLocalizationLiftOfDegree_mk (grading L)
    (Stacks.ExternalGrading.of_mem_summand d a) (chartFamily L a hV)
    (chartFamily_pow_mul L a hV) (chartFamily_one L a hV) (chartFamily_mul L a hV) n x hx

/-- **The chart ring map on a fraction, as a division of sections.** The fraction `x / aⁿ` with
`x` homogeneous of degree `n d` goes to the ratio `(a x) / a^{n+1}` of
`Stacks.SectionRingChartMap.numMap`, where `a x` is named by the section `t`. -/
public theorem chartRingMap_mk_eq_numMap (hV : V ≤ nvOpen L a) (n : ℕ) (x : sectionRing L)
    (hx : x ∈ grading L (n • d)) (t : powSections L (d * (n + 1)))
    (ht : DirectSum.of (powSections L) (d * (n + 1)) t
      = DirectSum.of (powSections L) d a * x) :
    chartRingMap L a hV
        (HomogeneousLocalization.Away.mk (grading L)
          (Stacks.ExternalGrading.of_mem_summand d a) n x hx)
      = numMap L a hV (n + 1) (Nat.le_add_left 1 n) (globalSection X _ t) := by
  rw [chartRingMap_mk, chartFamily_eq_numMap L a hV n x t ht]

/-! ### The chart morphism -/

/-- **The chart morphism `X_a ⟶ Proj Γ_*(X, L)`, with the proof that it lands in `D₊(a)`.**
`Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.chartHomEquiv` read backwards at the chart ring
map, after identifying the global sections of the open subscheme `X_a` with the sections of
`𝒪_X` over `X_a`. -/
public noncomputable def chartHomSubtype (hd : 0 < d) :
    {g : (nvOpen L a).toScheme ⟶ Proj (grading L) //
      g ⁻¹ᵁ Proj.basicOpen (grading L) (DirectSum.of (powSections L) d a) = ⊤} :=
  (Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.chartHomEquiv (grading L)
      (Stacks.ExternalGrading.of_mem_summand d a) hd (nvOpen L a).toScheme).symm
    (CommRingCat.ofHom (chartRingMap L a (le_refl (nvOpen L a))) ≫
      (Scheme.Opens.topIso (nvOpen L a)).inv)

/-- **The chart morphism `X_a ⟶ Proj Γ_*(X, L)`.** This is the first object Stacks Tag 01PZ gets:
the canonical morphism of the tag is glued from these over the cover of `X` by the nonvanishing
opens of homogeneous sections of positive degree. -/
public noncomputable def chartHom (hd : 0 < d) :
    (nvOpen L a).toScheme ⟶ Proj (grading L) :=
  (chartHomSubtype L a hd).1

/-- **The chart morphism lands in `D₊(a)`.** This is clause (1) of Stacks Tag 01PZ for the chart,
read on `X_a` rather than on `X`. -/
public theorem chartHom_preimage_basicOpen (hd : 0 < d) :
    chartHom L a hd ⁻¹ᵁ Proj.basicOpen (grading L) (DirectSum.of (powSections L) d a) = ⊤ :=
  (chartHomSubtype L a hd).2

/-- **The chart morphism induces the chart ring map.** With
`Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.eq_of_chartHomEquiv_eq` this characterizes
`chartHom` uniquely among the morphisms `X_a ⟶ Proj Γ_*(X, L)` landing in `D₊(a)`. -/
public theorem chartHomEquiv_chartHom (hd : 0 < d) :
    Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.chartHomEquiv (grading L)
        (Stacks.ExternalGrading.of_mem_summand d a) hd (nvOpen L a).toScheme
        ⟨chartHom L a hd, chartHom_preimage_basicOpen L a hd⟩
      = CommRingCat.ofHom (chartRingMap L a (le_refl (nvOpen L a))) ≫
          (Scheme.Opens.topIso (nvOpen L a)).inv :=
  (Stacks.AlgebraicGeometry.ProjF1DegreeOneChart.chartHomEquiv (grading L)
      (Stacks.ExternalGrading.of_mem_summand d a) hd (nvOpen L a).toScheme).apply_symm_apply _

end Monoidal

end Stacks.SectionRingChartMap

end

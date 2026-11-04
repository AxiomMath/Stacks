module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.CechComparison.OverlapRing
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.TwistSections.Basic

/-!
# The overlap term of the Čech complex of the projective line

The standard two-chart cover of `ℙ¹_R` has one overlap, `D₊(X₀X₁)`, and the Čech complex of the
twist `𝒪(d)` for that cover is

`Γ(D₊(X₀), 𝒪(d)) ⊕ Γ(D₊(X₁), 𝒪(d)) ⟶ Γ(D₊(X₀X₁), 𝒪(d))`,  `(a, b) ↦ a - b`.

`Stacks.ProjectiveSpace.TwistSections.twistSectionsAddEquivTwistChart` identifies the two chart
terms with the monomial charts
`Stacks.ProjectiveSpace.Cohomology.twistChart R 1 d {i}` on which
`Stacks.ProjectiveSpace.Cohomology.lineCechDiff` is defined. This file does the same for the
overlap term, which completes the identification of the three objects of that complex.

The degree-`d` Laurent monomials of the projective line with no regularity condition are the
`T₀^{d-a} T₁^{a}` for `a : ℤ`, so the overlap chart is the free `R`-module on `ℤ`, which is the
Laurent ring `R[t, t⁻¹]`; and the sections of `𝒪(d)` over `D₊(X₀X₁)` are free of rank one over
the ring of functions on that open by
`Stacks.ProjectiveSpace.TwistSections.twistSectionsOverlapEquivAway`, while that ring is
`R[t, t⁻¹]` by `Stacks.ProjectiveSpace.CechComparison.overlapAlgEquivLaurent`. Composing the
three gives the overlap term.

## Main definitions

* `Stacks.ProjectiveSpace.CechComparison.lineOverlapExponents` — the exponent vector of the
  degree-`d` Laurent monomial `T₀^{d-a} T₁^{a}`.
* `Stacks.ProjectiveSpace.CechComparison.twistChartUnivEquivLaurent` — the overlap chart of the
  projective line is the Laurent ring, as an `R`-module.

## Main results

* `Stacks.ProjectiveSpace.CechComparison.laurentMonomialsUnivFinTwoEquiv` — a degree-`d` Laurent
  monomial of the projective line is determined by its exponent at `T₁`.
* `Stacks.ProjectiveSpace.CechComparison.overlapSectionsAddEquivTwistChart` — **the overlap term
  of the Čech complex.** For `0 ≤ d` the sections of `𝒪(d)` over `D₊(X₀X₁)` are the monomial
  chart `twistChart R 1 d Set.univ`.

## Implementation notes

`overlapSectionsAddEquivTwistChart` keeps the section `f` of the standard open a variable with a
hypothesis `f = X₀X₁` rather than writing the product into its type. Writing the literal term
there makes the elaborator search for `AddCommMonoid ↥(twistSections R (X 0 * X 1) d)` and exceed
the default `synthInstance` heartbeat budget, although the same instance is found at once when
the argument is a variable; this is why `twistSectionsOverlapEquivAway` is phrased with a
factorization hypothesis in the first place.

As with `Stacks.ProjectiveSpace.TwistSections.twistSectionsAddEquivTwistChart`, the bridge is an
additive equivalence: the sections are linear over the ring of functions on the overlap and the
monomial chart is linear over `R`, and the two linearity statements are the separate results
`twistSectionsOverlapEquivAway`, `overlapAlgEquivLaurent` and `twistChartUnivEquivLaurent`.

No `@[stacks]` attribute is attached: the computation of the cohomology of `𝒪(d)` on `ℙⁿ` is tag
01XT, whose covering set needs the comparison of Čech with derived cohomology (tag 01XD) as well
as the identification of the Čech complex carried out here.

## References

* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open MvPolynomial Stacks.ProjectiveSpace.Cohomology Stacks.ProjectiveSpace.TwistSections

universe u

namespace Stacks.ProjectiveSpace.CechComparison

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R]

/-- The exponent vector of the degree-`d` Laurent monomial `T₀^{d-a} T₁^{a}` of the projective
line. Every degree-`d` Laurent monomial is of this form. -/
def lineOverlapExponents (d a : ℤ) : Fin 2 → ℤ := fun j => if j = 0 then d - a else a

/-- The exponent of `T₀` in the monomial `T₀^{d-a} T₁^{a}` is `d - a`. -/
@[simp]
theorem lineOverlapExponents_zero (d a : ℤ) : lineOverlapExponents d a 0 = d - a := by
  simp [lineOverlapExponents]

/-- The exponent of `T₁` in the monomial `T₀^{d-a} T₁^{a}` is `a`. -/
@[simp]
theorem lineOverlapExponents_one (d a : ℤ) : lineOverlapExponents d a 1 = a := by
  simp [lineOverlapExponents]

/-- The projective line has two coordinates, so an index other than `0` is `1`. -/
theorem eq_one_of_ne_zero_fin_two {j : Fin 2} (h : j ≠ 0) : j = 1 := by
  fin_cases j
  · exact absurd rfl h
  · rfl

/-- `T₀^{d-a} T₁^{a}` is a degree-`d` Laurent monomial of the projective line. -/
theorem lineOverlapExponents_mem (d a : ℤ) :
    lineOverlapExponents d a ∈ laurentMonomials 1 d (Set.univ : Set (Fin 2)) := by
  refine ⟨?_, fun i hi => absurd (Set.mem_univ i) hi⟩
  rw [Fin.sum_univ_two, lineOverlapExponents_zero, lineOverlapExponents_one]
  ring

/-- The two exponents of a degree-`d` Laurent monomial of the projective line sum to `d`. -/
theorem add_eq_of_mem_laurentMonomials_univ {d : ℤ} {e : Fin 2 → ℤ}
    (he : e ∈ laurentMonomials 1 d (Set.univ : Set (Fin 2))) : e 0 + e 1 = d := by
  have h := (mem_laurentMonomials.1 he).1
  rwa [Fin.sum_univ_two] at h

/-- **A degree-`d` Laurent monomial of the projective line is its exponent at `T₁`.** The
exponent at `T₀` is then forced by the total degree, and no regularity condition constrains
either, so the overlap chart is indexed by `ℤ`. -/
def laurentMonomialsUnivFinTwoEquiv (d : ℤ) :
    laurentMonomials 1 d (Set.univ : Set (Fin 2)) ≃ ℤ where
  toFun e := e.1 1
  invFun a := ⟨lineOverlapExponents d a, lineOverlapExponents_mem d a⟩
  left_inv e := Subtype.ext (funext fun j => by
    have hsum := add_eq_of_mem_laurentMonomials_univ e.2
    change lineOverlapExponents d (e.1 1) j = e.1 j
    rcases eq_or_ne j 0 with rfl | hj
    · rw [lineOverlapExponents_zero]; omega
    · rw [eq_one_of_ne_zero_fin_two hj, lineOverlapExponents_one])
  right_inv a := lineOverlapExponents_one d a

/-- **The overlap chart of the projective line is the Laurent ring.** The degree-`d` part of
`R[T₀, T₁][1/T₀T₁]` is free as an `R`-module on `ℤ`, the basis element attached to `a` being the
Laurent monomial `T₀^{d-a} T₁^{a}`. -/
def twistChartUnivEquivLaurent (R : Type u) [CommRing R] (d : ℤ) :
    twistChart R 1 d (Set.univ : Set (Fin 2)) ≃ₗ[R] LaurentPolynomial R :=
  (Finsupp.supportedEquivFinsupp _).trans
    ((Finsupp.domLCongr (laurentMonomialsUnivFinTwoEquiv d)).trans
      (AddMonoidAlgebra.coeffLinearEquiv R).symm)

/-- The ring of functions on an open of the form `D₊(X₀X₁)` is the Laurent ring. This is
`Stacks.ProjectiveSpace.CechComparison.overlapAlgEquivLaurent` read at a section presented by a
factorization hypothesis rather than as a literal product; see the implementation notes. -/
def awayAddEquivLaurent (R : Type u) [CommRing R] {f : MvPolynomial (Fin 2) R}
    (hfac : f = X 0 * X 1) :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) R) f ≃+ LaurentPolynomial R := by
  subst hfac
  exact (overlapAlgEquivLaurent R).toAddEquiv

/-- **The overlap term of the Čech complex of the standard cover of the projective line.** For
`0 ≤ d` the sections of `𝒪(d)` over the overlap `D₊(X₀X₁)` of the two standard charts are the
monomial chart `Stacks.ProjectiveSpace.Cohomology.twistChart R 1 d Set.univ`, on which
`Stacks.ProjectiveSpace.Cohomology.lineCechDiff` takes its values. With
`Stacks.ProjectiveSpace.TwistSections.twistSectionsAddEquivTwistChart` for the two chart terms,
this identifies all three objects of that complex. -/
def overlapSectionsAddEquivTwistChart (R : Type u) [CommRing R] {f : MvPolynomial (Fin 2) R}
    (hfac : f = X 0 * X 1) {d : ℤ} (hd : 0 ≤ d) :
    ↥(twistSections R f d) ≃+ ↥(twistChart R 1 d (Set.univ : Set (Fin 2))) :=
  ((twistSectionsOverlapEquivAway hfac hd).toAddEquiv.trans
      (awayAddEquivLaurent R hfac)).trans (twistChartUnivEquivLaurent R d).toAddEquiv.symm

end Stacks.ProjectiveSpace.CechComparison

end

module

public import StacksFrontier.AlgebraicGeometry.ProjTwistSectionRing.Multiplication
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TwistSectionsBijective

/-!
# The twisted sections of the projective line are generated in degree one

Let `k` be a field and `𝐏¹_k = Proj k[T₀, T₁]`. This file proves that the multiplication of
global sections

`Γ(𝐏¹_k, 𝒪(1)) × Γ(𝐏¹_k, 𝒪(d)) ⟶ Γ(𝐏¹_k, 𝒪(1 + d))`

of `Stacks.AlgebraicGeometry.ProjTwistSectionRing.mul` is **surjective up to sums**: every
global section of `𝒪(1 + d)` is a finite sum of products of a section of `𝒪(1)` with a section
of `𝒪(d)`.

## The argument

Both halves are already available and this is their composition. On the polynomial side the
degree-`1 + d` binary forms are the products of the linear forms with the degree-`d` forms,
because `MvPolynomial.homogeneousSubmodule_one_pow` presents every homogeneous piece as a power
of the linear one; that is `Stacks.ProjectiveSpace.Cohomology.polyGrading_one_add_eq_mul`. On
the geometric side the degree-`d` section map of Equation [Stacks, Tag 01MP] is bijective for
the projective line over a field, by
`Stacks.ProjectiveSpace.Cohomology.bijective_degreeSection_line`, and it carries the
multiplication of forms to the pointwise multiplication of sections, by
`Stacks.AlgebraicGeometry.ProjTwistSectionRing.mul_degreeSection`. So a section of `𝒪(1 + d)`
is the section of a form, the form is a finite sum of products, and the section is the
corresponding finite sum of products of sections.

## What this is for, and what became of the two compatibilities

This is the last step of the Stacks proof of [Stacks, Tag 0C2K] on the `k`-side: the degree-one
generation that the proof invokes when it says that `x^d, x^{d-1}y, …, y^d` map to a basis of
`H⁰(𝐏¹_k, 𝒪(d))`. What used to stand between it and the geometric statement
`K_{p+1} ≤ K₀ · K_p` of
`StacksFrontier/AlgebraicGeometry/Surfaces/ThickeningKernelFiltration.lean` were two
compatibilities, neither of which is proved in this file. Both now hold:

* the pairing of
  `AlgebraicGeometry.Scheme.IdealSheafData.sub_mul_sub_mem_thickeningKernel` *is*
  `Stacks.Divisors.restrictedIdealMulSections` under the identification of the graded pieces, by
  `AlgebraicGeometry.Scheme.IdealSheafData.gradedSectionsHomOfEq_restrictedIdealMulSections` of
  `StacksFrontier/AlgebraicGeometry/Surfaces/GradedSectionsLocal.lean`;
* the per-degree isomorphisms `i^*ℐ_{D ^ m} ≅ 𝒪_{𝐏¹}(m)` of
  `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
  `.nonempty_pullback_negativeTwist_pow_iso_twistingSheaf` are still *not* made compatible with
  the two multiplications, and they do not have to be. Only one identification in the degree of
  a *product* is needed, and it is built out of the two chosen ones in the degrees of the
  factors —
  `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.prodTwistIso` — so
  multiplicativity holds by construction:
  `AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind`
  `.prodTwistSection_restrictedIdealMulSections`, with the degree-one generation it yields as
  `…IsExceptionalCurveOfFirstKind.mem_closure_restrictedIdealMulSections`, both in
  `StacksFrontier/AlgebraicGeometry/Surfaces/ExceptionalCurveTwistMultiplicative.lean`.

With those, all four clauses of [Stacks, Tag 0C2K] are unconditional for an exceptional curve
of the first kind, in
`StacksFrontier/AlgebraicGeometry/Surfaces/ExceptionalCurveMonomialData.lean`.

Nothing here carries a `@[stacks]` attribute: Tag 0C2K asserts the structure of the ring of
compatible functions on the thickenings, and Tag 01XT asserts the degreewise bijectivity that
is used as an input; this is an assembly on the way between them.

## Main definitions

* `Stacks.ProjectiveSpace.Cohomology.degreeOneProducts` — the products of a global section of
  `𝒪(1)` with a global section of `𝒪(d)`, as a set of global sections of `𝒪(1 + d)`.

## Main results

* `Stacks.ProjectiveSpace.Cohomology.polyGrading_one_add_eq_mul` — the degree-`1 + d` forms are
  the linear forms times the degree-`d` forms.
* `Stacks.ProjectiveSpace.Cohomology.mem_closure_degreeOneProducts` — **every global section of
  `𝒪(1 + d)` on `𝐏¹_k` is a finite sum of products of a section of `𝒪(1)` with a section of
  `𝒪(d)`.**
* `Stacks.ProjectiveSpace.Cohomology.closure_degreeOneProducts_eq_top` — the same, as the
  statement that those products generate.

## References

* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
-/

@[expose] public noncomputable section

open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading)
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.ProjTwistSectionRing
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistGlobalSections degreeSection degreeSectionHom
  degreeSectionHom_apply)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.ProjectiveSpace.Cohomology

/-! ### The forms of degree `1 + d` are the linear forms times the forms of degree `d` -/

/-- **The degree-`1 + d` homogeneous polynomials are the linear ones times the degree-`d` ones.**
Every homogeneous piece of a polynomial ring is a power of the linear one, by
`MvPolynomial.homogeneousSubmodule_one_pow`, and the degrees add. -/
public theorem polyGrading_one_add_eq_mul (R : Type u) [CommRing R] (n d : ℕ) :
    polyGrading R n (1 + d) = polyGrading R n 1 * polyGrading R n d := by
  show MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R (1 + d) = _
  conv_lhs => rw [← MvPolynomial.homogeneousSubmodule_one_pow]
  rw [pow_add, pow_one, MvPolynomial.homogeneousSubmodule_one_pow]

/-! ### Degree-one generation of the twisted sections -/

/-- **The products of a global section of `𝒪(1)` with a global section of `𝒪(d)`**, as a set of
global sections of `𝒪(1 + d)` on `𝐏¹_k`. The product is the pointwise one,
`Stacks.AlgebraicGeometry.ProjTwistSectionRing.mul`. -/
public def degreeOneProducts (k : Type u) [Field k] (d : ℕ) :
    Set (twistGlobalSections (polyGrading k 1) (1 + d)) :=
  {t | ∃ (a : twistGlobalSections (polyGrading k 1) 1)
         (b : twistGlobalSections (polyGrading k 1) d),
       mul (polyGrading k 1) 1 d a b = t}

/-- **The twisted sections of the projective line are generated in degree one.** Every global
section of `𝒪(1 + d)` on `𝐏¹_k` is a finite sum of products of a global section of `𝒪(1)` with
a global section of `𝒪(d)`.

The section is the section of a binary form of degree `1 + d`, by
`Stacks.ProjectiveSpace.Cohomology.bijective_degreeSection_line`; that form is a finite sum of
products of a linear form with a degree-`d` form, by
`Stacks.ProjectiveSpace.Cohomology.polyGrading_one_add_eq_mul`; and the section of a product of
forms is the product of their sections, by
`Stacks.AlgebraicGeometry.ProjTwistSectionRing.mul_degreeSection`.

This is the `k`-side of the degree-one generation the Stacks proof of [Stacks, Tag 0C2K]
invokes when it asserts that the monomials `x^d, …, y^d` give a basis of `H⁰(𝐏¹_k, 𝒪(d))`. -/
public theorem mem_closure_degreeOneProducts (k : Type u) [Field k] (d : ℕ)
    (s : twistGlobalSections (polyGrading k 1) (1 + d)) :
    s ∈ AddSubgroup.closure (degreeOneProducts k d) := by
  set C : AddSubgroup (twistGlobalSections (polyGrading k 1) (1 + d)) :=
    AddSubgroup.closure (degreeOneProducts k d) with hC
  have hmul := polyGrading_one_add_eq_mul k 1 d
  have key : ∀ (r : MvPolynomial (Fin (1 + 1)) k)
      (hr : r ∈ polyGrading k 1 1 * polyGrading k 1 d),
      degreeSectionHom (polyGrading k 1) (1 + d) ⟨r, hmul.ge hr⟩ ∈ C := by
    intro r hr
    induction hr using Submodule.mul_induction_on' with
    | mem_mul_mem x hx y hy =>
      rw [hC]
      refine AddSubgroup.subset_closure ⟨degreeSection (polyGrading k 1) 1 ⟨x, hx⟩,
        degreeSection (polyGrading k 1) d ⟨y, hy⟩, ?_⟩
      rw [degreeSectionHom_apply]
      exact mul_degreeSection (polyGrading k 1) 1 d ⟨x, hx⟩ ⟨y, hy⟩
    | add x hx y hy ihx ihy =>
      show degreeSectionHom (polyGrading k 1) (1 + d)
        ((⟨x, hmul.ge hx⟩ : polyGrading k 1 (1 + d)) + ⟨y, hmul.ge hy⟩) ∈ C
      rw [map_add]
      exact AddSubgroup.add_mem _ ihx ihy
  obtain ⟨G, hG⟩ := (bijective_degreeSection_line k (1 + d)).surjective s
  obtain ⟨H, hH⟩ := G
  rw [← hG]
  exact key H (hmul.le hH)

/-- **The products of a section of `𝒪(1)` with a section of `𝒪(d)` generate `Γ(𝐏¹_k, 𝒪(1 + d))`**
— `Stacks.ProjectiveSpace.Cohomology.mem_closure_degreeOneProducts`, read as an equality of
subgroups. -/
public theorem closure_degreeOneProducts_eq_top (k : Type u) [Field k] (d : ℕ) :
    AddSubgroup.closure (degreeOneProducts k d) = ⊤ :=
  eq_top_iff.2 fun s _ => mem_closure_degreeOneProducts k d s

end Stacks.ProjectiveSpace.Cohomology

end

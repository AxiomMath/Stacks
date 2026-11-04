module

public import StacksFrontier.AlgebraicGeometry.ProjSaturation.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistSectionRing.Statement
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.ChartSectionsLinear
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.HypersurfaceCohomology
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TwistMonomialBasis
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TwistSectionsCoeffAction
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.TwistSectionsAreForms
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The canonical map to the twisted sections, as an equivalence on `𝐏¹`

Let `𝒮` be a nonnegatively graded ring and `X = Proj 𝒮`. Equation [Stacks, Tag 01MP] is the
canonical map `𝒮 ⟶ ⨁_{n ≥ 0} Γ(X, 𝒪(n))`, assembled degreewise from
`AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection`, which sends a homogeneous element
of degree `n` to the global section of `𝒪(n)` whose value at every point is `a / 1`. That the
degreewise maps are *multiplicative across degrees* is
`Stacks.AlgebraicGeometry.ProjTwistSectionRing.mul_degreeSection`, and the assembled ring map
is `Stacks.AlgebraicGeometry.ProjTwistSectionRing.globalSectionsRingMap`.

That these degreewise maps are **bijective** over a field is
`Stacks.ProjectiveSpace.Cohomology.bijective_degreeSection`, proved for `𝐏ⁿ_k` in
`StacksFrontier.AlgebraicGeometry.ProjectiveSpace.TwistSectionsAreForms`. This file records the
`𝐏¹_k` case under the name the twisted-section ring of the projective line uses, and packages it
as a `k`-linear **equivalence** together with the inverse law a symbol map needs.

## Main definitions

* `Stacks.ProjectiveSpace.Cohomology.degreeSectionEquivLine` — the degree-`d` section map on
  `𝐏¹_k` over a field as a `k`-linear equivalence `(k[T₀, T₁])_d ≅ Γ(𝐏¹_k, 𝒪(d))`.

## Main results

* `Stacks.ProjectiveSpace.Cohomology.bijective_degreeSection_line` — **the canonical map is
  bijective on the projective line over a field, in every degree.** This is the `n = 1` case of
  `Stacks.ProjectiveSpace.Cohomology.bijective_degreeSection`.
* `Stacks.ProjectiveSpace.Cohomology.degreeSectionEquivLine_symm_degreeSection` — the inverse
  reads a section off as a binary form; with
  `Stacks.AlgebraicGeometry.ProjTwistSectionRing.mul_degreeSection` this is the
  multiplicativity across degrees of `⨁_d Γ(𝐏¹_k, 𝒪(d)) = k[T₀, T₁]`.

## References

* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 0C2K](https://stacks.math.columbia.edu/tag/0C2K)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading)
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections

universe u w

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] ProjectiveSpectrum.isPrime

namespace Stacks.ProjectiveSpace.Cohomology

open Stacks.AlgebraicGeometry.ProjTwistSections
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistGlobalSections degreeSection degreeSectionHom
  degreeSectionHom_apply)

/-! ### Bijectivity on the projective line over a field -/

/-- **`Γ(𝐏¹_k, 𝒪(d))` is the module of binary forms of degree `d`, through the canonical map
of Equation [Stacks, Tag 01MP].**

For `k` a field and every `d ≥ 0`, the degree-`d` section map
`(k[T₀, T₁])_d ⟶ Γ(𝐏¹_k, 𝒪(d))` is bijective. This is the `n = 1` case of
`Stacks.ProjectiveSpace.Cohomology.bijective_degreeSection`, which is injective because
`k[T₀, …, Tₙ]` is a domain and surjective because
`Stacks.ProjectiveSpace.Cohomology.homogeneousIsoTwistSections` makes the two sides `k`-vector
spaces of the same finite dimension.

Together with the multiplicativity across degrees of
`Stacks.AlgebraicGeometry.ProjTwistSectionRing.mul_degreeSection` this is the identification of
the graded ring `⨁_d Γ(𝐏¹_k, 𝒪(d))` with `k[T₀, T₁]`. -/
@[stacks 01XT "degree zero, nonnegative twist, for the projective line over a field: the \
canonical map of Equation 01MP from the degree-d binary forms to the sections of O(d) is \
bijective", ega "II 8.14.11" "Case Y = Spec k"]
theorem bijective_degreeSection_line (k : Type u) [Field k] (d : ℕ) :
    Function.Bijective (degreeSection (polyGrading k 1) d) :=
  bijective_degreeSection 1 d

/-! ### The graded identification `⨁_d Γ(𝐏¹_k, 𝒪(d)) = k[T₀, T₁]` -/

/-- **`Γ(𝐏¹_k, 𝒪(d)) ≅ (k[T₀, T₁])_d`**, the `k`-linear equivalence that the canonical map of
Equation [Stacks, Tag 01MP] is, on the projective line over a field. -/
def degreeSectionEquivLine (k : Type u) [Field k] (d : ℕ) :
    polyGrading k 1 d ≃ₗ[k] twistSectionsModule k 1 (d : ℤ) :=
  LinearEquiv.ofBijective (degreeSectionLinear k 1 d) (bijective_degreeSection_line k d)

/-- The equivalence `degreeSectionEquivLine k d` sends a binary form `a` of degree `d` to its
section `degreeSection (polyGrading k 1) d a`. -/
@[simp]
theorem degreeSectionEquivLine_apply (k : Type u) [Field k] (d : ℕ) (a : polyGrading k 1 d) :
    degreeSectionEquivLine k d a = degreeSection (polyGrading k 1) d a :=
  rfl

/-- **Reading a section off as a binary form inverts the section map.** This is the direction a
symbol map uses, and with
`Stacks.AlgebraicGeometry.ProjTwistSectionRing.mul_degreeSection` — which says that the
pointwise product of the sections of two forms is the section of their product — it gives the
multiplicativity across degrees of the identification
`⨁_d Γ(𝐏¹_k, 𝒪(d)) = k[T₀, T₁]`: the cross-degree compatibility that the per-degree module
isomorphism `Stacks.ProjectiveSpace.Cohomology.twistCohomologyIsoHomogeneous` does not
carry. -/
theorem degreeSectionEquivLine_symm_degreeSection (k : Type u) [Field k] (d : ℕ)
    (a : polyGrading k 1 d) :
    (degreeSectionEquivLine k d).symm (degreeSection (polyGrading k 1) d a) = a :=
  (congrArg (degreeSectionEquivLine k d).symm (degreeSectionEquivLine_apply k d a).symm).trans
    ((degreeSectionEquivLine k d).symm_apply_apply a)

end Stacks.ProjectiveSpace.Cohomology

end

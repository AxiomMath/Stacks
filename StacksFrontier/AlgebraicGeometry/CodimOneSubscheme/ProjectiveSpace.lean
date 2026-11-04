module

public import StacksFrontier.AlgebraicGeometry.ProjNoetherian.Basic
public import StacksFrontier.AlgebraicGeometry.CodimOneSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.Basic

/-!
# One equation on each standard chart of a codimension-one subscheme of projective space

Let `R` be a Noetherian unique factorization domain and let `Z` be a closed subscheme of
`P^n_R = Proj R[T₀, …, Tₙ]` with no embedded points all of whose irreducible components have
codimension one. This file shows that over each standard open `D₊(Tₖ)` the ideal
`Ker(Γ(P^n_R, D₊(Tₖ)) ⟶ Γ(Z, i⁻¹ D₊(Tₖ)))` cutting `Z` out is principal.

The two inputs are proved elsewhere and are combined here without new mathematics. The general
chart statement is `AlgebraicGeometry.isPrincipal_ker_app_of_codimension_one`, which asks that
the sections of the ambient scheme over the chart form a Noetherian unique factorization domain.
That hypothesis is exactly what the chart identification of Tag 01NG supplies for projective
space: `Stacks.ProjectiveChart.sectionsChartEquiv` identifies `Γ(P^n_R, D₊(Tₖ))` with the
polynomial ring `R[Y₁, …, Yₙ]`, and the three transfer statements beside it give the domain,
Noetherian and unique-factorization properties of that ring of sections.

## Main results

* `AlgebraicGeometry.ProjectiveSpectrum.Proj`
  `.projectiveSpace_isPrincipal_ker_app_of_codimension_one`: one equation for `Z` over each
  standard chart of projective space.

## Implementation notes

`Z` is locally Noetherian rather than assumed so: `Proj` of a Noetherian graded ring is a
Noetherian scheme (Tag 0B5Q,
`Stacks.AlgebraicGeometry.Proj.isNoetherian_proj`), a closed immersion is locally of finite type,
and `AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian` transports the property to the
source.

The three ring-theoretic properties of the sections are theorems rather than instances in
Tag 01NG's file, deliberately, because the grading they are stated over is itself only a local
instance there; they are therefore introduced here with `have` before the chart statement is
applied.

This is **not** Tag 0BXL, which asks for the principality of the *homogeneous* ideal
`AlgebraicGeometry.ProjectiveSpectrum.Proj.idealOfClosedSubscheme` of `Z` in `R[T₀, …, Tₙ]`.
Passing from these chart ideals to that homogeneous ideal is Tag 0801's chart comparison, and it
is carried out in `StacksFrontier/AlgebraicGeometry/CodimOneSubscheme/ProjHeightOne.lean`, which
proves Tag 0BXL and carries its attribute. That file does not consume this one: it reads the
height of an associated prime on a standard chart directly, by way of
`AlgebraicGeometry.height_eq_one_of_mem_associatedPrimes_ker_app`, which needs no unique
factorization on the chart and hence no appeal to Tag 01NG.

## References

* [Stacks Project, Tag 0BXL](https://stacks.math.columbia.edu/tag/0BXL)
* [Stacks Project, Tag 01NG](https://stacks.math.columbia.edu/tag/01NG)
* [Stacks Project, Tag 0B5Q](https://stacks.math.columbia.edu/tag/0B5Q)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

open AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **One equation on each standard chart of projective space.** Let `R` be a Noetherian unique
factorization domain and let `Z` be a closed subscheme of `P^n_R` with no embedded points all of
whose irreducible components have codimension one. Then over each standard open `D₊(Tₖ)` the
ideal cutting `Z` out of projective space is principal.

The chart statement `AlgebraicGeometry.isPrincipal_ker_app_of_codimension_one` applies because
Tag 01NG identifies the sections over `D₊(Tₖ)` with a polynomial ring over `R`. -/
theorem projectiveSpace_isPrincipal_ker_app_of_codimension_one (R : Type u) [CommRing R]
    [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R] (n : ℕ) {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) [IsClosedImmersion i]
    (hno : HasNoEmbeddedPoints Z)
    (hcodim : ∀ W ∈ irreducibleComponents Z, ∀ x : Z,
      IsGenericPoint x W → codimension (IrreducibleCloseds.closureSingleton (i.base x)) = 1)
    (k : Fin (n + 1)) :
    (RingHom.ker (i.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (MvPolynomial.X k))).hom).IsPrincipal := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian i
  have := Stacks.ProjectiveChart.isDomain_sections (R := R) k
  have := Stacks.ProjectiveChart.isNoetherianRing_sections (R := R) k
  have := Stacks.ProjectiveChart.uniqueFactorizationMonoid_sections (R := R) k
  exact isPrincipal_ker_app_of_codimension_one i hno hcodim
    (Proj.isAffineOpen_basicOpen _ _ (MvPolynomial.isHomogeneous_X R k) one_pos)

end AlgebraicGeometry.ProjectiveSpectrum.Proj

end

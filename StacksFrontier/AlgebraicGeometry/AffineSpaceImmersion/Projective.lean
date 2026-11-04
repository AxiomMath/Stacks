module

public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.ProjectiveSpaceImmersion
public import StacksFrontier.AlgebraicGeometry.AffineSpaceImmersion.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.ProjectiveSpace

/-!
# Relative affine space is a standard chart of relative projective space

Projective `N`-space over a base scheme `S` is the base change of `Proj ℤ[T₀, …, T_N]` along
`S ⟶ Spec ℤ`, and affine `N`-space over `S` is the base change of `Spec ℤ[Y₁, …, Y_N]` along the
same morphism. Each standard open `D₊(Tᵢ)` of the integral model of projective space *is*
`Spec ℤ[Y₁, …, Y_N]` (Stacks 01NG, already available here as
`Stacks.ProjectiveChart.chartIsoAffineSpace`), so base changing that open immersion exhibits
`𝔸ᴺ_S` as an open subscheme of `ℙᴺ_S` over `S`, once for every homogeneous coordinate.

Composing the immersion of Stacks 04II with an open immersion of this kind gives the projective
form: a quasi-affine scheme locally of finite type over `S` immerses into `ℙᴺ_S` over `S`. This is
the conclusion of Stacks 01VS — a lemma of Stacks chapter 29 — for the structure sheaf, which is
the only case the proof of Chow's lemma over a Noetherian base consumes; it is
`AlgebraicGeometry.exists_immersion_projectiveSpace` of
`StacksFrontier/AlgebraicGeometry/Morphisms/ImmersionsAndAffine/ProjectiveSpaceImmersion.lean`.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpace.standardChart`: the standard open `D₊(Tᵢ)` of the integral
  model of projective space.
* `AlgebraicGeometry.ProjectiveSpace.standardChartIso`: that open is `Spec ℤ[Y₁, …, Y_N]`.
* `AlgebraicGeometry.ProjectiveSpace.fromAffineSpace`: the resulting open immersion
  `𝔸ᴺ_S ⟶ ℙᴺ_S` over `S`.

## Main results

* `AlgebraicGeometry.ProjectiveSpace.isPullback_fromAffineSpace`: `𝔸ᴺ_S` is the base change of
  the standard chart along `ℙᴺ_S ⟶ ℙᴺ_ℤ`, which is what makes `fromAffineSpace` an open
  immersion.
* `AlgebraicGeometry.ProjectiveSpace.opensRange_fromAffineSpaceZ`: the image of the `i`-th chart
  immersion of the integral model is `D₊(Tᵢ)`.

## Implementation notes

The coordinates of the affine space are indexed by `ULift (Fin N)`, which is the index type
`AlgebraicGeometry.AffineSpace` wants: it must live in the universe of the base scheme. The
identification of the chart is therefore `Stacks.ProjectiveChart.chartIsoAffineSpace` at the
equivalence `Equiv.ulift`, composed with `AlgebraicGeometry.AffineSpace.SpecIso` to land on
`Spec ℤ[ULift (Fin N)]` rather than on affine space over `Spec ℤ`; the latter is the spelling
that occurs in the pullback defining `𝔸ᴺ_S`. The number of affine coordinates is `N` for every
one of the `N + 1` homogeneous coordinates, so the index `i` is simply threaded through.

`AlgebraicGeometry.ProjectiveSpace.standardChart` is stated as an open of `ProjectiveSpaceZ N`
rather than of `Proj` of the polynomial ring, even though the two are definitionally equal: the
total-degree grading of a polynomial ring is only a local instance, so a statement mentioning
`Proj` of it would not elaborate in a file that has not installed the grading, while
`ProjectiveSpaceZ` carries it internally.

The tag `@[stacks 01VS]` is **not** attached to anything here. Stacks 01VS asserts, for an
arbitrary ample invertible sheaf `L` on `X`, that for every sufficiently large `d` there is an
immersion `i` into a projective space over `S` with `L^{⊗ d} ≅ i^* 𝒪(1)`. What is proved here is
the case `L = 𝒪_X` with `X` quasi-affine — where ampleness of the structure sheaf is automatic —
and without the identification of the pullback of the twisting sheaf, which would need a
statement of `𝒪(1)` on `ProjectiveSpaceZ` that this repository does not have. Attaching the tag
to a special case would record a weakening as the tag.

## References

* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 04II](https://stacks.math.columbia.edu/tag/04II)
* [Stacks Project, Tag 01NG](https://stacks.math.columbia.edu/tag/01NG)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ProjectiveSpace

/-- The standard open `D₊(Tᵢ)` of the integral model of projective `N`-space. -/
def standardChart (N : ℕ) (i : Fin (N + 1)) : (ProjectiveSpaceZ.{u} N).Opens :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) (ULift.{u} ℤ))
    (MvPolynomial.X i)

/-- **The standard open `D₊(Tᵢ)` of projective `N`-space over the integers is affine `N`-space
over the integers.** This is Stacks 01NG for the integral model, read through
`Stacks.ProjectiveChart.chartIsoAffineSpace` and
`AlgebraicGeometry.AffineSpace.SpecIso`. -/
def standardChartIso (N : ℕ) (i : Fin (N + 1)) :
    Spec (.of (MvPolynomial (ULift.{u} (Fin N)) (ULift.{u} ℤ))) ≅
      (standardChart.{u} N i).toScheme :=
  (AffineSpace.SpecIso (ULift.{u} (Fin N)) (.of (ULift.{u} ℤ))).symm ≪≫
    (Stacks.ProjectiveChart.chartIsoAffineSpace (ULift.{u} ℤ) N i Equiv.ulift).symm

/-- The standard chart of the integral model of projective space, as an open immersion of
`Spec ℤ[Y₁, …, Y_N]`. -/
def fromAffineSpaceZ (N : ℕ) (i : Fin (N + 1)) :
    Spec (.of (MvPolynomial (ULift.{u} (Fin N)) (ULift.{u} ℤ))) ⟶ ProjectiveSpaceZ.{u} N :=
  (standardChartIso.{u} N i).hom ≫ (standardChart.{u} N i).ι

/-- The `i`-th chart morphism `Spec ℤ[Y₁, …, Y_N] ⟶ ℙᴺ_ℤ` is an open immersion. -/
instance isOpenImmersion_fromAffineSpaceZ (N : ℕ) (i : Fin (N + 1)) :
    IsOpenImmersion (fromAffineSpaceZ.{u} N i) := by
  have : IsOpenImmersion (standardChartIso.{u} N i).hom := IsOpenImmersion.of_isIso _
  change IsOpenImmersion ((standardChartIso.{u} N i).hom ≫ (standardChart.{u} N i).ι)
  infer_instance

/-- The image of the `i`-th chart immersion of the integral model is `D₊(Tᵢ)`: precomposing the
inclusion of an open with an isomorphism does not change its image. -/
theorem opensRange_fromAffineSpaceZ (N : ℕ) (i : Fin (N + 1)) :
    (fromAffineSpaceZ.{u} N i).opensRange = standardChart.{u} N i :=
  (Scheme.Hom.opensRange_comp_of_isIso (standardChartIso.{u} N i).hom
    (standardChart.{u} N i).ι).trans (Scheme.Opens.opensRange_ι _)

/-- **Affine `N`-space over `S` as a standard chart of projective `N`-space over `S`**: the base
change of the `i`-th standard chart of the integral model along `S ⟶ Spec ℤ`. -/
def fromAffineSpace (N : ℕ) (i : Fin (N + 1)) (S : Scheme.{u}) :
    AffineSpace (ULift.{u} (Fin N)) S ⟶ ProjectiveSpace N S :=
  pullback.lift (AffineSpace (ULift.{u} (Fin N)) S ↘ S)
    (AffineSpace.toSpecMvPoly (ULift.{u} (Fin N)) S ≫ fromAffineSpaceZ.{u} N i)
    (terminal.hom_ext _ _)

/-- The morphism `fromAffineSpace N i S : 𝔸ᴺ_S ⟶ ℙᴺ_S` is a morphism over `S`. -/
@[reassoc (attr := simp)]
theorem fromAffineSpace_over (N : ℕ) (i : Fin (N + 1)) (S : Scheme.{u}) :
    fromAffineSpace.{u} N i S ≫ (ProjectiveSpace N S ↘ S) =
      AffineSpace (ULift.{u} (Fin N)) S ↘ S :=
  pullback.lift_fst _ _ _

/-- Composing `fromAffineSpace N i S` with `ℙᴺ_S ⟶ ℙᴺ_ℤ` equals composing
`𝔸ᴺ_S ⟶ Spec ℤ[Y₁, …, Y_N]` with the `i`-th chart `fromAffineSpaceZ N i`. -/
@[reassoc (attr := simp)]
theorem fromAffineSpace_toProjectiveSpaceZ (N : ℕ) (i : Fin (N + 1)) (S : Scheme.{u}) :
    fromAffineSpace.{u} N i S ≫ toProjectiveSpaceZ N S =
      AffineSpace.toSpecMvPoly (ULift.{u} (Fin N)) S ≫ fromAffineSpaceZ.{u} N i :=
  pullback.lift_snd _ _ _

/-- **Affine space over `S` is the base change of the standard chart.** Both `𝔸ᴺ_S` and `ℙᴺ_S`
are base changes from the integers, so the square comparing them is a pullback: it pastes with
the pullback square defining `ℙᴺ_S` to the pullback square defining `𝔸ᴺ_S`. -/
theorem isPullback_fromAffineSpace (N : ℕ) (i : Fin (N + 1)) (S : Scheme.{u}) :
    IsPullback (fromAffineSpace.{u} N i S) (AffineSpace.toSpecMvPoly (ULift.{u} (Fin N)) S)
      (toProjectiveSpaceZ N S) (fromAffineSpaceZ.{u} N i) := by
  refine IsPullback.of_right (h₁₂ := ProjectiveSpace N S ↘ S) ?_
    (fromAffineSpace_toProjectiveSpaceZ N i S)
    (IsPullback.of_hasPullback (terminal.from S) (terminal.from (ProjectiveSpaceZ.{u} N)))
  rw [fromAffineSpace_over N i S,
    show fromAffineSpaceZ.{u} N i ≫ terminal.from (ProjectiveSpaceZ.{u} N) =
      terminal.from (Spec (.of (MvPolynomial (ULift.{u} (Fin N)) (ULift.{u} ℤ)))) from
      terminal.hom_ext _ _]
  exact IsPullback.of_hasPullback (terminal.from S)
    (terminal.from (Spec (.of (MvPolynomial (ULift.{u} (Fin N)) (ULift.{u} ℤ)))))

/-- The morphism `fromAffineSpace N i S : 𝔸ᴺ_S ⟶ ℙᴺ_S` is an open immersion. -/
instance isOpenImmersion_fromAffineSpace (N : ℕ) (i : Fin (N + 1)) (S : Scheme.{u}) :
    IsOpenImmersion (fromAffineSpace.{u} N i S) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (isPullback_fromAffineSpace N i S).flip
    inferInstance

end ProjectiveSpace

end AlgebraicGeometry

end

end

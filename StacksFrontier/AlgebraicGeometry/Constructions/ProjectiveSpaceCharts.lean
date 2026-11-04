module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Dimension.Basic
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Away
public import StacksCore.Tactic.StacksAttribute

/-!
# The standard affine charts of projective space

Projective `n`-space over the integers is `Proj ℤ[T₀, …, Tₙ]` for the grading by total degree. It
is covered by the `n + 1` standard opens at the homogeneous coordinates,
`Pⁿ_ℤ = ⋃_i D₊(Tᵢ)`, and this file identifies each of them with affine `n`-space over the
integers.

The same `n + 1` opens are available over an arbitrary base scheme `S`, as the preimages of the
`D₊(Tᵢ)` under the projection `ℙⁿ_S ⟶ ℙⁿ_ℤ` of the base change defining `ℙⁿ_S`. They still cover
`ℙⁿ_S`, and over an affine base they are again affine: the projection to the integral model is
then the base change of an affine morphism, hence affine, so it pulls affine opens back to
affine opens. This exhibits `ℙⁿ_S` over an affine base as a scheme covered by `n + 1` affine
opens, which is what bounds its cohomological dimension.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpace.standardOpen`: the standard open at a homogeneous
  coordinate of projective `n`-space over a base scheme.

## Main results

* `AlgebraicGeometry.ProjectiveSpace.basicOpenXIsoSpec`: the standard open at a homogeneous
  coordinate of projective `n`-space over an arbitrary coefficient ring is the spectrum of a
  polynomial ring in `n` variables.
* `AlgebraicGeometry.ProjectiveSpace.basicOpenXIsoAffineSpace`: the standard open at a homogeneous
  coordinate of projective `n`-space over the integers is affine `n`-space over the integers.
* `AlgebraicGeometry.ProjectiveSpace.iSup_standardOpen_eq_top`: the `n + 1` standard opens cover
  projective `n`-space over any base scheme.
* `AlgebraicGeometry.ProjectiveSpace.isAffineOpen_standardOpen`: over an affine base they are
  affine opens.

## Implementation notes

The scheme `Proj ℤ[T₀, …, Tₙ]` is `AlgebraicGeometry.projectiveSpace n` by definition; the
statement is phrased with `AlgebraicGeometry.Proj` applied to
`MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℤ` so that `AlgebraicGeometry.Proj.basicOpen` and
the `Away` localizations apply to it without unfolding. As in
`StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpace`, the required `GradedAlgebra`
instance is `MvPolynomial.gradedAlgebra`, which is not a global instance and is supplied here as a
local one.

Both halves of the covering statement are already in this library in greater generality, so
nothing is reproved here. The covering itself is
`Stacks.ProjectiveSpace.iSup_basicOpen_X_eq_top`, stated for an arbitrary coefficient ring and an
arbitrary index type. The algebra of the chart is
`Stacks.AlgebraicGeometry.ProjPolyChart.chartEquiv`, which identifies the degree-zero homogeneous
localization `ℤ[T]_{(Tᵢ)}` with the polynomial ring on the affine coordinates `T_j / T_i`,
`j ≠ i`; all that happens here is the passage to schemes, by
`AlgebraicGeometry.Proj.basicOpenIsoSpec` and `AlgebraicGeometry.AffineSpace.SpecIso`, and the
reindexing of the affine coordinates by `Fin n` along `finSuccAboveEquiv`.

The index type of an `AlgebraicGeometry.AffineSpace` must live in the universe of the base scheme,
which pins the coefficient ring of the `AffineSpace`-spelled statement to universe zero; that is
no restriction for the tag, which is about the integers. The statement spelled with the spectrum
of a polynomial ring is kept at an arbitrary coefficient ring, because the universe-`u` model of
projective space is `Proj` of a polynomial ring over `ULift ℤ`, which is not `Proj` of a
polynomial ring over `ℤ`: the two live in different universes, so no isomorphism relates them and
the charts have to be available over both.

## References

* [Stacks Project, Tag 01NG](https://stacks.math.columbia.edu/tag/01NG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial

universe u

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

section GeneralCoefficients

variable (R : Type u) [CommRing R] (n : ℕ)

/-- **The standard open at a homogeneous coordinate of projective `n`-space over a ring `R` is
the spectrum of a polynomial ring in `n` variables over `R`.**

The identification sends the `j`-th affine coordinate to the ratio `T_{σ j} / Tᵢ`, for `σ` the
order-preserving inclusion `Fin n ↪ Fin (n + 1)` omitting `i`. -/
public noncomputable def basicOpenXIsoSpec (i : Fin (n + 1)) :
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (MvPolynomial.X i)).toScheme ≅ Spec (CommRingCat.of (MvPolynomial (Fin n) R)) :=
  (Proj.basicOpenIsoSpec (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)
      (Stacks.AlgebraicGeometry.ProjPolyChart.X_mem_one R n i) Nat.one_pos).trans
    (Scheme.Spec.mapIso
      ((MvPolynomial.renameEquiv R (finSuccAboveEquiv i)).toRingEquiv.trans
        (Stacks.AlgebraicGeometry.ProjPolyChart.chartEquiv R n i)).toCommRingCatIso.op)

end GeneralCoefficients

variable (n : ℕ)

/-- Reindexing the affine coordinates of a standard chart by `Fin n`: affine space on the
coordinates other than `Tᵢ` is affine `n`-space. -/
public noncomputable def affineSpaceChartReindex (i : Fin (n + 1)) (S : Scheme.{0}) :
    AffineSpace {j : Fin (n + 1) // j ≠ i} S ≅ AffineSpace (Fin n) S :=
  (AffineSpace.functor.mapIso (finSuccAboveEquiv i).toIso.op).app S

/-- **The standard open at a homogeneous coordinate of projective `n`-space over the integers is
affine `n`-space over the integers.**

The identification sends the affine coordinate indexed by `j ≠ i` to the ratio `T_j / T_i`. -/
@[stacks 01NG "affine-space charts"]
public noncomputable def basicOpenXIsoAffineSpace (i : Fin (n + 1)) :
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℤ)
      (MvPolynomial.X i)).toScheme ≅ AffineSpace (Fin n) (Spec (.of ℤ)) :=
  (Proj.basicOpenIsoSpec (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℤ) (MvPolynomial.X i)
      (Stacks.AlgebraicGeometry.ProjPolyChart.X_mem_one ℤ n i) Nat.one_pos).trans
    ((Scheme.Spec.mapIso
          (Stacks.AlgebraicGeometry.ProjPolyChart.chartEquiv ℤ n i).toCommRingCatIso.op).trans
      ((AffineSpace.SpecIso {j : Fin (n + 1) // j ≠ i} (.of ℤ)).symm.trans
        (affineSpaceChartReindex n i (Spec (.of ℤ)))))

/-! ### The standard opens over an arbitrary base -/

variable (S : Scheme.{u})

/-- The standard open at the `i`-th homogeneous coordinate of projective `n`-space over a base
scheme `S`: the preimage of `D₊(Tᵢ) ⊆ ℙⁿ_ℤ` under the projection to the integral model. -/
public noncomputable def standardOpen (i : Fin (n + 1)) : (projectiveSpaceOver n S).Opens :=
  projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ
    Proj.basicOpen (homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) (X i)

/-- **The `n + 1` standard opens cover projective `n`-space over any base scheme.** They are the
preimages of the standard opens of the integral model, which cover it by the covering half of
[Stacks, Tag 01NG]; no attribute is attached here, since this is that assertion transported
along a base change rather than a further assertion of the tag. -/
public theorem iSup_standardOpen_eq_top : (⨆ i, standardOpen n S i) = ⊤ :=
  (projectiveSpaceOver.toIntegralAtUniverse n S).iSup_preimage_eq_top
    (Stacks.ProjectiveSpace.iSup_basicOpen_X_eq_top (ULift.{u} ℤ) (Fin (n + 1)))

/-- **Projective space over an affine base is affine over its integral model.** The projection
`ℙⁿ_S ⟶ ℙⁿ_ℤ` is the base change of the structure morphism `S ⟶ Spec ℤ` along the structure
morphism of the integral model, and an affine morphism stays affine under base change. -/
public instance isAffineHom_toIntegralAtUniverse [IsAffine S] :
    IsAffineHom (projectiveSpaceOver.toIntegralAtUniverse n S) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom)
    (IsPullback.of_hasPullback (terminal.from S)
      (terminal.from (projectiveSpaceAtUniverse.{u} n)))
    (isAffineHom_of_isAffine _)

/-- **Over an affine base the standard opens are affine.** The standard open `D₊(Tᵢ)` of the
integral model is affine, and the projection to the integral model is an affine morphism. -/
public theorem isAffineOpen_standardOpen [IsAffine S] (i : Fin (n + 1)) :
    IsAffineOpen (standardOpen n S i) :=
  IsAffineHom.isAffine_preimage _
    (Proj.isAffineOpen_basicOpen _ (X i) (isHomogeneous_X (ULift.{u} ℤ) i) one_pos)

end AlgebraicGeometry.ProjectiveSpace

end

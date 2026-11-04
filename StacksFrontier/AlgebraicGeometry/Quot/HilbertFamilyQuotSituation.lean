module

public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFamilyStructureSheafDictionary
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorPresheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction

/-!
# The Quot situation of `𝒪_X/X/B`

Stacks 0D00 identifies the Hilbert functor of a morphism `f : X ⟶ Y` of finite presentation with
the Quot functor of its structure sheaf. This file builds the Quot situation of Stacks 09TR at
`F = 𝒪_X` and identifies the module `F_T` of which that situation takes quotients with the
structure sheaf `𝒪_{X_T}` of the base change.

## Main definitions

* `AlgebraicGeometry.Space.structureSheafQuotSituation`: **the Quot situation of `𝒪_X/X/B`** of
  Stacks 0D00 — the quotient situation of Stacks 082M whose module is the structure sheaf, with
  the finite-presentation field of Stacks 09TR taken from Situation 0CZY.
* `AlgebraicGeometry.Space.structureSheafTestScheme`: a scheme over the functor of points of `Y`,
  read as a test scheme of that situation.
* `AlgebraicGeometry.Space.baseChangeModuleIsoStructureSheaf`: **`F_T ≅ 𝒪_{X_T}`** for that
  situation.

## Main results

* `AlgebraicGeometry.Space.space_structureSheafTestScheme`,
  `AlgebraicGeometry.Space.sourceProjection_structureSheafTestScheme` and
  `AlgebraicGeometry.Space.projection_structureSheafTestScheme`: the base change `X_T` of the
  situation, and both of its projections, are the ones the Hilbert functor is stated with.

## Implementation notes

The Hilbert functor is indexed by `AlgebraicGeometry.Space.SchemesOverPresheaf`, schemes of the
site carrying a morphism of presheaves to the functor of points of `Y`, while a quotient situation
is indexed by `AlgebraicGeometry.Space.SchemesOver`, schemes of the site carrying a morphism *of
algebraic spaces* to `Y`. A morphism of algebraic spaces is a morphism of presheaves in a one-field
wrapper (`CategoryTheory.ObjectProperty.homMk`), so the translation is
`AlgebraicGeometry.Space.structureSheafTestScheme`, and under it the three results above hold by
`rfl`: both base changes are the same `CategoryTheory.Limits.pullback` of the same two morphisms,
and `IsAlgebraicSpace` is a proposition.

`F_T ≅ 𝒪_{X_T}` is not an equality: the module of Stacks 082M at a test scheme is the inverse image
of Stacks 03LU, which is a sheafification, so it is only isomorphic to the structure sheaf of the
base change; the isomorphism is `AlgebraicGeometry.Space.modulePullbackUnitIso`.

No tag attribute is placed in this file: Stacks 0D00 asserts the equality of the two functors, and
nothing here states it.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 082M](https://stacks.math.columbia.edu/tag/082M)
* [Stacks Project, Tag 09RP](https://stacks.math.columbia.edu/tag/09RP)
* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
* [Stacks Project, Tag 0CZY](https://stacks.math.columbia.edu/tag/0CZY)
* [Stacks Project, Tag 0D00](https://stacks.math.columbia.edu/tag/0D00)
* [Stacks Project, Tag 0D01](https://stacks.math.columbia.edu/tag/0D01)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-! ### The Quot situation of the structure sheaf -/

/-- **The Quot situation of `𝒪_X/X/B`.**  For a morphism `f : X ⟶ Y` of algebraic spaces over `S`
of finite presentation, the data of Stacks 09TR whose module is the structure sheaf of `X`: the
situation whose Quot functor Stacks 0D00 identifies with the Hilbert functor of `f`. -/
def structureSheafQuotSituation (f : X ⟶ Y) (hf : IsFinitePresentation B S hS f.hom) :
    QuotSituation B S hS where
  X := X
  Y := Y
  f := f
  F := structureSheafModule B S hS X
  quasicoherent := by infer_instance
  finitePresentation := hf

/-- A scheme of the site over the functor of points of `Y`, read as a test scheme of a quotient
situation on `Y`: the morphism of presheaves is wrapped as a morphism of algebraic spaces. -/
abbrev structureSheafTestScheme (T : SchemesOverPresheaf B S hS Y) : SchemesOver Y :=
  CostructuredArrow.mk (ObjectProperty.homMk T.hom)

/-- The base change of a quotient situation at such a test scheme is the base change `X_T` the
Hilbert functor is stated with. -/
theorem space_structureSheafTestScheme (f : X ⟶ Y) (hf : IsFinitePresentation B S hS f.hom)
    (T : SchemesOverPresheaf B S hS Y) :
    (structureSheafQuotSituation f hf).space (structureSheafTestScheme T) =
      schemeBaseChangeSpace f T :=
  rfl

/-- The projection `X_T ⟶ X`, along which the module of the situation is pulled back, is the
first projection of the Hilbert side's fibre product. -/
theorem sourceProjection_structureSheafTestScheme (f : X ⟶ Y)
    (hf : IsFinitePresentation B S hS f.hom) (T : SchemesOverPresheaf B S hS Y) :
    (structureSheafQuotSituation f hf).sourceProjection (structureSheafTestScheme T) =
      (ObjectProperty.homMk (pullback.fst f.hom T.hom) : schemeBaseChangeSpace f T ⟶ X) :=
  rfl

/-- The projection `X_T ⟶ T`, over which the quotients are required to be flat and properly
supported, is the one the Hilbert functor's three conditions are stated over. -/
theorem projection_structureSheafTestScheme (f : X ⟶ Y)
    (hf : IsFinitePresentation B S hS f.hom) (T : SchemesOverPresheaf B S hS Y) :
    (structureSheafQuotSituation f hf).projection (structureSheafTestScheme T) =
      schemeBaseChangeProjectionHom B S hS f T :=
  rfl

/-- **`F_T ≅ 𝒪_{X_T}` for the Quot situation of the structure sheaf.**  The module the Quot functor
takes quotients of is the structure sheaf of the base change, because the inverse image of
Stacks 03LU carries `𝒪_X` to `𝒪_{X_T}`
(`AlgebraicGeometry.Space.modulePullbackUnitIso`). The base change `X_T` is spelled
`AlgebraicGeometry.Space.baseChangeSpace` at `AlgebraicGeometry.Space.structureSheafTestScheme`,
which is `AlgebraicGeometry.Space.schemeBaseChangeSpace` by `rfl`. -/
def baseChangeModuleIsoStructureSheaf (f : X ⟶ Y) (hf : IsFinitePresentation B S hS f.hom)
    (T : SchemesOverPresheaf B S hS Y) :
    (structureSheafQuotSituation f hf).baseChangeModule (structureSheafTestScheme T) ≅
      structureSheafModule B S hS (baseChangeSpace f (structureSheafTestScheme T)) :=
  modulePullbackUnitIso B S hS (baseChangeProjection f (structureSheafTestScheme T))

end AlgebraicGeometry.Space

end

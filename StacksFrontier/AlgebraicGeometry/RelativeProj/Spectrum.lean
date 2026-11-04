module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.Assembled
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.GluedRepresents
import StacksCore.Tactic.StacksAttribute

/-!
# The relative homogeneous spectrum of a quasi-coherent graded algebra

Let `S` be a scheme and let `A` be a quasi-coherent sheaf of graded `𝒪_S`-algebras (Situation
01NN). The *relative homogeneous spectrum* of `A` over `S`, or the *relative Proj* of `A` over
`S`, is the scheme glued from the projective spectra `Proj Γ(U, A)` of the graded rings of
homogeneous sections of `A` over the affine opens `U` of `S`, together with its structure
morphism `π : Proj_S(A) → S`. This file names that scheme and that morphism and records, for the
named object, the defining properties of its canonical charts `Proj Γ(U, A) ⟶ Proj_S(A)`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProj.relativeHomogeneousSpectrum`: the scheme `Proj_S(A)`.
* `Stacks.AlgebraicGeometry.RelativeProj.relativeHomogeneousSpectrumToBase`: its structure
  morphism `π : Proj_S(A) → S`.
* `Stacks.AlgebraicGeometry.RelativeProj.relativeHomogeneousSpectrumChart`: the chart of
  `Proj_S(A)` over an affine open `U` of the base, from `Proj Γ(U, A)`.

## Main results

* `...RelativeProj.isPullback_relativeHomogeneousSpectrumChart`: each chart is the inverse image
  of its affine open, as a cartesian square.
* `...RelativeProj.projInclusionMap_comp_relativeHomogeneousSpectrumChart`: the charts are
  compatible with the morphisms of projective spectra induced by restriction of homogeneous
  sections.
* `...RelativeProj.existsUnique_isoOver_relativeHomogeneousSpectrum`: between `Proj_S(A)` and any
  scheme over `S` carrying the same charts there is exactly one isomorphism compatible with the
  charts, and it is an isomorphism over `S`.

## Implementation notes

The scheme and the morphism are the first two fields of the datum
`Stacks.AlgebraicGeometry.RelativeProj.relativeProj` of Tag 01NQ, which is a construction and
not a choice: there the scheme is the colimit of the chart functor on the small affine Zariski
site of `S` and the morphism is the one the relative glueing datum produces. Accordingly nothing
here is selected from an existence statement. The `@[simp]` lemmas unfold the three named objects
to the corresponding fields of that datum, which is the form in which the rest of the library
states its results about them.

The tag's reference to the functor `F` of the display 01NX, and to Lemma 01NZ which says that
`Proj_S(A)` represents `F`, is not re-asserted here: `F` itself is not constructed in this
repository. That representability is carried, together with the rest of the source's input to it,
in `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.RepresentingProjData`, and is proved there as
`...RelativeProjQcohSheaf.RepresentingProjData.relativeProjRepresentableBy`.

## References

* [Stacks Project, Tag 01O0](https://stacks.math.columbia.edu/tag/01O0)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01NX](https://stacks.math.columbia.edu/tag/01NX)
* [Stacks Project, Tag 01NZ](https://stacks.math.columbia.edu/tag/01NZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RelativeProjBridge

namespace Stacks.AlgebraicGeometry.RelativeProj

universe u

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

/-! ### The scheme and its structure morphism -/

/-- The relative homogeneous spectrum `Proj_S(A)`, or relative Proj, of a quasi-coherent sheaf
of graded `𝒪_S`-algebras `A` over a scheme `S`: the scheme glued from the projective spectra of
the graded rings of sections of `A` over the affine opens of `S`. -/
@[stacks 01O0 "the scheme Proj_S(A) itself. The tag NAMES the scheme constructed in Lemma \
01NQ, which in this repository is the field `scheme` of \
`Stacks.AlgebraicGeometry.RelativeProj.relativeProj`, a construction (a colimit over the small \
affine Zariski site of S) and not a choice; the structure morphism pi the tag's last sentence \
names is `relativeHomogeneousSpectrumToBase`, which carries this tag too. NOT re-asserted here: \
the tag's reference to the functor F of the display 01NX and to Lemma 01NZ, namely that this \
scheme REPRESENTS F. The functor F is not constructed in this repository; that representability \
is carried, with the source's inputs to it, in \
`...RelativeProjQcohSheaf.RepresentingProjData` and proved there as \
`...RepresentingProjData.relativeProjRepresentableBy`", ega "II 3.1.3", ega "II 8.3.1"]
public def relativeHomogeneousSpectrum : Scheme.{u} := (relativeProj A).scheme

/-- The structure morphism `π : Proj_S(A) → S` of the relative homogeneous spectrum. -/
@[stacks 01O0 "ONLY the structure morphism pi : Proj_S(A) → S of the tag's last sentence; the \
scheme itself is `relativeHomogeneousSpectrum`, whose clause string describes the covering set \
and what the tag's reference to 01NX/01NZ is and where it lives"]
public def relativeHomogeneousSpectrumToBase :
    relativeHomogeneousSpectrum A ⟶ S :=
  (relativeProj A).toBase

/-- The chart of the relative homogeneous spectrum over an affine open `U` of the base: the
canonical morphism from the projective spectrum of the graded ring of sections of `A` over `U`. -/
public def relativeHomogeneousSpectrumChart (U : S.Opens) (hU : IsAffineOpen U) :
    AlgebraicGeometry.Proj (A.grading U) ⟶ relativeHomogeneousSpectrum A :=
  (relativeProj A).chart U hU

/-- The relative homogeneous spectrum of `A` is the scheme of the datum `relativeProj A`. -/
@[simp]
public theorem relativeHomogeneousSpectrum_eq :
    relativeHomogeneousSpectrum A = (relativeProj A).scheme :=
  rfl

/-- The structure morphism of the relative homogeneous spectrum of `A` is the morphism to the
base of the datum `relativeProj A`. -/
@[simp]
public theorem relativeHomogeneousSpectrumToBase_eq :
    relativeHomogeneousSpectrumToBase A = (relativeProj A).toBase :=
  rfl

/-- The chart of the relative homogeneous spectrum of `A` over an affine open `U` is the chart
over `U` of the datum `relativeProj A`. -/
@[simp]
public theorem relativeHomogeneousSpectrumChart_eq (U : S.Opens) (hU : IsAffineOpen U) :
    relativeHomogeneousSpectrumChart A U hU = (relativeProj A).chart U hU :=
  rfl

/-! ### The defining properties of the charts -/

/-- Each chart of the relative homogeneous spectrum is the inverse image of its affine open: the
square it forms with the structure morphisms and the inclusion of the affine open is
cartesian. -/
public theorem isPullback_relativeHomogeneousSpectrumChart (U : S.Opens) (hU : IsAffineOpen U) :
    IsPullback (relativeHomogeneousSpectrumChart A U hU) (projInclusionToOpen A U hU)
      (relativeHomogeneousSpectrumToBase A) U.ι :=
  (relativeProj A).chart_isPullback U hU

/-- The charts of the relative homogeneous spectrum are compatible with restriction: for an
inclusion `U ⊆ V` of affine opens of the base, the chart over `U` factors the chart over `V`
through the morphism of projective spectra induced by restriction of homogeneous sections. -/
public theorem projInclusionMap_comp_relativeHomogeneousSpectrumChart (U V : S.Opens) (h : U ≤ V)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    projInclusionMap A U V h hU hV ≫ relativeHomogeneousSpectrumChart A V hV =
      relativeHomogeneousSpectrumChart A U hU :=
  (relativeProj A).chart_transition U V h hU hV

/-- The relative homogeneous spectrum is characterized by its charts: between `Proj_S(A)` and any
scheme over `S` carrying projective-spectrum charts on the affine opens of `S` there is exactly
one isomorphism compatible with the charts, and it is an isomorphism over `S`. -/
public theorem existsUnique_isoOver_relativeHomogeneousSpectrum (P : RelativeProjData A) :
    ∃! e : relativeHomogeneousSpectrum A ≅ P.scheme,
      (∀ U : S.affineOpens,
          relativeHomogeneousSpectrumChart A U.1 U.2 ≫ e.hom = P.chart U.1 U.2) ∧
        e.hom ≫ P.toBase = relativeHomogeneousSpectrumToBase A :=
  RelativeProjQcohSheaf.existsUnique_isoOver A P

end Stacks.AlgebraicGeometry.RelativeProj

end

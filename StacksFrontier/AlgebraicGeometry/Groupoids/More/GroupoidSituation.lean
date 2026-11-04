module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Groupoids.Basic

/-!
# The standing groupoid situations

The openness results for the loci of a groupoid presentation are all stated for the same
standing data: a groupoid scheme over a base whose source and target maps carry a regularity
hypothesis, together with a morphism `g : U' ⟶ U` to its object scheme carrying the matching
hypothesis.  The relevant morphism is the composite
`h : U' ×_{g, U, t} R ⟶ R ⟶ U` of the projection to the arrow scheme with the source map, and
the loci in question are opens of that fibre product.  Bundling the data once avoids repeating
seven hypotheses in each statement.

Two strengths of hypothesis are needed.  The Cohen–Macaulay and syntomic loci require the
structure maps to be flat and locally of finite presentation.  The relative-dimension locus
requires only that they be locally of finite type, which is the hypothesis under which
relative dimension is defined at all; the weaker situation is recorded separately rather than
derived, since the two are used by different results.

## Main definitions

* `AlgebraicGeometry.FlatLocallyFinitelyPresentedGroupoidSituation` is the standing groupoid
  situation with flat, locally finitely presented structure maps.
* `AlgebraicGeometry.FlatLocallyFinitelyPresentedGroupoidSituation.fiberProduct` is
  `U' ×_{g, U, t} R`.
* `AlgebraicGeometry.FlatLocallyFinitelyPresentedGroupoidSituation.h` is the composite of its
  projection to the arrow scheme with the source map.
* `AlgebraicGeometry.LocallyOfFiniteTypeGroupoidSituation` is the same data under the weaker
  hypothesis that the structure maps and `g` are locally of finite type, with
  `fiberProduct` and `h` defined in the same way.

## Implementation notes

The object and arrow schemes of the groupoid are objects over the base, while `U'` and `g` are
recorded in the category of schemes.  The projection denoted `pr₁` in the source is therefore
the second categorical pullback projection, from `U' ×_{g, U, t} R` to `R`.

## References

* [Stacks Project, Tag 04LE](https://stacks.math.columbia.edu/tag/04LE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- The standing situation of a groupoid scheme with flat, locally finitely
presented source and target maps, together with a locally finitely presented
morphism `g : U' ⟶ U` to its object scheme. -/
public structure FlatLocallyFinitelyPresentedGroupoidSituation where
  /-- The base scheme. -/
  S : Scheme.{u}
  /-- The groupoid scheme `(U, R, s, t, c, e, i)` over `S`. -/
  groupoid : GroupoidScheme S
  /-- The scheme `U'`. -/
  U' : Scheme.{u}
  /-- The morphism `g : U' ⟶ U`. -/
  g : U' ⟶ groupoid.objects.left
  /-- The source map `s : R ⟶ U` is flat. -/
  [sourceFlat : Flat groupoid.source.left]
  /-- The target map `t : R ⟶ U` is flat. -/
  [targetFlat : Flat groupoid.target.left]
  /-- The source map `s : R ⟶ U` is locally of finite presentation. -/
  [sourceLocallyOfFinitePresentation :
    LocallyOfFinitePresentation groupoid.source.left]
  /-- The target map `t : R ⟶ U` is locally of finite presentation. -/
  [targetLocallyOfFinitePresentation :
    LocallyOfFinitePresentation groupoid.target.left]
  /-- The morphism `g : U' ⟶ U` is locally of finite presentation. -/
  [gLocallyOfFinitePresentation : LocallyOfFinitePresentation g]

attribute [instance]
  FlatLocallyFinitelyPresentedGroupoidSituation.sourceFlat
  FlatLocallyFinitelyPresentedGroupoidSituation.targetFlat
  FlatLocallyFinitelyPresentedGroupoidSituation.sourceLocallyOfFinitePresentation
  FlatLocallyFinitelyPresentedGroupoidSituation.targetLocallyOfFinitePresentation
  FlatLocallyFinitelyPresentedGroupoidSituation.gLocallyOfFinitePresentation

namespace FlatLocallyFinitelyPresentedGroupoidSituation

/-- The fibre product `U' ×_{g, U, t} R`. -/
public noncomputable def fiberProduct
    (D : FlatLocallyFinitelyPresentedGroupoidSituation) : Scheme.{u} :=
  pullback D.g D.groupoid.target.left

/-- The map `h : U' ×_{g, U, t} R ⟶ U`, obtained by projecting to the arrow
scheme `R` and then applying the source map `s`. -/
public noncomputable def h
    (D : FlatLocallyFinitelyPresentedGroupoidSituation) :
    D.fiberProduct ⟶ D.groupoid.objects.left :=
  pullback.snd D.g D.groupoid.target.left ≫ D.groupoid.source.left

end FlatLocallyFinitelyPresentedGroupoidSituation

/-- The standing situation of a groupoid scheme whose source and target maps, together with a
morphism `g : U' ⟶ U` to its object scheme, are locally of finite type.  No flatness condition
is imposed on either structure map.  This is the hypothesis under which the relative dimension
of `h` is defined. -/
public structure LocallyOfFiniteTypeGroupoidSituation where
  /-- The base scheme. -/
  S : Scheme.{u}
  /-- The groupoid scheme `(U, R, s, t, c, e, i)` over `S`. -/
  groupoid : GroupoidScheme S
  /-- The scheme `U'`. -/
  U' : Scheme.{u}
  /-- The morphism `g : U' ⟶ U`. -/
  g : U' ⟶ groupoid.objects.left
  /-- The source map `s : R ⟶ U` is locally of finite type. -/
  [sourceLocallyOfFiniteType : LocallyOfFiniteType groupoid.source.left]
  /-- The target map `t : R ⟶ U` is locally of finite type. -/
  [targetLocallyOfFiniteType : LocallyOfFiniteType groupoid.target.left]
  /-- The morphism `g : U' ⟶ U` is locally of finite type. -/
  [gLocallyOfFiniteType : LocallyOfFiniteType g]

attribute [instance]
  LocallyOfFiniteTypeGroupoidSituation.sourceLocallyOfFiniteType
  LocallyOfFiniteTypeGroupoidSituation.targetLocallyOfFiniteType
  LocallyOfFiniteTypeGroupoidSituation.gLocallyOfFiniteType

namespace LocallyOfFiniteTypeGroupoidSituation

/-- The fibre product `U' ×_{g, U, t} R`. -/
public noncomputable def fiberProduct
    (D : LocallyOfFiniteTypeGroupoidSituation) : Scheme.{u} :=
  pullback D.g D.groupoid.target.left

/-- The map `h : U' ×_{g, U, t} R ⟶ U`, obtained by projecting to the arrow
scheme `R` and then applying the source map `s`. -/
public noncomputable def h
    (D : LocallyOfFiniteTypeGroupoidSituation) :
    D.fiberProduct ⟶ D.groupoid.objects.left :=
  pullback.snd D.g D.groupoid.target.left ≫ D.groupoid.source.left

end LocallyOfFiniteTypeGroupoidSituation

end AlgebraicGeometry

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.GorensteinFiber
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.Composition
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.LocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.CompositeChartData
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Gorenstein.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Gorenstein.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Composition of Gorenstein morphisms of algebraic spaces

For composable morphisms of algebraic spaces over `S` whose fibres are locally Noetherian,
Gorensteinness passes to the composite. Conversely, when the first morphism is flat,
Gorensteinness of the composite descends to the first morphism and to the second morphism at
every point of the image of the first.

## Main results

* `AlgebraicGeometry.Space.isGorensteinAt_comp` and `AlgebraicGeometry.Space.isGorenstein_comp`
  are the pointwise and global composition statements.
* `AlgebraicGeometry.Space.isGorensteinAt_left_of_comp_of_isFlatAt` and
  `AlgebraicGeometry.Space.isGorensteinAt_right_of_comp_of_isFlatAt` are the pointwise
  reflection statements.
* `AlgebraicGeometry.Space.isGorenstein_left_of_comp_of_isFlat` and
  `AlgebraicGeometry.Space.isGorensteinAt_right_of_comp_of_isFlat` are the global reflection
  statements.

## Implementation notes

The six declarations state part (1), part (2), the two conclusions of part (3) and the two
conclusions of part (4) of the source lemma. The second conclusion of part (4) is quantified
over the points of the source, which is how it expresses the claim at every point of the image
of the first morphism. The source states part (4) for `f ∘ g` with `f` flat; that is a slip for
`g ∘ f` with `f` flat, which is what the scheme-level statement Tag 0C11 says and what is proved
here.

The proof is the first of the two the source offers: working étale locally, the statement
follows from the corresponding result for schemes, Tag 0C11. A pair of composable morphisms
admits a compatible triple of étale scheme charts pointed over any point of the source: a
surjective étale scheme chart of the outer target, a surjective étale chart of the middle space
over it obtained as an atlas of the fibre product, and likewise a chart of the source. Both
conjuncts of `AlgebraicGeometry.Space.IsGorensteinAt` are chart conditions of Tag 04NC, so
`AlgebraicGeometry.Space.holdsOnEveryEtaleChartAtPoint_iff_of_chart` evaluates them on that one
triple, and the three statements for `f`, `g` and `f ≫ g` become the scheme statements of Tag
0C11 for the three chart morphisms, which are in turn the Gorenstein criterion for a flat local
homomorphism of Tag 0BJL.

What the standing hypothesis that the fibres are locally Noetherian is used for is exactly this:
the scheme-level predicate carries local Noetherianity of the fibres of the chart morphism as
data, and that is supplied by
`AlgebraicGeometry.Space.locallyNoetherianFibers_of_etale_pullback_chart`, which reads the
fibre of a chart morphism over a point of the target chart off the fibre of the morphism of
spaces over the residue field of that point through Tag 0CUW.

## References

* [Stacks Project, Tag 0E16](https://stacks.math.columbia.edu/tag/0E16)
* [Stacks Project, Tag 0C11](https://stacks.math.columbia.edu/tag/0C11)
* [Stacks Project, Tag 0BJL](https://stacks.math.columbia.edu/tag/0BJL)
* [Stacks Project, Tag 0E14](https://stacks.math.columbia.edu/tag/0E14)
* [Stacks Project, Tag 0E13](https://stacks.math.columbia.edu/tag/0E13)
* [Stacks Project, Tag 04NC](https://stacks.math.columbia.edu/tag/04NC)
* [Stacks Project, Tag 0CUX](https://stacks.math.columbia.edu/tag/0CUX)
* [Stacks Project, Tag 0CUW](https://stacks.math.columbia.edu/tag/0CUW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0E16, part (1).** The composite of two morphisms of algebraic spaces with locally
Noetherian fibres is Gorenstein at a point of its source as soon as the first is Gorenstein
there and the second is Gorenstein at the image of that point. -/
@[stacks 0E16 "part (1)"]
theorem isGorensteinAt_comp
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : HasLocallyNoetherianFibersAtPoints B S hS f)
    (hg : HasLocallyNoetherianFibersAtPoints B S hS g)
    (hgf : HasLocallyNoetherianFibersAtPoints B S hS (f ≫ g))
    (x : points B S hS X) (hfx : IsGorensteinAt B S hS f x)
    (hgy : IsGorensteinAt B S hS g (pointsMap B S hS X f x)) :
    IsGorensteinAt B S hS (f ≫ g) x := by
  obtain ⟨d⟩ := exists_compositeChartData B S hS hX hY hZ f g x
  let T := BigFppfOver.toScheme B S hS
  exact (isGorensteinAt_iff_chart B S hS (f ≫ g) x d.chartComp (d.noethComp hgf)).mpr
    (Scheme.Hom.isGorensteinAt_comp (T.map d.α) (T.map d.β) (d.noethF hf) (d.noethG hg)
      (d.noethComp hgf) (d.chartF.sourcePoint B S hS)
      ((isGorensteinAt_iff_chart B S hS f x d.chartF (d.noethF hf)).mp hfx)
      ((isGorensteinAt_iff_chart B S hS g _ d.chartG (d.noethG hg)).mp hgy))

/-- **Stacks 0E16, part (2).** The composite of two Gorenstein morphisms of algebraic spaces
with locally Noetherian fibres is Gorenstein. -/
@[stacks 0E16 "part (2)"]
theorem isGorenstein_comp
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : HasLocallyNoetherianFibersAtPoints B S hS f)
    (hg : HasLocallyNoetherianFibersAtPoints B S hS g)
    (hgf : HasLocallyNoetherianFibersAtPoints B S hS (f ≫ g))
    (hfm : IsGorenstein B S hS f) (hgm : IsGorenstein B S hS g) :
    IsGorenstein B S hS (f ≫ g) := fun x =>
  isGorensteinAt_comp B S hS hX hY hZ f g hf hg hgf x (hfm x)
    (hgm (pointsMap B S hS X f x))

/-- If the composite is Gorenstein at `x` and the first morphism is flat at `x`, then the first
morphism is Gorenstein at `x` and the second is Gorenstein at the image of `x`. -/
private theorem isGorensteinAt_and_of_comp_of_isFlatAt
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : HasLocallyNoetherianFibersAtPoints B S hS f)
    (hg : HasLocallyNoetherianFibersAtPoints B S hS g)
    (hgf : HasLocallyNoetherianFibersAtPoints B S hS (f ≫ g))
    (x : points B S hS X) (hcomp : IsGorensteinAt B S hS (f ≫ g) x)
    (hflat : IsFlatAt B S hS f x) :
    IsGorensteinAt B S hS f x ∧ IsGorensteinAt B S hS g (pointsMap B S hS X f x) := by
  obtain ⟨d⟩ := exists_compositeChartData B S hS hX hY hZ f g x
  let T := BigFppfOver.toScheme B S hS
  have hc := (isGorensteinAt_iff_chart B S hS (f ≫ g) x d.chartComp (d.noethComp hgf)).mp hcomp
  have hfl := (MorphismOfGerms.isFlat_ofSchemeHom_iff (T.map d.α)
    (d.chartF.sourcePoint B S hS)).mp (hflat d.chartF)
  exact ⟨(isGorensteinAt_iff_chart B S hS f x d.chartF (d.noethF hf)).mpr
      (Scheme.Hom.isGorensteinAt_left_of_comp (T.map d.α) (T.map d.β) (d.noethF hf)
        (d.noethG hg) (d.noethComp hgf) (d.chartF.sourcePoint B S hS) hc hfl),
    (isGorensteinAt_iff_chart B S hS g _ d.chartG (d.noethG hg)).mpr
      (Scheme.Hom.isGorensteinAt_right_of_comp (T.map d.α) (T.map d.β) (d.noethF hf)
        (d.noethG hg) (d.noethComp hgf) (d.chartF.sourcePoint B S hS) hc hfl)⟩

/-- **Stacks 0E16, part (3), first conclusion.** If the composite is Gorenstein at `x` and the
first morphism is flat at `x`, then the first morphism is Gorenstein at `x`. -/
@[stacks 0E16 "part (3), first conclusion"]
theorem isGorensteinAt_left_of_comp_of_isFlatAt
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : HasLocallyNoetherianFibersAtPoints B S hS f)
    (hg : HasLocallyNoetherianFibersAtPoints B S hS g)
    (hgf : HasLocallyNoetherianFibersAtPoints B S hS (f ≫ g))
    (x : points B S hS X) (hcomp : IsGorensteinAt B S hS (f ≫ g) x)
    (hflat : IsFlatAt B S hS f x) : IsGorensteinAt B S hS f x :=
  (isGorensteinAt_and_of_comp_of_isFlatAt B S hS hX hY hZ f g hf hg hgf x hcomp hflat).1

/-- **Stacks 0E16, part (3), second conclusion.** If the composite is Gorenstein at `x` and the
first morphism is flat at `x`, then the second morphism is Gorenstein at the image of `x`. -/
@[stacks 0E16 "part (3), second conclusion"]
theorem isGorensteinAt_right_of_comp_of_isFlatAt
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : HasLocallyNoetherianFibersAtPoints B S hS f)
    (hg : HasLocallyNoetherianFibersAtPoints B S hS g)
    (hgf : HasLocallyNoetherianFibersAtPoints B S hS (f ≫ g))
    (x : points B S hS X) (hcomp : IsGorensteinAt B S hS (f ≫ g) x)
    (hflat : IsFlatAt B S hS f x) :
    IsGorensteinAt B S hS g (pointsMap B S hS X f x) :=
  (isGorensteinAt_and_of_comp_of_isFlatAt B S hS hX hY hZ f g hf hg hgf x hcomp hflat).2

/-- **Stacks 0E16, part (4), first conclusion.** If the composite is Gorenstein and the first
morphism is flat, then the first morphism is Gorenstein. -/
@[stacks 0E16 "part (4), first conclusion"]
theorem isGorenstein_left_of_comp_of_isFlat
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : HasLocallyNoetherianFibersAtPoints B S hS f)
    (hg : HasLocallyNoetherianFibersAtPoints B S hS g)
    (hgf : HasLocallyNoetherianFibersAtPoints B S hS (f ≫ g))
    (hcomp : IsGorenstein B S hS (f ≫ g)) (hflat : IsFlat B S hS f) :
    IsGorenstein B S hS f := fun x =>
  isGorensteinAt_left_of_comp_of_isFlatAt B S hS hX hY hZ f g hf hg hgf x (hcomp x)
    (isFlatAt_of_isFlat B S hS f hflat x)

/-- **Stacks 0E16, part (4), second conclusion.** If the composite is Gorenstein and the first
morphism is flat, then the second morphism is Gorenstein at every point in the image of the
first. -/
@[stacks 0E16 "part (4), second conclusion"]
theorem isGorensteinAt_right_of_comp_of_isFlat
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : HasLocallyNoetherianFibersAtPoints B S hS f)
    (hg : HasLocallyNoetherianFibersAtPoints B S hS g)
    (hgf : HasLocallyNoetherianFibersAtPoints B S hS (f ≫ g))
    (hcomp : IsGorenstein B S hS (f ≫ g)) (hflat : IsFlat B S hS f)
    (x : points B S hS X) :
    IsGorensteinAt B S hS g (pointsMap B S hS X f x) :=
  isGorensteinAt_right_of_comp_of_isFlatAt B S hS hX hY hZ f g hf hg hgf x (hcomp x)
    (isFlatAt_of_isFlat B S hS f hflat x)

end Space

end AlgebraicGeometry

end

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Composition
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.CohenMacaulay.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.LocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.CohenMacaulay.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.CompositeChartData
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Composition of Cohen–Macaulay morphisms of algebraic spaces

For composable morphisms of algebraic spaces over `S` whose fibres are locally Noetherian,
Cohen–Macaulayness passes to the composite. Conversely, when the first morphism is flat,
Cohen–Macaulayness of the composite descends to the first morphism and to the second morphism
at every point of the image of the first.

## Main results

* `AlgebraicGeometry.Space.isCohenMacaulayAt_comp` and
  `AlgebraicGeometry.Space.isCohenMacaulay_comp` are the pointwise and global composition
  statements.
* `AlgebraicGeometry.Space.isCohenMacaulayAt_left_of_comp_of_isFlatAt` and
  `AlgebraicGeometry.Space.isCohenMacaulayAt_right_of_comp_of_isFlatAt` are the pointwise
  reflection statements.
* `AlgebraicGeometry.Space.isCohenMacaulay_left_of_comp_of_isFlat` and
  `AlgebraicGeometry.Space.isCohenMacaulayAt_right_of_comp_of_isFlat` are the global
  reflection statements.

## Implementation notes

The six declarations state part (1), part (2), the two conclusions of part (3) and the two
conclusions of part (4) of the source lemma. The second conclusion of part (4) is quantified
over the points of the source, which is how it expresses the claim at every point of the image
of the first morphism. The source states part (4) for `f ∘ g` with `f` flat; that is a slip for
`g ∘ f` with `f` flat, which is what the scheme-level statement Tag 0C0W says and what is
proved here.

The proof is the étale-local reduction the source indicates. A pair of composable morphisms
admits a compatible triple of étale scheme charts pointed over any point of the source: a
surjective étale scheme chart of the outer target, a surjective étale chart of the middle space
over it obtained as an atlas of the fibre product, and likewise a chart of the source. Both
conjuncts of `AlgebraicGeometry.Space.IsCohenMacaulayAt` are chart conditions of Tag 04NC, so
`AlgebraicGeometry.Space.holdsOnEveryEtaleChartAtPoint_iff_of_chart` evaluates them on that one
triple, and the three statements for `f`, `g` and `f ≫ g` become the scheme statements of Tag
0C0W for the three chart morphisms.

What the standing hypothesis that the fibres are locally Noetherian is used for is exactly
this: the scheme-level predicate carries local Noetherianity of the fibres of the chart
morphism as data, and that is supplied by
`AlgebraicGeometry.Space.locallyNoetherianFibers_of_etale_pullback_chart`, which reads the
fibre of a chart morphism over a point of the target chart off the fibre of the morphism of
spaces over the residue field of that point through Tag 0CUW.

## References

* [Stacks Project, Tag 0E0X](https://stacks.math.columbia.edu/tag/0E0X)
* [Stacks Project, Tag 0C0W](https://stacks.math.columbia.edu/tag/0C0W)
* [Stacks Project, Tag 0E0V](https://stacks.math.columbia.edu/tag/0E0V)
* [Stacks Project, Tag 04NC](https://stacks.math.columbia.edu/tag/04NC)
* [Stacks Project, Tag 0CUX](https://stacks.math.columbia.edu/tag/0CUX)
* [Stacks Project, Tag 0CUW](https://stacks.math.columbia.edu/tag/0CUW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0E0X, part (1).** The composite of two morphisms of algebraic spaces with
locally Noetherian fibres is Cohen–Macaulay at a point of its source as soon as the first
is Cohen–Macaulay there and the second is Cohen–Macaulay at the image of that point. -/
@[stacks 0E0X "part (1)", ega "IV 6.6.1" "a) of (i)", ega "IV 6.8.3" "(i), Cohen-Macaulay"]
theorem isCohenMacaulayAt_comp
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : HasLocallyNoetherianFibersAtPoints B S hS f)
    (hg : HasLocallyNoetherianFibersAtPoints B S hS g)
    (hgf : HasLocallyNoetherianFibersAtPoints B S hS (f ≫ g))
    (x : points B S hS X) (hfx : IsCohenMacaulayAt B S hS f x)
    (hgy : IsCohenMacaulayAt B S hS g (pointsMap B S hS X f x)) :
    IsCohenMacaulayAt B S hS (f ≫ g) x := by
  obtain ⟨d⟩ := exists_compositeChartData B S hS hX hY hZ f g x
  let T := BigFppfOver.toScheme B S hS
  exact (isCohenMacaulayAt_iff_chart B S hS (f ≫ g) x d.chartComp (d.noethComp hgf)).mpr
    (_root_.AlgebraicGeometry.isCohenMacaulayAt_comp (T.map d.α) (T.map d.β) (d.noethF hf)
      (d.noethG hg) (d.noethComp hgf) (d.chartF.sourcePoint B S hS)
      ((isCohenMacaulayAt_iff_chart B S hS f x d.chartF (d.noethF hf)).mp hfx)
      ((isCohenMacaulayAt_iff_chart B S hS g _ d.chartG (d.noethG hg)).mp hgy))

/-- **Stacks 0E0X, part (2).** The composite of two Cohen–Macaulay morphisms of algebraic
spaces with locally Noetherian fibres is Cohen–Macaulay. -/
@[stacks 0E0X "part (2)"]
theorem isCohenMacaulay_comp
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : HasLocallyNoetherianFibersAtPoints B S hS f)
    (hg : HasLocallyNoetherianFibersAtPoints B S hS g)
    (hgf : HasLocallyNoetherianFibersAtPoints B S hS (f ≫ g))
    (hfm : IsCohenMacaulay B S hS f) (hgm : IsCohenMacaulay B S hS g) :
    IsCohenMacaulay B S hS (f ≫ g) := fun x =>
  isCohenMacaulayAt_comp B S hS hX hY hZ f g hf hg hgf x (hfm x)
    (hgm (pointsMap B S hS X f x))

/-- If `f ≫ g` is Cohen–Macaulay and `f` flat at `x`, then `f` at `x` and `g` at the image of
`x` are Cohen–Macaulay, as soon as their fibres are locally Noetherian. -/
private theorem isCohenMacaulayAt_and_of_comp_of_isFlatAt
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hgf : HasLocallyNoetherianFibersAtPoints B S hS (f ≫ g))
    (x : points B S hS X) (hcomp : IsCohenMacaulayAt B S hS (f ≫ g) x)
    (hflat : IsFlatAt B S hS f x) :
    (HasLocallyNoetherianFibersAtPoints B S hS f → IsCohenMacaulayAt B S hS f x) ∧
      (HasLocallyNoetherianFibersAtPoints B S hS g →
        IsCohenMacaulayAt B S hS g (pointsMap B S hS X f x)) := by
  obtain ⟨d⟩ := exists_compositeChartData B S hS hX hY hZ f g x
  let T := BigFppfOver.toScheme B S hS
  have hC := (isCohenMacaulayAt_iff_chart B S hS (f ≫ g) x d.chartComp
    (d.noethComp hgf)).mp hcomp
  have hF := (MorphismOfGerms.isFlat_ofSchemeHom_iff (T.map d.α)
    (d.chartF.sourcePoint B S hS)).mp (hflat d.chartF)
  exact ⟨fun hf => (isCohenMacaulayAt_iff_chart B S hS f x d.chartF (d.noethF hf)).mpr
      (_root_.AlgebraicGeometry.isCohenMacaulayAt_left_of_comp_of_flatAt _ _
        (d.noethF hf) (d.noethComp hgf) _ hC hF),
    fun hg => (isCohenMacaulayAt_iff_chart B S hS g _ d.chartG (d.noethG hg)).mpr
      (_root_.AlgebraicGeometry.isCohenMacaulayAt_right_of_comp_of_flatAt _ _
        (d.noethG hg) (d.noethComp hgf) _ hC hF)⟩

/-- **Stacks 0E0X, part (3), first conclusion.** If the composite is Cohen–Macaulay at `x`
and the first morphism is flat at `x`, then the first morphism is Cohen–Macaulay at `x`. -/
@[stacks 0E0X "part (3), first conclusion"]
theorem isCohenMacaulayAt_left_of_comp_of_isFlatAt
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : HasLocallyNoetherianFibersAtPoints B S hS f)
    (hgf : HasLocallyNoetherianFibersAtPoints B S hS (f ≫ g))
    (x : points B S hS X) (hcomp : IsCohenMacaulayAt B S hS (f ≫ g) x)
    (hflat : IsFlatAt B S hS f x) : IsCohenMacaulayAt B S hS f x :=
  (isCohenMacaulayAt_and_of_comp_of_isFlatAt B S hS hX hY hZ f g hgf x hcomp hflat).1 hf

/-- **Stacks 0E0X, part (3), second conclusion.** If the composite is Cohen–Macaulay at `x`
and the first morphism is flat at `x`, then the second morphism is Cohen–Macaulay at the
image of `x`. -/
@[stacks 0E0X "part (3), second conclusion"]
theorem isCohenMacaulayAt_right_of_comp_of_isFlatAt
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg : HasLocallyNoetherianFibersAtPoints B S hS g)
    (hgf : HasLocallyNoetherianFibersAtPoints B S hS (f ≫ g))
    (x : points B S hS X) (hcomp : IsCohenMacaulayAt B S hS (f ≫ g) x)
    (hflat : IsFlatAt B S hS f x) :
    IsCohenMacaulayAt B S hS g (pointsMap B S hS X f x) :=
  (isCohenMacaulayAt_and_of_comp_of_isFlatAt B S hS hX hY hZ f g hgf x hcomp hflat).2 hg

/-- **Stacks 0E0X, part (4), first conclusion.** If the composite is Cohen–Macaulay and the
first morphism is flat, then the first morphism is Cohen–Macaulay. -/
@[stacks 0E0X "part (4), first conclusion"]
theorem isCohenMacaulay_left_of_comp_of_isFlat
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : HasLocallyNoetherianFibersAtPoints B S hS f)
    (hgf : HasLocallyNoetherianFibersAtPoints B S hS (f ≫ g))
    (hcomp : IsCohenMacaulay B S hS (f ≫ g)) (hflat : IsFlat B S hS f) :
    IsCohenMacaulay B S hS f := fun x =>
  isCohenMacaulayAt_left_of_comp_of_isFlatAt B S hS hX hY hZ f g hf hgf x (hcomp x)
    (isFlatAt_of_isFlat B S hS f hflat x)

/-- **Stacks 0E0X, part (4), second conclusion.** If the composite is Cohen–Macaulay and the
first morphism is flat, then the second morphism is Cohen–Macaulay at every point in the image
of the first. -/
@[stacks 0E0X "part (4), second conclusion",
  ega "IV 6.6.1" "a) of (ii)",
  ega "IV 6.8.3" "(ii), Cohen-Macaulay"]
theorem isCohenMacaulayAt_right_of_comp_of_isFlat
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg : HasLocallyNoetherianFibersAtPoints B S hS g)
    (hgf : HasLocallyNoetherianFibersAtPoints B S hS (f ≫ g))
    (hcomp : IsCohenMacaulay B S hS (f ≫ g)) (hflat : IsFlat B S hS f)
    (x : points B S hS X) :
    IsCohenMacaulayAt B S hS g (pointsMap B S hS X f x) :=
  isCohenMacaulayAt_right_of_comp_of_isFlatAt B S hS hX hY hZ f g hg hgf x (hcomp x)
    (isFlatAt_of_isFlat B S hS f hflat x)

end AlgebraicGeometry.Space

end

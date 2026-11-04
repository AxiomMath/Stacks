module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackSection
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreFlatnessChartPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreFlatnessGeometricPoint

/-!
# Stacks 05WZ: the fibrewise flatness terminology at a point of an algebraic space

Let `X ⟶ Y ⟶ Z` be morphisms of algebraic spaces over a scheme `S` of a big fppf site, let `F`
be a quasi-coherent `𝒪_X`-module and let `x` be a point of `|X|` with image `z` in `|Z|`.
Stacks 05WZ introduces three pieces of terminology, each defined by "the equivalent conditions
of Lemma 05WY are satisfied":

1. *the restriction of `F` to its fibre over `z` is flat at `x` over the fibre of `Y` over `z`*;
2. *the fibre of `X` over `z` is flat at `x` over the fibre of `Y` over `z`*, which is (1) at
   `F = 𝒪_X`;
3. *the fibre of `X` over `z` is flat over the fibre of `Y` over `z`*, which is (2) at every
   point of `|X|` lying over `z`.

## Main definitions

* `AlgebraicGeometry.Space.IsFlatOnFibreAt`: **Stacks 05WZ, part (1)**.
* the structure sheaf `𝒪_X` read as an `𝒪_X`-module is
  `AlgebraicGeometry.Space.structureModule`, which is the module part (2) specialises to.
* `AlgebraicGeometry.Space.IsFlatFibreAt`: **Stacks 05WZ, part (2)**.
* `AlgebraicGeometry.Space.IsFlatFibre`: **Stacks 05WZ, part (3)**.

## Main results

* `AlgebraicGeometry.Space.isFlatOnFibreAt_iff_isFibreFlatOverAtGeometricPoint_of_liesOver`: at
  any one geometric point above `x` the terminology of part (1) is the condition of Stacks 05WY
  at that point, so the universal quantification over geometric points below is not a
  strengthening.
* `AlgebraicGeometry.Space.isFlatOnFibreAt_iff_isFibreFlatOverAtGeometricPoint`: the same
  universal quantification written out, which holds by `Iff.rfl`.

## Implementation notes

The condition the terminology is defined by is the Stacks 05WY notion
`AlgebraicGeometry.Space.IsFibreFlatOverAtGeometricPoint` of
`StacksFrontier/AlgebraicGeometry/Spaces/FibreFlatnessGeometricPoint.lean`, namely condition (1)
of that lemma: the fibre `F_{x̄} / 𝔪_{z̄} F_{x̄}` of the geometric stalk is flat over the fibre
`𝒪_{Y, ȳ} / 𝔪_{z̄} 𝒪_{Y, ȳ}` of the étale local ring.  The equivalence that Stacks 05WZ invokes
is available in the form
`AlgebraicGeometry.Space.exists_flatQuotSMul_chart_iff_isFibreFlatOverAtGeometricPoint` and, at
an arbitrary chosen diagram,
`AlgebraicGeometry.Space.forall_flatQuotSMul_chart_iff_isFibreFlatOverAtGeometricPoint`, which
are Stacks 05WY for conditions (1) and (3), so the choice of condition (1) here is a choice of
representative for an established equivalence class of conditions and not a weakening.  No
condition of Stacks 05WY is restated here.

Condition (2) of Stacks 05WY — flatness of the pullback of `F` to the fibre
`X_z = Spec(K) ×_{z, Z} X` over `Y_z`, in the sense of Stacks 05VV — is available too, as
`Space.isFlatOverAtGeometricPoint_fieldFibreSpace_iff_isFibreFlatOverAtGeometricPoint` of
`StacksFrontier/AlgebraicGeometry/Spaces/FibreFlatnessFieldFibre.lean` (and, with flatness at a
point spelled by the chartwise predicate of Definition 05VV,
`AlgebraicGeometry.Space.isFlatOverAtPoint_fieldFibreSpace_iff_isFibreFlatOverAtGeometricPoint`),
so this terminology may equally be read through it.

The source states the condition after choosing a geometric point `x̄` above `x`, and parts (1)
and (2) here quantify universally over the geometric points above `x` instead.  Nothing is lost
or gained by that: the condition of Stacks 05WY at a geometric point depends only on the point
of `|X|` it lies over
(`AlgebraicGeometry.Space.isFibreFlatOverAtGeometricPoint_congr_of_image_eq`), so the universal
quantification is the condition at any single chosen geometric point above `x`, which is
`AlgebraicGeometry.Space.isFlatOnFibreAt_iff_isFibreFlatOverAtGeometricPoint_of_liesOver`;
every point of `|X|` carries one by
`AlgebraicGeometry.Space.exists_geometricRepresentative`.

That independence *is* a formal consequence of the equivalence of conditions (1) and
(3).  The chart conditions do each quantify over their own charts, but condition (3) in the form
`Space.exists_chartPoint_isFibreFlatOnChartSquares_iff_isFibreFlatOverAtGeometricPoint` carries
a point of a chart above `x` rather than a lift of `x̄`, and so mentions the geometric point
only through `AlgebraicGeometry.Space.GeometricPoint.image`; at two geometric points with the
same image it is therefore literally the same statement.  Note that
`AlgebraicGeometry.Space.isFlatOnFibreAt_iff_isFibreFlatOverAtGeometricPoint` below does not
give this: it restates one universal quantification as another and holds by `Iff.rfl`.

Part (2) is part (1) at `F = 𝒪_X`, which is `SheafOfModules.unit` of the structure ring sheaf of
the small étale ringed site.  Its module sections live in the universe of the structure rings,
so parts (2) and (3) are stated at that universe while part (1) carries an independent module
universe, as `AlgebraicGeometry.Space.IsFibreFlatOverAtGeometricPoint` does.

Part (3) quantifies over the points of `|X|` whose image under the composite is `z`; the map of
point sets is `AlgebraicGeometry.Space.pointsMap`.

## References

* [Stacks Project, Tag 05WZ](https://stacks.math.columbia.edu/tag/05WZ)
* [Stacks Project, Tag 05WY](https://stacks.math.columbia.edu/tag/05WY)
* [Stacks Project, Tag 05WX](https://stacks.math.columbia.edu/tag/05WX)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The terminology of Stacks 05WZ -/

/-- **Stacks 05WZ, part (1).** The restriction of an `𝒪_X`-module `F` to its fibre over the
image `z` of a point `x` of `|X|` is *flat at `x` over the fibre of `Y` over `z`* when the
condition of Stacks 05WY holds at every geometric point of `X` above `x`.

The source defines this by "the equivalent conditions of Lemma 05WY are satisfied"; the
condition used is `AlgebraicGeometry.Space.IsFibreFlatOverAtGeometricPoint`, condition (1) of
that lemma, whose equivalence with condition (3) is
`AlgebraicGeometry.Space.exists_flatQuotSMul_chart_iff_isFibreFlatOverAtGeometricPoint`.  See
`AlgebraicGeometry.Space.isFlatOnFibreAt_iff_isFibreFlatOverAtGeometricPoint` for the reading at
a single chosen geometric point. -/
@[stacks 05WZ "part (1), defined through the Lemma 05WY notion \
IsFibreFlatOverAtGeometricPoint (its condition (1)), asked at every geometric point over x; \
equal to that condition at any one such point by isFlatOnFibreAt_iff_..."]
def IsFlatOnFibreAt {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (h : Y ⟶ Z)
    (F : Modules.{u, m} B S hS X.1 X.2) (x : points B S hS X.1) : Prop :=
  ∀ xbar : GeometricPoint B S hS X.1, xbar.LiesOver x →
    IsFibreFlatOverAtGeometricPoint B S hS f h F xbar

/-- **The terminology of Stacks 05WZ, part (1), at one chosen geometric point above `x`.**  For
a geometric point `x̄` lying over `x`, part (1) at `x` is the condition of Stacks 05WY at `x̄`
alone.

The universal quantification in `AlgebraicGeometry.Space.IsFlatOnFibreAt` is therefore not a
strengthening of the source's "pick a geometric point above `x`": the condition of Stacks 05WY
at a geometric point depends only on its image in `|X|`
(`AlgebraicGeometry.Space.isFibreFlatOverAtGeometricPoint_congr_of_image_eq`), so holding at one
geometric point above `x` is holding at all of them. -/
theorem isFlatOnFibreAt_iff_isFibreFlatOverAtGeometricPoint_of_liesOver
    {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (h : Y ⟶ Z)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    {x : points B S hS X.1} (xbar : GeometricPoint B S hS X.1) (hxbar : xbar.LiesOver x) :
    IsFlatOnFibreAt B S hS f h F x ↔ IsFibreFlatOverAtGeometricPoint B S hS f h F xbar :=
  ⟨fun hall => hall xbar hxbar, fun hone ybar hybar =>
    (isFibreFlatOverAtGeometricPoint_congr_of_image_eq B S hS f h F xbar ybar
      (hxbar.trans hybar.symm)).1 hone⟩

/-- The terminology of Stacks 05WZ, part (1), read as the universal quantification it is: for a
geometric point `x̄` above `x`, part (1) at `x` is the condition of Stacks 05WY at every
geometric point with the same image as `x̄`.

This holds by `Iff.rfl` and is not the reduction to a single geometric point, which is
`AlgebraicGeometry.Space.isFlatOnFibreAt_iff_isFibreFlatOverAtGeometricPoint_of_liesOver`. -/
theorem isFlatOnFibreAt_iff_isFibreFlatOverAtGeometricPoint {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (h : Y ⟶ Z) (F : Modules.{u, m} B S hS X.1 X.2)
    (xbar : GeometricPoint B S hS X.1) :
    IsFlatOnFibreAt B S hS f h F xbar.image ↔
      ∀ ybar : GeometricPoint B S hS X.1, ybar.image = xbar.image →
        IsFibreFlatOverAtGeometricPoint B S hS f h F ybar :=
  Iff.rfl

-- `𝒪_X` read as an `𝒪_X`-module is
-- `AlgebraicGeometry.Space.structureModule` of
-- `StacksFrontier/AlgebraicGeometry/Quot/PicardStackSection.lean`, which this file imports.

/-- **Stacks 05WZ, part (2).** The fibre of `X` over the image `z` of a point `x` of `|X|` is
*flat at `x` over the fibre of `Y` over `z`* when part (1) holds for `F = 𝒪_X`. -/
@[stacks 05WZ "part (2), part (1) at F = O_X, hence defined through the Lemma 05WY \
notion IsFibreFlatOverAtGeometricPoint at every geometric point over x"]
def IsFlatFibreAt {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (h : Y ⟶ Z)
    (x : points B S hS X.1) : Prop :=
  IsFlatOnFibreAt B S hS f h (structureModule X) x

/-- **Stacks 05WZ, part (3).** The fibre of `X` over a point `z` of `|Z|` is *flat over the
fibre of `Y` over `z`* when part (2) holds at every point of `|X|` lying over `z`. -/
@[stacks 05WZ "part (3), part (2) at every point of |X| over z, hence defined through the \
Lemma 05WY notion IsFibreFlatOverAtGeometricPoint"]
def IsFlatFibre {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (h : Y ⟶ Z)
    (z : points B S hS Z.1) : Prop :=
  ∀ x : points B S hS X.1, pointsMap B S hS X.1 (f.hom ≫ h.hom) x = z →
    IsFlatFibreAt B S hS f h x

end AlgebraicGeometry.Space

end

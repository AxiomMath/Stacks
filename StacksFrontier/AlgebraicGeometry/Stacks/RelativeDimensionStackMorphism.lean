module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Dimension
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsFibreProductAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactFieldValuedPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasScheme
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack

/-!
# Relative dimension at a point of a 1-morphism of algebraic stacks

Let `f : 𝒯 ⟶ 𝒳` be a 1-morphism, locally of finite type, of locally Noetherian algebraic
stacks over `S`, and let `t ∈ |𝒯|` have image `x ∈ |𝒳|`. Stacks 0DRL defines the relative
dimension `dim_t(𝒯_x)` by choosing a field-valued point `Spec k ⟶ 𝒳` representing `x` and a
point `t'` of `𝒯 ×_𝒳 Spec k` above `t`, and setting
`dim_t(𝒯_x) = dim_{t'}(𝒯 ×_𝒳 Spec k)`. Here `𝒯 ×_𝒳 Spec k` is an algebraic stack
(Stacks 04T2) which is locally Noetherian (Stacks 06R6), so the right-hand side is the
dimension of a locally Noetherian algebraic stack at a point (Stacks 0AFN).

## Main definitions

* `AlgebraicGeometry.Stack.fieldFibreStackSquare` is the fibre `𝒯 ×_𝒳 Spec k` of `f` over a
  field-valued point of `𝒳`, as a 2-fibre product square of algebraic stacks.
* `AlgebraicGeometry.Stack.fieldFibreStackDimensionAt` is the right-hand side of the formula of
  Stacks 0DRL, for a given field-valued representative and a given point of the fibre.
* `AlgebraicGeometry.Stack.relativeStackDimensionAt` is **Stacks 0DRL**, the relative dimension
  of `f` at `t`.

## Main results

* `AlgebraicGeometry.Stack.isLocallyNoetherianStack_fieldFibreStackSquare`: the fibre of `f`
  over a field-valued point of `𝒳` is a locally Noetherian algebraic stack, so the dimension of
  Stacks 0AFN is defined on it.
* `AlgebraicGeometry.Stack.exists_point_fieldFibreStackSquare`: Stacks 04XH supplies the point
  `t'` above `t` that the formula of Stacks 0DRL chooses.
* `AlgebraicGeometry.Stack.relativeStackDimensionAt_le`: every admissible pair of choices in the
  formula of Stacks 0DRL bounds the relative dimension from above.
* `AlgebraicGeometry.Stack.exists_admissible_fieldFibreStackDimensionAt`: there is at least one
  admissible pair of choices, so the relative dimension is the infimum of a non-empty set of
  values rather than the infimum of the empty set.

## Implementation notes

The value lies in `EInt`, Mathlib's extended integers, because that is where the dimension of an
algebraic stack at a point lies: a classifying stack has negative dimension (Stacks 0AFR) and
the empty stack has dimension `-∞` (Stacks Remark 0AFQ).

The source defines `dim_t(𝒯_x)` as *the* value shared by all admissible pairs of choices, and
that is realized here by the infimum of the admissible values, exactly as
`AlgebraicGeometry.Stack.dimensionAtPoint` realizes Stacks 0AFN and
`AlgebraicGeometry.Space.dimensionAtPoint` realizes Stacks 04N5. So the body selects nothing: it
is determined by `f` and `t` alone, and `AlgebraicGeometry.Stack.relativeStackDimensionAt_le` is
the resulting bound. Independence of the two choices is Stacks 0DRM, which is not proved in this
file but is proved downstream of it; see the note below.

Local Noetherianity of the fibre is a consequence rather than a hypothesis: the projection
`𝒯 ×_𝒳 Spec k ⟶ Spec k` is a base change of `f`, hence locally of finite type by Stacks 06FU,
and the spectrum of a field is locally Noetherian, so Stacks 06R6 applies. The field spectrum of
a field-valued point is read as an `AlgebraicGeometry.Stack.FieldSpectrum` to reuse
`AlgebraicGeometry.Stack.isLocallyNoetherian_fieldSpectrum`, and the existential scheme criterion
of Stacks 04YF on the algebraic stack of a scheme is its own underlying scheme's property.

Local Noetherianity of `𝒯` and of `𝒳` are arguments of the definition but are used in neither
body, exactly as in `AlgebraicGeometry.Stack.dimensionAtPoint`: they are what give the defining
condition content.

**Where Stacks 0DRM is proved.** The independence of the two choices reduces, along a smooth
scheme atlas `U ⟶ 𝒯` and a point `u ∈ |U|` above `t`, to the identity
`dim_{t'}(𝒯 ×_𝒳 Spec k) = dim_u(U_x) - dim_u(U_t)` whose two right-hand terms are relative
dimensions in the sense of Stacks 0DRG and so already independent of both choices by Stacks 0DRH.
That identity is the dimension formula of Stacks 0DRJ. This file carries only the inequality
direction, `AlgebraicGeometry.Stack.relativeStackDimensionAt_le`, because the reverse inequality
is the independence of the smooth chart in Stacks 0AFN, which is Stacks 0AFM, and neither is
available at this point in the import order. Both become available in
`StacksFrontier/AlgebraicGeometry/Stacks/DimensionChartIndependence.lean`
(`AlgebraicGeometry.Stack.dimensionSubNat_eq_dimensionSubNat_of_isSmooth` and
`AlgebraicGeometry.Stack.dimensionAtPoint_eq_dimensionSubNat_of_isSmooth`), and Stacks 0DRM is
then proved, as `AlgebraicGeometry.Stack.relativeStackDimensionAt_eq_fieldFibreStackDimensionAt`
in `StacksFrontier/AlgebraicGeometry/Stacks/RelativeDimensionStackBaseChange.lean`.

## References

* [Stacks Project, Tag 0AFM](https://stacks.math.columbia.edu/tag/0AFM)
* [Stacks Project, Tag 0AFN](https://stacks.math.columbia.edu/tag/0AFN)
* [Stacks Project, Tag 0AFQ](https://stacks.math.columbia.edu/tag/0AFQ)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 04YF](https://stacks.math.columbia.edu/tag/04YF)
* [Stacks Project, Tag 06FU](https://stacks.math.columbia.edu/tag/06FU)
* [Stacks Project, Tag 06R6](https://stacks.math.columbia.edu/tag/06R6)
* [Stacks Project, Tag 0DRG](https://stacks.math.columbia.edu/tag/0DRG)
* [Stacks Project, Tag 0DRJ](https://stacks.math.columbia.edu/tag/0DRJ)
* [Stacks Project, Tag 0DRL](https://stacks.math.columbia.edu/tag/0DRL)
* [Stacks Project, Tag 0DRM](https://stacks.math.columbia.edu/tag/0DRM)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The fibre of a 1-morphism of algebraic stacks over a field-valued point -/

section FieldFibre

variable {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- The fibre `𝒯 ×_𝒳 Spec k` of `f` over a field-valued point `p` of `𝒳`: the canonical
2-fibre product square of the 1-morphism `Spec k ⟶ 𝒳` of `p` with `f`, taken in the 2-category
of algebraic stacks over `S`. -/
noncomputable abbrev fieldFibreStackSquare (f : 𝒯 ⟶ 𝒳)
    (p : FieldValuedPoint B S hS 𝒳.val.val) :
    Bicategory.TwoCommSq (fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 p) f :=
  twoFibreProductSquareAlgebraicStacks B S hS
    (fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 p) f

/-- **Stacks 04YF at the field spectrum of a field-valued point.** The algebraic stack of the
base of a field-valued point is locally Noetherian, its underlying scheme being the spectrum of
a field. -/
theorem isLocallyNoetherianStack_schemeStack_fieldValuedPoint
    (p : FieldValuedPoint B S hS 𝒳.val.val) :
    IsLocallyNoetherianStack.{u, w} B S hS (schemeStack.{u, w} B S hS p.base) := by
  let : ObjectProperty.IsLocal (fun T : Scheme.{u} => IsLocallyNoetherian T)
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) :=
    ObjectProperty.IsLocal.of_le Scheme.smoothPrecoverage_le_fppfPrecoverage
  exact (exists_scheme_atlas_iff_scheme.{u, w} B S hS
      (fun T : Scheme.{u} => IsLocallyNoetherian T) p.base).2
    (isLocallyNoetherian_fieldSpectrum B S hS
      { carrier := p.carrier, base := p.base, isSpec := p.isSpec })

/-- **Stacks 06FU at the fibre over a field-valued point.** The projection
`𝒯 ×_𝒳 Spec k ⟶ Spec k` is locally of finite type, being a base change of `f`. -/
theorem isLocallyOfFiniteType_fieldFibreStackSquare_fst (f : 𝒯 ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (p : FieldValuedPoint B S hS 𝒳.val.val) :
    AlgebraicStacks.IsLocallyOfFiniteType B S hS (fieldFibreStackSquare B S hS f p).fst :=
  AlgebraicStacks.isLocallyOfFiniteType_baseChange B S hS f
    (fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 p) _
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
      (fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 p) f) hf

/-- **Stacks 06R6 at the fibre over a field-valued point.** The fibre `𝒯 ×_𝒳 Spec k` is a
locally Noetherian algebraic stack: it is locally of finite type over the spectrum of a field. -/
theorem isLocallyNoetherianStack_fieldFibreStackSquare (f : 𝒯 ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (p : FieldValuedPoint B S hS 𝒳.val.val) :
    IsLocallyNoetherianStack.{u, w} B S hS (fieldFibreStackSquare B S hS f p).pt :=
  AlgebraicStacks.isLocallyNoetherian_of_isLocallyOfFiniteType B S hS
    (fieldFibreStackSquare B S hS f p).fst
    (isLocallyOfFiniteType_fieldFibreStackSquare_fst.{u, w} B S hS f hf p)
    (isLocallyNoetherianStack_schemeStack_fieldValuedPoint.{u, w} B S hS p)

/-- **Stacks 04XH at the fibre over a field-valued point.** If `p` represents the image of `t`,
some point of `𝒯 ×_𝒳 Spec k` maps to `t`; this is the point the formula of Stacks 0DRL
chooses. -/
theorem exists_point_fieldFibreStackSquare (f : 𝒯 ⟶ 𝒳)
    (t : points B S hS 𝒯.val.val 𝒯.val.property)
    (p : FieldValuedPoint B S hS 𝒳.val.val)
    (hp : pointClass B S hS 𝒳.val.val 𝒳.val.property p =
      pointsMap B S hS 𝒯.val.val 𝒯.val.property 𝒳.val.property f.hom.hom t) :
    ∃ q : points B S hS (fieldFibreStackSquare B S hS f p).pt.val.val
        (fieldFibreStackSquare B S hS f p).pt.val.property,
      pointsMap B S hS (fieldFibreStackSquare B S hS f p).pt.val.val
        (fieldFibreStackSquare B S hS f p).pt.val.property 𝒯.val.property
        (fieldFibreStackSquare B S hS f p).snd.hom.hom q = t := by
  obtain ⟨q, -, hq⟩ := exists_point_of_isTwoFibreProduct_algebraicStacks.{u, w} B S hS
    (fieldFibreStackSquare B S hS f p)
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
      (fieldValuedPointStackMorphism.{u, w} B S hS 𝒳 p) f)
    (pointClass B S hS (schemeFibredCategory B S hS p.base).val
      (schemeFibredCategory B S hS p.base).property (baseFieldValuedPoint B S hS p))
    t ((pointsMap_baseFieldValuedPoint B S hS (𝒳 := 𝒳.val) p).trans hp)
  exact ⟨q, hq⟩

end FieldFibre

/-! ### The relative dimension of Stacks 0DRL -/

section RelativeDimension

variable {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- The right-hand side of the formula of Stacks 0DRL: the dimension of the locally Noetherian
algebraic stack `𝒯 ×_𝒳 Spec k` at a point `q`, for a field-valued point `p` of `𝒳` with field
spectrum `Spec k`. -/
noncomputable def fieldFibreStackDimensionAt (f : 𝒯 ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (p : FieldValuedPoint B S hS 𝒳.val.val)
    (q : points B S hS (fieldFibreStackSquare B S hS f p).pt.val.val
      (fieldFibreStackSquare B S hS f p).pt.val.property) : EInt :=
  dimensionAtPoint B S hS (fieldFibreStackSquare B S hS f p).pt
    (isLocallyNoetherianStack_fieldFibreStackSquare.{u, w} B S hS f hf p) q

/-- **Stacks 0DRL.** The relative dimension `dim_t(𝒯_x)` at `t ∈ |𝒯|` of a 1-morphism `f`,
locally of finite type, of algebraic stacks: the infimum of the dimensions of the locally
Noetherian algebraic stack `𝒯 ×_𝒳 Spec k` at a point above `t`, over the field-valued points
`Spec k ⟶ 𝒳` representing the image `x` of `t` and the points above `t`. Those are the two
choices the source makes; a point above `t` exists by Stacks 04XH.

The source states the definition for `𝒯` and `𝒳` locally Noetherian, but neither is needed:
the only object whose dimension is taken is the fibre `𝒯 ×_𝒳 Spec k`, which is locally
Noetherian for every locally-of-finite-type `f` by
`AlgebraicGeometry.Stack.isLocallyNoetherianStack_fieldFibreStackSquare`. This is
`AlgebraicGeometry.Stack.relativeStackDimensionAt` without its two local Noetherianity
arguments, which that definition never uses
(`AlgebraicGeometry.Stack.relativeStackDimensionAt_eq_relativeStackDimension`). -/
noncomputable def relativeStackDimension (f : 𝒯 ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (t : points B S hS 𝒯.val.val 𝒯.val.property) : EInt :=
  sInf {z : EInt | ∃ (p : FieldValuedPoint B S hS 𝒳.val.val)
    (q : points B S hS (fieldFibreStackSquare B S hS f p).pt.val.val
      (fieldFibreStackSquare B S hS f p).pt.val.property),
    pointClass B S hS 𝒳.val.val 𝒳.val.property p =
        pointsMap B S hS 𝒯.val.val 𝒯.val.property 𝒳.val.property f.hom.hom t ∧
      pointsMap B S hS (fieldFibreStackSquare B S hS f p).pt.val.val
          (fieldFibreStackSquare B S hS f p).pt.val.property 𝒯.val.property
          (fieldFibreStackSquare B S hS f p).snd.hom.hom q = t ∧
        z = fieldFibreStackDimensionAt.{u, w} B S hS f hf p q}

/-- **Stacks 0DRL.** The relative dimension `dim_t(𝒯_x)` at `t ∈ |𝒯|` of a 1-morphism `f`,
locally of finite type, of locally Noetherian algebraic stacks: the infimum of the dimensions of
the locally Noetherian algebraic stack `𝒯 ×_𝒳 Spec k` at a point above `t`, over the
field-valued points `Spec k ⟶ 𝒳` representing the image `x` of `t` and the points above `t`.
Those are the two choices the source makes; a point above `t` exists by Stacks 04XH. -/
@[stacks 0DRL]
noncomputable def relativeStackDimensionAt (f : 𝒯 ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (_h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
    (_h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (t : points B S hS 𝒯.val.val 𝒯.val.property) : EInt :=
  relativeStackDimension.{u, w} B S hS f hf t

/-- The relative dimension of Stacks 0DRL does not depend on the two local Noetherianity
arguments of `AlgebraicGeometry.Stack.relativeStackDimensionAt`: it is
`AlgebraicGeometry.Stack.relativeStackDimension`. -/
theorem relativeStackDimensionAt_eq_relativeStackDimension (f : 𝒯 ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (t : points B S hS 𝒯.val.val 𝒯.val.property) :
    relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳 t =
      relativeStackDimension.{u, w} B S hS f hf t :=
  rfl

/-- Every admissible pair of choices in the formula of Stacks 0DRL bounds the relative dimension
at the point from above: its value is a member of the set whose infimum that dimension is. -/
theorem relativeStackDimensionAt_le (f : 𝒯 ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (t : points B S hS 𝒯.val.val 𝒯.val.property)
    (p : FieldValuedPoint B S hS 𝒳.val.val)
    (hp : pointClass B S hS 𝒳.val.val 𝒳.val.property p =
      pointsMap B S hS 𝒯.val.val 𝒯.val.property 𝒳.val.property f.hom.hom t)
    (q : points B S hS (fieldFibreStackSquare B S hS f p).pt.val.val
      (fieldFibreStackSquare B S hS f p).pt.val.property)
    (hq : pointsMap B S hS (fieldFibreStackSquare B S hS f p).pt.val.val
      (fieldFibreStackSquare B S hS f p).pt.val.property 𝒯.val.property
      (fieldFibreStackSquare B S hS f p).snd.hom.hom q = t) :
    relativeStackDimensionAt.{u, w} B S hS f hf h𝒯 h𝒳 t ≤
      fieldFibreStackDimensionAt.{u, w} B S hS f hf p q :=
  sInf_le ⟨p, q, hp, hq, rfl⟩

/-- Every admissible pair of choices in the formula of Stacks 0DRL bounds the relative dimension
at the point from above: its value is a member of the set whose infimum that dimension is. -/
theorem relativeStackDimension_le (f : 𝒯 ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (t : points B S hS 𝒯.val.val 𝒯.val.property)
    (p : FieldValuedPoint B S hS 𝒳.val.val)
    (hp : pointClass B S hS 𝒳.val.val 𝒳.val.property p =
      pointsMap B S hS 𝒯.val.val 𝒯.val.property 𝒳.val.property f.hom.hom t)
    (q : points B S hS (fieldFibreStackSquare B S hS f p).pt.val.val
      (fieldFibreStackSquare B S hS f p).pt.val.property)
    (hq : pointsMap B S hS (fieldFibreStackSquare B S hS f p).pt.val.val
      (fieldFibreStackSquare B S hS f p).pt.val.property 𝒯.val.property
      (fieldFibreStackSquare B S hS f p).snd.hom.hom q = t) :
    relativeStackDimension.{u, w} B S hS f hf t ≤
      fieldFibreStackDimensionAt.{u, w} B S hS f hf p q :=
  sInf_le ⟨p, q, hp, hq, rfl⟩

/-- The formula of Stacks 0DRL has at least one admissible pair of choices: a field-valued point
representing the image of `t` exists because the points of an algebraic stack are classes of
field-valued points, and a point above `t` in its fibre exists by Stacks 04XH. -/
theorem exists_admissible_fieldFibreStackDimensionAt (f : 𝒯 ⟶ 𝒳)
    (t : points B S hS 𝒯.val.val 𝒯.val.property) :
    ∃ (p : FieldValuedPoint B S hS 𝒳.val.val)
      (q : points B S hS (fieldFibreStackSquare B S hS f p).pt.val.val
        (fieldFibreStackSquare B S hS f p).pt.val.property),
      pointClass B S hS 𝒳.val.val 𝒳.val.property p =
          pointsMap B S hS 𝒯.val.val 𝒯.val.property 𝒳.val.property f.hom.hom t ∧
        pointsMap B S hS (fieldFibreStackSquare B S hS f p).pt.val.val
          (fieldFibreStackSquare B S hS f p).pt.val.property 𝒯.val.property
          (fieldFibreStackSquare B S hS f p).snd.hom.hom q = t := by
  obtain ⟨q, hq⟩ := exists_point_fieldFibreStackSquare.{u, w} B S hS f t
    (Quotient.out (pointsMap B S hS 𝒯.val.val 𝒯.val.property 𝒳.val.property f.hom.hom t))
    (Quotient.out_eq _)
  exact ⟨_, q, Quotient.out_eq _, hq⟩

end RelativeDimension

end AlgebraicGeometry.Stack

end

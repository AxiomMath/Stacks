module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.NormalRegular
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.NormalTFAE
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.RegularSmooth
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.SmoothLocus

/-!
# A geometrically normal proper curve is smooth

Let `K` be a field and let `Y` be a proper curve over `K`. If `Y` is geometrically normal over
`K` then its structure morphism is smooth. Indeed every base change of `Y` to a field extension
of `K` is normal, is locally Noetherian, and has the same dimension one, and normality and
regularity agree in dimension one; so the structure morphism is geometrically regular at every
point, which for a morphism locally of finite type over a field is smoothness at that point.

## Main results

* `AlgebraicGeometry.isGeometricallyRegular_of_isGeometricallyNormal_of_isCurve`: a geometrically
  normal proper curve over a field is geometrically regular.
* `AlgebraicGeometry.smooth_of_isGeometricallyNormal_of_isCurve`: a geometrically normal proper
  curve over a field is smooth over that field.

## Implementation notes

Smoothness is Mathlib's `AlgebraicGeometry.Smooth`, the morphism property, reached from the
pointwise condition through `AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_top_iff`, exactly as in
`StacksFrontier.AlgebraicGeometry.Curves.SmoothModelOverPerfectField`. The pointwise step is Tag
038X, `AlgebraicGeometry.isGeometricallyRegularAt_iff_smoothAt`.

Geometric normality is unfolded through the second clause of
`AlgebraicGeometry.geometricallyNormal_tfae` (Tag 0380), which says that the base change to every
field extension is normal. Dimension one passes to those base changes because the structure
morphism is proper (`AlgebraicGeometry.topologicalKrullDim_baseChange`, the dimension clause of
Tag 0BY9), and normal plus dimension at most one gives regular by Tag 0BX2. Properness is used
only for that dimension step.

## References

* [Stacks Project, Tag 0BX2](https://stacks.math.columbia.edu/tag/0BX2)
* [Stacks Project, Tag 038X](https://stacks.math.columbia.edu/tag/038X)
* [Stacks Project, Tag 0380](https://stacks.math.columbia.edu/tag/0380)
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CommRingCat

universe u

namespace AlgebraicGeometry

/-- A geometrically normal proper curve over a field is geometrically regular: each base change
to a field extension is normal, locally Noetherian and again of dimension one, hence regular. -/
public theorem isGeometricallyRegular_of_isGeometricallyNormal_of_isCurve
    (K : Type u) [Field K] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of K)) [IsCurve K sY] [IsProper sY]
    (h : IsGeometricallyNormal sY) :
    IsGeometricallyRegular sY := by
  have hdim1 : topologicalKrullDim Y = 1 :=
    IsCurve.topologicalKrullDim_eq_one (k := K) (f := sY)
  have hnormal := ((geometricallyNormal_tfae K Y sY).out 1 2).mp h
  intro x L _ _ _ g x' _
  have _ : IsNormal (pullback sY g) := hnormal L
  have _ : IsLocallyNoetherian (pullback sY g) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd sY g)
  have hd : topologicalKrullDim (pullback sY g : Scheme.{u}) = 1 := by
    rw [topologicalKrullDim_baseChange K L (pullback.fst sY g) (pullback.snd sY g) sY
      (IsPullback.of_hasPullback _ _)]
    exact hdim1
  exact (((isRegular_tfae (pullback sY g)).out 1 2 rfl rfl).mp
    (isRegular_of_isNormal_of_topologicalKrullDim_le_one _ (le_of_eq hd))).2 x'

/-- A geometrically normal proper curve over a field is smooth over that field: it is
geometrically regular, and for a morphism locally of finite type over a field geometric
regularity at a point is smoothness at that point. -/
public theorem smooth_of_isGeometricallyNormal_of_isCurve
    (K : Type u) [Field K] {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of K)) [IsCurve K sY] [IsProper sY]
    (h : IsGeometricallyNormal sY) :
    Smooth sY := by
  have hgr := isGeometricallyRegular_of_isGeometricallyNormal_of_isCurve K sY h
  have _ : LocallyOfFinitePresentation sY :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← top_le_iff]
  intro x _
  exact InfinitesimalLifting.SmoothAt.formallySmooth_stalkMap sY x
    ((isGeometricallyRegularAt_iff_smoothAt sY x).mp (hgr x))

end AlgebraicGeometry

end

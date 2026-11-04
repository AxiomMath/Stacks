module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesGenusOverField
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesPrestableGenus
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliSmoothCurvesDenseOnPoints
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesOfGenusOpen
public import StacksFrontier.Topology.Dimension.LocalKrullDim

/-!
# The genus of the fibres of a family in `Curves^{prestable}_g` (towards Stacks 0E6V, 0E87)

Let `f : X → S` be a prestable family of curves with `R¹f_*𝒪_X` locally free of rank `g`, and let
`X_p` be its fibre over a field-valued point `p : Spec k → S`. The proof of Stacks 0E87 (through
`𝓜_g = Curves^{smooth} ∩ 𝓜̄_g`) needs that `X_p` has genus `g`. In the source this is what
Stacks 0E6V gives: by part (1) the classifying morphism of `X → S` factors through
`Curves^{prestable}_g`, hence so does that of `X_p`, and by part (2) `X_p` has genus `g`.

This file carries out that deduction from the openness part of part (1) of Stacks 0E6V alone
(condition (o) of Stacks 0E0E for `Curves^{prestable}_g`). The fibre `X_p` is the total space of a
family of curves over `Spec k` mapping to `X → S`, so it is prestable with `R¹` locally free of
rank `g`. Over the field, `R¹` is locally free of rank the genus of `X_p`
(`AlgebraicGeometry.isFiniteLocallyFreeOfRank_firstDirectImage_curveFamilyOverFieldOfProper_genus`,
from Stacks 071N), and the rank over a nonempty base is unique; the dimension bound `dim X_p ≤ 1`
that this needs is the relative-dimension condition of the family, read over the one-point base.

## Main definitions

* `AlgebraicGeometry.CurveFamily.fibreFamily`: the family of curves over `Spec k` whose total
  space is the fibre of a family over a field-valued point, given as a cartesian square.
* `AlgebraicGeometry.CurveFamily.fibreFamilyHom`: its cartesian morphism to the family.

## Main results

* `AlgebraicGeometry.CurveFamily.topologicalKrullDim_fibre_le_one`: the fibre has dimension at
  most one.
* `AlgebraicGeometry.genus_fibre_eq_of_isOpenCurvesLocus`: the fibres of a prestable family of
  genus `g` have genus `g`, given condition (o) for `Curves^{prestable}_g` — the input `h0E6V` of
  `AlgebraicGeometry.isOpen_dense_pointSet_moduliSmoothOfGenus_in_stableOfGenus_of_two_le`.
* `AlgebraicGeometry.dense_preimage_pointSet_moduliSmoothOfGenus_of_isOpenCurvesLocus`: the
  density part of Stacks 0E87 on the points of `𝓜̄_g`, from that openness.

## Implementation notes

No declaration here carries a `stacks` attribute: the results take the statements of other tags
as hypotheses.

## References

* [Stacks Project, Tag 0E6V](https://stacks.math.columbia.edu/tag/0E6V)
* [Stacks Project, Tag 0E87](https://stacks.math.columbia.edu/tag/0E87)
* [Stacks Project, Tag 0E6K](https://stacks.math.columbia.edu/tag/0E6K)
* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
* [Stacks Project, Tag 0BY7](https://stacks.math.columbia.edu/tag/0BY7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace CurveFamily

variable (F : CurveFamily B hZ)
  {p : Space.FieldValuedPoint B integerBase hZ (schemeSpace F.base).obj}
  {V : BigFppfOver B integerBase hZ} {v : V ⟶ p.siteObject} {q : yoneda.obj V ⟶ F.total.obj}

/-- A cartesian square of presheaves exhibiting `V` as the fibre of a family of curves over a
field-valued point is a cartesian square of algebraic spaces. -/
theorem isPullback_fibre_of_isPullback
    (hsq : IsPullback q (yoneda.map v) F.toBase.hom (yonedaEquiv.symm p.value)) :
    IsPullback (ObjectProperty.homMk q : schemeSpace V ⟶ F.total) (schemeSpaceMap v) F.toBase
      (schemeSpaceMap p.value) :=
  IsPullback.of_map_of_faithful (ObjectProperty.ι _) hsq

/-- **The fibre of a family of curves over a field-valued point, as a family of curves.** Given a
cartesian square exhibiting the object `V` of the site as the fibre of `f : X → S` over a
field-valued point `p : Spec k → S`, the morphism `V ⟶ Spec k` is a family of curves: flatness,
properness and finite presentation are stable under base change, and so is the relative dimension
at a point (Stacks 04NS). -/
def fibreFamily (hsq : IsPullback q (yoneda.map v) F.toBase.hom (yonedaEquiv.symm p.value)) :
    CurveFamily B hZ where
  base := p.siteObject
  total := schemeSpace V
  toBase := schemeSpaceMap v
  flat := (Space.isFlat_isStableUnderBaseChange B integerBase hZ).of_isPullback
    (F.isPullback_fibre_of_isPullback hsq) F.flat
  proper := (Space.isProper_isStableUnderBaseChange B integerBase hZ).of_isPullback
    (F.isPullback_fibre_of_isPullback hsq) F.proper
  finitePresentation :=
    (Space.isFinitePresentation_isStableUnderBaseChange (B := B) (S := integerBase)
      (hS := hZ)).of_isPullback (F.isPullback_fibre_of_isPullback hsq) F.finitePresentation
  relativeDimensionLE := by
    intro x'
    obtain ⟨e, he, hrel⟩ := F.relativeDimensionLE (Space.pointsMap B integerBase hZ _ q x')
    have hfinite : Space.IsLocallyOfFiniteType B integerBase hZ F.toBase.hom :=
      Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B integerBase hZ
        F.finitePresentation.1
    exact ⟨e, he, (Space.hasRelativeDimensionAt_iff_of_isPullback B integerBase hZ hsq
      F.total.property (schemeSpace p.siteObject).property (schemeSpace F.base).property hfinite
      x' (e : ℕ∞)).mp hrel⟩

/-- **The cartesian morphism from the fibre over a field-valued point to the family.** -/
def fibreFamilyHom (hsq : IsPullback q (yoneda.map v) F.toBase.hom (yonedaEquiv.symm p.value)) :
    F.fibreFamily hsq ⟶ F where
  baseMap := p.value
  totalMap := ObjectProperty.homMk q
  cartesian := F.isPullback_fibre_of_isPullback hsq

/-- The fibre of a family of curves over a field-valued point is proper over the field. -/
theorem isProper_fibre
    (hsq : IsPullback q (yoneda.map v) F.toBase.hom (yonedaEquiv.symm p.value)) :
    IsProper ((BigFppfOver.toScheme B integerBase hZ).map v) :=
  isProper_of_isPullback_fieldValuedPoint (F.isPullback_fibre_of_isPullback hsq)

/-- **The fibre of a family of curves over a field-valued point has dimension at most one.** At
a point `t` of the fibre `X_p`, the relative dimension of `X_p → Spec k` is at most one, and over
the one-point scheme `Spec k` the fibre of `X_p → Spec k` through `t` is all of `X_p`, so its
dimension there is the local dimension of `X_p` at `t`. -/
theorem topologicalKrullDim_fibre_le_one
    (hsq : IsPullback q (yoneda.map v) F.toBase.hom (yonedaEquiv.symm p.value)) :
    topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj V) ≤ 1 := by
  have : Subsingleton ((BigFppfOver.toScheme B integerBase hZ).obj p.siteObject) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of p.carrier)))
  rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
  refine iSup_le fun t => ?_
  let r := Space.schemePointRepresentative B integerBase hZ V t
  let x : Space.points B integerBase hZ (yoneda.obj V) := r.class B integerBase hZ (yoneda.obj V)
  have hx : Space.pointsToScheme B integerBase hZ V x = t :=
    Space.schemePointRepresentative_point B integerBase hZ V t
  obtain ⟨e, he, hchart⟩ := (F.fibreFamily hsq).relativeDimensionLE x
  have hg := (Space.holdsOnEveryEtaleChartAtPoint_yoneda_map_iff B integerBase hZ _
    (fiberDimensionAt_isEtaleLocalOnSourceAndTarget (e : ℕ∞)) v x).1 hchart
  rw [hx, hasFiberDimensionAt_ofSchemeHom_iff,
    topologicalKrullDimAt_fiber_asFiber_eq_of_subsingleton] at hg
  rw [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim, hg]
  exact_mod_cast he

end CurveFamily

/-- **The fibres of a prestable family of genus `g` have genus `g`**, given condition (o) of
Stacks 0E0E for `Curves^{prestable}_g` (`h0E6V`, the openness part of part (1) of Stacks 0E6V).
The fibre `X_p` over a field-valued point is the total space of a family over `Spec k` mapping to
the family, so it is prestable with `R¹` locally free of rank `g`; over the field `R¹` is locally
free of rank the genus of `X_p` (Stacks 071N), and the rank over a nonempty base is unique.

This is the input `h0E6V` of
`AlgebraicGeometry.isOpen_dense_pointSet_moduliSmoothOfGenus_in_stableOfGenus_of_two_le`. -/
theorem genus_fibre_eq_of_isOpenCurvesLocus {g : ℕ}
    (h0E6V : IsOpenCurvesLocus B hZ
      (fun X => IsPrestableCurveFamily B hZ X ∧ CurveFamily.HasGenus B hZ X g)) :
    ∀ F : CurveFamily B hZ, IsPrestableCurveFamily B hZ F →
      CurveFamily.HasGenus B hZ F g →
      ∀ (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace F.base).obj)
        (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject)
        (q : yoneda.obj V ⟶ F.total.obj),
        IsPullback q (yoneda.map v) F.toBase.hom (yonedaEquiv.symm p.value) →
          genus ((BigFppfOver.toScheme B integerBase hZ).map v) = g := by
  intro F hpre hgen p V v q hsq
  have hFp := h0E6V.prop_of_hom (F.fibreFamilyHom hsq) ⟨hpre, hgen⟩
  have hrk := isFiniteLocallyFreeOfRank_firstDirectImage_curveFamilyOverFieldOfProper_genus
    p.carrier v rfl (F.isProper_fibre hsq) (F.topologicalKrullDim_fibre_le_one hsq)
  have s : (BigFppfOver.toScheme B integerBase hZ).obj p.siteObject :=
    IsLocalRing.closedPoint (CommRingCat.of p.carrier)
  have h := CurveFamily.hasGenus_unique B hZ hFp.2 hrk s
  rw [h, eqToHom_refl, Category.comp_id]

variable (B hZ)
  (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)

/-- **The density of `|𝓜_g|` in `|𝓜̄_g|` on the points of `𝓜̄_g`, from condition (o) for
`Curves^{prestable}_g`** (the density part of Stacks 0E87, in the form the proof of Stacks 0E9A
consumes it). The genus of the fibres is supplied by
`AlgebraicGeometry.genus_fibre_eq_of_isOpenCurvesLocus`. -/
theorem dense_preimage_pointSet_moduliSmoothOfGenus_of_isOpenCurvesLocus (g : ℕ) (hg : 2 ≤ g)
    (h0E6V : IsOpenCurvesLocus B hZ
      (fun X => IsPrestableCurveFamily B hZ X ∧ CurveFamily.HasGenus B hZ X g))
    (hP : IsOpenCurvesLocus B hZ (IsStableCurveFamilyOfGenus B hZ g))
    (hQ : IsOpenCurvesLocus B hZ
      (fun X => IsSmoothH0Family B hZ X ∧ CurveFamily.HasGenus B hZ X g)) :
    @Dense _ (Stack.pointTopology B integerBase hZ
        (curvesSmallOpenSubstack B hZ h hP).toAlgebraicStack.val)
      (Stack.AlgebraicStacks.pointsMap B integerBase hZ
          (curvesSmallOpenSubstack B hZ h hP).inclusion ⁻¹'
        (curvesSmallOpenSubstack B hZ h hQ).pointSet B integerBase hZ) :=
  dense_preimage_pointSet_moduliSmoothOfGenus_of_two_le B hZ h g hg
    (genus_fibre_eq_of_isOpenCurvesLocus h0E6V) hP hQ

end AlgebraicGeometry

end

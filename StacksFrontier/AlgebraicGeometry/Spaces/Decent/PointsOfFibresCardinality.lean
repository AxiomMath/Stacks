module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Conditions
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFinitePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# The fibre of an algebraic space over a field-valued point

Let `f : X ⟶ Y` be a morphism of presheaves on the big fppf site of a scheme `S` and let `p`
be a field-valued point of `Y`, presenting a point `y` of `|Y|` by a morphism
`Spec k ⟶ Y`. The fibre `X_k = X ×_Y Spec k` has a canonical map `|X_k| → |X|`, and
Stacks 0AC8 says that when `Spec k ⟶ Y` is a quasi-compact monomorphism this map is a
homeomorphism onto `f^{-1}(\{y\})` with the induced topology.

This file proves that `|X_k| → |X|` has image exactly `f^{-1}(\{y\})`, and that it is
injective as soon as `Spec k ⟶ Y` is a monomorphism, so that it is a bijection onto the
set-theoretic fibre. It also proves the finiteness statement on which the topological half of
the source argument rests: above a point carrying a quasi-compact field-valued
representative, every étale chart with quasi-compact underlying scheme has a finite fibre.

## Main results

* `AlgebraicGeometry.Space.range_pointsMap_fibre_fieldMorphism`: the image of `|X_k| → |X|`
  is the set-theoretic fibre of `|f|` above the point presented by `p`.
* `AlgebraicGeometry.Space.injective_pointsMap_fibre_fieldMorphism`: that map is injective
  when the presenting morphism is a monomorphism.
* `AlgebraicGeometry.Space.finite_fibre_pointsMap_of_isQuasiCompact_fieldMorphism`: an étale
  chart with quasi-compact underlying scheme has a finite fibre above a point presented by a
  quasi-compact field-valued point.
* `AlgebraicGeometry.Space.hasFiniteChartFibersAtEveryPoint_of_isDecentSpace`: a decent
  algebraic space satisfies condition `(α)` of Stacks 03JX.

## Implementation notes

The image statement needs nothing about the presenting morphism: `Spec k` has one point, so
every point of `|Spec k|` maps to `y`, and a point of `|X|` above `y` lifts to the fibre by
Stacks 03H4, surjectivity of the comparison map of a cartesian square on points. Injectivity
is Stacks 06RV applied to the projection `X_k ⟶ X`, which is a monomorphism as a base change
of one.

The finiteness statement is the argument of Stacks 03IJ run on the chart instead of on the
relation: the base change of the chart along `Spec k ⟶ Y` is represented by an object of the
site which is étale over `Spec k`, and quasi-compact because quasi-compactness of
`Spec k ⟶ Y` is tested against the quasi-compact algebraic space `h_V`; a quasi-compact
scheme étale over a one-point scheme is finite, and the fibre is the image of its points.

The topological half of Stacks 0AC8 is not proved here. It needs the comparison of condition
(1) and condition (4) of Stacks 03JV — a chart above `y` with *exactly one* point there,
obtained by shrinking a chart with finitely many — and that comparison is not available in
this repository; `AlgebraicGeometry.Space.finite_fibre_pointsMap_of_isQuasiCompact_fieldMorphism`
is the half of it which is, and it is what such a shrinking argument starts from.

## References

* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03IJ](https://stacks.math.columbia.edu/tag/03IJ)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 06RV](https://stacks.math.columbia.edu/tag/06RV)
* [Stacks Project, Tag 0AC8](https://stacks.math.columbia.edu/tag/0AC8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Every point of the presheaf represented by the field spectrum of a field-valued point is
carried by the presenting morphism to the point that field-valued point presents. -/
theorem pointsMap_fieldMorphism_eq_class (p : FieldValuedPoint B S hS Y)
    (z : points B S hS (yoneda.obj p.siteObject)) :
    pointsMap B S hS (yoneda.obj p.siteObject) (fieldMorphism B S hS Y p) z =
      p.class B S hS Y := by
  have hsub : Subsingleton (points B S hS (yoneda.obj p.siteObject)) :=
    subsingleton_points_yoneda_siteObject B S hS p
  rw [hsub.elim z ((p.tautologicalPoint B S hS Y).class B S hS (yoneda.obj p.siteObject)),
    pointsMap_fieldMorphism_tautologicalPoint]

/-- A point of `X` above the point presented by `p` lifts along the first projection of any
cartesian square over `Spec k ⟶ Y`. -/
private theorem exists_pointsMap_eq_of_isPullback_fieldMorphism
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {p : FieldValuedPoint B S hS Y} {fst : W ⟶ X}
    {snd : W ⟶ yoneda.obj p.siteObject}
    (sq : IsPullback fst snd f (fieldMorphism B S hS Y p)) (x : points B S hS X)
    (hx : pointsMap B S hS X f x = p.class B S hS Y) :
    ∃ w, pointsMap B S hS W fst w = x :=
  (exists_points_of_isPullback B S hS sq x
    ((p.tautologicalPoint B S hS Y).class B S hS (yoneda.obj p.siteObject))
    (by rwa [pointsMap_fieldMorphism_tautologicalPoint])).imp fun _ h ↦ h.1

/-- **Stacks 0AC8, the image of the fibre.** For a morphism `f : X ⟶ Y` of presheaves on the
big fppf site of `S` and a field-valued point `p` of `Y`, the map on points induced by the
projection `X ×_Y Spec k ⟶ X` has image exactly the fibre of `|f|` above the point presented
by `p`. -/
@[stacks 0AC8 "the image of the fibre"]
theorem range_pointsMap_fibre_fieldMorphism (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y) :
    Set.range (pointsMap B S hS (pullback f (fieldMorphism B S hS Y p))
        (pullback.fst f (fieldMorphism B S hS Y p))) =
      {x : points B S hS X | pointsMap B S hS X f x = p.class B S hS Y} := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    exact (pointsMap_apply_comm B S hS (pullback.condition (f := f)
      (g := fieldMorphism B S hS Y p)) w).trans (pointsMap_fieldMorphism_eq_class B S hS p _)
  · intro hx
    exact exists_pointsMap_eq_of_isPullback_fieldMorphism B S hS
      (IsPullback.of_hasPullback f (fieldMorphism B S hS Y p)) x hx

/-- **Stacks 0AC8, injectivity of the fibre.** When the morphism presenting a field-valued
point `p` of `Y` is a monomorphism, the map on points induced by the projection
`X ×_Y Spec k ⟶ X` is injective. -/
@[stacks 0AC8 "injectivity of the fibre"]
theorem injective_pointsMap_fibre_fieldMorphism (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y)
    (hp : Mono (fieldMorphism B S hS Y p)) :
    Function.Injective (pointsMap B S hS (pullback f (fieldMorphism B S hS Y p))
      (pullback.fst f (fieldMorphism B S hS Y p))) := by
  have : Mono (pullback.fst f (fieldMorphism B S hS Y p)) :=
    (IsPullback.of_hasPullback f (fieldMorphism B S hS Y p)).mono_fst_of_mono hp
  exact pointsMap_injective_of_mono B S hS _

/-- **An étale chart has a finite fibre above a quasi-compact field-valued point.** Let `p` be
a field-valued point of `Y` whose presenting morphism `Spec k ⟶ Y` is quasi-compact in the
sense of Stacks 03HE, and let `φ : h_V ⟶ Y` be an étale chart whose underlying scheme is
quasi-compact. Then the fibre of `|V| → |Y|` above the point presented by `p` is finite.

This is the argument of Stacks 03IJ applied to the chart: the base change of `φ` along
`Spec k ⟶ Y` is represented by an object of the site, étale over `Spec k` and quasi-compact,
hence with finitely many points, and the fibre is the image of those. -/
theorem finite_fibre_pointsMap_of_isQuasiCompact_fieldMorphism
    (p : FieldValuedPoint B S hS Y) (hp : IsQuasiCompact B S hS (fieldMorphism B S hS Y p))
    {V : BigFppfOver B S hS} (hV : CompactSpace ((BigFppfOver.toScheme B S hS).obj V))
    (φ : yoneda.obj V ⟶ Y)
    (hφ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ) :
    (pointsMap B S hS (yoneda.obj V) φ ⁻¹' {p.class B S hS Y}).Finite := by
  -- The base change of the chart along the field-valued point, as an object of the site.
  have sq := hφ.rep.isPullback (fieldMorphism B S hS Y p)
  have hetale : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map
      (hφ.rep.snd (fieldMorphism B S hS Y p))) := hφ.property_snd _
  have hsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj p.siteObject) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of p.carrier)))
  -- It is quasi-compact, because quasi-compactness of `Spec k ⟶ Y` is tested on `h_V`.
  have hqcs : IsQuasiCompactSpace B S hS (pullback φ (fieldMorphism B S hS Y p)) :=
    hp (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V)
      (isQuasiCompactSpace_yoneda_obj B S hS hV) _
  have hcpt : CompactSpace ((BigFppfOver.toScheme B S hS).obj
      (hφ.rep.pullback (fieldMorphism B S hS Y p))) :=
    compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS
      (hqcs.of_iso B S hS
        ((IsPullback.of_hasPullback φ (fieldMorphism B S hS Y p)).isoIsPullback _ _ sq))
  -- A quasi-compact scheme étale over a one-point scheme is finite.
  have hfin : Finite ((BigFppfOver.toScheme B S hS).obj
      (hφ.rep.pullback (fieldMorphism B S hS Y p))) :=
    finite_of_etale_of_subsingleton ((BigFppfOver.toScheme B S hS).map
      (hφ.rep.snd (fieldMorphism B S hS Y p)))
  have hpts : Finite (points B S hS
      (yoneda.obj (hφ.rep.pullback (fieldMorphism B S hS Y p)))) :=
    Finite.of_equiv _ (pointsEquivScheme B S hS _).symm
  refine Set.Finite.subset (Set.finite_range (pointsMap B S hS _
    (hφ.rep.fst (fieldMorphism B S hS Y p)))) ?_
  intro v hv
  exact exists_pointsMap_eq_of_isPullback_fieldMorphism B S hS sq v hv

/-- **A decent algebraic space satisfies condition `(α)` of Stacks 03JX.** Every étale chart
of a decent algebraic space by an affine scheme has a finite fibre above every point.

Decency is `AlgebraicGeometry.Space.IsDecentSpace`, condition (4) of Stacks 03JV, so this is
the implication from that condition to condition (2) of Stacks 03JS; the equivalences of
Stacks 03JV and 03JS themselves are not available in this repository. -/
theorem hasFiniteChartFibersAtEveryPoint_of_isDecentSpace (hY : IsDecentSpace B S hS Y) :
    HasFiniteChartFibersAtEveryPoint B S hS Y := by
  intro x V hV φ hφ
  obtain ⟨p, hpx, -, hpqc⟩ := hY x
  have hcpt : CompactSpace ((BigFppfOver.toScheme B S hS).obj V) := by
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj V) := hV
    infer_instance
  have := finite_fibre_pointsMap_of_isQuasiCompact_fieldMorphism B S hS p hpqc hcpt φ hφ
  rwa [hpx] at this

end AlgebraicGeometry.Space

end

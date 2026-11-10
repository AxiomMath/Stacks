module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ClosedPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresCardinality
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionZeroOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.JacobsonClosedPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback

/-!
# Finite type points of a decent Jacobson algebraic space

Let `X` be a decent Jacobson algebraic space over a scheme `S`. The set `X_{ft-pts}` of finite
type points of `X` is then exactly the set of closed points of `|X|`. This is **Stacks 0BA5**,
the algebraic-space counterpart of the equivalence of conditions (1) and (2) of Stacks 01TB
for schemes.

## Main results

* `AlgebraicGeometry.Space.isFiniteTypePoint_iff_isClosed_singleton`: a point of a decent
  Jacobson algebraic space is a finite type point exactly when it is a closed point of `|X|`.
* `AlgebraicGeometry.Space.finiteTypePoints_eq_setOf_isClosed_singleton`: the same statement
  as the equality of the two subsets of `|X|`.
* `AlgebraicGeometry.Space.isClosed_singleton_of_isFiniteTypePoint_pointsMap`: above a finite
  type point of a Jacobson algebraic space, *every* point of an étale chart by a Jacobson
  scheme is closed.

## Implementation notes

The source statement is an equality of two subsets of `|X|`, and that is the form of
`AlgebraicGeometry.Space.finiteTypePoints_eq_setOf_isClosed_singleton`; it matches the
scheme-level `AlgebraicGeometry.jacobsonSpace_finiteTypePoints_tfae`, whose condition (2) is
written the same way. The pointwise `Iff` is stated as well, because the inclusions are proved
at a point and the two forms are interchangeable by `Set.ext`.

The Jacobson condition on `X` is written out as the existence of a surjective étale atlas by a
Jacobson scheme, which is the source's definition and the form that
`AlgebraicGeometry.Space.exists_jacobson_atlas_of_isLocallyOfFiniteType` — Stacks 0BA3 — and
`AlgebraicGeometry.Space.exists_isClosed_pointsToScheme_of_isFiniteTypePoint` —
Stacks 0BA4 — consume. The same atlas serves both inclusions. Decency is
`AlgebraicGeometry.Space.IsDecentSpace`, condition (4) of Stacks 03JV, and it enters only
through condition `(α)` of Stacks 03JX, by
`AlgebraicGeometry.Space.hasFiniteChartFibersAtEveryPoint_of_isDecentSpace`.

That a closed point of `|X|` is a finite type point is read off any surjective étale chart: a
specialization of a point of the chart above a closed point of `|X|` again lies above that
point, so Stacks 03K5 identifies the two, the chart point is closed and Stacks 06EF applies.

For the converse the quasi-compact monomorphic representative of the source proof is replaced
by the chart fibre statement
`AlgebraicGeometry.Space.isClosed_singleton_of_isFiniteTypePoint_pointsMap`, whose proof is the
source's: a finite type point is represented by a morphism `Spec k ⟶ X` locally of finite type,
the base change of the chart along it is a scheme étale over `Spec k` and therefore discrete,
every point of the chart above the given point is the image of a point of that base change, and
the base change is locally of finite type over the chart, so those images are closed because the
chart is Jacobson. Discreteness replaces the source's description of an étale scheme over a
field as a disjoint union of spectra of fields: étale morphisms are locally quasi-finite
(Stacks 03II) and local quasi-finiteness over a one-point base is discreteness of the source.
A specialization in `|X|` of the finite type point then lifts to the chart by Stacks 03K2 and
lands on a closed point, so it is trivial.

The passage between a point of a chart and the corresponding point of the representing scheme is
clause (1) of Stacks 03BX, in the form
`AlgebraicGeometry.Space.isClosed_singleton_iff_isClosed_singleton_pointsToScheme`.

## References

* [Stacks Project, Tag 01TB](https://stacks.math.columbia.edu/tag/01TB)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03II](https://stacks.math.columbia.edu/tag/03II)
* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 03K2](https://stacks.math.columbia.edu/tag/03K2)
* [Stacks Project, Tag 03K5](https://stacks.math.columbia.edu/tag/03K5)
* [Stacks Project, Tag 06EF](https://stacks.math.columbia.edu/tag/06EF)
* [Stacks Project, Tag 06EG](https://stacks.math.columbia.edu/tag/06EG)
* [Stacks Project, Tag 0BA3](https://stacks.math.columbia.edu/tag/0BA3)
* [Stacks Project, Tag 0BA4](https://stacks.math.columbia.edu/tag/0BA4)
* [Stacks Project, Tag 0BA5](https://stacks.math.columbia.edu/tag/0BA5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Let `X` be an algebraic space over `S` and let `φ : h_U ⟶ X` be an étale chart of `X` by a
Jacobson scheme. Every point of the chart above a finite type point of `X` is a closed point of
the chart. -/
theorem isClosed_singleton_of_isFiniteTypePoint_pointsMap
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {U : BigFppfOver B S hS} {φ : yoneda.obj U ⟶ X}
    (hφetale : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ)
    (hUJac : JacobsonSpace ((BigFppfOver.toScheme B S hS).obj U))
    {x : points B S hS X} (hx : IsFiniteTypePoint B S hS X x)
    (u : points B S hS (yoneda.obj U))
    (hu : pointsMap B S hS (yoneda.obj U) φ u = x) :
    IsClosed ({u} : Set (points B S hS (yoneda.obj U))) := by
  obtain ⟨p, hpx, hplft⟩ := hx
  set A : BigFppfOver B S hS := p.siteObject B S hS X with hA
  set η : yoneda.obj A ⟶ X := yonedaEquiv.symm p.value with hη
  -- The base change of the chart along the locally finite type representative of `x`.
  have hrep : yoneda.relativelyRepresentable η :=
    (Functor.relativelyRepresentable.diag_iff (F := yoneda) (X := X)).mp
      hX.diagonal_representable η
  obtain ⟨R, r, s, hsq⟩ : ∃ (R : BigFppfOver B S hS) (r : R ⟶ A) (s : R ⟶ U),
      IsPullback (yoneda.map r) (yoneda.map s) η φ := by
    refine ⟨hrep.pullback φ, yoneda.preimage (hrep.fst φ), hrep.snd φ, ?_⟩
    rw [yoneda.map_preimage]
    exact hrep.isPullback φ
  have hrEtale : Etale ((BigFppfOver.toScheme B S hS).map r) :=
    hφetale.property η (yoneda.map s) r hsq.flip
  have hsLft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map s) :=
    hplft R U (yoneda.map r) φ s
      ((presheaf_yoneda_map_etale_iff B S hS r).2 hrEtale) hφetale hsq.w.symm
  -- The base change is étale over the spectrum of a field, hence discrete.
  have _ : Subsingleton ((BigFppfOver.toScheme B S hS).obj A) := by
    change Subsingleton (Spec (CommRingCat.of p.carrier)); infer_instance
  have _ : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map r) :=
    (locallyQuasiFinite_of_etale ((BigFppfOver.toScheme B S hS).map r)).1
  have _ : DiscreteTopology ((BigFppfOver.toScheme B S hS).obj R) :=
    (locallyQuasiFinite_iff_discreteTopology_of_subsingleton
      ((BigFppfOver.toScheme B S hS).map r)).mp
      (locallyQuasiFinite_of_etale ((BigFppfOver.toScheme B S hS).map r)).2
  -- The given point of the chart is the image of a point of the base change.
  obtain ⟨z₀, -⟩ := surjective_pointsToScheme B S hS A (IsLocalRing.closedPoint p.carrier)
  obtain ⟨w, -, hwu⟩ := exists_point_of_isPullback_presheaf B S hS hsq z₀ u
    ((FieldValuedPoint.pointsMap_eq_class B S hS p z₀).trans (hpx.trans hu.symm))
  -- A closed point of the base change has closed image in the Jacobson chart.
  rw [isClosed_singleton_iff_isClosed_singleton_pointsToScheme, ← hwu,
    pointsToScheme_pointsMap]
  exact ((BigFppfOver.toScheme B S hS).map s).closedPoints_subset_preimage_closedPoints
    (isClosed_discrete _)

/-- **Stacks 0BA5**, pointwise. Let `X` be a decent Jacobson algebraic space over `S`, the
Jacobson condition being written as the existence of a surjective étale atlas by a Jacobson
scheme. A point of `X` is a finite type point exactly when it is a closed point of `|X|`. -/
@[stacks 0BA5 "pointwise form"]
theorem isFiniteTypePoint_iff_isClosed_singleton
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X)
    (hJac : ∃ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) a ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      JacobsonSpace ((BigFppfOver.toScheme B S hS).obj U))
    (x : points B S hS X) :
    IsFiniteTypePoint B S hS X x ↔ IsClosed ({x} : Set (points B S hS X)) := by
  obtain ⟨U, φ, hφsurj, hφetale, hUJac⟩ := hJac
  have hα : HasFiniteChartFibersAtEveryPoint B S hS X :=
    hasFiniteChartFibersAtEveryPoint_of_isDecentSpace B S hS hdec
  have hφEtale : IsEtale B S hS φ := (isEtale_iff_presheaf_of_yoneda B S hS φ).2 hφetale
  have hsurj : Function.Surjective (pointsMap B S hS (yoneda.obj U) φ) :=
    (surjective_iff_surjective_pointsMap B S hS X hX U φ).1 hφsurj
  constructor
  · -- A finite type point is closed: a specialization of it lifts to a closed chart point.
    intro hx
    refine isClosed_of_closure_subset fun y hy ↦ ?_
    obtain ⟨w, hwy⟩ := hsurj y
    obtain ⟨u, huw, hux⟩ := exists_specializes_pointsMap_eq_of_isEtale B S hS hX
      (specializes_iff_mem_closure.2 hy) (hα x) U φ hφetale w hwy
    have huclosed : IsClosed ({u} : Set (points B S hS (yoneda.obj U))) :=
      isClosed_singleton_of_isFiniteTypePoint_pointsMap B S hS hX hφetale hUJac hx u hux
    have hweq : w = u := huw.mem_closed huclosed rfl
    rw [Set.mem_singleton_iff, ← hwy, hweq, hux]
  · -- A closed point has closed points above it in the chart, so it is of finite type.
    intro hx
    obtain ⟨u, hux⟩ := hsurj x
    have huclosed : IsClosed ({u} : Set (points B S hS (yoneda.obj U))) := by
      refine isClosed_of_closure_subset fun v hv ↦ ?_
      have hspec : u ⤳ v := specializes_iff_mem_closure.2 hv
      have hvx : pointsMap B S hS (yoneda.obj U) φ v = x :=
        (hspec.map (continuous_pointsMap B S hS φ)).mem_closed hx hux
      rw [Set.mem_singleton_iff]
      exact eq_of_specializes_of_pointsMap_eq_of_hasFiniteChartFibers B S hS hX hα U φ hφetale
        v u (by rw [hvx, hux]) hspec
    refine (isFiniteTypePoint_iff_exists_isClosed_etaleChart B S hS X hX x).2
      ⟨U, φ, schemePointRepresentative B S hS U (pointsToScheme B S hS U u), hφEtale,
        ?_, ?_⟩
    · rw [schemePointRepresentative_point B S hS U (pointsToScheme B S hS U u)]
      exact (isClosed_singleton_iff_isClosed_singleton_pointsToScheme B S hS U u).1 huclosed
    · rwa [class_schemePointRepresentative_pointsToScheme B S hS U u]

/-- **Stacks 0BA5.** Let `X` be a decent Jacobson algebraic space over `S`, the Jacobson
condition being written as the existence of a surjective étale atlas by a Jacobson scheme.
Then `X_{ft-pts} ⊂ |X|` is the set of closed points. -/
@[stacks 0BA5]
theorem finiteTypePoints_eq_setOf_isClosed_singleton
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X)
    (hJac : ∃ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) a ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a ∧
      JacobsonSpace ((BigFppfOver.toScheme B S hS).obj U)) :
    finiteTypePoints B S hS X = {x | IsClosed ({x} : Set (points B S hS X))} :=
  Set.ext fun x ↦ isFiniteTypePoint_iff_isClosed_singleton B S hS hX hdec hJac x

end AlgebraicGeometry.Space

end

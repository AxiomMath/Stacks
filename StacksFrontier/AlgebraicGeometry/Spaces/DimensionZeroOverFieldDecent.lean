module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionZeroOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointsFiniteFibres

/-!
# A decent algebraic space with finitely many points over a one-point base

Stacks 0ACA compares five conditions on an algebraic space `X` locally of finite type over a
field `k`: that `|X|` is finite, that `|X|` is discrete, that `dim(|X|) = 0`, that `dim(X) = 0`,
and that `X ⟶ Spec(k)` is locally quasi-finite. The source asserts the last four to be
equivalent, and that the first implies them **when `X` is decent**.
`StacksFrontier/AlgebraicGeometry/Spaces/DimensionZeroOverField.lean` proves the implications among
the last four which the available library supports and leaves condition (1) untreated. This file
adds the arrow out of condition (1): a decent algebraic space locally of finite type over a
one-point base whose point set is finite has discrete point set.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.discreteTopology_of_finite_of_locallyOfFiniteType`: a scheme with finitely
  many points which is locally of finite type over a scheme with at most one point is discrete.
* `AlgebraicGeometry.Space.discreteTopology_points_of_finite_of_isDecentSpace` is Stacks 0ACA,
  condition (1) implies condition (2) for a decent algebraic space.

## Implementation notes

The scheme-level statement is the "Jacobson-type" input the space-level one needs, and Mathlib
supplies both halves of it. A scheme with at most one point is `T1Space`, hence a
`JacobsonSpace`; `AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace` propagates that to the
source of a morphism locally of finite type; and a finite Jacobson space is discrete, which is
Mathlib's `JacobsonSpace.discreteTopology` read for `Set.toFinite`. Concretely: a finite type
algebra over a field with finitely many primes has dimension zero, because a Jacobson domain
with finitely many maximal ideals is a field.

Decency enters only to make one *affine* étale chart finite. For a point `x` of `|X|` the chart
is `AlgebraicGeometry.Space.exists_affine_etale_chart_at_point`; each point `y` of `|X|` has a
quasi-compact monomorphic field-valued representative, whose fibre in that chart is finite by
Tag 03JV (`AlgebraicGeometry.Space.finite_setFibre_of_isQuasiCompact_fieldMorphism`, which uses
only the quasi-compactness); and `|X|` being finite, the chart is the union of finitely many such
fibres. Only quasi-compactness of the representative is used, so the hypothesis could be weakened
to that; it is left as decency because that is the source's hypothesis.

The hypothesis on the base is `Subsingleton` of its underlying scheme rather than that it is the
spectrum of a field, matching
`AlgebraicGeometry.Space.isLocallyQuasiFinite_iff_dimension_le_zero`; the two one-point
reductions this file shares with that one are stated there.

**What is not proved.** The implications from condition (2) or (3) back to condition (4) or (5)
are not here. Without a decency hypothesis they need the transcendence-degree input recorded in
the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/DimensionZeroOverField.lean`. With one they are within
reach of the argument above — the preimage of an isolated point of `|X|` in a chart is open and,
by Tag 03JV, finite, and an open subspace of a Jacobson space is Jacobson — but that is not
carried out here. Condition (1) is treated only in the direction the source states it, and only
for a decent space: a finite point set says nothing about the topology of a chart without the
finiteness of the chart fibres.

## References

* [Stacks Project, Tag 03I8](https://stacks.math.columbia.edu/tag/03I8)
* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
* [Stacks Project, Tag 0ACA](https://stacks.math.columbia.edu/tag/0ACA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A finite scheme locally of finite type over a one-point base is discrete.** If the target
of a morphism of schemes locally of finite type has at most one point and the source has
finitely many points, then the source is a discrete topological space.

The target is `T1Space`, hence a `JacobsonSpace`, so the source is a Jacobson space by
`AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace`, and a finite Jacobson space is discrete.
This is the ring-theoretic fact that a finite type algebra over a field with finitely many primes
has dimension zero. -/
theorem discreteTopology_of_finite_of_locallyOfFiniteType {U V : Scheme.{u}} (h : U ⟶ V)
    [Subsingleton V] [LocallyOfFiniteType h] [Finite U] : DiscreteTopology U :=
  have : JacobsonSpace (U : Type u) := LocallyOfFiniteType.jacobsonSpace h
  inferInstance

namespace Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {k : BigFppfOver B S hS}

/-- **Stacks 0ACA, condition (1) implies condition (2) for a decent space.** Let `X` be a
decent algebraic space over `S`, locally of finite type over a representable base whose
underlying scheme has at most one point. If the point set of `X` is finite, then it is discrete.

An affine étale chart through a given point of `|X|` has finite fibre above every point of `|X|`,
by Tag 03JV applied to the quasi-compact monomorphic field-valued representative that decency
supplies there; so the chart has finitely many points, and being locally of finite type over a
one-point base it is discrete. The chart is open on points, so the given point is isolated. -/
@[stacks 0ACA "decent clause of the corrected statement: (1) => (2)"]
theorem discreteTopology_points_of_finite_of_isDecentSpace
    (hX : IsAlgebraicSpace B S hS X)
    (hk : Subsingleton ((BigFppfOver.toScheme B S hS).obj k)) (g : X ⟶ yoneda.obj k)
    (hg : IsLocallyOfFiniteType B S hS g) (hdec : IsDecentSpace B S hS X)
    (hfin : Finite (points B S hS X)) :
    DiscreteTopology (points B S hS X) := by
  classical
  rw [discreteTopology_iff_isOpen_singleton]
  intro x
  obtain ⟨W, b, hWaff, hb, w, hwx⟩ := exists_affine_etale_chart_at_point B S hS X hX x
  have hWcpt : CompactSpace ((BigFppfOver.toScheme B S hS).obj W) :=
    have := hWaff
    inferInstance
  have hbet : IsEtale B S hS b := isEtale_of_presheaf_etale B S hS hb
  -- The chart is covered by the finitely many fibres above the finitely many points of `|X|`.
  have hWfin : Finite (points B S hS (yoneda.obj W)) := by
    have hcov : (Set.univ : Set (points B S hS (yoneda.obj W))) ⊆
        ⋃ y : points B S hS X, setFibre B S hS b (hdec y).choose := by
      intro z _
      refine Set.mem_iUnion.2 ⟨pointsMap B S hS (yoneda.obj W) b z, ?_⟩
      exact ((hdec (pointsMap B S hS (yoneda.obj W) b z)).choose_spec.1).symm
    have hfin' : (Set.univ : Set (points B S hS (yoneda.obj W))).Finite :=
      Set.Finite.subset (Set.finite_iUnion fun y ↦
        finite_setFibre_of_isQuasiCompact_fieldMorphism B S hS (hdec y).choose
          (hdec y).choose_spec.2.2 hWcpt hbet) hcov
    exact Set.finite_univ_iff.mp hfin'
  have hWfin' : Finite ((BigFppfOver.toScheme B S hS).obj W) :=
    Finite.of_equiv _ (pointsEquivScheme B S hS W)
  -- The chart is locally of finite type over the base, read on the chart square over `𝟙`.
  have := isMultiplicative_presheaf_etale B S hS
  have hid : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (𝟙 (yoneda.obj k)) :=
    MorphismProperty.id_mem _ _
  have hcomm : yoneda.map (yoneda.preimage (b ≫ g)) ≫ 𝟙 (yoneda.obj k) = b ≫ g := by
    rw [Category.comp_id, yoneda.map_preimage]
  have hft := hg W k b (𝟙 (yoneda.obj k)) (yoneda.preimage (b ≫ g)) hb hid hcomm
  have hdisc : DiscreteTopology ((BigFppfOver.toScheme B S hS).obj W) :=
    have := hk
    have := hft
    discreteTopology_of_finite_of_locallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (b ≫ g)))
  -- The chart is open on points, so the image of an isolated point is isolated.
  have hwopen : @IsOpen _ (pointTopology B S hS (yoneda.obj W)) {w} := by
    rw [isOpen_pointTopology_yoneda_iff_isOpen_image]
    exact Set.image_singleton ▸ isOpen_discrete _
  have hop := isOpenMap_pointsMap_of_presheafEtale B S hS b hb {w} hwopen
  rwa [Set.image_singleton, hwx] at hop

end Space

end AlgebraicGeometry

end

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.LocalRingDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedLocalRings
import StacksFrontier.RingTheory.Henselian.PermanenceOfProperties

/-!
# The local ring at a point and the stalks at the geometric points above it

The local ring of an algebraic space `F` at a point `x` of `|F|` is computed on an étale
scheme chart at a point above `x`, while the stalk of the structure sheaf at a geometric
point `xbar` of `F` is the strict henselization of such a local ring. A property of local
rings that is insensitive to strict henselization therefore holds at `x` exactly when it
holds at one, equivalently at every, geometric point above `x`. This file does that for the
Krull dimension and for reducedness.

## Main results

* `AlgebraicGeometry.Space.ringKrullDim_etaleLocalRing_eq_localRingDimension`: the Krull
  dimension of the stalk at a geometric point is the dimension of the local ring of the
  space at the image of that geometric point.
* `AlgebraicGeometry.Space.isReduced_etaleLocalRing_iff_hasLocalRingPropertyAtPoint`: the
  stalk at a geometric point is reduced exactly when the local ring of the space at the
  image of that geometric point is reduced.
* `AlgebraicGeometry.Space.localRingDimension_eq_tfae`: the dimension of the local ring at a
  point is `d` exactly when the stalk at some, equivalently at every, geometric point above
  it has Krull dimension `d`.
* `AlgebraicGeometry.Space.isReduced_localRing_tfae`: the local ring at a point is reduced
  exactly when the stalk at some, equivalently at every, geometric point above it is
  reduced.

## Implementation notes

The link between the two sides is Stacks 04KF in the form
`AlgebraicGeometry.Space.strictHenselizationEquivEtaleLocalRing`: for a small étale
neighbourhood `V` of a geometric point, the stalk at that geometric point is the strict
henselization of the local ring of the chart scheme at the point the lift selects. That point
is the one `AlgebraicGeometry.Space.schemePoint` attaches to
`AlgebraicGeometry.Space.chartFieldValuedPoint V`, a field-valued point of the chart
whose class lies over the image of the geometric point; so the chart conditions of
Stacks 04NA and Stacks 0BBL may be read at it. The ring-theoretic inputs are then that a
local ring and its strict henselization have the same Krull dimension (Stacks 06LK) and are
reduced together (Stacks 06DH).

Chart independence is already built into the two definitions on the point side:
`AlgebraicGeometry.Space.localRingDimension_eq_of_chartPoint` evaluates the dimension on an
arbitrary chart, and for reducedness the one-chart condition of
`AlgebraicGeometry.Space.HasLocalRingPropertyAtPoint` is turned into the every-chart
condition by the étale-chart equivalence of Stacks 04N2. Independence of the geometric point
is not assumed: each of the three conditions is shown equivalent to the one about the point
of `|F|`, and a geometric point above a given point exists by
`AlgebraicGeometry.Space.exists_geometricRepresentative`.

## References

* [Stacks Project, Tag 04N9](https://stacks.math.columbia.edu/tag/04N9)
* [Stacks Project, Tag 0E01](https://stacks.math.columbia.edu/tag/0E01)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The chart point underlying `AlgebraicGeometry.Space.chartFieldValuedPoint` is the
point at which Stacks 04KF compares the stalk at the geometric point with a strict
henselization. -/
theorem schemePoint_chartFieldValuedPoint {x : GeometricPoint B S hS F}
    (V : SmallEtaleNeighborhood x) :
    schemePoint B S hS V.chart.obj.left (chartFieldValuedPoint V) =
      (chartGeometricPoint V).hom
        (closedPoint (chartGeometricPoint V).residueField) :=
  rfl

/-- Reducedness is invariant under ring isomorphism. -/
private theorem isReduced_iff_of_ringEquiv {R R' : Type*} [CommRing R] [CommRing R']
    (e : R ≃+* R') : _root_.IsReduced R ↔ _root_.IsReduced R' :=
  ⟨fun _ ↦ isReduced_of_injective e.symm e.symm.injective,
    fun _ ↦ isReduced_of_injective e e.injective⟩

/-- An étale scheme chart at a point above the image of a geometric point on which both the
Krull dimension and reducedness of the stalk at that geometric point can be read: by
Stacks 04KF the stalk is the strict henselization of the local ring of the chart there, and
a strict henselization has the same Krull dimension (Stacks 06LK) and is reduced together
with the ring it henselizes (Stacks 06DH). -/
private theorem exists_chart_comparison (hF : IsAlgebraicSpace B S hS F)
    (x : GeometricPoint B S hS F) :
    ∃ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) a ∧
      ∃ p : FieldValuedPoint B S hS (yoneda.obj U),
        pointsMap B S hS (yoneda.obj U) a (p.class B S hS (yoneda.obj U)) = x.image ∧
        ringKrullDim (((BigFppfOver.toScheme B S hS).obj U).presheaf.stalk
            (schemePoint B S hS U p)) =
          ringKrullDim (etaleLocalRing B S hS F x) ∧
        (_root_.IsReduced (((BigFppfOver.toScheme B S hS).obj U).presheaf.stalk
            (schemePoint B S hS U p)) ↔
          _root_.IsReduced (etaleLocalRing B S hS F x)) := by
  obtain ⟨U₀, f, hSurj, hEtale⟩ := hF.exists_atlas
  obtain ⟨⟨V, -⟩⟩ := exists_pointed_smallEtaleNeighborhood B S hS F hF x f hSurj hEtale
  have hV : (bigEtaleSiteOfFppfSite B).Contains (chartScheme V.chart) :=
    V.chart.obj.left.left.property
  let R := (neighborhoodChartScheme V).presheaf.stalk
    ((chartGeometricPoint V).hom (closedPoint (chartGeometricPoint V).residueField))
  let κ := separableClosure (ResidueField R) (chartGeometricPoint V).residueField
  let T := henselizationTower R κ
  let e : T.strictHenselization ≃+* etaleLocalRing B S hS F x :=
    strictHenselizationEquivEtaleLocalRing hF V (bigEtaleSiteOfFppfSite B) hV T
  refine ⟨V.chart.obj.left, V.chart.obj.hom, V.chart.property,
    chartFieldValuedPoint V, chartFieldValuedPoint_pointsMap V, ?_, ?_⟩
  · rw [schemePoint_chartFieldValuedPoint]
    exact ((ringKrullDim_eq_henselization_eq_strictHenselization R T.henselization
      T.strictHenselization κ).1.trans
      (ringKrullDim_eq_henselization_eq_strictHenselization R T.henselization
        T.strictHenselization κ).2).trans (ringKrullDim_eq_of_ringEquiv e)
  · rw [schemePoint_chartFieldValuedPoint]
    refine ((isReduced_tfae_henselization_strictHenselization R T.henselization
      T.strictHenselization κ).out 1 3).trans (isReduced_iff_of_ringEquiv e)

/-- **Stacks 04N9, the comparison step.** The Krull dimension of the stalk of an algebraic
space at a geometric point is the dimension of the local ring of the space at the image of
that geometric point. -/
theorem ringKrullDim_etaleLocalRing_eq_localRingDimension
    (hF : IsAlgebraicSpace B S hS F) (x : GeometricPoint B S hS F) :
    ringKrullDim (etaleLocalRing B S hS F x) =
      (localRingDimension B S hS x.image : WithBot ℕ∞) := by
  obtain ⟨U, a, ha, p, hp, hdim, -⟩ := exists_chart_comparison hF x
  rw [← hdim]
  exact (localRingDimension_eq_of_chartPoint B S hS hF U a ha (schemePoint B S hS U p)
    x.image ⟨p, rfl, hp⟩).symm

/-- **Stacks 0E01, the comparison step.** The stalk of an algebraic space at a geometric
point is reduced exactly when the local ring of the space at the image of that geometric
point is reduced. -/
theorem isReduced_etaleLocalRing_iff_hasLocalRingPropertyAtPoint
    (hF : IsAlgebraicSpace B S hS F) (x : GeometricPoint B S hS F) :
    _root_.IsReduced (etaleLocalRing B S hS F x) ↔
      HasLocalRingPropertyAtPoint B S hS F hF x.image
        (fun (R : Type u) ↦ fun [CommRing R] ↦ _root_.IsReduced R)
        isReduced_localization_etale_invariant := by
  have hQEtale : GermOfScheme.IsEtaleLocal
      (fun g : GermOfScheme.{u} ↦ _root_.IsReduced (g.scheme.presheaf.stalk g.point)) := by
    refine GermOfScheme.isEtaleLocal_stalk_property
      (P := fun (R : Type u) ↦ fun [CommRing R] ↦ _root_.IsReduced R)
      isReduced_localization_etale_invariant ?_
    intro R R' _ _ _ _ eR
    exact isReduced_iff_of_ringEquiv eR
  obtain ⟨U, a, ha, p, hp, -, hred⟩ := exists_chart_comparison hF x
  refine ⟨fun h ↦ ⟨U, a, ha, p, hp, hred.mpr h⟩, fun h ↦ hred.mp ?_⟩
  exact (forall_etale_chart_iff_exists_etale_chart B S hS F hF x.image _ hQEtale).2 h U a ha p hp

/-- **Stacks 04N9.** For a point `x` of an algebraic space and `d` in `ℕ∞`, the dimension of
the local ring of the space at `x` is `d` exactly when the stalk at some geometric point
above `x` has Krull dimension `d`, and exactly when the stalk at every geometric point above
`x` does. -/
@[stacks 04N9]
theorem localRingDimension_eq_tfae (hF : IsAlgebraicSpace B S hS F)
    (x : points B S hS F) (d : ℕ∞) :
    List.TFAE
      [localRingDimension B S hS x = d,
        ∃ xbar : GeometricPoint B S hS F, xbar.LiesOver x ∧
          ringKrullDim (etaleLocalRing B S hS F xbar) = (d : WithBot ℕ∞),
        ∀ xbar : GeometricPoint B S hS F, xbar.LiesOver x →
          ringKrullDim (etaleLocalRing B S hS F xbar) = (d : WithBot ℕ∞)] := by
  tfae_have 1 → 3 := by
    rintro h xbar rfl
    rw [ringKrullDim_etaleLocalRing_eq_localRingDimension hF xbar, h]
  tfae_have 3 → 2 := by
    intro h
    obtain ⟨xbar, hxbar⟩ := exists_geometricRepresentative B S hS F x
    exact ⟨xbar, hxbar, h xbar hxbar⟩
  tfae_have 2 → 1 := by
    rintro ⟨xbar, rfl, h⟩
    rw [ringKrullDim_etaleLocalRing_eq_localRingDimension hF xbar] at h
    exact WithBot.coe_injective h
  tfae_finish

/-- **Stacks 0E01.** For a point `x` of an algebraic space, the local ring of the space at
`x` is reduced exactly when the stalk at some geometric point above `x` is reduced, and
exactly when the stalk at every geometric point above `x` is reduced. -/
@[stacks 0E01]
theorem isReduced_localRing_tfae (hF : IsAlgebraicSpace B S hS F) (x : points B S hS F) :
    List.TFAE
      [HasLocalRingPropertyAtPoint B S hS F hF x
          (fun (R : Type u) ↦ fun [CommRing R] ↦ _root_.IsReduced R)
          isReduced_localization_etale_invariant,
        ∃ xbar : GeometricPoint B S hS F, xbar.LiesOver x ∧
          _root_.IsReduced (etaleLocalRing B S hS F xbar),
        ∀ xbar : GeometricPoint B S hS F, xbar.LiesOver x →
          _root_.IsReduced (etaleLocalRing B S hS F xbar)] := by
  tfae_have 1 → 3 := by
    rintro h xbar rfl
    exact (isReduced_etaleLocalRing_iff_hasLocalRingPropertyAtPoint hF xbar).mpr h
  tfae_have 3 → 2 := by
    intro h
    obtain ⟨xbar, hxbar⟩ := exists_geometricRepresentative B S hS F x
    exact ⟨xbar, hxbar, h xbar hxbar⟩
  tfae_have 2 → 1 := by
    rintro ⟨xbar, rfl, h⟩
    exact (isReduced_etaleLocalRing_iff_hasLocalRingPropertyAtPoint hF xbar).mp h
  tfae_finish

end AlgebraicGeometry.Space

end

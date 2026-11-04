module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleStalkDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Dimension

/-!
# The dimension of the local ring of an algebraic space at a point

Let `x` be a point of an algebraic space `F` over `S`. Measuring the Krull dimension of the
local ring of an étale scheme chart of `F` at a point above `x` gives an answer that does not
depend on the chart nor on the chosen point above `x`, and for a scheme it is the dimension
of the scheme's own local ring. That common value is the dimension of the local ring of `F`
at `x`.

## Main definitions

* `AlgebraicGeometry.Space.ChartPoint`: a point of a scheme chart lies over a point of the
  presheaf when some field-valued representative of it maps to that point.
* `AlgebraicGeometry.Space.HasChartLocalRingDimension` and
  `AlgebraicGeometry.Space.AllChartsLocalRingDimension`: the one-chart and every-chart
  conditions on the dimension of the local ring.
* `AlgebraicGeometry.Space.localRingDimension`: the dimension of the local ring of an
  algebraic space at a point.

## Main results

* `AlgebraicGeometry.GermOfScheme.isEtaleLocal_ringKrullDim_stalk_eq`: having a local ring of
  a prescribed Krull dimension is an étale-local property of germs of schemes.
* `AlgebraicGeometry.Space.chartPoint_pointsToScheme`: the scheme point underlying a point
  of a represented presheaf lies over its image along any chart.
* `AlgebraicGeometry.Space.hasChartLocalRingDimension_iff_allChartsLocalRingDimension`: the
  one-chart and every-chart conditions agree, so the measured dimension is independent of
  the chart.
* `AlgebraicGeometry.Space.hasChartLocalRingDimension_iff_ringKrullDim_stalk`: for a
  represented algebraic space the condition is the dimension of the representing scheme's
  local ring.
* `AlgebraicGeometry.Space.localRingDimension_eq_iff_hasChartLocalRingDimension`: the
  dimension of the local ring at a point is characterized by the existence of an étale chart
  realizing it.
* `AlgebraicGeometry.Space.localRingDimension_eq_of_chartPoint`: consequently it is the Krull
  dimension of the local ring of any étale scheme chart at any point above it.

## Implementation notes

Points of the algebraic space are classes of field-valued points (Tag 03BU), and the point
of a chart `U` selected by a field-valued point of `yoneda.obj U` is
`AlgebraicGeometry.Space.schemePoint`. `ChartPoint` records that a scheme point of `U` arises
this way from a field-valued point whose class maps to `x`.

Chart independence is the étale-chart equivalence of Tag 04N2 applied to the property of
germs "the local ring has Krull dimension `d`", which is étale local because an étale
morphism of schemes preserves the dimension of local rings (Tag 04N8).

`localRingDimension` is the infimum of the values realized by some étale chart. The
characterization `localRingDimension_eq_iff_hasChartLocalRingDimension` shows that for an
algebraic space this set is a singleton, so the infimum is the common chart value; clients
should use the characterization rather than unfolding the infimum. In particular a
codimension-zero condition at `x` is the equation `localRingDimension B S hS x = 0`.

The dimension measured here is the Krull dimension of a local ring, so it takes values in
`ℕ∞`; it is not the local dimension of the underlying topological space, which is
`AlgebraicGeometry.Space.dimensionAtPoint` and takes values in `WithBot ℕ∞`.

## References

* [Stacks Project, Tag 04NA](https://stacks.math.columbia.edu/tag/04NA)
* [Stacks Project, Tag 0BAM](https://stacks.math.columbia.edu/tag/0BAM)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Having a local ring of Krull dimension `d` is an étale-local property of germs of
schemes: an étale morphism of schemes preserves the dimension of the local rings at
corresponding points, which is Tag 04N8. -/
theorem GermOfScheme.isEtaleLocal_ringKrullDim_stalk_eq (d : WithBot ℕ∞) :
    GermOfScheme.IsEtaleLocal fun X : GermOfScheme.{u} ↦
      ringKrullDim (X.scheme.presheaf.stalk X.point) = d := by
  intro X Y f hf
  obtain ⟨g, -, hg⟩ := hf
  have : Etale g.hom := hg
  have : Etale (Scheme.Opens.ι g.source) := inferInstance
  have h := (ringKrullDim_stalk_eq_of_etale (Scheme.Opens.ι g.source)
      ⟨X.point, g.mem_source⟩).symm.trans
    (ringKrullDim_stalk_eq_of_etale g.hom ⟨X.point, g.mem_source⟩)
  rw [show Scheme.Opens.ι g.source ⟨X.point, g.mem_source⟩ = X.point from rfl,
    g.map_point] at h
  show (ringKrullDim (Y.scheme.presheaf.stalk Y.point) = d) ↔
    (ringKrullDim (X.scheme.presheaf.stalk X.point) = d)
  rw [h]

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A point `u` of a scheme chart `a : yoneda.obj U ⟶ F` lies over the point `x` of `F` when
some field-valued point of `yoneda.obj U` selects `u` and has class `x` in `|F|`.

This is the relation "`u` is a point of the chart above `x`" used by Tag 0BAM. -/
def ChartPoint (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F)
    (u : (BigFppfOver.toScheme B S hS).obj U) (x : points B S hS F) : Prop :=
  ∃ p : FieldValuedPoint B S hS (yoneda.obj U),
    schemePoint B S hS U p = u ∧
      pointsMap B S hS (yoneda.obj U) a (p.class B S hS (yoneda.obj U)) = x

/-- The scheme point underlying a point of a represented presheaf lies over the image of that
point along any chart. -/
theorem chartPoint_pointsToScheme (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F)
    (y : points B S hS (yoneda.obj U)) :
    ChartPoint B S hS U a (pointsToScheme B S hS U y)
      (pointsMap B S hS (yoneda.obj U) a y) :=
  Quot.inductionOn y fun q ↦ ⟨q, rfl, rfl⟩

/-- **Stacks 0BAM, condition on one chart.** Some étale scheme chart of `F` has a local ring
of Krull dimension `d` at a point above `x`. -/
abbrev HasChartLocalRingDimension (x : points B S hS F) (d : ℕ∞) : Prop :=
  ∃ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F)
    (u : (BigFppfOver.toScheme B S hS).obj U),
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) a ∧
    ChartPoint B S hS U a u x ∧
    ringKrullDim (((BigFppfOver.toScheme B S hS).obj U).presheaf.stalk u) = (d : WithBot ℕ∞)

/-- **Stacks 0BAM, condition on every chart.** Every étale scheme chart of `F` has a local
ring of Krull dimension `d` at each of its points above `x`. -/
abbrev AllChartsLocalRingDimension (x : points B S hS F) (d : ℕ∞) : Prop :=
  ∀ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F)
    (u : (BigFppfOver.toScheme B S hS).obj U),
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) a →
    ChartPoint B S hS U a u x →
    ringKrullDim (((BigFppfOver.toScheme B S hS).obj U).presheaf.stalk u) = (d : WithBot ℕ∞)

/-- The one-chart condition rewritten with the field-valued point selecting the chart point,
which is the shape in which Tag 04N2 states the chart equivalence. -/
private theorem hasChartLocalRingDimension_iff_fieldChart (x : points B S hS F) (d : ℕ∞) :
    HasChartLocalRingDimension B S hS x d ↔
      ∃ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F),
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) a ∧
        ∃ p : FieldValuedPoint B S hS (yoneda.obj U),
          pointsMap B S hS (yoneda.obj U) a (p.class B S hS (yoneda.obj U)) = x ∧
          ringKrullDim (((BigFppfOver.toScheme B S hS).obj U).presheaf.stalk
            (schemePoint B S hS U p)) = (d : WithBot ℕ∞) := by
  constructor
  · rintro ⟨U, a, u, ha, ⟨p, rfl, hx⟩, hd⟩
    exact ⟨U, a, ha, p, hx, hd⟩
  · rintro ⟨U, a, ha, p, hx, hd⟩
    exact ⟨U, a, _, ha, ⟨p, rfl, hx⟩, hd⟩

/-- **Stacks 0BAM.** The Krull dimension of the local ring measured on an étale scheme chart
of an algebraic space is independent of the chart and of the point above `x`: one chart
realizes the value `d` exactly when every chart does. -/
@[stacks 0BAM "equivalence of étale-chart conditions"]
theorem hasChartLocalRingDimension_iff_allChartsLocalRingDimension
    (hF : IsAlgebraicSpace B S hS F) (x : points B S hS F) (d : ℕ∞) :
    HasChartLocalRingDimension B S hS x d ↔ AllChartsLocalRingDimension B S hS x d := by
  have hchart := forall_etale_chart_iff_exists_etale_chart B S hS F hF x
    (fun X : GermOfScheme.{u} ↦
      ringKrullDim (X.scheme.presheaf.stalk X.point) = (d : WithBot ℕ∞))
    (GermOfScheme.isEtaleLocal_ringKrullDim_stalk_eq (d : WithBot ℕ∞))
  rw [hasChartLocalRingDimension_iff_fieldChart]
  constructor
  · rintro h V b w hb ⟨q, rfl, hx⟩
    exact hchart.mpr h V b hb q hx
  · intro hall
    refine hchart.mp fun U a ha q hx ↦ hall U a _ ha ⟨q, rfl, hx⟩

/-- **Stacks 0BAM, the representable case.** For a represented algebraic space the chart
condition at a point is the Krull dimension of the local ring of the representing scheme at
the corresponding scheme point. -/
@[stacks 0BAM "representable case"]
theorem hasChartLocalRingDimension_iff_ringKrullDim_stalk (U : BigFppfOver B S hS)
    (u : (BigFppfOver.toScheme B S hS).obj U) (x : points B S hS (yoneda.obj U))
    (hx : ChartPoint B S hS U (𝟙 (yoneda.obj U)) u x) (d : ℕ∞) :
    HasChartLocalRingDimension B S hS x d ↔
      ringKrullDim (((BigFppfOver.toScheme B S hS).obj U).presheaf.stalk u) =
        (d : WithBot ℕ∞) := by
  obtain ⟨p, rfl, hpx⟩ := hx
  have hrepr := exists_etale_chart_iff_of_representable B S hS (yoneda.obj U) U (Iso.refl _) p
    (fun X : GermOfScheme.{u} ↦
      ringKrullDim (X.scheme.presheaf.stalk X.point) = (d : WithBot ℕ∞))
    (GermOfScheme.isEtaleLocal_ringKrullDim_stalk_eq (d : WithBot ℕ∞))
  simpa [hasChartLocalRingDimension_iff_fieldChart, hpx] using hrepr

/-- The Krull dimension of a stalk of a scheme is a natural number or infinity, never `⊥`. -/
private theorem exists_coe_eq_ringKrullDim_stalk (X : Scheme.{u}) (x : X) :
    ∃ d : ℕ∞, ringKrullDim (X.presheaf.stalk x) = (d : WithBot ℕ∞) := by
  have hnonneg : (0 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x) :=
    ringKrullDim_nonneg_of_nontrivial
  exact WithBot.ne_bot_iff_exists.mp
    (ne_of_gt (lt_of_lt_of_le (WithBot.bot_lt_coe (0 : ℕ∞)) hnonneg)) |>.imp fun _ h ↦ h.symm

/-- Every point of an algebraic space is realized by some étale scheme chart whose local ring
there has a finite Krull dimension, so the set of values entering `localRingDimension` is
nonempty. -/
private theorem exists_hasChartLocalRingDimension (hF : IsAlgebraicSpace B S hS F)
    (x : points B S hS F) : ∃ d : ℕ∞, HasChartLocalRingDimension B S hS x d := by
  obtain ⟨U, a, ha, p, hp⟩ := exists_etale_chart_at_point B S hS F hF x
  obtain ⟨d, hd⟩ := exists_coe_eq_ringKrullDim_stalk
    ((BigFppfOver.toScheme B S hS).obj U) (schemePoint B S hS U p)
  exact ⟨d, U, a, _, ha, ⟨p, rfl, hp⟩, hd⟩

/-- At most one value is realized by an étale scheme chart of an algebraic space at a point,
by the chart equivalence of Tag 0BAM. -/
private theorem hasChartLocalRingDimension_unique (hF : IsAlgebraicSpace B S hS F)
    (x : points B S hS F) {d e : ℕ∞} (hd : HasChartLocalRingDimension B S hS x d)
    (he : HasChartLocalRingDimension B S hS x e) : d = e := by
  obtain ⟨U, a, u, ha, hu, hdim⟩ := he
  exact_mod_cast ((hasChartLocalRingDimension_iff_allChartsLocalRingDimension
    B S hS hF x d).mp hd U a u ha hu).symm.trans hdim

/-- **Stacks 04NA.** The Krull dimension of the local ring of an algebraic space at a point,
measured on an étale scheme chart at a point above it.

By `AlgebraicGeometry.Space.localRingDimension_eq_iff_hasChartLocalRingDimension` exactly one
value is realized by such a chart, and it is this infimum. -/
@[stacks 04NA "dimension"]
noncomputable def localRingDimension (x : points B S hS F) : ℕ∞ :=
  sInf {d : ℕ∞ | HasChartLocalRingDimension B S hS x d}

/-- **Stacks 04NA.** The dimension of the local ring of an algebraic space at a point is the
value measured on any étale scheme chart at a point above it. -/
@[stacks 04NA "characterization by étale charts"]
theorem localRingDimension_eq_iff_hasChartLocalRingDimension (hF : IsAlgebraicSpace B S hS F)
    (x : points B S hS F) (d : ℕ∞) :
    localRingDimension B S hS x = d ↔ HasChartLocalRingDimension B S hS x d := by
  obtain ⟨d₀, h₀⟩ := exists_hasChartLocalRingDimension B S hS hF x
  have hset : {e : ℕ∞ | HasChartLocalRingDimension B S hS x e} = {d₀} := by
    ext e
    exact ⟨fun he ↦ hasChartLocalRingDimension_unique B S hS hF x he h₀, fun he ↦ he ▸ h₀⟩
  rw [localRingDimension, hset, sInf_singleton]
  exact ⟨fun h ↦ h ▸ h₀, fun h ↦ (hasChartLocalRingDimension_unique B S hS hF x h h₀).symm⟩

/-- The dimension of the local ring of an algebraic space at a point is the Krull dimension of
the local ring of an étale scheme chart at any point above it. -/
theorem localRingDimension_eq_of_chartPoint (hF : IsAlgebraicSpace B S hS F)
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F)
    (ha : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) a)
    (u : (BigFppfOver.toScheme B S hS).obj U) (x : points B S hS F)
    (hu : ChartPoint B S hS U a u x) :
    (localRingDimension B S hS x : WithBot ℕ∞) =
      ringKrullDim (((BigFppfOver.toScheme B S hS).obj U).presheaf.stalk u) := by
  obtain ⟨d, hd⟩ := exists_coe_eq_ringKrullDim_stalk ((BigFppfOver.toScheme B S hS).obj U) u
  rw [hd]
  exact congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞))
    ((localRingDimension_eq_iff_hasChartLocalRingDimension B S hS hF x d).2
      ⟨U, a, u, ha, hu, hd⟩)

end Space

end AlgebraicGeometry

end

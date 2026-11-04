module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionZeroPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleSourceDecency
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresCardinality
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.QuasiCompactMonomorphicPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Sober
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Specializations
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionEtaleInvariance
public import StacksFrontier.Topology.Sober.Generization

/-!
# Codimension-zero points of a decent algebraic space

Let `X` be a decent algebraic space over a scheme `S` and let `x` be a point of `|X|`. Being a
generic point of an irreducible component of `|X|` is the same as having a local ring of
dimension zero, and the condition may equally be tested at one, or at every, point above `x`
under an étale morphism of algebraic spaces onto `X`. This is **Stacks 0ABV**.

## Main results

* `AlgebraicGeometry.Space.eq_of_specializes_of_localRingDimension_eq_zero`: a point whose
  local ring has dimension zero admits no generization but itself.
* `AlgebraicGeometry.Space.localRingDimension_eq_zero_of_mem_genericPoints`: a generic point
  of an irreducible component has a local ring of dimension zero.
* `AlgebraicGeometry.Space.mem_genericPoints_of_localRingDimension_eq_zero`: the converse.
* `AlgebraicGeometry.Space.mem_genericPoints_iff_localRingDimension_eq_zero`: those two as an
  equivalence.
* `AlgebraicGeometry.Space.mem_genericPoints_tfae`: **Stacks 0ABV**, the four conditions
  together.

## Implementation notes

The source lists five conditions. Its (4), that the dimension of the local ring of `X` at `x`
is zero, and its (5), that `x` is a point of codimension `0` on `X`, are the same condition
by the definition of Stacks 04NA; here both read `localRingDimension B S hS x = 0`, so they
occur once in the list below.

Passing between a point of `|X|` and a point of an étale scheme chart above it is Stacks
0BAQ, in the two forms `localRingDimension_eq_zero_iff_exists_etale_genericPoint` and
`localRingDimension_eq_zero_iff_all_etale_genericPoints`; the chart is produced by
`exists_affine_etale_chart_of_point`. Lifting a generization of `x` to the chart is
Stacks 03K2 and collapsing a generization inside a single chart fibre is Stacks 03K5.

The step from "`x` admits no generization but itself" to "`closure {x}` is an irreducible
component" is **not** formal: it fails on an infinite set with the cofinite topology, which is
Kolmogorov and in which no point has a proper generization, yet which is irreducible, so that
its only irreducible component is the whole space
(`not_quasiSober_cofiniteTopology`, `irreducibleComponents_cofiniteTopology`). What closes it
is sobriety of the point space of a decent algebraic space, which is Stacks 03K6,
`AlgebraicGeometry.Space.quasiSober_points_of_isDecentSpace`. It is needed not only on `X` but
on the source of each étale morphism onto `X`, which is again decent by Stacks 0ABU.

## References

* [Stacks Project, Tag 0ABV](https://stacks.math.columbia.edu/tag/0ABV)
* [Stacks Project, Tag 03K2](https://stacks.math.columbia.edu/tag/03K2)
* [Stacks Project, Tag 03K5](https://stacks.math.columbia.edu/tag/03K5)
* [Stacks Project, Tag 03K6](https://stacks.math.columbia.edu/tag/03K6)
* [Stacks Project, Tag 04NA](https://stacks.math.columbia.edu/tag/04NA)
* [Stacks Project, Tag 0ABU](https://stacks.math.columbia.edu/tag/0ABU)
* [Stacks Project, Tag 0BAQ](https://stacks.math.columbia.edu/tag/0BAQ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### A codimension-zero point has no proper generization -/

/-- Specialization between points of a chart is detected on the associated scheme points. -/
private theorem pointsToScheme_specializes_iff (U : BigFppfOver B S hS)
    (u' u : points B S hS (yoneda.obj U)) :
    pointsToScheme B S hS U u' ⤳ pointsToScheme B S hS U u ↔ u' ⤳ u := by
  simp only [← schemePointsHomeomorph_apply]
  exact (schemePointsHomeomorph B S hS U).isInducing.specializes_iff

/-- A point of a decent algebraic space over `S` whose local ring has dimension zero admits no
generization but itself: a point above it in an affine étale chart is a generic point of an
irreducible component of the chart by Stacks 0BAQ, the generization lifts to the chart by
Stacks 03K2, and the lift is therefore the point it lifts. -/
theorem eq_of_specializes_of_localRingDimension_eq_zero (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) {x : points B S hS X}
    (hx : localRingDimension B S hS x = 0) (x' : points B S hS X) (hs : x' ⤳ x) : x' = x := by
  obtain ⟨U, φ, u, hUaff, hφ, hux⟩ := exists_affine_etale_chart_of_point B S hS X hX x
  have hetale : IsEtale B S hS φ := (isEtale_iff_presheaf_of_yoneda B S hS φ).2 hφ
  have hchart : ChartPoint B S hS U φ (pointsToScheme B S hS U u) x := by
    rw [← hux]
    exact chartPoint_pointsToScheme B S hS U φ u
  have hgen : pointsToScheme B S hS U u ∈
      genericPoints ((BigFppfOver.toScheme B S hS).obj U) :=
    (localRingDimension_eq_zero_iff_all_etale_genericPoints B S hS hX x).mp hx U φ _ hetale
      hchart
  obtain ⟨u', hu'u, hu'⟩ := exists_specializes_pointsMap_eq_of_isEtale B S hS hX hs
    (fun V hV ψ hψ ↦ hasFiniteChartFibersAtEveryPoint_of_isDecentSpace B S hS hdec x' V hV ψ hψ)
    U φ hφ u hux
  have hu'eq : u' = u :=
    (schemePointsHomeomorph B S hS U).injective
      (forall_specializes_eq_of_mem_genericPoints hgen _
        ((pointsToScheme_specializes_iff B S hS U u' u).2 hu'u))
  rw [← hu', hu'eq, hux]

/-! ### Conditions (1) and (4) -/

/-- **Stacks 0ABV, (1) implies (4).** A generic point of an irreducible component of the point
space of a decent algebraic space over `S` has a local ring of dimension zero: a point above it
in an affine étale chart has no proper generization, because a generization of it maps to a
generization of the point, which is the point itself, and Stacks 03K5 then collapses the lifted
generization. -/
theorem localRingDimension_eq_zero_of_mem_genericPoints (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) {x : points B S hS X}
    (hx : x ∈ genericPoints (points B S hS X)) : localRingDimension B S hS x = 0 := by
  have := t0Space_points_of_isDecentSpace B S hS hX hdec
  obtain ⟨U, φ, u, hUaff, hφ, hux⟩ := exists_affine_etale_chart_of_point B S hS X hX x
  have hetale : IsEtale B S hS φ := (isEtale_iff_presheaf_of_yoneda B S hS φ).2 hφ
  refine (localRingDimension_eq_zero_iff_exists_etale_genericPoint B S hS hX x).mpr
    ⟨U, φ, pointsToScheme B S hS U u, hetale, ?_, ?_⟩
  · rw [← hux]
    exact chartPoint_pointsToScheme B S hS U φ u
  refine mem_genericPoints_of_forall_specializes_eq ?_
  intro w hw
  obtain ⟨u', rfl⟩ : ∃ u', pointsToScheme B S hS U u' = w :=
    ⟨(schemePointsHomeomorph B S hS U).symm w,
      (schemePointsHomeomorph B S hS U).apply_symm_apply w⟩
  have hu'u := (pointsToScheme_specializes_iff B S hS U u' u).1 hw
  have himg : pointsMap B S hS (yoneda.obj U) φ u = pointsMap B S hS (yoneda.obj U) φ u' := by
    have hspec : pointsMap B S hS (yoneda.obj U) φ u' ⤳ x := by
      simpa [hux] using hu'u.map (continuous_pointsMap B S hS φ)
    rw [hux, forall_specializes_eq_of_mem_genericPoints hx _ hspec]
  rw [eq_of_specializes_of_pointsMap_eq_of_hasFiniteChartFibers B S hS hX
    (hasFiniteChartFibersAtEveryPoint_of_isDecentSpace B S hS hdec) U φ hφ u u' himg hu'u]

/-- **Stacks 0ABV, (4) implies (1).** A point of a decent algebraic space over `S` whose local
ring has dimension zero is a generic point of an irreducible component of the point space. The
point admits no generization but itself, and sobriety of the point space, Stacks 03K6, turns
that into maximality of the closure of the point. -/
theorem mem_genericPoints_of_localRingDimension_eq_zero (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) {x : points B S hS X}
    (hx : localRingDimension B S hS x = 0) : x ∈ genericPoints (points B S hS X) := by
  have := t0Space_points_of_isDecentSpace B S hS hX hdec
  have := quasiSober_points_of_isDecentSpace B S hS hX hdec
  exact mem_genericPoints_of_forall_specializes_eq
    (eq_of_specializes_of_localRingDimension_eq_zero B S hS hX hdec hx)

/-! ### The four conditions -/

/-- **Stacks 0ABV.** For a point `x` of a decent algebraic space `X` over `S` the following
are equivalent: `x` is a generic point of an irreducible component of `|X|`; for every étale
morphism of algebraic spaces onto `X`, every point above `x` is a generic point of an
irreducible component of the source; for some étale morphism onto `X` some point above `x`
is; and the local ring of `X` at `x` has dimension zero, which is to say that `x` is a point
of codimension `0` on `X`. -/
@[stacks 0ABV]
theorem mem_genericPoints_tfae (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (x : points B S hS X) :
    List.TFAE
      [ x ∈ genericPoints (points B S hS X),
        ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS Y → ∀ f : Y ⟶ X,
          IsEtale B S hS f → ∀ y : points B S hS Y, pointsMap B S hS Y f y = x →
            y ∈ genericPoints (points B S hS Y),
        ∃ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS Y) (f : Y ⟶ X)
          (y : points B S hS Y), IsEtale B S hS f ∧ pointsMap B S hS Y f y = x ∧
            y ∈ genericPoints (points B S hS Y),
        localRingDimension B S hS x = 0 ] := by
  have hid : IsEtale B S hS (𝟙 X) := isEtale_of_isIso B S hS (𝟙 X)
  have hmapid : pointsMap B S hS X (𝟙 X) x = x := congrFun (pointsMap_id B S hS X) x
  tfae_have 1 → 4 := localRingDimension_eq_zero_of_mem_genericPoints B S hS hX hdec
  tfae_have 4 → 2 := by
    intro hx Y hY f hf y hy
    have hYdec : IsDecentSpace B S hS Y := isDecentSpace_of_isEtale B S hS f hY hX hf hdec
    refine mem_genericPoints_of_localRingDimension_eq_zero B S hS hY hYdec ?_
    rw [← localRingDimension_pointsMap_of_etale B S hS hY hX f hf y, hy]
    exact hx
  tfae_have 2 → 3 := fun h ↦ ⟨X, hX, 𝟙 X, x, hid, hmapid, h X hX (𝟙 X) hid x hmapid⟩
  tfae_have 3 → 1 := by
    rintro ⟨Y, hY, f, y, hf, hy, hygen⟩
    have hYdec : IsDecentSpace B S hS Y := isDecentSpace_of_isEtale B S hS f hY hX hf hdec
    refine mem_genericPoints_of_localRingDimension_eq_zero B S hS hX hdec ?_
    rw [← hy, localRingDimension_pointsMap_of_etale B S hS hY hX f hf y]
    exact localRingDimension_eq_zero_of_mem_genericPoints B S hS hY hYdec hygen
  tfae_finish

/-- **Stacks 0ABV, conditions (1) and (4).** A point of a decent algebraic space over `S` is a
generic point of an irreducible component of the point space exactly when its local ring has
dimension zero, that is, exactly when it is a point of codimension `0`. -/
theorem mem_genericPoints_iff_localRingDimension_eq_zero (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (x : points B S hS X) :
    x ∈ genericPoints (points B S hS X) ↔ localRingDimension B S hS x = 0 :=
  ⟨localRingDimension_eq_zero_of_mem_genericPoints B S hS hX hdec,
    mem_genericPoints_of_localRingDimension_eq_zero B S hS hX hdec⟩

end AlgebraicGeometry.Space

end

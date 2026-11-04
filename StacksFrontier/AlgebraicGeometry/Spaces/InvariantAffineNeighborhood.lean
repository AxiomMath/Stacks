module

public import Mathlib.AlgebraicGeometry.Restrict
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GroupoidOfEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Groupoids.GroupSchemeProperties.InvariantAffineOpen
public import StacksFrontier.AlgebraicGeometry.Properties.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionZeroPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFinitePoints
import StacksCore.Tactic.EgaSgaAttribute

/-!
# An invariant affine neighbourhood of a codimension-zero point of an étale chart

Let `F` be an algebraic space over a scheme `S` with an étale chart `q : h_U ⟶ F` whose
relation `R = U ×_F U` has finite locally free projections, and let `x` be a point of `F` whose
local ring has dimension zero. The fibre of `|U| → |F|` above `x` is then a finite set of
generic points of irreducible components of `U`, so when `U` is quasi-separated that fibre lies
in a single affine open, and saturating gives an affine open of `U` which is invariant under
`R` and still meets the fibre.

That invariant affine open is the open subscheme out of which the schematic open subspace of
Tag 0BAS is built.

## Main results

* `AlgebraicGeometry.exists_isAffineOpen_invariant_of_isFiniteLocallyFree` is Tag 03JE read for
  an equivalence relation of schemes rather than for a groupoid scheme, with invariance stated
  as an equivalence rather than as an implication.
* `AlgebraicGeometry.subobjectPullback_mk_opens_ι` computes the pullback of the subobject cut
  out by an open subscheme, which is how the previous result feeds into
  `AlgebraicGeometry.Space.IsInvariantSubscheme`, and
  `AlgebraicGeometry.isOpenImmersion_subobjectMk_opens_arrow` records that the arrow of that
  subobject is again an open immersion.
* `AlgebraicGeometry.Space.mem_genericPoints_of_pointsMap_eq` : a point of an étale chart above
  a codimension-zero point is the generic point of an irreducible component.
* `AlgebraicGeometry.Space.exists_isAffineOpen_fiber_subset` : the whole fibre above a
  codimension-zero point lies in one affine open of a quasi-separated chart.
* `AlgebraicGeometry.Space.pointsMap_eq_of_isPullback_relation` : the two legs of the relation
  of a chart agree after composing with the chart, on points.

## Implementation notes

Tag 03JE is stated in the library for a groupoid scheme, and its conclusion is the pointwise
invariance `Stacks.Groupoids.IsInvariantOpen`. The groupoid canonically extending an
equivalence relation carries its schemes of objects and arrows only propositionally, so the
relation form below obtains the groupoid and then eliminates both equalities with `cases`;
after that the source and target maps are the given ones and no transport remains. The
backward implication of the invariance is the one the subobject formulation needs, and it comes
from symmetry of the relation cut out on points, which is
`Stacks.Groupoids.GroupoidScheme.equivalence_sourceTargetRel`.

The finite family of irreducible components fed to Tag 01ZV is indexed by the fibre itself:
each of its points is a generic point, the component is the closure of the point, and
injectivity of the family is injectivity of `closure {·}`, which holds because the underlying
space of a scheme is T0.

## References

* [Stacks Project, Tag 03JE](https://stacks.math.columbia.edu/tag/03JE)
* [Stacks Project, Tag 01ZV](https://stacks.math.columbia.edu/tag/01ZV)
* [Stacks Project, Tag 03IJ](https://stacks.math.columbia.edu/tag/03IJ)
* [Stacks Project, Tag 0BAQ](https://stacks.math.columbia.edu/tag/0BAQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The pullback along a morphism of schemes of the subobject cut out by an open subscheme is
the subobject cut out by the preimage of that open. -/
theorem subobjectPullback_mk_opens_ι {X Y : Scheme.{u}} (f : X ⟶ Y) (W : Y.Opens) :
    (Subobject.pullback f).obj (Subobject.mk W.ι) = Subobject.mk (f ⁻¹ᵁ W).ι :=
  Subobject.pullback_obj_mk (isPullback_morphismRestrict f W)

/-- The arrow of the subobject of a scheme cut out by an open subscheme is an open
immersion. -/
theorem isOpenImmersion_subobjectMk_opens_arrow {X : Scheme.{u}} (W : X.Opens) :
    IsOpenImmersion (Subobject.mk W.ι).arrow := by
  have hRI : MorphismProperty.RespectsIso (@IsOpenImmersion.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine (MorphismProperty.cancel_left_of_respectsIso (@IsOpenImmersion.{u})
    (Subobject.underlyingIso W.ι).inv _).1 ?_
  rw [Subobject.underlyingIso_arrow]
  infer_instance

/-- **Stacks 03JE for an equivalence relation.** Let `t, s : R ⟶ U` be an equivalence relation
of schemes over `S` with finite locally free source and target maps. A point of `U` whose orbit
is contained in an affine open has an invariant affine open neighbourhood, invariance meaning
that an arrow of the relation has its source in the open exactly when it has its target
there. -/
@[sga "1 V 1.8" "special case"]
theorem exists_isAffineOpen_invariant_of_isFiniteLocallyFree {S : Scheme.{u}} {R U : Over S}
    (t s : R ⟶ U) [Stacks.Morphisms.IsFiniteLocallyFree s.left]
    [Stacks.Morphisms.IsFiniteLocallyFree t.left] [IsEquivalenceRelation t s] (x : U.left)
    (W : U.left.Opens) (hW : IsAffineOpen W)
    (horbit : ∀ r : R.left, s.left.base r = x → t.left.base r ∈ W) :
    ∃ V : U.left.Opens, IsAffineOpen V ∧ x ∈ V ∧
      ∀ r : R.left, (s.left.base r ∈ V ↔ t.left.base r ∈ V) := by
  classical
  set j : Stacks.Groupoids.PreRelation R U := prod.lift t s with hj
  have hjt : j.target = t := by simp [hj, Stacks.Groupoids.PreRelation.target]
  have hjs : j.source = s := by simp [hj, Stacks.Groupoids.PreRelation.source]
  have _ : IsEquivalenceRelation j.target j.source := by rw [hjt, hjs]; infer_instance
  obtain ⟨G, hG, -⟩ := existsUnique_groupoidScheme_of_isEquivalenceRelation j
  obtain ⟨ho, ha, hsrc, htgt⟩ := hG
  cases ha
  cases ho
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hsrc htgt
  rw [hjs] at hsrc
  rw [hjt] at htgt
  have _ : Stacks.Morphisms.IsFiniteLocallyFree G.source.left := by rw [hsrc]; infer_instance
  have _ : Stacks.Morphisms.IsFiniteLocallyFree G.target.left := by rw [htgt]; infer_instance
  obtain ⟨V, hVaff, hxV, hVinv⟩ :=
    GroupoidScheme.exists_invariant_affine_open_of_orbit_subset_affine G x
      ⟨W, hW, fun r hr => by rw [htgt]; exact horbit r (by rw [← hsrc]; exact hr)⟩
  refine ⟨V, hVaff, hxV, fun r => ⟨fun hr => ?_, fun hr => ?_⟩⟩
  · rw [← htgt]
    exact hVinv r (by rw [hsrc]; exact hr)
  · obtain ⟨r', hr'₁, hr'₂⟩ := G.equivalence_sourceTargetRel.symm
      (show Function.SourceTargetRel G.source.left.base G.target.left.base
        (G.target.left.base r) (G.source.left.base r) from ⟨r, rfl, rfl⟩)
    rw [← hsrc, ← hr'₁]
    exact hVinv r' (by rw [hr'₂, htgt]; exact hr)

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A point of an étale scheme chart lying above a point of codimension zero is the generic
point of an irreducible component of the chart.

This is Tag 0BAQ, condition (3), applied to the chart point underlying a point of the
represented presheaf. -/
theorem mem_genericPoints_of_pointsMap_eq (hF : IsAlgebraicSpace B S hS F)
    (U : BigFppfOver B S hS) (q : yoneda.obj U ⟶ F) (hq : IsEtale B S hS q)
    {x : points B S hS F} (hx : localRingDimension B S hS x = 0)
    (a : points B S hS (yoneda.obj U)) (ha : pointsMap B S hS (yoneda.obj U) q a = x) :
    pointsToScheme B S hS U a ∈
      genericPoints ((BigFppfOver.toScheme B S hS).obj U) :=
  (localRingDimension_eq_zero_iff_all_etale_genericPoints B S hS hF x).mp hx U q _ hq
    (ha ▸ chartPoint_pointsToScheme B S hS U q a)

/-- The whole fibre of a quasi-separated étale scheme chart above a point of codimension zero
lies in a single affine open of the chart.

The fibre is finite by Tag 03IJ and consists of generic points of irreducible components by
Tag 0BAQ, so Tag 01ZV applies; this is the step of Tag 0BAS at which quasi-separatedness of
the chart is used. -/
theorem exists_isAffineOpen_fiber_subset (hF : IsAlgebraicSpace B S hS F)
    (U : BigFppfOver B S hS) (q : yoneda.obj U ⟶ F) (hq : IsEtale B S hS q)
    (hqcfst : IsQuasiCompact B S hS (pullback.fst q q))
    (hqcsnd : IsQuasiCompact B S hS (pullback.snd q q))
    (hUqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj U))
    {x : points B S hS F} (hx : localRingDimension B S hS x = 0) :
    ∃ W : ((BigFppfOver.toScheme B S hS).obj U).Opens, IsAffineOpen W ∧
      ∀ a : points B S hS (yoneda.obj U), pointsMap B S hS (yoneda.obj U) q a = x →
        pointsToScheme B S hS U a ∈ W := by
  classical
  have _ := hUqs
  set T : Set ((BigFppfOver.toScheme B S hS).obj U) :=
    pointsToScheme B S hS U '' (pointsMap B S hS (yoneda.obj U) q ⁻¹' {x}) with hTdef
  have hTfin : T.Finite :=
    (finite_fiber_pointsMap_of_etale_presentation B S hS F U q hq hqcfst hqcsnd x).image _
  have hTgen : ∀ y ∈ T, y ∈ genericPoints ((BigFppfOver.toScheme B S hS).obj U) := by
    rintro y ⟨a, ha, rfl⟩
    exact mem_genericPoints_of_pointsMap_eq B S hS hF U q hq hx a ha
  have _ : Finite ↥T := hTfin.to_subtype
  obtain ⟨W, hWaff, hWmem⟩ :=
    exists_affine_open_containing_generic_points
      (X := (BigFppfOver.toScheme B S hS).obj U)
      (fun y : ↥T => closure ({y.1} : Set ((BigFppfOver.toScheme B S hS).obj U)))
      (fun y => hTgen y.1 y.2)
      (fun y z h => Subtype.ext (inseparable_iff_closure_eq.mpr h).eq)
      (fun y => y.1) (fun _ => rfl)
  exact ⟨W, hWaff, fun a ha => hWmem ⟨pointsToScheme B S hS U a, ⟨a, ha, rfl⟩⟩⟩

/-- The two legs of the relation of a chart induce the same map on points after composing with
the chart: a point of `R = U ×_F U` has the same image in `|F|` whichever projection to `|U|`
is used. -/
theorem pointsMap_eq_of_isPullback_relation {U R : BigFppfOver B S hS}
    (q : yoneda.obj U ⟶ F) (t s : R ⟶ U)
    (hR : IsPullback (yoneda.map t) (yoneda.map s) q q)
    (b : points B S hS (yoneda.obj R)) :
    pointsMap B S hS (yoneda.obj U) q
        (pointsMap B S hS (yoneda.obj R) (yoneda.map t) b) =
      pointsMap B S hS (yoneda.obj U) q
        (pointsMap B S hS (yoneda.obj R) (yoneda.map s) b) := by
  rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, hR.w]

end Space

end AlgebraicGeometry

end

module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricFieldChange.QuasiFiniteCodimensionOne
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericallyFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.TranscendenceDegreeChart

/-!
# Quasi-finiteness over a point of codimension at most one

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type, with `Y` locally Noetherian, and let `y` be a point of `|Y|` whose local ring has
dimension at most one (Stacks 04NA). Write `X⁰` for the set of points of `|X|` whose local
ring has dimension zero. Stacks 0AD1 says that `f` is quasi-finite at every point above `y`
as soon as one of four generic conditions holds: the transcendence degree of `x` over `f(x)`
is zero for every `x` of `X⁰`, or for every such `x` whose image specializes to `y`, or `f` is
quasi-finite at every point of `X⁰`, or `f` is quasi-finite at a dense set of points of `|X|`.

The statement for algebraic spaces is derived here from the statement for schemes, which is
Stacks 0AB6: a morphism of schemes locally of finite type is quasi-finite at every point above
a point whose local ring is Noetherian of dimension at most one, as soon as one of the same
four generic conditions holds. That scheme-level statement is carried as an explicit hypothesis
of the result below, in exactly the form it has for schemes, so the result is conditional on it
and supplying a proof of Stacks 0AB6 discharges it outright.

## Main results

* `AlgebraicGeometry.Space.isQuasiFiniteAt_of_localRingDimension_le_one`: **Stacks 0AD1**,
  conditional on Stacks 0AB6 for schemes.

## Implementation notes

The reduction to the scheme case happens in a pointed pair of étale charts `U ⟶ V` of `f` at the
chosen point: quasi-finiteness at a point of an algebraic space is quasi-finiteness of the
induced morphism of schemes in every such chart
(`AlgebraicGeometry.Space.isQuasiFiniteAt_iff_forall_quasiFiniteAt_chart`). Three translations
feed the scheme statement.

The local ring of `V` at the chart point of `y` has the dimension of the local ring of `Y` at
`y`, by Stacks 0BAM, and `V` is locally Noetherian because it is an étale chart of a locally
Noetherian algebraic space (Stacks 03E8).

The points of `U` above `X⁰` are exactly the generic points of `U`, by Stacks 0BAQ; this turns
each of the first three conditions into its scheme counterpart at the generic points of `U`.
For the first two that passes through the transcendence degree of Stacks 04NM, which is the
degree of the residue field extension of the morphism of charts: the germ of a morphism of
schemes at a point of its source has the transcendence degree of that extension, and a
transcendence degree of zero over a field is algebraicity.

For the fourth condition the chart map on points is open, since the chart is étale (Stacks
03IR), so the preimage of a dense set of points of `|X|` is a dense set of points of `U`.

The second condition also needs its specialization hypothesis transported: specialization in
`V` is carried to specialization in `|Y|` by the chart map on points, which is continuous for
the topology of Stacks 03BX.

`AlgebraicGeometry.MorphismOfGerms.HasResidueFieldTranscendenceDegree` is a property of germs
and is matched against a given morphism of schemes through
`AlgebraicGeometry.MorphismOfGerms.hasResidueFieldTranscendenceDegree_unique`; the
identification of its value at the germ of a morphism of schemes is
`AlgebraicGeometry.MorphismOfGerms.hasResidueFieldTranscendenceDegree_ofSchemeHom` of
`StacksFrontier.AlgebraicGeometry.Spaces.TranscendenceDegreeChart`. The two facts about the
point selected by a pointed pair of étale charts —
`AlgebraicGeometry.Space.sourcePoint_eq_schemePoint` and
`AlgebraicGeometry.Space.chartPoint_map_sourcePoint` — are taken from
`StacksFrontier.AlgebraicGeometry.Spaces.GenericallyFinite`, which this file imports.

## References

* [Stacks Project, Tag 0AD1](https://stacks.math.columbia.edu/tag/0AD1)
* [Stacks Project, Tag 0AB6](https://stacks.math.columbia.edu/tag/0AB6)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03E8](https://stacks.math.columbia.edu/tag/03E8)
* [Stacks Project, Tag 03IR](https://stacks.math.columbia.edu/tag/03IR)
* [Stacks Project, Tag 04NA](https://stacks.math.columbia.edu/tag/04NA)
* [Stacks Project, Tag 04NK](https://stacks.math.columbia.edu/tag/04NK)
* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
* [Stacks Project, Tag 0BAM](https://stacks.math.columbia.edu/tag/0BAM)
* [Stacks Project, Tag 0BAQ](https://stacks.math.columbia.edu/tag/0BAQ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### The transcendence degree of the germ of a morphism of schemes -/

/-- A morphism of schemes whose germ at a point of its source has residue-field transcendence
degree zero has an algebraic residue field extension there. -/
theorem isAlgebraic_residueField_of_hasResidueFieldTranscendenceDegree_zero
    {V W : Scheme.{u}} (g : V ⟶ W) (v : V)
    (h : MorphismOfGerms.HasResidueFieldTranscendenceDegree 0
      (MorphismOfGerms.ofSchemeHom g v)) :
    letI := (g.residueFieldMap v).hom.toAlgebra
    Algebra.IsAlgebraic (W.residueField (g v)) (V.residueField v) := by
  let _ := (g.residueFieldMap v).hom.toAlgebra
  have hzero : Cardinal.toENat (Algebra.trdeg (W.residueField (g v)) (V.residueField v)) = 0 :=
    MorphismOfGerms.hasResidueFieldTranscendenceDegree_unique
      (MorphismOfGerms.hasResidueFieldTranscendenceDegree_ofSchemeHom g v) h
  exact trdeg_eq_zero_iff.mp (Cardinal.toENat_eq_zero.mp hzero)

namespace Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The points selected by a pointed pair of étale charts

`sourcePoint_eq_schemePoint` and `chartPoint_map_sourcePoint` are proved in
`StacksFrontier.AlgebraicGeometry.Spaces.GenericallyFinite`, which this file imports. -/

/-- The pointed pair of étale charts obtained from a given one by moving its field-valued
representative to the canonical representative of a prescribed point of the source chart. -/
private noncomputable def chartAtSchemePoint {f : X ⟶ Y} {x : points B S hS X}
    (c : EtaleChartAtPoint B S hS f x) (z : (BigFppfOver.toScheme B S hS).obj c.U) :
    EtaleChartAtPoint B S hS f (pointsMap B S hS (yoneda.obj c.U) c.a
      ((schemePointRepresentative B S hS c.U z).class B S hS (yoneda.obj c.U))) where
  U := c.U
  V := c.V
  a := c.a
  b := c.b
  h := c.h
  a_etale := c.a_etale
  b_etale := c.b_etale
  comm := c.comm
  representative := schemePointRepresentative B S hS c.U z
  point := IsLocalRing.closedPoint (schemePointRepresentative B S hS c.U z).carrier
  maps_to := rfl

private lemma chartAtSchemePoint_sourcePoint {f : X ⟶ Y} {x : points B S hS X}
    (c : EtaleChartAtPoint B S hS f x) (z : (BigFppfOver.toScheme B S hS).obj c.U) :
    (chartAtSchemePoint B S hS c z).sourcePoint B S hS = z := by
  rw [sourcePoint_eq_schemePoint]
  exact schemePointRepresentative_point B S hS c.U z

/-- The point of an algebraic space below a point of one of its étale charts is the image of
the canonical representative of that chart point. -/
private lemma pointsMap_schemePointRepresentative_class_eq {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F)
    (u : (BigFppfOver.toScheme B S hS).obj U) (w : points B S hS F)
    (hu : ChartPoint B S hS U a u w) :
    pointsMap B S hS (yoneda.obj U) a
      ((schemePointRepresentative B S hS U u).class B S hS (yoneda.obj U)) = w := by
  obtain ⟨p, hp, hpw⟩ := hu
  have hclass : p.class B S hS (yoneda.obj U) =
      (schemePointRepresentative B S hS U u).class B S hS (yoneda.obj U) := by
    refine (pointsEquivScheme B S hS U).injective ?_
    change schemePoint B S hS U p = schemePoint B S hS U (schemePointRepresentative B S hS U u)
    rw [hp, schemePointRepresentative_point]
  rwa [← hclass]

/-- The inverse of the homeomorphism between points of a chart and its scheme points sends a
point to the class of its canonical representative. -/
private lemma schemePointsHomeomorph_symm_eq_class (U : BigFppfOver B S hS)
    (z : (BigFppfOver.toScheme B S hS).obj U) :
    (schemePointsHomeomorph B S hS U).symm z =
      (schemePointRepresentative B S hS U z).class B S hS (yoneda.obj U) := by
  refine (schemePointsHomeomorph B S hS U).injective ?_
  rw [Homeomorph.apply_symm_apply, schemePointsHomeomorph_apply]
  exact (schemePointRepresentative_point B S hS U z).symm

/-! ### Stacks 0AD1 -/

/-- **Stacks Project, Tag 0AD1.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`
which is locally of finite type, with `Y` locally Noetherian, and let `y` be a point of `|Y|`
whose local ring has dimension at most one. Write `X⁰` for the points of `|X|` whose local
ring has dimension zero. If one of the following holds — the transcendence degree of `x` over
`f(x)` is zero for every `x` of `X⁰`; the same for every `x` of `X⁰` whose image specializes
to `y`; `f` is quasi-finite at every point of `X⁰`; `f` is quasi-finite at a dense set of
points of `|X|` — then `f` is quasi-finite at every point of `|X|` above `y`.

The proof reduces to the corresponding statement for morphisms of schemes, Stacks 0AB6, which
is `AlgebraicGeometry.quasiFiniteAt_of_target_stalk_dimension_le_one`, applied in an étale
chart of the target. -/
@[stacks 0AD1]
theorem isQuasiFiniteAt_of_localRingDimension_le_one
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    (hNoeth : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (y : points B S hS Y) (hy : localRingDimension B S hS y ≤ 1)
    (hgeneric :
      (∀ x : points B S hS X, localRingDimension B S hS x = 0 →
        HasTranscendenceDegreeAt B S hS f x 0) ∨
      (∀ x : points B S hS X, localRingDimension B S hS x = 0 →
        pointsMap B S hS X f x ⤳ y → HasTranscendenceDegreeAt B S hS f x 0) ∨
      (∀ x : points B S hS X, localRingDimension B S hS x = 0 →
        IsQuasiFiniteAt B S hS f x) ∨
      Dense {x : points B S hS X | IsQuasiFiniteAt B S hS f x}) :
    ∀ x : points B S hS X, pointsMap B S hS X f x = y → IsQuasiFiniteAt B S hS f x := by
  classical
  intro x hxy
  refine (isQuasiFiniteAt_iff_forall_quasiFiniteAt_chart B S hS hX hY f hf x).mpr fun c ↦ ?_
  set T := BigFppfOver.toScheme B S hS
  set g := T.map c.h
  set ξ := c.sourcePoint B S hS
  -- The target chart is locally Noetherian, and its local ring at the image point of `y` has
  -- the dimension of the local ring of `Y` at `y`.
  have hVnoeth : IsLocallyNoetherian (T.obj c.V) :=
    (exists_atlas_iff_forall_etale B S hS Y
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) hY).mp hNoeth c.V c.b c.b_etale
  have hchartY : ChartPoint B S hS c.V c.b (g ξ) y :=
    hxy ▸ chartPoint_map_sourcePoint B S hS c
  have hdim : ringKrullDim ((T.obj c.V).presheaf.stalk (g ξ)) ≤ 1 := by
    rw [← localRingDimension_eq_of_chartPoint B S hS hY c.V c.b c.b_etale (g ξ) y hchartY]
    exact_mod_cast hy
  have hft : LocallyOfFiniteType g :=
    hf c.U c.V c.a c.b c.h c.a_etale c.b_etale c.comm
  have hstalk : IsNoetherianRing ((T.obj c.V).presheaf.stalk (g ξ)) := by
    let _ := hVnoeth
    infer_instance
  -- The generic points of the source chart lie over the codimension-zero points of `X`.
  have hgen (z : T.obj c.U) (hz : z ∈ genericPoints (T.obj c.U)) :
      localRingDimension B S hS (pointsMap B S hS (yoneda.obj c.U) c.a
        ((schemePointRepresentative B S hS c.U z).class B S hS (yoneda.obj c.U))) = 0 :=
    (localRingDimension_eq_zero_iff_exists_etale_genericPoint B S hS hX _).2
      ⟨c.U, c.a, z, (isEtale_iff_presheaf_of_yoneda B S hS c.a).mpr c.a_etale,
        ⟨schemePointRepresentative B S hS c.U z,
          schemePointRepresentative_point B S hS c.U z, rfl⟩, hz⟩
  -- Quasi-finiteness of the morphism of charts at a point, from quasi-finiteness of `f` at the
  -- point below it.
  have hqf (z : T.obj c.U) (hz : IsQuasiFiniteAt B S hS f
      (pointsMap B S hS (yoneda.obj c.U) c.a
        ((schemePointRepresentative B S hS c.U z).class B S hS (yoneda.obj c.U)))) :
      quasiFiniteAt g z := by
    have := (isQuasiFiniteAt_iff_forall_quasiFiniteAt_chart B S hS hX hY f hf _).mp hz
      (chartAtSchemePoint B S hS c z)
    rwa [chartAtSchemePoint_sourcePoint] at this
  -- The residue field extension of the morphism of charts at a point, from the transcendence
  -- degree of `f` at the point below it.
  have halg (z : T.obj c.U) (hz : HasTranscendenceDegreeAt B S hS f
      (pointsMap B S hS (yoneda.obj c.U) c.a
        ((schemePointRepresentative B S hS c.U z).class B S hS (yoneda.obj c.U))) 0) :
      let := (g.residueFieldMap z).hom.toAlgebra
      Algebra.IsAlgebraic ((T.obj c.V).residueField (g z)) ((T.obj c.U).residueField z) := by
    refine isAlgebraic_residueField_of_hasResidueFieldTranscendenceDegree_zero g z ?_
    have hchart := hz (chartAtSchemePoint B S hS c z)
    rwa [chartAtSchemePoint_sourcePoint] at hchart
  refine quasiFiniteAt_of_target_stalk_dimension_le_one g (g ξ) hstalk hdim ?_ ξ rfl
  rcases hgeneric with h1 | h2 | h3 | h4
  · exact Or.inl fun η hη ↦ halg η (h1 _ (hgen η hη))
  · -- Specialization in the target chart is carried to specialization in `|Y|`.
    refine Or.inr (Or.inl fun η hη hspec ↦ halg η (h2 _ (hgen η hη) ?_))
    have hcont : Continuous fun z : T.obj c.V ↦ pointsMap B S hS (yoneda.obj c.V) c.b
        ((schemePointRepresentative B S hS c.V z).class B S hS (yoneda.obj c.V)) := by
      simp_rw [← schemePointsHomeomorph_symm_eq_class]
      exact (continuous_pointsMap B S hS c.b).comp
        (schemePointsHomeomorph B S hS c.V).symm.continuous
    have hcη : ChartPoint B S hS c.V c.b (g η)
        (pointsMap B S hS X f (pointsMap B S hS (yoneda.obj c.U) c.a
          ((schemePointRepresentative B S hS c.U η).class B S hS (yoneda.obj c.U)))) := by
      have hc' := chartPoint_map_sourcePoint B S hS (chartAtSchemePoint B S hS c η)
      rwa [chartAtSchemePoint_sourcePoint] at hc'
    have hmap := hspec.map hcont
    rwa [pointsMap_schemePointRepresentative_class_eq B S hS c.V c.b (g ξ) y hchartY,
      pointsMap_schemePointRepresentative_class_eq B S hS c.V c.b (g η) _ hcη] at hmap
  · exact Or.inr (Or.inr (Or.inl fun η hη ↦ hqf η (h3 _ (hgen η hη))))
  · refine Or.inr (Or.inr (Or.inr ⟨hVnoeth, ?_⟩))
    -- The chart map on points is open, so the preimage of a dense set is dense.
    have hopen : IsOpenMap (pointsMap B S hS (yoneda.obj c.U) c.a) :=
      isOpenMap_pointsMap_of_isEtale B S hS c.a (isAlgebraicSpace_yoneda B S hS c.U) hX
        ((isEtale_iff_presheaf_of_yoneda B S hS c.a).mpr c.a_etale)
    have hdense := h4.preimage hopen
    have himage : (schemePointsHomeomorph B S hS c.U).symm ⁻¹'
        (pointsMap B S hS (yoneda.obj c.U) c.a ⁻¹'
          {x : points B S hS X | IsQuasiFiniteAt B S hS f x}) ⊆
        {z : T.obj c.U | quasiFiniteAt g z} := by
      intro z hz
      refine hqf z ?_
      rw [← schemePointsHomeomorph_symm_eq_class]
      exact hz
    exact (hdense.preimage (schemePointsHomeomorph B S hS c.U).symm.isOpenMap).mono himage

end Space

end AlgebraicGeometry

end

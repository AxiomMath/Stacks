module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaHub.EtaleLocalRingHub
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaHub.GenericStalkEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.AffineRefinementOfNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.OrderOfVanishingEtaleChart
public import StacksFrontier.RingTheory.HenselizationUniverse.Basic

/-!
# The comparison map of Stacks 0EMZ does not depend on the chart

Let `X` be a decent algebraic space, let `x` be a point of it and let `x̄` be a geometric point
lying over `x`. The map `𝒪^h_{X, x} → 𝒪_{X, x̄}` of Stacks 0EMZ is produced by the universal
property of the henselization, Stacks 04GS, over the local ring of *one* elementary étale
neighbourhood of `x`: at the generic point of a prime divisor
`AlgebraicGeometry.Space.PrimeDivisor.henselianToEtaleLocalRing` uses the chosen chart
`AlgebraicGeometry.Space.PrimeDivisor.genericChart`, and both
`AlgebraicGeometry.Space.PrimeDivisor.henselianToEtaleLocalRing_stalkToHenselianLocalRing` and
the uniqueness `AlgebraicGeometry.Space.PrimeDivisor.eq_henselianToEtaleLocalRing` are stated
there.

This file shows that the map lies over the local ring of *every* elementary étale neighbourhood
of `x`. That is what a consumer holding a chart it did not choose needs — for instance the chart
square of `AlgebraicGeometry.Space.exists_henselianLocalRingHom_chartSquare`, whose étale chart
of `X` is existentially quantified and cannot be forced to be the chosen one.

## Main results

* `AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.liftGeometricPoint_comp`: the chosen lift
  of a geometric point to the scheme of an elementary étale neighbourhood is natural in the
  neighbourhood. This is uniqueness of the factorization through the residue-field point,
  Stacks 0H2X, which is what an elementary étale neighbourhood supplies beyond étaleness.
* `AlgebraicGeometry.Space.chartStalkToEtaleLocalRing_neighborhoodStalkMap`: the canonical map
  of Stacks 05VP is natural in the elementary étale neighbourhood.
* `AlgebraicGeometry.Space.exists_isLocalHom_henselianLocalRing_to_etaleLocalRing`: over the
  local ring of an arbitrary elementary étale neighbourhood of `x` there is a local homomorphism
  `𝒪^h_{X, x} → 𝒪_{X, x̄}` extending the canonical map of Stacks 05VP.
* `AlgebraicGeometry.Space.PrimeDivisor.henselianToEtaleLocalRing_stalkToHenselianLocalRing_chart`:
  **the chart independence.** At the generic point of a prime divisor the map of Stacks 0EMZ
  lies over the local ring of every elementary étale neighbourhood.

## Implementation notes

A *common refinement suffices*, and nothing stronger is needed: neither the equalizing half of
Stacks 0BGV nor affineness of the refinement is used. The argument is the one of
`AlgebraicGeometry.Space.PrimeDivisor.neighborhoodTotalFractionRingToGeneric_pullback_eq` for the
embedding of Stacks 0ENK. Given a neighbourhood `V` and the chosen chart `U₀`, take a common
refinement `W` (Stacks 0BGV,
`AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.exists_cone_objs`) with `a : W ⟶ U₀` and
`b : W ⟶ V`, and let `k : 𝒪^h_{X, ξ} → 𝒪_{X, x̄}` be the homomorphism Stacks 04GS produces over
`𝒪_{W, w}`. Both the map of Stacks 0EMY
(`AlgebraicGeometry.Space.stalkToHenselianLocalRing_naturality`) and the map of Stacks 05VP are
natural in the neighbourhood, so `k` lies over `𝒪_{U₀, u₀}` along `a`; the uniqueness statement at
`U₀` then gives `k = ` the map of Stacks 0EMZ, and reading the same naturality along `b` gives the
conclusion at `V`.

Two notes in this library asserting that cofilteredness of the elementary étale neighbourhoods,
Stacks 0BGV, is unavailable here are **false**: it is
`AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.exists_cone_objs` together with
`AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.exists_cone_maps`,
`isCofilteredOrEmpty` and `isCofiltered_of_nonempty`
(`StacksFrontier/AlgebraicGeometry/Spaces/Decent/ElementaryEtaleNeighborhoodCofiltered.lean`), and
in the stronger form with the refinement taken affine it is
`AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.exists_affine_cone_objs`
(`StacksFrontier/AlgebraicGeometry/Spaces/Decent/AffineRefinementOfNeighborhood.lean`). The notes
are in base files and are left in place; one of them is in the references list of
`StacksFrontier/AlgebraicGeometry/Spaces/Chow/FlatPullbackOrderOfVanishing.lean`.

The naturality of Stacks 05VP is phrased for an opaque pair `(V, f)` of a neighbourhood and a
morphism rather than for a constructed chart square: the fields of a constructed square are
choice terms built from étaleness proofs, which the elaborator unfolds on every definitional
check.

## References

* [Stacks Project, Tag 04GS](https://stacks.math.columbia.edu/tag/04GS)
* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 0BGV](https://stacks.math.columbia.edu/tag/0BGV)
* [Stacks Project, Tag 0EMY](https://stacks.math.columbia.edu/tag/0EMY)
* [Stacks Project, Tag 0EMZ](https://stacks.math.columbia.edu/tag/0EMZ)
* [Stacks Project, Tag 0H2X](https://stacks.math.columbia.edu/tag/0H2X)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
  (x : points B S hS X)

namespace ElementaryEtaleNeighborhood

/-- The chosen lift of a geometric point to the scheme of an elementary étale neighbourhood is
natural in the neighbourhood. -/
theorem liftGeometricPoint_comp
    {V U : ElementaryEtaleNeighborhood B S hS X hX x} (f : V ⟶ U)
    (xbar : GeometricPoint B S hS X) (hxbar : xbar.LiesOver x) :
    V.liftGeometricPoint xbar hxbar ≫ f.hom = U.liftGeometricPoint xbar hxbar := by
  have hg : (V.liftResidueField xbar hxbar ≫ neighborhoodResidueFieldMap B S hS X hX x f) ≫
      U.fromResidueField = V.liftGeometricPoint xbar hxbar ≫ f.hom := by
    rw [Category.assoc, neighborhoodResidueFieldMap_comp, liftGeometricPoint, Category.assoc]
  have hval : X.map (V.liftResidueField xbar hxbar ≫
        neighborhoodResidueFieldMap B S hS X hX x f).op
      (neighborhoodFieldPoint B S hS X hX x U).value = xbar.val.value := by
    calc X.map (V.liftResidueField xbar hxbar ≫
            neighborhoodResidueFieldMap B S hS X hX x f).op
          (neighborhoodFieldPoint B S hS X hX x U).value
        = yonedaEquiv (yoneda.map (V.liftResidueField xbar hxbar ≫
            neighborhoodResidueFieldMap B S hS X hX x f) ≫
            yoneda.map U.fromResidueField ≫ U.toSpace) := yonedaEquiv_naturality _ _
      _ = yonedaEquiv (yoneda.map (V.liftGeometricPoint xbar hxbar) ≫ V.toSpace) := by
          rw [← Category.assoc, ← yoneda.map_comp, hg, yoneda.map_comp, Category.assoc, f.over]
      _ = xbar.val.value := by
          rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
          exact V.toSpace_liftGeometricPoint xbar hxbar
  have key : V.liftResidueField xbar hxbar ≫ neighborhoodResidueFieldMap B S hS X hX x f =
      U.liftResidueField xbar hxbar :=
    (FieldValuedPoint.existsUnique_factor_of_class_eq_of_mono B S hS X hX
      (neighborhoodFieldPoint B S hS X hX x U) xbar.val
      ((neighborhoodFieldPoint_class B S hS X hX x U).trans hxbar.symm)).unique hval
      (U.map_liftResidueField xbar hxbar)
  calc V.liftGeometricPoint xbar hxbar ≫ f.hom
      = V.liftResidueField xbar hxbar ≫
          (neighborhoodResidueFieldMap B S hS X hX x f ≫ U.fromResidueField) := by
        rw [liftGeometricPoint, Category.assoc, neighborhoodResidueFieldMap_comp]
    _ = U.liftGeometricPoint xbar hxbar := by
        rw [← Category.assoc, key, liftGeometricPoint]

end ElementaryEtaleNeighborhood

/-- Reading the canonical map of Stacks 05VP on the stalk at one spelling of the chart point or
at another gives the same map, up to the identification of the two stalks. -/
theorem chartStalkToEtaleLocalRing_stalkCongr {xbar : GeometricPoint B S hS X}
    (N : SmallEtaleNeighborhood xbar) {p q : chartScheme N.chart}
    (hp : chartPoint B S hS X N = p) (h : p = q)
    (r : (chartScheme N.chart).presheaf.stalk p) :
    chartStalkToEtaleLocalRing B S hS hX N (hp.trans h)
        (((chartScheme N.chart).presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom r) =
      chartStalkToEtaleLocalRing B S hS hX N hp r := by
  subst h
  simp [chartStalkToEtaleLocalRing, TopCat.Presheaf.stalkCongr]

/-- **The canonical map of Stacks 05VP is compatible with a morphism of charts.** Read on the
stalk at a chosen spelling `p` of the chart point, the map of Stacks 05VP precomposed with the
stalk map of a morphism of charts is the map of Stacks 05VP of the target chart, which carries
the image of `p` as its chart point. -/
theorem chartStalkToEtaleLocalRing_stalkMap {xbar : GeometricPoint B S hS X}
    (N : SmallEtaleNeighborhood xbar) (C : SmallEtale B S hS X)
    (g : N.chart.obj.left ⟶ C.obj.left)
    (hcomm : N.chart.obj.hom ≫ 𝟙 X = yoneda.map g ≫ C.obj.hom)
    {p : chartScheme N.chart} (hp : chartPoint B S hS X N = p)
    (hq : chartPoint B S hS X (targetNeighborhood B S hS N C g hcomm) =
      ((BigFppfOver.toScheme B S hS).map g).base p)
    (r : (chartScheme C).presheaf.stalk (((BigFppfOver.toScheme B S hS).map g).base p)) :
    chartStalkToEtaleLocalRing B S hS hX N hp
        ((((BigFppfOver.toScheme B S hS).map g).stalkMap p).hom r) =
      chartStalkToEtaleLocalRing B S hS hX (targetNeighborhood B S hS N C g hcomm) hq r := by
  subst hp
  have h := RingHom.congr_fun
    (chartLocalRingToEtaleLocalRing_comp_stalkMap B S hS X hX N C g hcomm) r
  rw [RingHom.comp_apply] at h
  rw [chartStalkToEtaleLocalRing_rfl]
  refine h.trans ?_
  exact (RingHom.congr_fun
    (chartStalkToEtaleLocalRing_rfl B S hS hX (targetNeighborhood B S hS N C g hcomm)) r).symm

/-- **The canonical map of Stacks 05VP is natural in the elementary étale neighbourhood.** For a
morphism `f : V ⟶ U` of elementary étale neighbourhoods of `x` and a geometric point `x̄` over
`x`, the map `𝒪_{U, u} → 𝒪_{X, x̄}` of Stacks 05VP is the map `𝒪_{V, v} → 𝒪_{X, x̄}` precomposed
with the homomorphism of local rings induced by `f`. -/
theorem chartStalkToEtaleLocalRing_neighborhoodStalkMap
    {V U : ElementaryEtaleNeighborhood B S hS X hX x} (f : V ⟶ U)
    {xbar : GeometricPoint B S hS X} (hxbar : xbar.LiesOver x)
    (r : U.scheme.left.1.presheaf.stalk U.point) :
    chartStalkToEtaleLocalRing B S hS hX (V.smallEtaleNeighborhood xbar hxbar)
        (chartPoint_smallEtaleNeighborhood B S hS X hX V xbar hxbar)
        ((neighborhoodStalkMap B S hS X hX x f).hom r) =
      chartStalkToEtaleLocalRing B S hS hX (U.smallEtaleNeighborhood xbar hxbar)
        (chartPoint_smallEtaleNeighborhood B S hS X hX U xbar hxbar) r := by
  have hcomm : (V.smallEtaleNeighborhood xbar hxbar).chart.obj.hom ≫ 𝟙 X =
      yoneda.map f.hom ≫ U.chart.obj.hom := by
    rw [Category.comp_id]; exact f.over.symm
  set t := ((U.scheme.left.1.presheaf.stalkCongr
    (Inseparable.of_eq f.map_point.symm)).hom).hom r with ht
  have h1 := chartStalkToEtaleLocalRing_stalkMap B S hS hX
    (V.smallEtaleNeighborhood xbar hxbar) U.chart f.hom hcomm
    (chartPoint_smallEtaleNeighborhood B S hS X hX V xbar hxbar)
    (congrArg (((BigFppfOver.toScheme B S hS).map f.hom).base)
      (chartPoint_smallEtaleNeighborhood B S hS X hX V xbar hxbar)) t
  have h2 := RingHom.congr_fun (chartStalkToEtaleLocalRing_congr B S hS hX
    (W := U.chart) (ℓ₁ := V.liftGeometricPoint xbar hxbar ≫ f.hom)
    (ℓ₂ := U.liftGeometricPoint xbar hxbar)
    (targetNeighborhood B S hS (V.smallEtaleNeighborhood xbar hxbar) U.chart f.hom
      hcomm).point_comp
    (U.smallEtaleNeighborhood xbar hxbar).point_comp
    (ElementaryEtaleNeighborhood.liftGeometricPoint_comp B S hS hX x f xbar hxbar)
    (congrArg (((BigFppfOver.toScheme B S hS).map f.hom).base)
      (chartPoint_smallEtaleNeighborhood B S hS X hX V xbar hxbar))
    ((chartPoint_smallEtaleNeighborhood B S hS X hX U xbar hxbar).trans f.map_point.symm)) t
  have h3 := chartStalkToEtaleLocalRing_stalkCongr B S hS hX
    (U.smallEtaleNeighborhood xbar hxbar)
    (chartPoint_smallEtaleNeighborhood B S hS X hX U xbar hxbar) f.map_point.symm r
  exact ((h1.trans h2).trans h3)

/-! ### The map of Stacks 0EMZ at an arbitrary elementary étale neighbourhood -/

/-- **The map `𝒪^h_{X, x} → 𝒪_{X, x̄}` of Stacks 0EMZ exists over the local ring of *any*
elementary étale neighbourhood.** For an elementary étale neighbourhood `(V, v)` of a point `x`
of a decent algebraic space and a geometric point `x̄` over `x`, there is a local homomorphism
`𝒪^h_{X, x} → 𝒪_{X, x̄}` which on the image of `𝒪_{V, v}` is the canonical map of Stacks 05VP.

This is Stacks 04GS: `𝒪^h_{X, x}` is a henselization of `𝒪_{V, v}`
(`AlgebraicGeometry.Space.henselianLocalRing_isHenselization`, for *every* neighbourhood) and
`𝒪_{X, x̄}` is a henselian local `𝒪_{V, v}`-algebra along the canonical map of Stacks 05VP
(`AlgebraicGeometry.Space.isHenselization_chartStalkToEtaleLocalRing`). -/
theorem exists_isLocalHom_henselianLocalRing_to_etaleLocalRing
    (hdec : IsDecentSpace B S hS X) (V : ElementaryEtaleNeighborhood B S hS X hX x)
    {xbar : GeometricPoint B S hS X} (hxbar : xbar.LiesOver x) :
    ∃ k : (henselianLocalRing B S hS X hX x hdec : Type (u + 1)) →+*
        (etaleLocalRing B S hS X xbar : Type (u + 1)),
      letI := henselianLocalRing_isLocalRing B S hS X hX x hdec
      letI := isLocalRing_etaleLocalRing B S hS X hX xbar
      IsLocalHom k ∧
        ∀ r, k (stalkToHenselianLocalRing B S hS X hX x hdec V r) =
          chartStalkToEtaleLocalRing B S hS hX (V.smallEtaleNeighborhood xbar hxbar)
            (chartPoint_smallEtaleNeighborhood B S hS X hX V xbar hxbar) r := by
  let := henselianLocalRing_isLocalRing B S hS X hX x hdec
  let := stalkAlgebra B S hS X hX x hdec V
  let := isLocalRing_etaleLocalRing B S hS X hX xbar
  let : Algebra (V.scheme.left.1.presheaf.stalk V.point)
      (etaleLocalRing B S hS X xbar : Type (u + 1)) :=
    (chartStalkToEtaleLocalRing B S hS hX (V.smallEtaleNeighborhood xbar hxbar)
      (chartPoint_smallEtaleNeighborhood B S hS X hX V xbar hxbar)).toAlgebra
  let hH := henselianLocalRing_isHenselization B S hS X hX x hdec V
  let hR : IsHenselization (V.scheme.left.1.presheaf.stalk V.point)
      (SeparableClosure (ResidueField (V.scheme.left.1.presheaf.stalk V.point)))
      (etaleLocalRing B S hS X xbar : Type (u + 1)) :=
    isHenselization_chartStalkToEtaleLocalRing B S hS hX
      (V.smallEtaleNeighborhood xbar hxbar)
      (chartPoint_smallEtaleNeighborhood B S hS X hX V xbar hxbar)
  let : IsLocalHom (algebraMap (V.scheme.left.1.presheaf.stalk V.point)
      (henselianLocalRing B S hS X hX x hdec : Type (u + 1))) :=
    IsHenselization.isLocalHom
      (L := ResidueField (V.scheme.left.1.presheaf.stalk V.point))
  let : IsLocalHom (algebraMap (V.scheme.left.1.presheaf.stalk V.point)
      (etaleLocalRing B S hS X xbar : Type (u + 1))) :=
    IsHenselization.isLocalHom
      (L := SeparableClosure (ResidueField (V.scheme.left.1.presheaf.stalk V.point)))
  let : HenselianLocalRing (etaleLocalRing B S hS X xbar : Type (u + 1)) :=
    IsHenselization.henselian
      (L := SeparableClosure (ResidueField (V.scheme.left.1.presheaf.stalk V.point)))
      (R := V.scheme.left.1.presheaf.stalk V.point)
  obtain ⟨k, hk, -⟩ := StacksDraft.existsUnique_isLocalHom_of_indEtale
    (A := V.scheme.left.1.presheaf.stalk V.point)
    (B := (henselianLocalRing B S hS X hX x hdec : Type (u + 1)))
    (C := (etaleLocalRing B S hS X xbar : Type (u + 1)))
    (IsHenselization.ind_etale
      (L := ResidueField (V.scheme.left.1.presheaf.stalk V.point)))
    (IsHenselization.residueField_map_bijective
      (R := V.scheme.left.1.presheaf.stalk V.point)
      (Rh := (henselianLocalRing B S hS X hX x hdec : Type (u + 1)))).2
  exact ⟨k.toRingHom, ⟨fun a ha ↦ hk.map_nonunit a ha⟩, fun r ↦ k.commutes r⟩

/-- A local homomorphism over the local ring of `W` which is the canonical map of Stacks 05VP
there is also the canonical map over the local ring of every neighbourhood `U` refined by `W`. -/
private theorem map_stalkToHenselianLocalRing_eq_chartStalk
    (hdec : IsDecentSpace B S hS X) {x : points B S hS X} {xbar : GeometricPoint B S hS X}
    (hxbar : xbar.LiesOver x) {W U : ElementaryEtaleNeighborhood B S hS X hX x} (f : W ⟶ U)
    (k : (henselianLocalRing B S hS X hX x hdec : Type (u + 1)) →+*
      (etaleLocalRing B S hS X xbar : Type (u + 1)))
    (hkW : ∀ r, k (stalkToHenselianLocalRing B S hS X hX x hdec W r) =
      chartStalkToEtaleLocalRing B S hS hX (W.smallEtaleNeighborhood xbar hxbar)
        (chartPoint_smallEtaleNeighborhood B S hS X hX W xbar hxbar) r)
    (s : U.scheme.left.1.presheaf.stalk U.point) :
    k (stalkToHenselianLocalRing B S hS X hX x hdec U s) =
      chartStalkToEtaleLocalRing B S hS hX (U.smallEtaleNeighborhood xbar hxbar)
        (chartPoint_smallEtaleNeighborhood B S hS X hX U xbar hxbar) s := by
  have h1 := RingHom.congr_fun (stalkToHenselianLocalRing_naturality B S hS X hX x hdec f) s
  rw [RingHom.comp_apply] at h1
  rw [← h1, hkW]
  exact chartStalkToEtaleLocalRing_neighborhoodStalkMap B S hS hX x f hxbar s

/-- **The map of Stacks 0EMZ does not depend on the chart.** At the generic point `ξ` of a prime
divisor of a decent algebraic space, the map `𝒪^h_{X, ξ} → 𝒪_{X, x̄}` of Stacks 0EMZ — which is
pinned by lying over the local ring of the *chosen* elementary étale neighbourhood
`AlgebraicGeometry.Space.PrimeDivisor.genericChart` — lies over the local ring of *every*
elementary étale neighbourhood of `ξ`, along the canonical map of Stacks 05VP.

Two elementary étale neighbourhoods of `ξ` are refined by a common one (Stacks 0BGV,
`AlgebraicGeometry.Space.ElementaryEtaleNeighborhood.exists_cone_objs`), and a common refinement
suffices: on it Stacks 04GS produces a local homomorphism `𝒪^h_{X, ξ} → 𝒪_{X, x̄}` over its local
ring, that homomorphism lies over the local ring of the chosen chart because both the map of
Stacks 0EMY and the map of Stacks 05VP are natural in the neighbourhood, and the uniqueness
`AlgebraicGeometry.Space.PrimeDivisor.eq_henselianToEtaleLocalRing` then identifies it with the
map of Stacks 0EMZ. -/
theorem PrimeDivisor.henselianToEtaleLocalRing_stalkToHenselianLocalRing_chart
    (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)
    {xbar : GeometricPoint B S hS X} (hxbar : xbar.LiesOver (Z.genericPoint B S hS X))
    (V : ElementaryEtaleNeighborhood B S hS X hX (Z.genericPoint B S hS X))
    (r : V.scheme.left.1.presheaf.stalk V.point) :
    Z.henselianToEtaleLocalRing B S hS hX hdec hxbar
        (stalkToHenselianLocalRing B S hS X hX (Z.genericPoint B S hS X) hdec V r) =
      chartStalkToEtaleLocalRing B S hS hX (V.smallEtaleNeighborhood xbar hxbar)
        (chartPoint_smallEtaleNeighborhood B S hS X hX V xbar hxbar) r := by
  obtain ⟨W, a, b, -⟩ := ElementaryEtaleNeighborhood.exists_cone_objs B S hS X hX
    (Z.genericPoint B S hS X) (Z.genericChart B S hS hX hdec) V
  obtain ⟨k, hkloc, hkW⟩ := exists_isLocalHom_henselianLocalRing_to_etaleLocalRing B S hS hX
    (Z.genericPoint B S hS X) hdec W hxbar
  have hk : k = Z.henselianToEtaleLocalRing B S hS hX hdec hxbar :=
    Z.eq_henselianToEtaleLocalRing B S hS hX hdec hxbar k hkloc
      (map_stalkToHenselianLocalRing_eq_chartStalk B S hS hX hdec hxbar a k hkW)
  rw [← hk]
  exact map_stalkToHenselianLocalRing_eq_chartStalk B S hS hX hdec hxbar b k hkW r

end AlgebraicGeometry.Space

end

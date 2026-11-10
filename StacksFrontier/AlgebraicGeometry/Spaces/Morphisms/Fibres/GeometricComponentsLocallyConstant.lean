module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteSmallEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricComponentCount
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.GeometricComponentsLowerSemicontinuous
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.GeometricallyReduced
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperReducedGlobalFunctionsRank

/-!
# Local constancy of the number of geometric connected components of the fibres

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is proper, flat and
of finite presentation, with geometrically reduced fibres. Stacks 0E1E says that the function
`n_{X/Y} : |Y| → ℤ` counting the geometric connected components of the fibres (Stacks 0E1B,
`AlgebraicGeometry.Space.numberGeometricConnectedComponents`) is locally constant.

This file reduces it to the upper semicontinuity of `n_{X_U/U}` on the étale charts `U` of `Y`,
and identifies `n_{X/Y}` at an algebraically closed point with the dimension of the global
functions of the fibre.

## Main results

* `AlgebraicGeometry.Space.numberGeometricConnectedComponents_class_eq_finrank`: at a point
  represented by a field-valued point `p` with algebraically closed field `k`, if the fibre
  `X_k` is proper and reduced, then `n_{X/Y}` is `dim_k Γ(X_k, 𝒪)`.
* `AlgebraicGeometry.Space.isLocallyConstant_of_lowerSemicontinuous_of_etaleCharts`: a
  lower semicontinuous `ℕ∞`-valued function on `|Y|` whose pullback to every étale chart is an
  upper semicontinuous `ℕ`-valued function is locally constant.
* `AlgebraicGeometry.Space.isLocallyConstant_numberGeometricConnectedComponents_of_etaleCharts`:
  the reduction of Stacks 0E1E to its two semicontinuity inputs, read on étale charts of `Y`
  through the base change compatibility of Stacks 0E1B.
* `AlgebraicGeometry.Space.isLocallyConstant_numberGeometricConnectedComponents_of`: Stacks 0E1E
  under its own hypotheses, from the chart input of Stacks 0E0R.

## References

* [Stacks Project, Tag 0E1E](https://stacks.math.columbia.edu/tag/0E1E)
* [Stacks Project, Tag 0E1B](https://stacks.math.columbia.edu/tag/0E1B)
* [Stacks Project, Tag 0E1D](https://stacks.math.columbia.edu/tag/0E1D)
* [Stacks Project, Tag 0DMY](https://stacks.math.columbia.edu/tag/0DMY)
* [Stacks Project, Tag 0E0R](https://stacks.math.columbia.edu/tag/0E0R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The count at a geometric point is the dimension of the global functions -/

section GlobalFunctions

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **At an algebraically closed point, `n_{X/Y}` is the dimension of the global functions of
the fibre.** Let `p : Spec k ⟶ Y` be a field-valued point with `k` algebraically closed whose
fibre `X_k` is proper and reduced over `k`. Then the number of geometric connected components
of the fibres of `f` at the point of `|Y|` represented by `p` is `dim_k Γ(X_k, 𝒪_{X_k})`. -/
theorem numberGeometricConnectedComponents_class_eq_finrank (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y)
    [IsAlgClosed p.carrier]
    (z : fibreOverFieldValuedPoint B S hS f p ⟶ yoneda.obj (baseObject p.carrier B p.contained))
    (hz : IsProper B (Spec (.of p.carrier)) p.contained z)
    (hred : HasEtaleLocalProperty B (Spec (.of p.carrier)) p.contained
      (fibreOverFieldValuedPoint B S hS f p)
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced T)) :
    numberGeometricConnectedComponents B S hS f (p.class B S hS Y) =
      (Module.finrank p.carrier (globalFunctions B (Spec (.of p.carrier)) p.contained
        (fibreOverFieldValuedPoint B S hS f p)) : ℕ∞) := by
  have hF := isAlgebraicSpace_fibreOverFieldValuedPoint B S hS f hX hY p
  have := finite_connectedComponents_points_of_isProper p.carrier B p.contained _ hF z hz
  rw [finrank_globalFunctions_eq_card_connectedComponents p.carrier B p.contained _ hF z hz hred,
    numberGeometricConnectedComponents_eq B S hS hX hY f ⟨p, inferInstance⟩,
    geometricFiberComponentCount_eq_overField B S hS hX hY f p]
  change Cardinal.toENat (Cardinal.mk (ConnectedComponents
    (points B (Spec (.of p.carrier)) p.contained (fibreOverFieldValuedPoint B S hS f p)))) = _
  rw [← Nat.cast_card, Cardinal.toENat_nat]

end GlobalFunctions

/-! ### Semicontinuity on étale charts -/

section Topology

variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Local constancy from semicontinuity on étale charts.** A lower semicontinuous
`ℕ∞`-valued function `n` on the points of an algebraic space `Y` is locally constant as soon as,
on every étale chart `U` of `Y`, its pullback to the scheme `U` is (the image of) an upper
semicontinuous `ℕ`-valued function. -/
theorem isLocallyConstant_of_lowerSemicontinuous_of_etaleCharts
    (hY : IsAlgebraicSpace B S hS Y) (n : points B S hS Y → ℕ∞) (hlow : LowerSemicontinuous n)
    (hup : ∀ U : SmallEtale B S hS Y,
      ∃ β : (BigFppfOver.toScheme B S hS).obj U.obj.left → ℕ, UpperSemicontinuous β ∧
        ∀ v, n (pointsMap B S hS _ U.obj.hom
          ((schemePointsHomeomorph B S hS U.obj.left).symm v)) = (β v : ℕ∞)) :
    IsLocallyConstant n := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  obtain ⟨U, p, hp⟩ := exists_chart_point B S hS Y hY y
  obtain ⟨β, hβ, hnβ⟩ := hup U
  let e := schemePointsHomeomorph B S hS U.obj.left
  let φ : (BigFppfOver.toScheme B S hS).obj U.obj.left → points B S hS Y :=
    fun v => pointsMap B S hS _ U.obj.hom (e.symm v)
  have hφc : Continuous φ := (continuous_pointsMap B S hS U.obj.hom).comp e.symm.continuous
  have hφo : IsOpenMap φ :=
    (isOpenMap_pointsMap_of_isEtale B S hS U.obj.hom
      (isAlgebraicSpace_yoneda B S hS U.obj.left) hY
      (isEtale_hom_of_isEtaleChart B S hS U.property)).comp e.symm.isOpenMap
  let x := e p
  have hx : φ x = y := (congrArg (pointsMap B S hS _ U.obj.hom) (e.symm_apply_apply p)).trans hp
  have hle : ∀ᶠ v in 𝓝 x, β v ≤ β x := by
    filter_upwards [hβ x (β x + 1) (Nat.lt_succ_self _)] with v hv
    omega
  have hge : ∀ᶠ v in 𝓝 x, β x ≤ β v := by
    rcases Nat.eq_zero_or_pos (β x) with h0 | hpos
    · exact Filter.Eventually.of_forall fun v => by omega
    · have hlt : ((β x - 1 : ℕ) : ℕ∞) < n (φ x) := by
        rw [hnβ x]
        exact_mod_cast Nat.sub_lt hpos Nat.one_pos
      filter_upwards [hφc.continuousAt.eventually (hlow (φ x) _ hlt)] with v hv
      rw [hnβ v] at hv
      have : β x - 1 < β v := by exact_mod_cast hv
      omega
  obtain ⟨V, hVsub, hVo, hxV⟩ := mem_nhds_iff.mp (hle.and hge)
  refine Filter.mem_of_superset ((hφo V hVo).mem_nhds ⟨x, hxV, hx⟩) ?_
  rintro y' ⟨v, hv, rfl⟩
  change n (φ v) = n y
  rw [← hx, hnβ v, hnβ x, le_antisymm (hVsub hv).1 (hVsub hv).2]

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The reduction of Stacks 0E1E to semicontinuity on étale charts.** The number of geometric
connected components of the fibres of `f : X ⟶ Y` is locally constant on `|Y|` as soon as it is
lower semicontinuous and, for every étale chart `U` of `Y`, the same function for the base
change `X ×_Y U ⟶ U` is, on the scheme `U`, an upper semicontinuous `ℕ`-valued function. -/
theorem isLocallyConstant_numberGeometricConnectedComponents_of_etaleCharts
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hlow : LowerSemicontinuous (numberGeometricConnectedComponents B S hS f))
    (hup : ∀ U : SmallEtale B S hS Y,
      ∃ β : (BigFppfOver.toScheme B S hS).obj U.obj.left → ℕ, UpperSemicontinuous β ∧
        ∀ v, numberGeometricConnectedComponents B S hS (pullback.snd f U.obj.hom)
          ((schemePointsHomeomorph B S hS U.obj.left).symm v) = (β v : ℕ∞)) :
    IsLocallyConstant (numberGeometricConnectedComponents B S hS f) := by
  refine isLocallyConstant_of_lowerSemicontinuous_of_etaleCharts B S hS hY _ hlow fun U => ?_
  obtain ⟨β, hβ, hnβ⟩ := hup U
  refine ⟨β, hβ, fun v => ?_⟩
  rw [← hnβ v, numberGeometricConnectedComponents_baseChange B S hS hX hY
    (isAlgebraicSpace_yoneda B S hS U.obj.left) f U.obj.hom]
  rfl

/-- **Stacks 0E1E, from the upper semicontinuity input of Stacks 0E0R.** Let `f : X ⟶ Y` be a
morphism of algebraic spaces over `S` which is proper, flat and of finite presentation, with
geometrically reduced fibres. The function `n_{X/Y}` counting the geometric connected
components of the fibres (Stacks 0E1B) is locally constant, given

* `hup`, the input supplied by Stacks 0E0R at `i = 0`: on every étale chart `U` of `Y`, the
  function `n_{X_U/U}` is an upper semicontinuous `ℕ`-valued function on the scheme `U`. -/
theorem isLocallyConstant_numberGeometricConnectedComponents_of
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsProper B S hS f) (hfl : IsFlat B S hS f) (hfp : IsFinitePresentation B S hS f)
    (_hred : ∀ y, IsGeometricallyReducedFibreAt B S hS f hX hY y)
    (hup : ∀ U : SmallEtale B S hS Y,
      ∃ β : (BigFppfOver.toScheme B S hS).obj U.obj.left → ℕ, UpperSemicontinuous β ∧
        ∀ v, numberGeometricConnectedComponents B S hS (pullback.snd f U.obj.hom)
          ((schemePointsHomeomorph B S hS U.obj.left).symm v) = (β v : ℕ∞)) :
    IsLocallyConstant (numberGeometricConnectedComponents B S hS f) :=
  isLocallyConstant_numberGeometricConnectedComponents_of_etaleCharts B S hS hX hY f
    (lowerSemicontinuous_numberGeometricConnectedComponents B S hS hX hY f hf hfl hfp) hup

end Topology

end AlgebraicGeometry.Space

end

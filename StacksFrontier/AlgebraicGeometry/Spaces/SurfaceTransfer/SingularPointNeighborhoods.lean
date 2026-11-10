module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.NormalFibre
public import StacksFrontier.AlgebraicGeometry.NormalizationQuotient.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleChartNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.QuasiCompactMonomorphicPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Specializations
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsAtClosedPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalIntegralEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalSurfaceSingularPointsFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.StalkBaseChangeNormalCompletion
public import StacksFrontier.RingTheory.DiscreteValuationRing.TFAE
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Elementary étale neighbourhoods of the singular points of a normal surface

Let `X` be an integral algebraic space over a scheme `S`, normal, with locally Noetherian étale
charts and of dimension at most two, with finitely many singular points, at each of which the
completion of the henselian local ring is normal. Then the singular points are closed, and they
admit a family of elementary étale neighbourhoods `(Vᵢ, vᵢ)` in the sense of Section 0BH9 of the
Stacks project, each an affine normal integral Noetherian scheme whose only singular point is
`vᵢ`, a point of local dimension two at which the completed local ring is normal.

This is the step "choose a collection of elementary étale neighbourhoods `(Vᵢ, vᵢ) ⟶ (Y, yᵢ)` as
in Section 0BH9" of the proof of (4) `⇒` (3) of [Stacks, Tag 0BHY].

## The argument

* A normal Noetherian local domain of dimension at most one is regular, so a singular point has
  local dimension at least two, and at most two since the dimension is at most two
  (`AlgebraicGeometry.Space.two_le_ringKrullDim_stalk_of_not_isRegularAt`).
* A singular point is closed: a proper specialization of it lifts to an étale chart by
  [Stacks, Tag 03K2], and on a chart of dimension at most two a point of local dimension two
  has no proper specialization (`AlgebraicGeometry.Space.isClosed_singleton_of_not_isRegularAt`).
* At a singular point `x` an affine elementary étale neighbourhood with a single point over `x`
  ([Stacks, Tag 0BBP]) contains a normal integral affine open through its distinguished point
  ([Stacks, Tag 0AYH]); a basic open of it avoiding the closed preimage of the other singular
  points is the neighbourhood. Its regular points are those over regular points of `X`, so its
  only singular point is the distinguished one.
* The henselian local ring at `x` is a henselization of the local ring of the neighbourhood, so
  the two have isomorphic completions.

## Main results

* `AlgebraicGeometry.Space.two_le_ringKrullDim_of_not_isRegularLocalRing`
* `AlgebraicGeometry.Space.isClosed_singleton_of_not_isRegularAt`
* `AlgebraicGeometry.Space.exists_closedPointNeighborhoods_singularPoints`

## References

* [Stacks Project, Tag 0BHY](https://stacks.math.columbia.edu/tag/0BHY)
* [Stacks Project, Tag 0BH9](https://stacks.math.columbia.edu/tag/0BH9)
* [Stacks Project, Tag 0BBP](https://stacks.math.columbia.edu/tag/0BBP)
* [Stacks Project, Tag 03K2](https://stacks.math.columbia.edu/tag/03K2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- **A non-regular normal local ring has dimension at least two.** A Noetherian local normal
domain of dimension at most one is a field or a discrete valuation ring, hence regular. -/
@[ega "IV 5.8.6" "(i), special case", ega "IV 7.9.1" "regularity"]
theorem two_le_ringKrullDim_of_not_isRegularLocalRing (R : Type u) [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] [IsDomain R] [IsIntegrallyClosed R]
    (h : ¬ IsRegularLocalRing R) : 2 ≤ ringKrullDim R := by
  by_contra hlt
  have hdim : ringKrullDim R ≤ 1 := by
    obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp (ne_of_gt (lt_of_lt_of_le
      (WithBot.bot_lt_coe (0 : ℕ∞)) (ringKrullDim_nonneg_of_nontrivial (R := R))))
    rw [← hd] at hlt ⊢
    have hlt' : d < 1 + 1 := by
      rw [one_add_one_eq_two]
      exact WithBot.coe_lt_coe.mp (not_le.mp hlt)
    exact WithBot.coe_le_coe.mpr (Order.le_of_lt_add_one hlt')
  apply h
  by_cases hfield : IsField R
  · let : Field R := hfield.toField
    infer_instance
  · have : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr hdim
    have hdimone : ringKrullDim R = 1 :=
      (ringKrullDim_eq_one_iff_of_isLocalRing_isDomain).2 ⟨hfield, fun a ha => by
        rw [Ideal.radical_eq_sInf]
        refine le_sInf fun J hJ => ?_
        have haJ : a ∈ J := hJ.1 (Ideal.subset_span (by simp))
        have hJne : J ≠ ⊥ := fun he => ha (by simpa [he] using haJ)
        exact (IsLocalRing.eq_maximalIdeal (hJ.2.isMaximal_of_ne_bot hJne)).symm.le⟩
    have hinput : IsNoetherianRing R ∧ IsLocalRing R ∧ IsDomain R ∧
        IsIntegrallyClosed R ∧ ringKrullDim R = 1 :=
      ⟨inferInstance, inferInstance, inferInstance, inferInstance, hdimone⟩
    have hout : IsRegularLocalRing R ∧ ringKrullDim R = 1 :=
      ((isDiscreteValuationRing_tfae R).out 5 3).mp hinput
    exact hout.1

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An étale chart has dimension at most that of the space.** The local dimension of a chart
at each of its points is the dimension of the space at the image point (Stacks 04N5). -/
theorem topologicalKrullDim_le_dimension_of_etale {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X)
    (ha : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a) :
    topologicalKrullDim ((BigFppfOver.toScheme B S hS).obj U) ≤ dimension B S hS X hX := by
  have hsup : topologicalKrullDim ((BigFppfOver.toScheme B S hS).obj U) =
      ⨆ u, topologicalKrullDimAt ((BigFppfOver.toScheme B S hS).obj U) u := by
    simpa only [TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim] using
      TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim _
  rw [hsup]
  refine iSup_le fun u => ?_
  rw [← schemePointRepresentative_point B S hS U u, ← dimensionAtPoint_eq_of_etale_chart B S hS X
    hX _ U a ha (schemePointRepresentative B S hS U u) rfl]
  exact le_iSup (dimensionAtPoint B S hS X hX) _

/-- **Regularity of a chart at a point is regularity of the space at its image.** -/
theorem isRegularLocalRing_stalk_iff_isRegularAt {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X)
    (ha : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a)
    (w : points B S hS (yoneda.obj U)) :
    IsRegularLocalRing (((BigFppfOver.toScheme B S hS).obj U).presheaf.stalk
        (pointsToScheme B S hS U w)) ↔
      IsRegularAt B S hS X (pointsMap B S hS (yoneda.obj U) a w) := by
  obtain ⟨p, rfl⟩ := Quot.exists_rep w
  exact ⟨fun h => (isRegularAt_iff_exists_etale_chart B S hS X hX _).mpr ⟨U, a, ha, p, rfl, h⟩,
    fun h => h U a ha p rfl⟩

/-- **A singular point of a normal space of dimension at most two has local dimension two at
every chart point above it.** -/
theorem ringKrullDim_stalk_eq_two_of_not_isRegularAt {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hXnormal : HasEtaleLocalProperty B S hS X
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsNormal T))
    (hXnoeth : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hXdim : dimension B S hS X hX ≤ 2) (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X)
    (ha : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) a)
    (w : points B S hS (yoneda.obj U))
    (hw : ¬ IsRegularAt B S hS X (pointsMap B S hS (yoneda.obj U) a w)) :
    ringKrullDim (((BigFppfOver.toScheme B S hS).obj U).presheaf.stalk
      (pointsToScheme B S hS U w)) = 2 := by
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U) :=
    (exists_atlas_iff_forall_etale B S hS X _ hX).mp hXnoeth U a ha
  have : _root_.AlgebraicGeometry.IsNormal ((BigFppfOver.toScheme B S hS).obj U) :=
    (exists_atlas_iff_forall_etale B S hS X _ hX).mp hXnormal U a ha
  have : IsIntegrallyClosed (((BigFppfOver.toScheme B S hS).obj U).presheaf.stalk
      (pointsToScheme B S hS U w)) := IsNormal.stalk_normal _
  exact le_antisymm
    ((Stacks.AlgebraicGeometry.NormalizationQuotient.ringKrullDim_stalk_le_topologicalKrullDim
      _ _).trans ((topologicalKrullDim_le_dimension_of_etale B S hS hX U a ha).trans hXdim))
    (two_le_ringKrullDim_of_not_isRegularLocalRing _
      (mt (isRegularLocalRing_stalk_iff_isRegularAt B S hS hX U a ha w).mp hw))

/-- **Singular points are closed.** In a decent normal algebraic space of dimension at most two
with locally Noetherian étale charts, every singular point is a closed point: a proper
specialization of it would lift to an étale chart (Stacks 03K2), where the point above it has a
local ring of dimension two in a scheme of dimension at most two, so has no proper
specialization. -/
theorem isClosed_singleton_of_not_isRegularAt {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hdec : IsDecentSpace B S hS X)
    (hXnormal : HasEtaleLocalProperty B S hS X
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsNormal T))
    (hXnoeth : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hXdim : dimension B S hS X hX ≤ 2) (y : points B S hS X)
    (hy : ¬ IsRegularAt B S hS X y) : IsClosed ({y} : Set (points B S hS X)) := by
  refine isClosed_of_closure_subset fun z hz => ?_
  obtain ⟨U, a, has, hae⟩ := hX.exists_atlas
  obtain ⟨w, hw⟩ := (surjective_iff_surjective_pointsMap B S hS X hX U a).mp has z
  have hfin := hasFiniteChartFibersAtEveryPoint_of_hasFiniteChartAndRelationFibers B S hS X
    ((isDecentSpace_iff_hasFiniteChartAndRelationFibersAtEveryPoint B S hS X hX).mp hdec)
  obtain ⟨w', hw'w, hw'⟩ := exists_specializes_pointsMap_eq_of_isEtale B S hS hX
    (specializes_iff_mem_closure.mpr hz)
    (hfin y) U a hae w hw
  have hclosed := AlgebraicGeometry.isClosed_singleton_of_two_le_ringKrullDim_stalk _
    ((topologicalKrullDim_le_dimension_of_etale B S hS hX U a hae).trans hXdim) _
    (ringKrullDim_stalk_eq_two_of_not_isRegularAt B S hS hX hXnormal hXnoeth hXdim U a hae
      w' (hw' ▸ hy)).symm.le
  have heq : pointsToScheme B S hS U w = pointsToScheme B S hS U w' :=
    hclosed.closure_subset (specializes_iff_mem_closure.mp
      (hw'w.map (schemePointsHomeomorph B S hS U).continuous))
  rw [← hw, ← hw', injective_pointsToScheme B S hS U heq]
  rfl

/-- **Points of an open restriction.** The image in `X` of a point of the restriction of an
elementary étale neighbourhood `E` to an open `W` is the image of its image in `E`. -/
theorem pointsMap_openRestrictionNeighborhood_toSpace {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (x : points B S hS X)
    (E : ElementaryEtaleNeighborhood B S hS X hX x) (W : E.scheme.left.1.Opens) (hW : E.point ∈ W)
    (y : points B S hS (yoneda.obj (openRestrictionNeighborhood B S hS X hX x E W hW).scheme)) :
    pointsMap B S hS _ (openRestrictionNeighborhood B S hS X hX x E W hW).toSpace y =
      pointsMap B S hS _ E.toSpace
        (pointsMap B S hS _ (yoneda.map (openRestrictionMap B S hS X hX x E W)) y) := by
  change pointsMap B S hS _
    (yoneda.map (openRestrictionMap B S hS X hX x E W) ≫ E.toSpace) y = _
  rw [pointsMap_comp]
  rfl

/-- **Uniqueness of the point over `x` in an open restriction.** If an elementary étale
neighbourhood `E` of `x` has a single point over `x`, so does its restriction to an open `W`. -/
theorem eq_presheafPoint_of_openRestrictionNeighborhood {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (x : points B S hS X)
    (E : ElementaryEtaleNeighborhood B S hS X hX x) (W : E.scheme.left.1.Opens) (hW : E.point ∈ W)
    (huniq : ∀ y : points B S hS (yoneda.obj E.scheme),
      pointsMap B S hS (yoneda.obj E.scheme) E.toSpace y = x →
        y = presheafPoint B S hS E.scheme E.point E.residueField_contained)
    (y : points B S hS (yoneda.obj (openRestrictionNeighborhood B S hS X hX x E W hW).scheme))
    (hy : pointsMap B S hS _ (openRestrictionNeighborhood B S hS X hX x E W hW).toSpace y = x) :
    y = presheafPoint B S hS (openRestrictionNeighborhood B S hS X hX x E W hW).scheme
      (openRestrictionNeighborhood B S hS X hX x E W hW).point
      (openRestrictionNeighborhood B S hS X hX x E W hW).residueField_contained := by
  rw [pointsMap_openRestrictionNeighborhood_toSpace] at hy
  have hz := congrArg (pointsToScheme B S hS E.scheme) (huniq _ hy)
  rw [pointsToScheme_pointsMap_yoneda, pointsToScheme_presheafPoint] at hz
  apply injective_pointsToScheme B S hS _
  rw [pointsToScheme_presheafPoint]
  exact W.ι.isOpenEmbedding.injective hz

/-- The structure morphism of an elementary étale neighbourhood is an étale chart. -/
private theorem presheaf_etale_toSpace_of_elementaryEtaleNeighborhood
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X) {x : points B S hS X}
    (E : ElementaryEtaleNeighborhood B S hS X hX x) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) E.toSpace :=
  (isEtale_iff_presheaf_of_yoneda B S hS E.toSpace).mp E.etale_toSpace

/-- An étale local property of `X` holds for the scheme of an elementary étale neighbourhood. -/
private theorem of_hasEtaleLocalProperty_elementaryEtaleNeighborhood
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {P : ObjectProperty Scheme.{u}} [P.IsLocal Scheme.etalePrecoverage]
    (hP : HasEtaleLocalProperty B S hS X P) {x : points B S hS X}
    (E : ElementaryEtaleNeighborhood B S hS X hX x) : P E.scheme.left.1 :=
  (exists_atlas_iff_forall_etale B S hS X _ hX).mp hP _ _
    (presheaf_etale_toSpace_of_elementaryEtaleNeighborhood B S hS hX E)

/-- **One neighbourhood.** At a singular point `x` of `X` and a finite set `T` of closed points
not containing `x`, there is an elementary étale neighbourhood of `x` whose scheme is affine,
integral, normal and locally Noetherian, which carries a single point over `x` and no point over
`T`. -/
theorem exists_elementaryEtaleNeighborhood_avoiding {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hXint : IsIntegralSpace B S hS X)
    (hXnormal : HasEtaleLocalProperty B S hS X
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsNormal T))
    (hXnoeth : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (x : points B S hS X) (T : Set (points B S hS X)) (hT : T.Finite)
    (hTc : ∀ t ∈ T, IsClosed ({t} : Set (points B S hS X))) (hxT : x ∉ T) :
    ∃ E : ElementaryEtaleNeighborhood B S hS X hX x,
      IsAffine E.scheme.left.1 ∧ IsIntegral E.scheme.left.1 ∧
      _root_.AlgebraicGeometry.IsNormal E.scheme.left.1 ∧
      IsLocallyNoetherian E.scheme.left.1 ∧
      (∀ y : points B S hS (yoneda.obj E.scheme),
        pointsMap B S hS (yoneda.obj E.scheme) E.toSpace y = x →
          y = presheafPoint B S hS E.scheme E.point E.residueField_contained) ∧
      (∀ y : points B S hS (yoneda.obj E.scheme),
        pointsMap B S hS (yoneda.obj E.scheme) E.toSpace y ∉ T) := by
  classical
  obtain ⟨E, hEaff, huniq, -⟩ := exists_affine_elementaryEtaleNeighborhood' B S hS hX
    (hXint.isDecentSpace B S hS X) x
  have hEet := presheaf_etale_toSpace_of_elementaryEtaleNeighborhood B S hS hX E
  let Es := E.scheme.left.1
  have : _root_.AlgebraicGeometry.IsNormal Es :=
    of_hasEtaleLocalProperty_elementaryEtaleNeighborhood B S hS hX hXnormal E
  obtain ⟨W₀, hW₀, hW₀aff, -, hW₀int⟩ :=
    exists_isAffineOpen_isNormal_isIntegral_of_isAffine_etaleChart B S hS hX hXnormal hXint
      E.scheme hEaff E.toSpace hEet E.point
  let e := schemePointsHomeomorph B S hS E.scheme
  let π : Es → points B S hS X := fun w => pointsMap B S hS _ E.toSpace (e.symm w)
  have hπpt (z : points B S hS (yoneda.obj E.scheme)) :
      π (pointsToScheme B S hS E.scheme z) = pointsMap B S hS _ E.toSpace z := by
    simp only [π]
    rw [← schemePointsHomeomorph_apply, e.symm_apply_apply]
  have hTclosed : IsClosed T := Set.biUnion_of_singleton T ▸ hT.isClosed_biUnion hTc
  let C : Set Es := π ⁻¹' T
  have hptx : π E.point = x := by
    rw [← pointsToScheme_presheafPoint B S hS E.scheme E.point E.residueField_contained, hπpt,
      E.map_point]
  have hptC : E.point ∉ C := fun h => hxT (hptx ▸ h)
  let O : Es.Opens := ⟨Cᶜ, (hTclosed.preimage
    ((continuous_pointsMap B S hS E.toSpace).comp e.symm.continuous)).isOpen_compl⟩
  obtain ⟨f, hfle, hfmem⟩ := hW₀aff.exists_basicOpen_le (V := O) ⟨E.point, hptC⟩ hW₀
  let W : Es.Opens := Es.basicOpen f
  let E' := openRestrictionNeighborhood B S hS X hX x E W hfmem
  have hpts (y : points B S hS (yoneda.obj E'.scheme)) :
      pointsMap B S hS _ E'.toSpace y =
        π (W.ι (pointsToScheme B S hS E'.scheme y)) := by
    rw [pointsMap_openRestrictionNeighborhood_toSpace B S hS hX x E W hfmem y, ← hπpt,
      pointsToScheme_pointsMap_yoneda]
    rfl
  have : Nonempty W.toScheme := ⟨⟨E.point, hfmem⟩⟩
  refine ⟨E', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hW₀aff.basicOpen f : IsAffineOpen W)
  · have : Nonempty E'.scheme.left.1 := ⟨E'.point⟩
    have : IsIntegral W₀.toScheme := hW₀int
    exact isIntegral_of_isOpenImmersion (Es.homOfLE (Es.basicOpen_le f))
  · exact of_hasEtaleLocalProperty_elementaryEtaleNeighborhood B S hS hX hXnormal E'
  · exact of_hasEtaleLocalProperty_elementaryEtaleNeighborhood B S hS hX hXnoeth E'
  · exact eq_presheafPoint_of_openRestrictionNeighborhood B S hS hX x E W hfmem huniq
  · intro y hy
    rw [hpts] at hy
    exact hfle ((Scheme.Opens.range_ι W).subset (Set.mem_range_self _)) hy

/-- **The singular locus of a neighbourhood avoiding the other singular points.** If an
elementary étale neighbourhood `E` of a singular point `x` has a single point over `x` and no
point over another singular point, then its only singular point is its distinguished point. -/
theorem singularLocus_eq_singleton_of_elementaryEtaleNeighborhood
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (x : points B S hS X) (hx : ¬ IsRegularAt B S hS X x)
    (E : ElementaryEtaleNeighborhood B S hS X hX x)
    (huniq : ∀ y : points B S hS (yoneda.obj E.scheme),
      pointsMap B S hS (yoneda.obj E.scheme) E.toSpace y = x →
        y = presheafPoint B S hS E.scheme E.point E.residueField_contained)
    (havoid : ∀ y : points B S hS (yoneda.obj E.scheme),
      pointsMap B S hS (yoneda.obj E.scheme) E.toSpace y ∉
        {y | ¬ IsRegularAt B S hS X y} \ {x}) :
    singularLocus E.scheme.left.1 = {E.point} := by
  have hEet := presheaf_etale_toSpace_of_elementaryEtaleNeighborhood B S hS hX E
  ext w
  obtain ⟨z, rfl⟩ := surjective_pointsToScheme B S hS E.scheme w
  refine (not_congr (isRegularLocalRing_stalk_iff_isRegularAt B S hS hX E.scheme E.toSpace
    hEet z)).trans ?_
  rw [Set.mem_singleton_iff]
  refine ⟨fun hz => ?_, fun hz => ?_⟩
  · rw [huniq z (of_not_not fun hne => havoid z ⟨hz, hne⟩), pointsToScheme_presheafPoint]
  · obtain rfl : z = presheafPoint B S hS E.scheme E.point E.residueField_contained :=
      injective_pointsToScheme B S hS E.scheme
        (hz.trans (pointsToScheme_presheafPoint B S hS _ _ _).symm)
    rwa [E.map_point]

/-- **Elementary étale neighbourhoods of the singular points of a normal surface.** Let `X` be an
integral algebraic space over `S`, normal, with locally Noetherian étale charts, of dimension at
most two, with finitely many singular points at each of which the completion of the henselian
local ring is normal. Then the singular points `x₁, …, xₙ` are closed and carry a family of
elementary étale neighbourhoods `(Vᵢ, vᵢ)` as in Section 0BH9 of the Stacks project, each `Vᵢ`
an affine integral normal locally Noetherian scheme whose only singular point is `vᵢ`, of local
dimension two, with normal completed local ring. -/
theorem exists_closedPointNeighborhoods_singularPoints (X : AlgebraicSpaces B S hS)
    (hXint : IsIntegralSpace B S hS X.obj)
    (hXnormal : HasEtaleLocalProperty B S hS X.obj
      (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsNormal T))
    (hXnoeth : HasEtaleLocalProperty B S hS X.obj (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hXdim : dimension B S hS X.obj X.property ≤ 2)
    (hsing : {y : points B S hS X.obj | ¬ IsRegularAt B S hS X.obj y}.Finite)
    (hcompl : ∀ y, ¬ IsRegularAt B S hS X.obj y →
      letI := henselianLocalRing_isLocalRing B S hS X.obj X.property y
        (hXint.isDecentSpace B S hS X.obj)
      IsNormalRing (AdicCompletion
        (IsLocalRing.maximalIdeal (henselianLocalRing B S hS X.obj X.property y
          (hXint.isDecentSpace B S hS X.obj) : Type (u + 1)))
        (henselianLocalRing B S hS X.obj X.property y
          (hXint.isDecentSpace B S hS X.obj) : Type (u + 1)))) :
    ∃ (n : ℕ) (D : ClosedPointNeighborhoods B S hS n), D.space = X ∧
      Set.range D.point = {y | ¬ IsRegularAt B S hS D.space.obj y} ∧
      ∀ i, IsAffine (D.neighborhood i).scheme.left.1 ∧
        IsIntegral (D.neighborhood i).scheme.left.1 ∧
        _root_.AlgebraicGeometry.IsNormal (D.neighborhood i).scheme.left.1 ∧
        IsLocallyNoetherian (D.neighborhood i).scheme.left.1 ∧
        singularLocus (D.neighborhood i).scheme.left.1 = {(D.neighborhood i).point} ∧
        ringKrullDim ((D.neighborhood i).scheme.left.1.presheaf.stalk
          (D.neighborhood i).point) = 2 ∧
        IsNormalRing (AdicCompletion
          (IsLocalRing.maximalIdeal ((D.neighborhood i).scheme.left.1.presheaf.stalk
            (D.neighborhood i).point))
          ((D.neighborhood i).scheme.left.1.presheaf.stalk (D.neighborhood i).point)) := by
  classical
  have hX : IsAlgebraicSpace B S hS X.obj := X.property
  have hdec : IsDecentSpace B S hS X.obj := hXint.isDecentSpace B S hS X.obj
  let Sg := {y : points B S hS X.obj | ¬ IsRegularAt B S hS X.obj y}
  have hclosed : ∀ y ∈ Sg, IsClosed ({y} : Set (points B S hS X.obj)) := fun y hy =>
    isClosed_singleton_of_not_isRegularAt B S hS hX hdec hXnormal hXnoeth hXdim y hy
  let n := hsing.toFinset.card
  let eqv : Fin n ≃ hsing.toFinset := hsing.toFinset.equivFin.symm
  let pt : Fin n → points B S hS X.obj := fun i => (eqv i).1
  have hptSg (i : Fin n) : pt i ∈ Sg := hsing.mem_toFinset.mp (eqv i).2
  have hpt_inj : Function.Injective pt := fun i j h => eqv.injective (Subtype.ext h)
  choose E hEaff hEint hEnorm hEnoeth hEuniq hEavoid using fun i : Fin n =>
    exists_elementaryEtaleNeighborhood_avoiding B S hS hX hXint hXnormal hXnoeth (pt i)
      (Sg \ {pt i}) (hsing.subset Set.sdiff_subset) (fun t ht => hclosed t ht.1) (fun h => h.2 rfl)
  let D : ClosedPointNeighborhoods B S hS n :=
    { space := X
      decent := hdec
      point := pt
      point_injective := hpt_inj
      isClosed_point := fun i => hclosed _ (hptSg i)
      neighborhood := E
      isAffine_neighborhood := hEaff
      eq_of_map_eq_point := hEuniq
      map_ne_point := fun i j hij y hy =>
        hEavoid i y (hy ▸ ⟨hptSg j, fun h => hij (hpt_inj h).symm⟩) }
  refine ⟨n, D, rfl, ?_, fun i => ⟨hEaff i, hEint i, hEnorm i, hEnoeth i, ?_, ?_, ?_⟩⟩
  · ext y
    refine ⟨?_, fun hy => ?_⟩
    · rintro ⟨i, rfl⟩
      exact hptSg i
    · obtain ⟨i, hi⟩ := eqv.surjective ⟨y, hsing.mem_toFinset.mpr hy⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  · exact singularLocus_eq_singleton_of_elementaryEtaleNeighborhood B S hS hX (pt i) (hptSg i)
      (E i) (hEuniq i) (hEavoid i)
  · have h := ringKrullDim_stalk_eq_two_of_not_isRegularAt B S hS hX hXnormal hXnoeth hXdim
      (E i).scheme (E i).toSpace
      (presheaf_etale_toSpace_of_elementaryEtaleNeighborhood B S hS hX (E i))
      (presheafPoint B S hS (E i).scheme (E i).point (E i).residueField_contained)
      (by rw [(E i).map_point]; exact hptSg i)
    rwa [pointsToScheme_presheafPoint] at h
  · let := henselianLocalRing_isLocalRing B S hS X.obj hX (pt i) hdec
    let := stalkAlgebra B S hS X.obj hX (pt i) hdec (E i)
    have := henselianLocalRing_isHenselization B S hS X.obj hX (pt i) hdec (E i)
    obtain ⟨e, -⟩ := StacksDraft.exists_adicCompletion_ringEquiv_of_isHenselization
      (R := (E i).scheme.left.1.presheaf.stalk (E i).point)
      (H := (henselianLocalRing B S hS X.obj hX (pt i) hdec : Type (u + 1)))
    exact IsNormalRing.congr e.symm (hcompl (pt i) (hptSg i))

end AlgebraicGeometry.Space

end

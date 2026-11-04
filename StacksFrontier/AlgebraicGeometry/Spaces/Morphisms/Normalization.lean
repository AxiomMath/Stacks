module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEffectiveDescent
public import StacksFrontier.AlgebraicGeometry.Descent.FiniteDescentFromAffine
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.IrreducibleComponents
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Nagata
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NormalMorphism.SmoothLocalSource
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.FiniteEtaleCover
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.RelativeGenericPoints
public import StacksFrontier.AlgebraicGeometry.Morphisms.SingularLocus.IrreducibleComponents
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Reduction
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.UniversalProperty
public import StacksFrontier.AlgebraicGeometry.NormalizationBirational.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionZeroPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedFactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Coverings
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationOverField
public import StacksFrontier.Topology.Irreducible.GenericPoints

/-!
# Normalization of an algebraic space

An algebraic space over a scheme `S` can be normalized as soon as its étale scheme charts have
finitely many irreducible components over every quasi-compact open; this is the condition
`AlgebraicGeometry.Space.HasLocallyFiniteIrreducibleComponents`. This file gives equivalent forms
of that condition and two sufficient conditions for it. For any normalization datum
`AlgebraicGeometry.Space.NormalizationData` it proves that the normalization is normal, that the
normalization morphism is integral and surjective, bijects points of codimension zero and is
universal among morphisms from normal algebraic spaces preserving codimension zero, that it is
finite for a Nagata algebraic space, and that it factors through any closed subspace carrying every
point.

## Main results

* `Space.exists_surjective_etale_chart_iff_hasLocallyFiniteIrreducibleComponents`: the finiteness
  condition holds as soon as it holds on one surjective étale scheme chart.
* `Space.hasLocallyFiniteIrreducibleComponents_iff_finite_codimensionZeroPoints`: the condition
  holds exactly when every quasi-compact algebraic space étale over the space has finitely many
  points of codimension zero.
* `Space.hasLocallyFiniteIrreducibleComponents_iff_finite_irreducibleComponents`: the condition
  holds exactly when every quasi-compact algebraic space étale over the space has finitely many
  irreducible components.
* `Space.hasLocallyFiniteIrreducibleComponents_iff_of_isRepresentable`: the condition for a
  representable algebraic space.
* `Space.localRingDimension_eq_zero_of_isFlat`: a flat morphism of algebraic spaces preserves
  points of codimension zero.
* `Space.hasLocallyFiniteIrreducibleComponents_of_isFlat_of_isLocallyOfFiniteType`: the condition
  ascends along a flat morphism locally of finite type.
* `Space.isIntegralHom_iff_etaleChart` and `Space.isFinite_iff_etaleChart`: a morphism of algebraic
  spaces is integral, respectively finite, exactly when its base change along some surjective étale
  scheme chart of the target is.
* `Space.NormalizationData.hasEtaleLocalProperty_isNormal`: the normalization is normal.
* `Space.NormalizationData.isSurjective_hom` and `Space.NormalizationData.isIntegralHom_hom`: the
  normalization morphism is surjective and integral.
* `Space.NormalizationData.bijOn_codimensionZeroPoints_hom`: the normalization morphism is a
  bijection on points of codimension zero.
* `Space.NormalizationData.existsUnique_lift_hom`: a morphism from a normal algebraic space
  preserving codimension zero factors uniquely through the normalization.
* `Space.NormalizationData.isFinite_pullback_snd_of_isNagataScheme`,
  `Space.NormalizationData.isFinite_pullback_snd` and
  `Space.NormalizationData.isFinite_of_representable_of_isNagataScheme`: finiteness of the base
  change of the normalization morphism along a Nagata chart, and of the normalization morphism of a
  representable Nagata space.
* `Space.NormalizationData.isFinite_hom`: the normalization morphism of a Nagata algebraic space is
  finite.
* `Space.hasLocallyFiniteIrreducibleComponents_of_range_pointsMap_eq_univ`: a closed subspace
  carrying every point satisfies the condition when the space does.
* `Space.NormalizationData.existsUnique_lift_hom_reduction` and
  `Space.NormalizationData.existsUnique_iso_of_hom_reduction`: the normalization morphism factors
  uniquely through a closed subspace carrying every point, and the normalization is then the
  normalization of that subspace.

## References

* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
* [Stacks Project, Tag 0AYG](https://stacks.math.columbia.edu/tag/0AYG)
* [Stacks Project, Tag 0BB1](https://stacks.math.columbia.edu/tag/0BB1)
* [Stacks Project, Tag 0BB2](https://stacks.math.columbia.edu/tag/0BB2)
* [Stacks Project, Tag 0BB3](https://stacks.math.columbia.edu/tag/0BB3)
* [Stacks Project, Tag 0BB4](https://stacks.math.columbia.edu/tag/0BB4)
* [Stacks Project, Tag 0BB5](https://stacks.math.columbia.edu/tag/0BB5)
* [Stacks Project, Tag 0GMB](https://stacks.math.columbia.edu/tag/0GMB)
* [Stacks Project, Tag 0GMC](https://stacks.math.columbia.edu/tag/0GMC)
* [Stacks Project, Tag 0GMD](https://stacks.math.columbia.edu/tag/0GMD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- A space with finitely many irreducible components on its universal open has finitely many
irreducible components. -/
private theorem finite_irreducibleComponents_of_top (X : Type*) [TopologicalSpace X]
    (h : (irreducibleComponents (⊤ : Opens X)).Finite) :
    (irreducibleComponents X).Finite :=
  (ncard_irreducibleComponents_le_of_surjective (Homeomorph.Set.univ X)
    (Homeomorph.Set.univ X).continuous (Homeomorph.Set.univ X).surjective h).1

/-- A sober space homeomorphic to a space with finitely many generic points has finitely many
irreducible components. -/
private theorem finite_irreducibleComponents_of_finite_genericPoints
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T0Space X] [QuasiSober X]
    (e : X ≃ₜ Y) (hfin : (genericPoints Y).Finite) :
    (irreducibleComponents X).Finite := by
  have : Finite (genericPoints Y) := hfin
  have : Finite (genericPoints X) :=
    Finite.of_injective
      (fun x : genericPoints X ↦ (⟨e x.1, e.mem_genericPoints x.2⟩ : genericPoints Y))
      fun x y h ↦ Subtype.ext (e.injective (congrArg Subtype.val h))
  exact Finite.of_equiv (genericPoints X) (genericPoints.equiv (α := X))

/-- The normalization morphism of a scheme whose quasi-compact opens have finitely many irreducible
components is a bijection on the generic points of the irreducible components. -/
private theorem bijOn_genericPoints_normalization (X : Scheme.{u})
    (hX : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite) :
    Set.BijOn (X.normalization hX) (genericPoints (X.normalizationScheme hX))
      (genericPoints X) := by
  obtain ⟨e, he⟩ := X.exists_normalizationScheme_iso_reduction hX
  have hred : IsReduced X.nilradical.subscheme := by
    simpa only [Scheme.IdealSheafData.vanishingIdeal_top] using
      Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal (X := X) ⊤
  have hsurj : Function.Surjective X.nilradical.subschemeι := fun x ↦
    Set.mem_range.mp (by rw [X.nilradical.range_subschemeι, Scheme.support_nilradical]; trivial)
  refine (((Homeomorph.bijOn_genericPoints
      (X.nilradical.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorphOfSurjective
        hsurj)).comp
    (X.nilradical.subscheme.isBirational_normalization
      (X.finite_irreducibleComponents_reduction hX)).bijOn).comp
    (Homeomorph.bijOn_genericPoints (Scheme.Hom.homeomorph e.hom))).congr
    fun x _ ↦ ?_
  rw [← he]
  rfl

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Finiteness of the irreducible components of the quasi-compact opens of a scheme is an
étale-local property of schemes. -/
@[sga "7 VIII 6.4" "special case"]
private instance finiteIrreducibleComponents_isLocal_etale :
    ObjectProperty.IsLocal
      (fun X : Scheme.{u} =>
        ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
      Scheme.etalePrecoverage :=
  ObjectProperty.IsLocal.of_le Scheme.etalePrecoverage_le_fppfPrecoverage

/-- A quasi-compact open of an étale scheme chart is itself an étale chart, by an object of the
site whose underlying scheme is that open and which is quasi-compact as an algebraic space. -/
private theorem exists_isQuasiCompactSpace_isEtale_of_isCompact
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ F)
    (hf : IsEtale B S hS f) (V : ((BigFppfOver.toScheme B S hS).obj U).Opens)
    (hV : IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj U))) :
    ∃ (W : BigFppfOver B S hS) (a : yoneda.obj W ⟶ F),
      (BigFppfOver.toScheme B S hS).obj W = V.toScheme ∧
        IsQuasiCompactSpace B S hS (yoneda.obj W) ∧ IsEtale B S hS a := by
  have hsize : V.toScheme.size < B.cutoff :=
    (Scheme.size_coe_opens_le _ V).trans_lt U.left.property
  let i : B.obj hsize ⟶ U.left := B.inclusion.preimage V.ι
  let W : BigFppfOver B S hS := Over.mk (i ≫ U.hom)
  let j : W ⟶ U := Over.homMk i
  refine ⟨W, yoneda.map j ≫ f, rfl, ?_, ?_⟩
  · refine ⟨W, 𝟙 _, ?_, (surjective_iff_surjective_pointsMap B S hS (yoneda.obj W)
      (isAlgebraicSpace_yoneda B S hS W) W (𝟙 _)).2
        (isSurjective_id B S hS (yoneda.obj W)), isEtale_id B S hS (yoneda.obj W)⟩
    show CompactSpace V.toScheme
    exact isCompact_iff_compactSpace.mp (by simpa using hV)
  · refine (isEtale_iff_presheaf_of_yoneda B S hS _).mpr
      (etale_comp_of_scheme B S hS j f ?_ ((isEtale_iff_presheaf_of_yoneda B S hS f).mp hf))
    have hj : (BigFppfOver.toScheme B S hS).map j = V.ι := B.inclusion.map_preimage _
    rw [hj]
    exact AlgebraicGeometry.Etale.instOfIsOpenImmersion V.ι

/-- A quasi-compact algebraic space étale over `F` is covered by a surjective étale scheme chart
with finitely many irreducible components, when `F` satisfies
`HasLocallyFiniteIrreducibleComponents`. -/
private theorem exists_surjective_etale_finite_irreducibleComponents
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (h : HasLocallyFiniteIrreducibleComponents B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (hqc : IsQuasiCompactSpace B S hS G) (g : G ⟶ F)
    (hg : IsEtale B S hS g) :
    ∃ (U : BigFppfOver B S hS) (v : yoneda.obj U ⟶ G),
      Function.Surjective (pointsMap B S hS (yoneda.obj U) v) ∧ IsEtale B S hS v ∧
        (irreducibleComponents ((BigFppfOver.toScheme B S hS).obj U)).Finite := by
  obtain ⟨U, v, hUcompact, hvSurj, hvEtale⟩ := hqc
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj U) := hUcompact
  exact ⟨U, v, (surjective_iff_surjective_pointsMap B S hS G hG U v).mp hvSurj, hvEtale,
    finite_irreducibleComponents_of_top _
    (h U (v ≫ g) (isEtale_comp B S hS hvEtale hg) ⊤ (by simpa using
      (isCompact_univ : IsCompact (Set.univ : Set ((BigFppfOver.toScheme B S hS).obj U)))))⟩

/-! ### The four equivalent finiteness conditions -/

/-- An algebraic space has a surjective étale scheme chart with finitely many irreducible
components over each of its quasi-compact opens if and only if every étale scheme chart has that
property. -/
@[stacks 0BB1 "conditions (1) and (2)"]
theorem exists_surjective_etale_chart_iff_hasLocallyFiniteIrreducibleComponents
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F) :
    (∃ (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ F),
        IsSurjective B S hS f ∧ IsEtale B S hS f ∧
          ∀ V : ((BigFppfOver.toScheme B S hS).obj U).Opens,
            IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj U)) →
              (irreducibleComponents V).Finite) ↔
      HasLocallyFiniteIrreducibleComponents B S hS F := by
  have hAtlas := exists_atlas_iff_forall_etale B S hS F
    (fun X : Scheme.{u} ↦
      ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite) hF
  constructor
  · rintro ⟨U, f, hsurj, hetale, hP⟩ V g hg
    exact hAtlas.mp ⟨U, f,
      (surjective_iff_surjective_pointsMap B S hS F hF U f).2 hsurj,
      (isEtale_iff_presheaf_of_yoneda B S hS f).mp hetale, hP⟩
      V g ((isEtale_iff_presheaf_of_yoneda B S hS g).mp hg)
  · intro h
    obtain ⟨U, f, hsurj, hetale, hP⟩ :=
      hAtlas.mpr fun V g hg ↦ h V g ((isEtale_iff_presheaf_of_yoneda B S hS g).mpr hg)
    exact ⟨U, f, (surjective_iff_surjective_pointsMap B S hS F hF U f).1 hsurj,
      (isEtale_iff_presheaf_of_yoneda B S hS f).mpr hetale, hP⟩

/-- Every étale scheme chart of `F` has finitely many irreducible components over each of its
quasi-compact opens exactly when every quasi-compact algebraic space étale over `F` has finitely
many points of codimension zero. -/
@[stacks 0BB1 "conditions (2) and (3)"]
theorem hasLocallyFiniteIrreducibleComponents_iff_finite_codimensionZeroPoints
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} :
    HasLocallyFiniteIrreducibleComponents B S hS F ↔
      ∀ (G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS G →
        IsQuasiCompactSpace B S hS G → ∀ g : G ⟶ F, IsEtale B S hS g →
          {x : points B S hS G | localRingDimension B S hS x = 0}.Finite := by
  constructor
  · intro h G hG hqc g hg
    obtain ⟨U, v, hvSurj, hvEtale, hXcomp⟩ :=
      exists_surjective_etale_finite_irreducibleComponents B S hS h hG hqc g hg
    have : Finite (genericPoints ((BigFppfOver.toScheme B S hS).obj U)) :=
      genericPoints.finite hXcomp
    refine (Set.toFinite (Set.range fun η : genericPoints ((BigFppfOver.toScheme B S hS).obj U) ↦
      pointsMap B S hS (yoneda.obj U) v ((schemePointsHomeomorph B S hS U).symm η.1))).subset ?_
    intro x hx
    obtain ⟨y, hy⟩ :=
      hvSurj x
    refine ⟨⟨pointsToScheme B S hS U y,
      (localRingDimension_eq_zero_iff_all_etale_genericPoints B S hS hG x).mp hx U v _ hvEtale
        (hy ▸ chartPoint_pointsToScheme B S hS U v y)⟩, ?_⟩
    show pointsMap B S hS (yoneda.obj U) v
      ((schemePointsHomeomorph B S hS U).symm (pointsToScheme B S hS U y)) = x
    rw [← schemePointsHomeomorph_apply B S hS U y,
      (schemePointsHomeomorph B S hS U).symm_apply_apply y]
    exact hy
  · intro h U f hf V hV
    obtain ⟨W, a, hW, hqcW, hEt⟩ :=
      exists_isQuasiCompactSpace_isEtale_of_isCompact B S hS U f hf V hV
    have hgeneric : (genericPoints (points B S hS (yoneda.obj W))).Finite := by
      refine (h (yoneda.obj W) (isAlgebraicSpace_yoneda B S hS W) hqcW a hEt).subset ?_
      intro p hp
      exact (localRingDimension_eq_zero_iff_genericPoint_of_isRepresentable B S hS
        (isAlgebraicSpace_yoneda B S hS W) inferInstance p).mpr hp
    show (irreducibleComponents V.toScheme).Finite
    rw [← hW]
    exact finite_irreducibleComponents_of_finite_genericPoints
      (schemePointsHomeomorph B S hS W).symm hgeneric

/-- Every étale scheme chart of `F` has finitely many irreducible components over each of its
quasi-compact opens exactly when the space of points of every quasi-compact algebraic space étale
over `F` has finitely many irreducible components. -/
@[stacks 0BB1 "conditions (2) and (4)"]
theorem hasLocallyFiniteIrreducibleComponents_iff_finite_irreducibleComponents
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} :
    HasLocallyFiniteIrreducibleComponents B S hS F ↔
      ∀ (G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS G →
        IsQuasiCompactSpace B S hS G → ∀ g : G ⟶ F, IsEtale B S hS g →
          (irreducibleComponents (points B S hS G)).Finite := by
  constructor
  · intro h G hG hqc g hg
    obtain ⟨U, v, hvSurj, hvEtale, hXcomp⟩ :=
      exists_surjective_etale_finite_irreducibleComponents B S hS h hG hqc g hg
    exact (ncard_irreducibleComponents_le_of_surjective
      (pointsMap B S hS (yoneda.obj U) v ∘ (schemePointsHomeomorph B S hS U).symm)
      ((continuous_pointsMap B S hS v).comp (schemePointsHomeomorph B S hS U).symm.continuous)
      (hvSurj.comp
        (schemePointsHomeomorph B S hS U).symm.surjective) hXcomp).1
  · intro h U f hf V hV
    obtain ⟨W, a, hW, hqcW, hEt⟩ :=
      exists_isQuasiCompactSpace_isEtale_of_isCompact B S hS U f hf V hV
    rw [← hW]
    exact (ncard_irreducibleComponents_le_of_surjective (schemePointsHomeomorph B S hS W)
      (schemePointsHomeomorph B S hS W).continuous
      (schemePointsHomeomorph B S hS W).surjective
      (h (yoneda.obj W) (isAlgebraicSpace_yoneda B S hS W) hqcW a hEt)).1

/-- For an algebraic space represented by a scheme of the site,
`HasLocallyFiniteIrreducibleComponents` is finiteness of the irreducible components of the
quasi-compact opens of that scheme. -/
@[stacks 0BB1 "representable case"]
theorem hasLocallyFiniteIrreducibleComponents_iff_of_isRepresentable
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} [F.IsRepresentable]
    (hF : IsAlgebraicSpace B S hS F) :
    HasLocallyFiniteIrreducibleComponents B S hS F ↔
      ∀ V : ((BigFppfOver.toScheme B S hS).obj F.reprX).Opens,
        IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj F.reprX)) →
          (irreducibleComponents V).Finite := by
  refine (exists_surjective_etale_chart_iff_hasLocallyFiniteIrreducibleComponents
    B S hS hF).symm.trans (Iff.trans ?_ (exists_atlas_iff_of_representable B S hS F
      (fun X : Scheme.{u} ↦
        ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
      F.reprX F.reprW.symm))
  exact exists_congr fun U ↦ exists_congr fun f ↦ and_congr
    (surjective_iff_surjective_pointsMap B S hS F hF U f).symm
    (and_congr (isEtale_iff_presheaf_of_yoneda B S hS f) Iff.rfl)

/-- A point of an étale scheme chart of an algebraic space which is the generic point of an
irreducible component of that chart lies over a point of codimension zero. -/
private theorem localRingDimension_eq_zero_of_mem_genericPoints
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F) (ha : IsEtale B S hS a)
    (z : points B S hS (yoneda.obj U))
    (hz : pointsToScheme B S hS U z ∈
      genericPoints ((BigFppfOver.toScheme B S hS).obj U)) :
    localRingDimension B S hS (pointsMap B S hS (yoneda.obj U) a z) = 0 :=
  (localRingDimension_eq_zero_iff_exists_etale_genericPoint B S hS hF _).mpr
    ⟨U, a, _, ha, chartPoint_pointsToScheme B S hS U a z, hz⟩

/-- Above a point of codimension zero, every point of every étale scheme chart is the generic
point of an irreducible component of that chart. -/
private theorem mem_genericPoints_of_localRingDimension_eq_zero
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F) (ha : IsEtale B S hS a)
    (z : points B S hS (yoneda.obj U))
    (hz : localRingDimension B S hS (pointsMap B S hS (yoneda.obj U) a z) = 0) :
    pointsToScheme B S hS U z ∈
      genericPoints ((BigFppfOver.toScheme B S hS).obj U) :=
  (localRingDimension_eq_zero_iff_all_etale_genericPoints B S hS hF _).mp hz U a _ ha
    (chartPoint_pointsToScheme B S hS U a z)

/-- Points of the two corners of a cartesian square of algebraic spaces with the same image in the
base come from a point of the pullback. -/
private theorem exists_point_of_isPullback_presheaf
    {P Z X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hP : IsAlgebraicSpace B S hS P) (hZ : IsAlgebraicSpace B S hS Z)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    {p : P ⟶ Z} {q : P ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y} (sq : IsPullback p q g f)
    (z : points B S hS Z) (x : points B S hS X)
    (h : pointsMap B S hS Z g z = pointsMap B S hS X f x) :
    ∃ w : points B S hS P, pointsMap B S hS P p w = z ∧ pointsMap B S hS P q w = x := by
  have sq' : IsPullback
      (ObjectProperty.homMk p : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z, hZ⟩)
      (ObjectProperty.homMk q : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩)
      (ObjectProperty.homMk g : (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
      (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) sq
  exact exists_point_of_isPullback B S hS sq' z x h

/-- A morphism from a normal chart to a chart whose generic points go to generic points lifts
uniquely through the chart of its normalization. -/
private theorem existsUnique_comp_eq_of_normalization {U Uν Q : BigFppfOver B S hS}
    (hU : ∀ V : ((BigFppfOver.toScheme B S hS).obj U).Opens,
      IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj U)) →
        (irreducibleComponents V).Finite)
    (p : Uν ⟶ U) (e : (BigFppfOver.toScheme B S hS).obj Uν ≅
      Scheme.normalizationScheme ((BigFppfOver.toScheme B S hS).obj U) hU)
    (hp : (BigFppfOver.toScheme B S hS).map p =
      e.hom ≫ Scheme.normalization ((BigFppfOver.toScheme B S hS).obj U) hU)
    [IsNormal ((BigFppfOver.toScheme B S hS).obj Q)] (a : Q ⟶ U)
    (ha : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj Q),
      (BigFppfOver.toScheme B S hS).map a η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj U)) :
    ∃! d : Q ⟶ Uν, d ≫ p = a := by
  obtain ⟨l, hl, hu⟩ := Scheme.existsUnique_lift_normalization hU _ ha
  have hlp : (l ≫ e.inv) ≫ (BigFppfOver.toScheme B S hS).map p =
      (BigFppfOver.toScheme B S hS).map a := by
    rw [hp]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact hl
  have hbase : (l ≫ e.inv) ≫ B.inclusion.map Uν.hom = B.inclusion.map Q.hom := by
    have hpbase : (BigFppfOver.toScheme B S hS).map p ≫ B.inclusion.map U.hom =
        B.inclusion.map Uν.hom := congrArg B.inclusion.map p.w
    rw [← hpbase, ← Category.assoc, hlp]
    exact congrArg B.inclusion.map a.w
  let d : Q ⟶ Uν := Over.homMk (B.inclusion.preimage (l ≫ e.inv)) (by
    apply B.inclusion.map_injective
    rw [Functor.map_comp, B.inclusion.map_preimage]
    exact hbase)
  have hd : (BigFppfOver.toScheme B S hS).map d = l ≫ e.inv := B.inclusion.map_preimage _
  refine ⟨d, ?_, fun d' hd' ↦ Over.OverMorphism.ext (B.inclusion.map_injective ?_)⟩
  · refine Over.OverMorphism.ext (B.inclusion.map_injective ?_)
    change (BigFppfOver.toScheme B S hS).map (d ≫ p) = (BigFppfOver.toScheme B S hS).map a
    rw [Functor.map_comp, hd]
    exact hlp
  · change (BigFppfOver.toScheme B S hS).map d' = (BigFppfOver.toScheme B S hS).map d
    have h1 : (BigFppfOver.toScheme B S hS).map d' ≫ e.hom = l :=
      hu _ (by beta_reduce; rw [Category.assoc, ← hp, ← Functor.map_comp, hd'])
    rw [hd, ← h1, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- A scheme-étale morphism of the site composed with an étale chart is an étale chart. -/
private theorem isEtale_yoneda_map_comp {X Y : BigFppfOver B S hS}
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (q : X ⟶ Y) (c : yoneda.obj Y ⟶ G)
    (hq : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map q)) (hc : IsEtale B S hS c) :
    IsEtale B S hS (yoneda.map q ≫ c) :=
  isEtale_comp B S hS ((isEtale_iff_presheaf_of_yoneda B S hS (yoneda.map q)).mpr
    ((presheaf_yoneda_map_etale_iff B S hS q).mpr hq)) hc

/-- A scheme-surjective morphism of the site composed with a map surjective on points is
surjective on points. -/
private theorem surjective_pointsMap_yoneda_map_comp {X Y : BigFppfOver B S hS}
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (q : X ⟶ Y) (c : yoneda.obj Y ⟶ G)
    (hq : AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hc : Function.Surjective (pointsMap B S hS (yoneda.obj Y) c)) :
    Function.Surjective (pointsMap B S hS (yoneda.obj X) (yoneda.map q ≫ c)) := by
  rw [pointsMap_comp]
  exact hc.comp ((surjective_yonedaMap_iff_surjective_pointsMap B S hS q).mp
    ((presheaf_yoneda_map_iff B S hS inferInstance q).mpr hq))

/-- Two morphisms from representable presheaves to an algebraic space have a representable
pullback. -/
private theorem exists_isPullback_yoneda_map {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) {U V : BigFppfOver B S hS} (c : yoneda.obj V ⟶ F)
    (a : yoneda.obj U ⟶ F) :
    ∃ (W : BigFppfOver B S hS) (s : W ⟶ V) (t : W ⟶ U),
      IsPullback (yoneda.map s) (yoneda.map t) c a := by
  have hc : yoneda.relativelyRepresentable c :=
    (Functor.relativelyRepresentable.diag_iff (F := yoneda) (X := F)).mp
      hF.diagonal_representable c
  refine ⟨_, yoneda.preimage (hc.fst a), hc.snd a, ?_⟩
  rw [yoneda.map_preimage]
  exact hc.isPullback a

/-- A cartesian square with a representable corner and a morphism of the site as one leg lifts
a pair of compatible morphisms from a representable presheaf to a morphism of the site. -/
private theorem exists_comp_eq_of_isPullback_yoneda {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {A C Q : BigFppfOver B S hS} {fst : yoneda.obj A ⟶ X} {j : A ⟶ C} {h : X ⟶ Y}
    {k : yoneda.obj C ⟶ Y} (sq : IsPullback fst (yoneda.map j) h k) (x : yoneda.obj Q ⟶ X)
    (y : Q ⟶ C) (w : x ≫ h = yoneda.map y ≫ k) :
    ∃ l : Q ⟶ A, yoneda.map l ≫ fst = x ∧ l ≫ j = y := by
  refine ⟨yoneda.preimage (sq.lift x (yoneda.map y) w), ?_, yoneda.map_injective ?_⟩
  · rw [yoneda.map_preimage]
    exact sq.lift_fst _ _ _
  · rw [Functor.map_comp, yoneda.map_preimage]
    exact sq.lift_snd _ _ _

/-! ### Flat morphisms and codimension-zero points -/

/-- A flat morphism of algebraic spaces takes points of codimension zero to points of codimension
zero. -/
@[stacks 0GMC]
theorem localRingDimension_eq_zero_of_isFlat
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsFlat B S hS f)
    (x : points B S hS X) (hx : localRingDimension B S hS x = 0) :
    localRingDimension B S hS (pointsMap B S hS X f x) = 0 := by
  obtain ⟨V, q, hq_surj, hq_etale⟩ := hY.exists_atlas
  obtain ⟨U, p, α, hcomm, hp_surj, hp_etale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V q hq_surj hq_etale
  obtain ⟨z, hzx⟩ := (surjective_iff_surjective_pointsMap B S hS X hX U p).mp hp_surj x
  have hu_generic := mem_genericPoints_of_localRingDimension_eq_zero B S hS hX U p
    ((isEtale_iff_presheaf_of_yoneda B S hS p).mpr hp_etale) z (hzx ▸ hx)
  have : AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map α) :=
    hf U V p q α hp_etale hq_etale hcomm.symm
  rw [show pointsMap B S hS X f x =
    pointsMap B S hS (yoneda.obj V) q (pointsMap B S hS (yoneda.obj U) (yoneda.map α) z) from ?_]
  · exact localRingDimension_eq_zero_of_mem_genericPoints B S hS hY V q
      ((isEtale_iff_presheaf_of_yoneda B S hS q).mpr hq_etale) _ (by
        rw [pointsToScheme_pointsMap B S hS α z]
        exact genericPoints_image_of_generalizingMap _
          (AlgebraicGeometry.Flat.generalizingMap _) hu_generic)
  · rw [← hzx, ← Function.comp_apply (f := pointsMap B S hS X f),
      ← Function.comp_apply (f := pointsMap B S hS (yoneda.obj V) q),
      ← pointsMap_comp, ← pointsMap_comp, hcomm]

/-- If `f : X ⟶ Y` is a flat morphism of algebraic spaces locally of finite type and `Y` satisfies
`HasLocallyFiniteIrreducibleComponents`, then so does `X`. -/
theorem hasLocallyFiniteIrreducibleComponents_of_isFlat_of_isLocallyOfFiniteType
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsFlat B S hS f)
    (hft : IsLocallyOfFiniteType B S hS f)
    (hYfinite : HasLocallyFiniteIrreducibleComponents B S hS Y) :
    HasLocallyFiniteIrreducibleComponents B S hS X := by
  obtain ⟨V, q, hqSurj, hqEtale⟩ := hY.exists_atlas
  obtain ⟨U, p, α, hcomm, hpSurj, hpEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V q hqSurj hqEtale
  have : AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map α) :=
    hf U V p q α hpEtale hqEtale hcomm.symm
  have : AlgebraicGeometry.LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map α) :=
    hft U V p q α hpEtale hqEtale hcomm.symm
  exact (exists_surjective_etale_chart_iff_hasLocallyFiniteIrreducibleComponents
    B S hS hX).mp ⟨U, p,
      (surjective_iff_surjective_pointsMap B S hS X hX U p).mp hpSurj,
      (isEtale_iff_presheaf_of_yoneda B S hS p).mpr hpEtale,
      finite_irreducibleComponents_of_flat_locallyOfFiniteType
        ((BigFppfOver.toScheme B S hS).map α)
        (hYfinite V q ((isEtale_iff_presheaf_of_yoneda B S hS q).mpr hqEtale))⟩

/-! ### Integral and finite morphisms on an étale chart -/

/-- A morphism of algebraic spaces over `S` is integral exactly when its base change along some
surjective étale morphism from a representable presheaf onto its target is integral. -/
@[stacks 03ZQ "integral: conditions (2) and (3)"]
theorem isIntegralHom_iff_etaleChart {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) :
    IsIntegralHom B S hS f ↔
      ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
        (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf g ∧
        (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf g ∧
          IsIntegralHom B S hS (pullback.snd f g) :=
  have _hri : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.IsIntegralHom.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  holdsOnAffineBaseChange_iff_exists_etaleChart B S hS isZariskiLocalAtTarget_isIntegralHom
    (fun p hp hZ ↦ isAffine_of_isIntegralHom p hp hZ)
    (isEffectiveDescentAlongSurjectiveEtale_isIntegralHom_of_isAffineHom
      (isEffectiveDescentAlongSurjectiveEtale_isAffineHom B S hS)) hX hY f

/-- A morphism of algebraic spaces over `S` is finite exactly when its base change along some
surjective étale morphism from a representable presheaf onto its target is finite. -/
@[stacks 03ZQ "finite: conditions (2) and (3)"]
theorem isFinite_iff_etaleChart {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) :
    IsFinite B S hS f ↔
      ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
        (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf g ∧
        (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf g ∧
          IsFinite B S hS (pullback.snd f g) := by
  have _hri : MorphismProperty.RespectsIso
      (@AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [isFinite_iff_holdsOnAffineBaseChange,
    holdsOnAffineBaseChange_iff_exists_etaleChart B S hS isZariskiLocalAtTarget_isFinite
      (fun p hp hZ ↦ isAffine_of_isFinite p hp hZ)
      (isEffectiveDescentAlongSurjectiveEtale_isFinite_of_isAffineHom
        (isEffectiveDescentAlongSurjectiveEtale_isAffineHom B S hS)) hX hY f]
  exact ⟨fun ⟨V, g, hs, he, h⟩ ↦
      ⟨V, g, hs, he, (isFinite_iff_holdsOnAffineBaseChange _).2 h⟩,
    fun ⟨V, g, hs, he, h⟩ ↦
      ⟨V, g, hs, he, (isFinite_iff_holdsOnAffineBaseChange _).1 h⟩⟩

/-! ### Normality, integrality and surjectivity of the normalization -/

namespace NormalizationData

variable {B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The normalization of an algebraic space is normal. -/
@[stacks 0BB4 "part (1): the normalization is normal"]
theorem hasEtaleLocalProperty_isNormal (D : NormalizationData B S hS F)
    (hF : IsAlgebraicSpace B S hS F) :
    HasEtaleLocalProperty B S hS D.space (fun X : Scheme.{u} => IsNormal X) := by
  obtain ⟨U, f, hsurj, hetale⟩ := hF.exists_atlas
  obtain ⟨hU, Uν, p, g, e, hp, hpb⟩ := D.chart U f
    ((surjective_iff_surjective_pointsMap B S hS F hF U f).mp hsurj)
    ((isEtale_iff_presheaf_of_yoneda B S hS f).mpr hetale)
  have hSurjBC : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hEtBC : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  refine ⟨Uν, g, MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip hsurj,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip hetale, ?_⟩
  have : IsNormal (Scheme.normalizationScheme ((BigFppfOver.toScheme B S hS).obj U) hU) :=
    Scheme.isNormal_normalizationScheme _ hU
  exact isNormal_of_iso e

/-- The normalization morphism of an algebraic space is surjective. -/
@[stacks 0BB4 "part (2): the normalization morphism is surjective"]
theorem isSurjective_hom (D : NormalizationData B S hS F)
    (hF : IsAlgebraicSpace B S hS F) : IsSurjective B S hS D.hom := by
  obtain ⟨U, f, hsurj, hetale⟩ := hF.exists_atlas
  have hsurj' := (surjective_iff_surjective_pointsMap B S hS F hF U f).mp hsurj
  obtain ⟨hU, Uν, p, g, e, hp, hpb⟩ := D.chart U f hsurj'
    ((isEtale_iff_presheaf_of_yoneda B S hS f).mpr hetale)
  have : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS inferInstance
  have hp' : Function.Surjective
      (pointsMap B S hS (yoneda.obj Uν) (yoneda.map p)) :=
    (surjective_yonedaMap_iff_surjective_pointsMap B S hS p).mp
      (MorphismProperty.relative_map
        (P := MorphismProperty.inverseImage
          (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))
        (show AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map p) by
          rw [hp]; infer_instance))
  intro x
  obtain ⟨a, ha⟩ := hsurj' x
  obtain ⟨b, hb⟩ := hp' a
  refine ⟨pointsMap B S hS (yoneda.obj Uν) g b, ?_⟩
  rw [← Function.comp_apply (f := pointsMap B S hS D.space D.hom), ← pointsMap_comp,
    hpb.w, pointsMap_comp, Function.comp_apply, hb, ha]

/-- The normalization morphism of an algebraic space is an integral morphism of algebraic
spaces. -/
@[stacks 0BB4 "part (2): the normalization morphism is integral"]
theorem isIntegralHom_hom (D : NormalizationData B S hS F)
    (hF : IsAlgebraicSpace B S hS F) : IsIntegralHom B S hS D.hom := by
  obtain ⟨U, g, hgs, hge⟩ := hF.exists_atlas
  exact (isIntegralHom_iff_etaleChart B S hS D.hom D.isAlgebraicSpace hF).2
    ⟨U, g, hgs, hge, D.isIntegralHom_pullback_snd hF U g
      (isSurjective_of_presheafSurjective B S hS g hgs)
      ((isEtale_iff_presheaf_of_yoneda B S hS g).mpr hge)⟩

/-- The normalization morphism induces a bijection between the codimension-zero points of the
normalization and those of the algebraic space. -/
@[stacks 0BB4 "part (3): bijection on codimension-zero points"]
theorem bijOn_codimensionZeroPoints_hom (D : NormalizationData B S hS F)
    (hF : IsAlgebraicSpace B S hS F) :
    Set.BijOn (pointsMap B S hS D.space D.hom)
      {x : points B S hS D.space | localRingDimension B S hS x = 0}
      {x : points B S hS F | localRingDimension B S hS x = 0} := by
  obtain ⟨U, f, hf, hfe⟩ := hF.exists_atlas
  have hfSurj := (surjective_iff_surjective_pointsMap B S hS F hF U f).mp hf
  have hfe' : IsEtale B S hS f := (isEtale_iff_presheaf_of_yoneda B S hS f).mpr hfe
  obtain ⟨hU, Uν, p, g, e, hp, hpull⟩ := D.chart U f hfSurj hfe'
  have hgEtale : IsEtale B S hS g := isEtale_of_isPullback_yoneda B S hS hpull.flip hfe'
  have hUν := isAlgebraicSpace_yoneda B S hS Uν
  have hUsp := isAlgebraicSpace_yoneda B S hS U
  have hgSurj : Function.Surjective (pointsMap B S hS (yoneda.obj Uν) g) := fun x ↦ by
    obtain ⟨y, hy⟩ := hfSurj (pointsMap B S hS D.space D.hom x)
    obtain ⟨z, hzg, -⟩ := exists_point_of_isPullback_presheaf B S hS hUν D.isAlgebraicSpace hUsp hF
      hpull x y hy.symm
    exact ⟨z, hzg⟩
  have hbij : Set.BijOn ((BigFppfOver.toScheme B S hS).map p)
      (genericPoints ((BigFppfOver.toScheme B S hS).obj Uν))
      (genericPoints ((BigFppfOver.toScheme B S hS).obj U)) := by
    refine ((bijOn_genericPoints_normalization _ hU).comp
      (Homeomorph.bijOn_genericPoints (Scheme.Hom.homeomorph e.hom))).congr fun x _ ↦ ?_
    rw [hp]
    rfl
  have hcomm (z : points B S hS (yoneda.obj Uν)) :
      pointsMap B S hS (yoneda.obj U) f (pointsMap B S hS (yoneda.obj Uν) (yoneda.map p) z) =
        pointsMap B S hS D.space D.hom (pointsMap B S hS (yoneda.obj Uν) g z) := by
    rw [← Function.comp_apply (f := pointsMap B S hS (yoneda.obj U) f), ← pointsMap_comp,
      ← hpull.w, pointsMap_comp, Function.comp_apply]
  refine ⟨fun x hx ↦ ?_, fun x hx y hy hxy ↦ ?_, fun y hy ↦ ?_⟩
  · obtain ⟨z, hz⟩ := hgSurj x
    have hu := mem_genericPoints_of_localRingDimension_eq_zero B S hS D.isAlgebraicSpace Uν g
      hgEtale z (hz ▸ hx)
    have hgoal : localRingDimension B S hS
        (pointsMap B S hS (yoneda.obj U) f
          (pointsMap B S hS (yoneda.obj Uν) (yoneda.map p) z)) = 0 := by
      refine localRingDimension_eq_zero_of_mem_genericPoints B S hS hF U f hfe' _ ?_
      rw [pointsToScheme_pointsMap B S hS p z]
      exact hbij.1 hu
    show localRingDimension B S hS (pointsMap B S hS D.space D.hom x) = 0
    rw [← hz, ← hcomm z]
    exact hgoal
  · obtain ⟨zU, hzU⟩ := hfSurj (pointsMap B S hS D.space D.hom x)
    obtain ⟨z, hzg, hzp⟩ := exists_point_of_isPullback_presheaf B S hS hUν D.isAlgebraicSpace
      hUsp hF hpull x zU hzU.symm
    obtain ⟨w, hwg, hwp⟩ := exists_point_of_isPullback_presheaf B S hS hUν D.isAlgebraicSpace
      hUsp hF hpull y zU (hxy.symm.trans hzU.symm)
    have huz := mem_genericPoints_of_localRingDimension_eq_zero B S hS D.isAlgebraicSpace Uν g
      hgEtale z (hzg ▸ hx)
    have huw := mem_genericPoints_of_localRingDimension_eq_zero B S hS D.isAlgebraicSpace Uν g
      hgEtale w (hwg ▸ hy)
    have hscheme : (BigFppfOver.toScheme B S hS).map p (pointsToScheme B S hS Uν z) =
        (BigFppfOver.toScheme B S hS).map p (pointsToScheme B S hS Uν w) := by
      rw [← pointsToScheme_pointsMap B S hS p z, ← pointsToScheme_pointsMap B S hS p w]
      rw [hzp, hwp]
    rw [← hzg, ← hwg,
      injective_pointsToScheme B S hS Uν (hbij.2.1 huz huw hscheme)]
  · obtain ⟨zU, hzU⟩ := hfSurj y
    obtain ⟨uν, huν, hpu⟩ := hbij.2.2
      (mem_genericPoints_of_localRingDimension_eq_zero B S hS hF U f hfe' zU (hzU ▸ hy))
    obtain ⟨zν, hzν⟩ := surjective_pointsToScheme B S hS Uν uν
    have hpclass : pointsMap B S hS (yoneda.obj Uν) (yoneda.map p) zν = zU :=
      injective_pointsToScheme B S hS U
        (by rw [pointsToScheme_pointsMap B S hS p zν, hzν, hpu])
    refine ⟨pointsMap B S hS (yoneda.obj Uν) g zν,
      localRingDimension_eq_zero_of_mem_genericPoints B S hS D.isAlgebraicSpace Uν g hgEtale zν
        (hzν ▸ huν), ?_⟩
    rw [← hcomm zν, hpclass, hzU]

/-! ### The universal property of the normalization -/

/-- A morphism to `F` from a normal algebraic space which carries points of codimension zero to
points of codimension zero factors uniquely through the normalization of `F`. -/
@[stacks 0BB4 "part (4): the universal property", sga "3 X 8.9" "partial"]
theorem existsUnique_lift_hom (D : NormalizationData B S hS F)
    (hF : IsAlgebraicSpace B S hS F) {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hZ : IsAlgebraicSpace B S hS Z)
    (hZnormal : HasEtaleLocalProperty B S hS Z fun Y : Scheme.{u} => IsNormal Y) (f : Z ⟶ F)
    (hgeneric : ∀ z : points B S hS Z, localRingDimension B S hS z = 0 →
      localRingDimension B S hS (pointsMap B S hS Z f z) = 0) :
    ∃! g : Z ⟶ D.space, g ≫ D.hom = f := by
  classical
  let T := BigFppfOver.toScheme B S hS
  have _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  obtain ⟨U, u, huSurjP, huEtaleP⟩ := hF.exists_atlas
  have huSurj : IsSurjective B S hS u :=
    (surjective_iff_surjective_pointsMap B S hS F hF U u).mp huSurjP
  have huEtale : IsEtale B S hS u := (isEtale_iff_presheaf_of_yoneda B S hS u).mpr huEtaleP
  obtain ⟨hU, Uν, p, gU, e, hnormChart, hpbChart⟩ := D.chart U u huSurj huEtale
  obtain ⟨V, v, hvSurjP, hvEtaleP, hVnormal⟩ := hZnormal
  have hvEtale : IsEtale B S hS v := (isEtale_iff_presheaf_of_yoneda B S hS v).mpr hvEtaleP
  have hvSurj : Function.Surjective (pointsMap B S hS (yoneda.obj V) v) :=
    (surjective_iff_surjective_pointsMap B S hS Z hZ V v).mp hvSurjP
  have _ : IsNormal (T.obj V) := hVnormal
  obtain ⟨W, q, b, hWpb'⟩ := exists_isPullback_yoneda_map B S hS hF (v ≫ f) u
  have hWpb := hWpb'.flip
  have hqSurj : AlgebraicGeometry.Surjective (T.map q) :=
    huSurjP.property (v ≫ f) (yoneda.map b) q hWpb
  have hqEtale : AlgebraicGeometry.Etale (T.map q) :=
    huEtaleP.property (v ≫ f) (yoneda.map b) q hWpb
  have _ : IsNormal (T.obj W) := isNormal_of_etale (T.map q)
  have hgenericb : ∀ η : genericPoints (T.obj W), T.map b η.1 ∈ genericPoints (T.obj U) := by
    intro η
    obtain ⟨zW, hzW⟩ := surjective_pointsToScheme B S hS W η.1
    have hqgen : T.map q η.1 ∈ genericPoints (T.obj V) :=
      genericPoints_image_of_generalizingMap _
        (AlgebraicGeometry.Flat.generalizingMap (T.map q)) η.2
    have hdimZ : localRingDimension B S hS
        (pointsMap B S hS (yoneda.obj V) v
          (pointsMap B S hS (yoneda.obj W) (yoneda.map q) zW)) = 0 :=
      localRingDimension_eq_zero_of_mem_genericPoints B S hS hZ V v hvEtale _ (by
        rw [pointsToScheme_pointsMap B S hS q zW, hzW]
        exact hqgen)
    have himg : pointsMap B S hS (yoneda.obj U) u
        (pointsMap B S hS (yoneda.obj W) (yoneda.map b) zW) =
          pointsMap B S hS Z f (pointsMap B S hS (yoneda.obj V) v
            (pointsMap B S hS (yoneda.obj W) (yoneda.map q) zW)) := by
      rw [← pointsMap_comp_apply, show yoneda.map b ≫ u = (yoneda.map q ≫ v) ≫ f by
        rw [Category.assoc]; exact hWpb.w, pointsMap_comp_apply, pointsMap_comp_apply]
    have hmem := mem_genericPoints_of_localRingDimension_eq_zero B S hS hF U u huEtale
      (pointsMap B S hS (yoneda.obj W) (yoneda.map b) zW) (by
        rw [himg]; exact hgeneric _ hdimZ)
    rwa [pointsToScheme_pointsMap B S hS b zW, hzW] at hmem
  obtain ⟨ellW, hellWp, -⟩ :=
    existsUnique_comp_eq_of_normalization B S hS hU p e hnormChart b hgenericb
  let gW : yoneda.obj W ⟶ D.space := yoneda.map ellW ≫ gU
  have hgW : gW ≫ D.hom = (yoneda.map q ≫ v) ≫ f := by
    calc gW ≫ D.hom = yoneda.map ellW ≫ gU ≫ D.hom := rfl
      _ = yoneda.map ellW ≫ yoneda.map p ≫ u := by rw [hpbChart.w]
      _ = yoneda.map (ellW ≫ p) ≫ u := by rw [Functor.map_comp, Category.assoc]
      _ = yoneda.map b ≫ u := by rw [hellWp]
      _ = (yoneda.map q ≫ v) ≫ f := hWpb.w
  have hwSurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map q ≫ v) :=
    (surjective_iff_surjective_pointsMap B S hS Z hZ W (yoneda.map q ≫ v)).mpr
      (surjective_pointsMap_yoneda_map_comp B S hS q v hqSurj hvSurj)
  have hwEtale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map q ≫ v) :=
    (isEtale_iff_presheaf_of_yoneda B S hS (yoneda.map q ≫ v)).mp
      (isEtale_yoneda_map_comp B S hS q v hqEtale hvEtale)
  obtain ⟨R, s, t, hR⟩ :=
    exists_isPullback_yoneda_map B S hS hZ (yoneda.map q ≫ v) (yoneda.map q ≫ v)
  have hsEtale : AlgebraicGeometry.Etale (T.map s) :=
    hwEtale.property (yoneda.map q ≫ v) (yoneda.map t) s hR.flip
  have htEtale : AlgebraicGeometry.Etale (T.map t) :=
    hwEtale.property (yoneda.map q ≫ v) (yoneda.map s) t hR
  have _ : IsNormal (T.obj R) := isNormal_of_etale (T.map s)
  have hgenericcomp : ∀ m : R ⟶ W, AlgebraicGeometry.Etale (T.map m) →
      ∀ η : genericPoints (T.obj R), T.map (m ≫ b) η.1 ∈ genericPoints (T.obj U) :=
    fun m _ η ↦ by
      simpa only [Functor.map_comp, AlgebraicGeometry.Scheme.Hom.comp_apply] using
        hgenericb ⟨T.map m η.1, genericPoints_image_of_generalizingMap _
          (AlgebraicGeometry.Flat.generalizingMap (T.map m)) η.2⟩
  obtain ⟨R₀, r₁, r₂, hR₀⟩ := exists_isPullback_yoneda_map B S hS hF u u
  have hxy : yoneda.map (s ≫ b) ≫ u = yoneda.map (t ≫ b) ≫ u := by
    have hsw : yoneda.map s ≫ yoneda.map q ≫ v ≫ f = yoneda.map t ≫ yoneda.map q ≫ v ≫ f := by
      simpa only [Category.assoc] using congrArg (· ≫ f) hR.w
    calc yoneda.map (s ≫ b) ≫ u = yoneda.map s ≫ yoneda.map b ≫ u := by
          rw [Functor.map_comp, Category.assoc]
      _ = yoneda.map s ≫ yoneda.map q ≫ v ≫ f := by rw [hWpb.w]
      _ = yoneda.map t ≫ yoneda.map q ≫ v ≫ f := hsw
      _ = yoneda.map t ≫ yoneda.map b ≫ u := by rw [hWpb.w]
      _ = yoneda.map (t ≫ b) ≫ u := by rw [Functor.map_comp, Category.assoc]
  obtain ⟨r, hr₁', hr₂⟩ := exists_comp_eq_of_isPullback_yoneda B S hS hR₀ _ (t ≫ b) hxy
  have hr₁ : r ≫ r₁ = s ≫ b := yoneda.map_injective (by rw [Functor.map_comp]; exact hr₁')
  have hr₁Surj : AlgebraicGeometry.Surjective (T.map r₁) :=
    huSurjP.property u (yoneda.map r₂) r₁ hR₀.flip
  have hr₁Etale : AlgebraicGeometry.Etale (T.map r₁) :=
    huEtaleP.property u (yoneda.map r₂) r₁ hR₀.flip
  let a₀ : yoneda.obj R₀ ⟶ F := yoneda.map r₁ ≫ u
  have ha₀Etale : IsEtale B S hS a₀ := isEtale_yoneda_map_comp B S hS r₁ u hr₁Etale huEtale
  have ha₀Surj : IsSurjective B S hS a₀ :=
    surjective_pointsMap_yoneda_map_comp B S hS r₁ u hr₁Surj huSurj
  obtain ⟨hR₀fin, R₀ν, p₀, g₀, e₀, hnormR₀, hpbR₀⟩ := D.chart R₀ a₀ ha₀Surj ha₀Etale
  have hrGeneric : ∀ η : genericPoints (T.obj R), T.map r η.1 ∈ genericPoints (T.obj R₀) := by
    intro η
    have hbGeneric : T.map r₁ (T.map r η.1) ∈ genericPoints (T.obj U) := by
      rw [← AlgebraicGeometry.Scheme.Hom.comp_apply, ← Functor.map_comp, hr₁]
      exact hgenericcomp s hsEtale η
    obtain ⟨zR₀, hzR₀⟩ := surjective_pointsToScheme B S hS R₀ (T.map r η.1)
    have hdim : localRingDimension B S hS (pointsMap B S hS (yoneda.obj R₀) a₀ zR₀) = 0 := by
      rw [show pointsMap B S hS (yoneda.obj R₀) a₀ zR₀ =
        pointsMap B S hS (yoneda.obj U) u
          (pointsMap B S hS (yoneda.obj R₀) (yoneda.map r₁) zR₀) from
        pointsMap_comp_apply B S hS (yoneda.map r₁) u zR₀]
      exact localRingDimension_eq_zero_of_mem_genericPoints B S hS hF U u huEtale _ (by
        rw [pointsToScheme_pointsMap B S hS r₁ zR₀, hzR₀]
        exact hbGeneric)
    have hmem := mem_genericPoints_of_localRingDimension_eq_zero B S hS hF R₀ a₀
      ha₀Etale zR₀ hdim
    rwa [hzR₀] at hmem
  obtain ⟨ellR, hellRp₀, -⟩ :=
    existsUnique_comp_eq_of_normalization B S hS hR₀fin p₀ e₀ hnormR₀ r hrGeneric
  have hg₀r₁ : g₀ ≫ D.hom = yoneda.map (p₀ ≫ r₁) ≫ u := by
    rw [Functor.map_comp, Category.assoc]
    exact hpbR₀.w
  obtain ⟨c₁, hc₁g, hc₁p⟩ := exists_comp_eq_of_isPullback_yoneda B S hS hpbChart g₀ _ hg₀r₁
  obtain ⟨c₂, hc₂g, hc₂p⟩ := exists_comp_eq_of_isPullback_yoneda B S hS hpbChart g₀ (p₀ ≫ r₂)
    (by simp only [hg₀r₁, Functor.map_comp, Category.assoc, hR₀.w])
  have hliftS : s ≫ ellW = ellR ≫ c₁ :=
    (existsUnique_comp_eq_of_normalization B S hS hU p e hnormChart (s ≫ b)
      (hgenericcomp s hsEtale)).unique (by rw [Category.assoc, hellWp])
      (by rw [Category.assoc, hc₁p, ← Category.assoc, hellRp₀, hr₁])
  have hliftT : t ≫ ellW = ellR ≫ c₂ :=
    (existsUnique_comp_eq_of_normalization B S hS hU p e hnormChart (t ≫ b)
      (hgenericcomp t htEtale)).unique (by rw [Category.assoc, hellWp])
      (by rw [Category.assoc, hc₂p, ← Category.assoc, hellRp₀, hr₂])
  have hgEqual : yoneda.map s ≫ gW = yoneda.map t ≫ gW := by
    calc yoneda.map s ≫ gW = yoneda.map (s ≫ ellW) ≫ gU := by
          rw [Functor.map_comp, Category.assoc]
      _ = yoneda.map (ellR ≫ c₁) ≫ gU := by rw [hliftS]
      _ = yoneda.map ellR ≫ g₀ := by rw [Functor.map_comp, Category.assoc, hc₁g]
      _ = yoneda.map (ellR ≫ c₂) ≫ gU := by rw [Functor.map_comp, Category.assoc, hc₂g]
      _ = yoneda.map (t ≫ ellW) ≫ gU := by rw [← hliftT]
      _ = yoneda.map t ≫ gW := by rw [Functor.map_comp, Category.assoc]
  obtain ⟨hRsh, hWsh, hcolim⟩ :=
    isCoequalizer_of_surjectiveEtale B S hS (yoneda.map q ≫ v) s t hR hZ hwSurj hwEtale
  let RF : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨yoneda.obj R, hRsh⟩
  let WF : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨yoneda.obj W, hWsh⟩
  let ZF : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨Z, hZ.isSheaf⟩
  let NF : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨D.space, D.isAlgebraicSpace.isSheaf⟩
  let FF : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨F, hF.isSheaf⟩
  let sf : RF ⟶ WF := ⟨yoneda.map s⟩
  let tf : RF ⟶ WF := ⟨yoneda.map t⟩
  let wf : WF ⟶ ZF := ⟨yoneda.map q ≫ v⟩
  have hcomm : sf ≫ wf = tf ≫ wf := Sheaf.hom_ext hR.w
  obtain ⟨hcol⟩ : Nonempty (IsColimit (Cofork.ofπ wf hcomm)) := hcolim
  let gWSheaf : WF ⟶ NF := ⟨gW⟩
  have hgSheaf : sf ≫ gWSheaf = tf ≫ gWSheaf := Sheaf.hom_ext hgEqual
  let gSheaf : ZF ⟶ NF := hcol.desc (Cofork.ofπ gWSheaf hgSheaf)
  have hfg : (yoneda.map q ≫ v) ≫ gSheaf.hom = gW :=
    Sheaf.hom_ext_iff.mp (Cofork.IsColimit.π_desc hcol)
  refine ⟨gSheaf.hom, ?_, ?_⟩
  · refine Sheaf.hom_ext_iff.mp (Cofork.IsColimit.hom_ext hcol
      (k := gSheaf ≫ (⟨D.hom⟩ : NF ⟶ FF)) (l := (⟨f⟩ : ZF ⟶ FF)) (Sheaf.hom_ext ?_))
    show ((yoneda.map q ≫ v) ≫ gSheaf.hom) ≫ D.hom = (yoneda.map q ≫ v) ≫ f
    rw [hfg, hgW]
  · intro g' hg'
    have hcompat : ((yoneda.map q ≫ v) ≫ g') ≫ D.hom = yoneda.map b ≫ u := by
      rw [hWpb.w]
      simp only [Category.assoc, hg']
    obtain ⟨d, hdg, hdp⟩ :=
      exists_comp_eq_of_isPullback_yoneda B S hS hpbChart ((yoneda.map q ≫ v) ≫ g') b hcompat
    have hdSite : d = ellW :=
      (existsUnique_comp_eq_of_normalization B S hS hU p e hnormChart b hgenericb).unique
        hdp hellWp
    have hafter : (yoneda.map q ≫ v) ≫ g' = gW := by rw [← hdg, hdSite]
    refine Sheaf.hom_ext_iff.mp (Cofork.IsColimit.hom_ext hcol
      (k := (⟨g'⟩ : ZF ⟶ NF)) (l := gSheaf) (Sheaf.hom_ext ?_))
    show (yoneda.map q ≫ v) ≫ g' = (yoneda.map q ≫ v) ≫ gSheaf.hom
    rw [hafter, hfg]

/-! ### Finiteness of the normalization of a Nagata algebraic space -/

/-- The base change of the normalization morphism of an algebraic space along a surjective étale
scheme chart by a *Nagata* scheme is a finite morphism of algebraic spaces. -/
theorem isFinite_pullback_snd_of_isNagataScheme (D : NormalizationData B S hS F)
    (hF : IsAlgebraicSpace B S hS F) (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ F)
    (hf : IsSurjective B S hS f) (hfe : IsEtale B S hS f)
    (hU : IsNagataScheme ((BigFppfOver.toScheme B S hS).obj U)) :
    IsFinite B S hS (pullback.snd D.hom f) := by
  obtain ⟨hUfin, Uν, p, g, e, hp, hpb⟩ := D.chart U f hf hfe
  have hUspace : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hPull : IsAlgebraicSpace B S hS (pullback D.hom f) :=
    isAlgebraicSpace_pullback B S hS D.hom f D.isAlgebraicSpace hUspace hF
  have hrelp := relative_inverseImage_isFinite_yoneda_map p (by
    rw [hp]
    have : _root_.AlgebraicGeometry.IsFinite
        (Scheme.normalization ((BigFppfOver.toScheme B S hS).obj U) hUfin) :=
      Scheme.isFinite_normalization hU hUfin
    infer_instance)
  have hrelq : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative yoneda (pullback.snd D.hom f) := by
    refine (((MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative yoneda).cancel_left_of_respectsIso
      hpb.isoPullback.hom (pullback.snd D.hom f)).mp ?_
    rw [hpb.isoPullback_hom_snd]
    exact hrelp
  exact (isFinite_iff_representable B S hS (pullback.snd D.hom f) hPull hUspace).2
    ⟨hrelq.1, hrelq⟩

/-- The base change of the normalization morphism of a Nagata algebraic space along any surjective
étale scheme chart is a finite morphism of algebraic spaces. -/
theorem isFinite_pullback_snd (D : NormalizationData B S hS F)
    (hF : IsAlgebraicSpace B S hS F)
    (hNagata : HasEtaleLocalProperty B S hS F (fun X : Scheme.{u} => IsNagataScheme X))
    (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ F)
    (hf : IsSurjective B S hS f) (hfe : IsEtale B S hS f) :
    IsFinite B S hS (pullback.snd D.hom f) :=
  D.isFinite_pullback_snd_of_isNagataScheme hF U f hf hfe
    ((exists_atlas_iff_forall_etale B S hS F (fun X : Scheme.{u} ↦ IsNagataScheme X) hF).mp
      hNagata U f ((isEtale_iff_presheaf_of_yoneda B S hS f).mp hfe))

/-- The normalization morphism of the algebraic space represented by a Nagata object of the big
fppf site of `S` is a finite morphism of algebraic spaces. -/
theorem isFinite_of_representable_of_isNagataScheme {X : BigFppfOver B S hS}
    (D : NormalizationData B S hS (yoneda.obj X))
    (hX : IsNagataScheme ((BigFppfOver.toScheme B S hS).obj X)) :
    IsFinite B S hS D.hom := by
  obtain ⟨hXfin, Xν, p, g, e, hp, hpb⟩ := D.chart_self
  have hg : IsIso g := hpb.isIso_fst_of_isIso
  have hrelp := relative_inverseImage_isFinite_yoneda_map p (by
    rw [hp]
    have : _root_.AlgebraicGeometry.IsFinite
        (Scheme.normalization ((BigFppfOver.toScheme B S hS).obj X) hXfin) :=
      Scheme.isFinite_normalization hX hXfin
    infer_instance)
  have hD : D.hom = inv g ≫ yoneda.map p := by
    rw [← cancel_epi g, IsIso.hom_inv_id_assoc]
    simpa only [Category.comp_id] using hpb.w
  have hrel := (((MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative yoneda).cancel_left_of_respectsIso
      (inv g) (yoneda.map p)).mpr hrelp
  rw [hD]
  exact (isFinite_iff_representable B S hS (inv g ≫ yoneda.map p)
    D.isAlgebraicSpace (isAlgebraicSpace_yoneda B S hS X)).2 ⟨hrel.1, hrel⟩

/-- The normalization morphism of a Nagata algebraic space over `S` is a finite morphism of
algebraic spaces. -/
@[stacks 0BB5]
theorem isFinite_hom
    (D : NormalizationData B S hS F) (hF : IsAlgebraicSpace B S hS F)
    (hNagata : HasEtaleLocalProperty B S hS F (fun X : Scheme.{u} => IsNagataScheme X)) :
    IsFinite B S hS D.hom := by
  obtain ⟨U, g, hgs, hge, -⟩ := id hNagata
  exact (isFinite_iff_etaleChart B S hS D.hom D.isAlgebraicSpace hF).2
    ⟨U, g, hgs, hge, D.isFinite_pullback_snd hF hNagata U g
      (isSurjective_of_presheafSurjective B S hS g hgs)
      ((isEtale_iff_presheaf_of_yoneda B S hS g).mpr hge)⟩

end NormalizationData

/-! ### Charts of a closed subspace carrying every point -/

/-- A closed subspace whose points are all the points of the ambient algebraic space is cut out of
every surjective étale scheme chart by a homeomorphism of underlying spaces. -/
private theorem exists_chart_of_range_pointsMap_eq_univ
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (R : Subfunctor F) (hR : IsClosedSubspace B S hS R)
    (hfull : Set.range (pointsMap B S hS R.toFunctor R.ι) = Set.univ)
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F) (ha : IsSurjective B S hS a)
    (hae : IsEtale B S hS a) :
    ∃ (P : BigFppfOver B S hS) (j : P ⟶ U) (i : yoneda.obj P ⟶ R.toFunctor)
      (e : ((BigFppfOver.toScheme B S hS).obj P) ≃ₜ
        ((BigFppfOver.toScheme B S hS).obj U)),
      IsPullback i (yoneda.map j) R.ι a ∧ IsSurjective B S hS i ∧ IsEtale B S hS i ∧
        ∀ x, e x = (BigFppfOver.toScheme B S hS).map j x := by
  obtain ⟨P, j, i, hij⟩ := hR.2.1 a
  have hjClosed : AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map j) := hR.2.2 a i j hij
  have hPsp := isAlgebraicSpace_yoneda B S hS P
  have hUsp := isAlgebraicSpace_yoneda B S hS U
  have hjSurj : Function.Surjective
      (pointsMap B S hS (yoneda.obj P) (yoneda.map j)) := fun x ↦ by
    obtain ⟨z, hz⟩ : ∃ z, pointsMap B S hS R.toFunctor R.ι z =
        pointsMap B S hS (yoneda.obj U) a x :=
      Set.mem_range.mp (by rw [hfull]; exact Set.mem_univ _)
    obtain ⟨w, -, hw⟩ := exists_point_of_isPullback_presheaf B S hS hPsp hR.1 hUsp hF hij z x hz
    exact ⟨w, hw⟩
  have hjSurjScheme : AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map j) :=
    (presheaf_yoneda_map_iff B S hS inferInstance j).mp
      ((surjective_yonedaMap_iff_surjective_pointsMap B S hS j).mpr hjSurj)
  refine ⟨P, j, i,
    ((BigFppfOver.toScheme B S hS).map j).isClosedEmbedding.isEmbedding.toHomeomorphOfSurjective
      hjSurjScheme.surj, hij, fun z ↦ ?_, isEtale_of_isPullback_yoneda B S hS hij.flip hae,
    fun x ↦ Topology.IsEmbedding.toHomeomorphOfSurjective_apply _ _ x⟩
  obtain ⟨y, hy⟩ := ha (pointsMap B S hS R.toFunctor R.ι z)
  obtain ⟨w, hw, -⟩ :=
    exists_point_of_isPullback_presheaf B S hS hPsp hR.1 hUsp hF hij z y hy.symm
  exact ⟨w, hw⟩

/-- A closed subspace whose points are all the points of the ambient algebraic space satisfies
`HasLocallyFiniteIrreducibleComponents` as soon as the space does. -/
theorem hasLocallyFiniteIrreducibleComponents_of_range_pointsMap_eq_univ
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS F)
    (R : Subfunctor F) (hR : IsClosedSubspace B S hS R)
    (hfull : Set.range (pointsMap B S hS R.toFunctor R.ι) = Set.univ) :
    HasLocallyFiniteIrreducibleComponents B S hS R.toFunctor := by
  obtain ⟨U, a, ha, hae, hU⟩ :=
    (exists_surjective_etale_chart_iff_hasLocallyFiniteIrreducibleComponents B S hS hF).mpr hfin
  obtain ⟨P, j, i, e, -, hiSurj, hiEtale, -⟩ :=
    exists_chart_of_range_pointsMap_eq_univ B S hS hF R hR hfull U a ha hae
  refine (exists_surjective_etale_chart_iff_hasLocallyFiniteIrreducibleComponents
    B S hS hR.1).mp ⟨P, i, hiSurj, hiEtale, fun V hV ↦ ?_⟩
  have himage := hU ⟨e '' (V : Set ((BigFppfOver.toScheme B S hS).obj P)),
    e.isOpen_image.mpr V.2⟩ (hV.image e.continuous)
  exact (ncard_irreducibleComponents_le_of_surjective
    ((e.image (V : Set ((BigFppfOver.toScheme B S hS).obj P))).trans
      (Homeomorph.setCongr rfl)).symm
    ((e.image _).trans (Homeomorph.setCongr rfl)).symm.continuous
    ((e.image _).trans (Homeomorph.setCongr rfl)).symm.surjective himage).1

/-- The inclusion of a closed subspace whose points are all the points of the ambient algebraic
space preserves and reflects codimension zero. -/
private theorem localRingDimension_eq_zero_iff_of_range_pointsMap_eq_univ
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (R : Subfunctor F) (hR : IsClosedSubspace B S hS R)
    (hfull : Set.range (pointsMap B S hS R.toFunctor R.ι) = Set.univ)
    (x : points B S hS R.toFunctor) :
    localRingDimension B S hS x = 0 ↔
      localRingDimension B S hS (pointsMap B S hS R.toFunctor R.ι x) = 0 := by
  obtain ⟨U, a, haSurjP, haEtaleP⟩ := hF.exists_atlas
  have ha : IsSurjective B S hS a :=
    (surjective_iff_surjective_pointsMap B S hS F hF U a).mp haSurjP
  have hae : IsEtale B S hS a := (isEtale_iff_presheaf_of_yoneda B S hS a).mpr haEtaleP
  obtain ⟨P, j, i, e, hij, hiSurj, hiEtale, heval⟩ :=
    exists_chart_of_range_pointsMap_eq_univ B S hS hF R hR hfull U a ha hae
  obtain ⟨z, hz⟩ := hiSurj x
  have hjz : pointsToScheme B S hS U
      (pointsMap B S hS (yoneda.obj P) (yoneda.map j) z) =
        (BigFppfOver.toScheme B S hS).map j (pointsToScheme B S hS P z) :=
    pointsToScheme_pointsMap B S hS j z
  have haz : pointsMap B S hS (yoneda.obj U) a
      (pointsMap B S hS (yoneda.obj P) (yoneda.map j) z) =
        pointsMap B S hS R.toFunctor R.ι (pointsMap B S hS (yoneda.obj P) i z) := by
    rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, ← hij.w]
  have hgen : (BigFppfOver.toScheme B S hS).map j (pointsToScheme B S hS P z) ∈
      genericPoints ((BigFppfOver.toScheme B S hS).obj U) ↔
        pointsToScheme B S hS P z ∈
          genericPoints ((BigFppfOver.toScheme B S hS).obj P) := by
    rw [← heval]
    exact e.mem_genericPoints_iff _
  rw [← hz, ← haz]
  refine ⟨fun hdim ↦ ?_, fun hdim ↦ ?_⟩
  · refine localRingDimension_eq_zero_of_mem_genericPoints B S hS hF U a hae _ ?_
    rw [hjz]
    exact hgen.mpr
      (mem_genericPoints_of_localRingDimension_eq_zero B S hS hR.1 P i hiEtale z hdim)
  · refine localRingDimension_eq_zero_of_mem_genericPoints B S hS hR.1 P i hiEtale z ?_
    refine hgen.mp ?_
    rw [← hjz]
    exact mem_genericPoints_of_localRingDimension_eq_zero B S hS hF U a hae _ hdim

/-! ### The normalization and the reduction -/

namespace NormalizationData

variable {B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The normalization morphism of an algebraic space factors uniquely through any closed subspace
whose points are all the points of the space, in particular through the reduction. -/
@[stacks 0BB3 "the factorization through the reduction"]
theorem existsUnique_lift_hom_reduction (D : NormalizationData B S hS F)
    (hF : IsAlgebraicSpace B S hS F) (R : Subfunctor F) (hR : IsClosedSubspace B S hS R)
    (hfull : Set.range (pointsMap B S hS R.toFunctor R.ι) = Set.univ) :
    ∃! g : D.space ⟶ R.toFunctor, g ≫ R.ι = D.hom := by
  have hNred : HasEtaleLocalProperty B S hS D.space fun Y : Scheme.{u} ↦ IsReduced Y := by
    obtain ⟨U, a, hsurj, hetale, hnormal⟩ := D.hasEtaleLocalProperty_isNormal hF
    refine ⟨U, a, hsurj, hetale, ?_⟩
    have : IsNormal ((BigFppfOver.toScheme B S hS).obj U) := hnormal
    infer_instance
  obtain ⟨g, hg⟩ := (exists_lift_closedSubspace_iff_pointsMap_range_subset B S hS hF
    D.isAlgebraicSpace R hR hNred D.hom).mpr (by
      rw [hfull]
      exact Set.subset_univ _)
  exact ⟨g, hg, fun g' hg' ↦ (cancel_mono R.ι).1 (hg'.trans hg.symm)⟩

/-- The factorization of the normalization morphism through the reduction exhibits the
normalization of an algebraic space as the normalization of its reduction: it is carried to any
normalization morphism of the reduction by a unique isomorphism. -/
@[stacks 0BB3 "the normalization of the reduction"]
theorem existsUnique_iso_of_hom_reduction (D : NormalizationData B S hS F)
    (hF : IsAlgebraicSpace B S hS F) (R : Subfunctor F) (hR : IsClosedSubspace B S hS R)
    (hfull : Set.range (pointsMap B S hS R.toFunctor R.ι) = Set.univ)
    (D' : NormalizationData B S hS R.toFunctor) (g : D.space ⟶ R.toFunctor)
    (hg : g ≫ R.ι = D.hom) :
    ∃! e : D.space ≅ D'.space, e.hom ≫ D'.hom = g := by
  have hdim := localRingDimension_eq_zero_iff_of_range_pointsMap_eq_univ
    B S hS hF R hR hfull
  have hν := (D.bijOn_codimensionZeroPoints_hom hF).1
  have hμ := (D'.bijOn_codimensionZeroPoints_hom hR.1).1
  have hNnormal := D.hasEtaleLocalProperty_isNormal hF
  have hMnormal := D'.hasEtaleLocalProperty_isNormal hR.1
  have hgenericG : ∀ z : points B S hS D.space, localRingDimension B S hS z = 0 →
      localRingDimension B S hS (pointsMap B S hS D.space g z) = 0 := by
    intro z hz
    refine (hdim _).2 ?_
    rw [← pointsMap_comp_apply, hg]
    exact hν hz
  have hgenericM : ∀ z : points B S hS D'.space, localRingDimension B S hS z = 0 →
      localRingDimension B S hS (pointsMap B S hS D'.space (D'.hom ≫ R.ι) z) = 0 := by
    intro z hz
    rw [pointsMap_comp_apply]
    exact (hdim _).1 (hμ hz)
  obtain ⟨a, ha, huniq⟩ :=
    existsUnique_lift_hom D' hR.1 D.isAlgebraicSpace hNnormal g hgenericG
  obtain ⟨b, hb, -⟩ :=
    existsUnique_lift_hom D hF D'.isAlgebraicSpace hMnormal (D'.hom ≫ R.ι) hgenericM
  have hab : a ≫ b = 𝟙 D.space := by
    refine ExistsUnique.unique (existsUnique_lift_hom D hF D.isAlgebraicSpace hNnormal D.hom
      fun z hz ↦ hν hz) ?_ (Category.id_comp D.hom)
    calc (a ≫ b) ≫ D.hom = (a ≫ D'.hom) ≫ R.ι := by
          rw [Category.assoc, hb, Category.assoc]
      _ = g ≫ R.ι := by rw [ha]
      _ = D.hom := hg
  have hba : b ≫ a = 𝟙 D'.space := by
    refine ExistsUnique.unique (existsUnique_lift_hom D' hR.1 D'.isAlgebraicSpace hMnormal
      D'.hom fun z hz ↦ hμ hz) ((cancel_mono R.ι).1 ?_) (Category.id_comp D'.hom)
    calc ((b ≫ a) ≫ D'.hom) ≫ R.ι = b ≫ (a ≫ D'.hom) ≫ R.ι := by
          simp only [Category.assoc]
      _ = b ≫ D.hom := by rw [ha, hg]
      _ = D'.hom ≫ R.ι := hb
  exact ⟨⟨a, b, hab, hba⟩, ha, fun e he ↦ Iso.ext (huniq e.hom he)⟩

end NormalizationData

/-! ### The normalization morphism -/

add_to_stacks 0BB2 AlgebraicGeometry.Space.NormalizationData.hom

end AlgebraicGeometry.Space

/-! ### Generic points of a relative normalization of schemes -/

add_to_stacks 0AYG AlgebraicGeometry.exists_genericPoint_irreducibleComponent_mapping_to

end

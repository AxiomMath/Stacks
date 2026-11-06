module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteOverFieldStalks
public import StacksFrontier.AlgebraicGeometry.Properties.DimensionZero
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.NoetherianQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.QuasiCompactMonomorphicPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionLocalRings
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionZeroOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.ChangeOfBaseScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.SpectralPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedCodimensionZero
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Zero
public import StacksFrontier.Topology.Dimension.LocalKrullDim

/-!
# Zero-dimensional algebraic spaces are separated schemes

An algebraic space of dimension zero over a scheme `S` which is quasi-separated — or, a
fortiori, locally of finite type over a field, or Noetherian — is a separated scheme all of
whose quasi-compact opens are affine. This is **Stacks 06LZ** at its conditions (1), (2)
and (3).

## Main definitions

* `IsSeparatedSchemeWithAffineQuasiCompactOpens`: the space is represented by an object of the
  site whose underlying scheme is separated and every quasi-compact open of which is affine.

## Main results

* `isRepresentable_of_isAbsolutelyQuasiSeparated_of_dimension_eq_zero`: such a space is a scheme.
* `isSeparatedSchemeWithAffineQuasiCompactOpens_of_isAbsolutelyQuasiSeparated_of_dimension_eq_zero`
  is **Stacks 06LZ** under its condition (1).
* `isSeparatedSchemeWithAffineQuasiCompactOpens_of_isLocallyOfFiniteType_over_field`
  is **Stacks 06LZ** under its condition (2).
* `isSeparatedSchemeWithAffineQuasiCompactOpens_of_isNoetherian_of_dimension_eq_zero`
  is **Stacks 06LZ** under its condition (3).
* `isDecentSpace_of_isLocallyOfFiniteType_over_field` and
  `isAbsolutelyQuasiSeparated_of_isLocallyOfFiniteType_over_field`: an algebraic space of
  dimension zero locally of finite type over a field is decent and quasi-separated.
* `topologicalKrullDim_chart_le_zero`: an étale scheme chart of a zero-dimensional algebraic space
  has Krull dimension zero.

## References

* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03EA](https://stacks.math.columbia.edu/tag/03EA)
* [Stacks Project, Tag 03I8](https://stacks.math.columbia.edu/tag/03I8)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 03XF](https://stacks.math.columbia.edu/tag/03XF)
* [Stacks Project, Tag 04MU](https://stacks.math.columbia.edu/tag/04MU)
* [Stacks Project, Tag 06LH](https://stacks.math.columbia.edu/tag/06LH)
* [Stacks Project, Tag 06LZ](https://stacks.math.columbia.edu/tag/06LZ)
* [Stacks Project, Tag 06NH](https://stacks.math.columbia.edu/tag/06NH)
* [Stacks Project, Tag 0A4H](https://stacks.math.columbia.edu/tag/0A4H)
* [Stacks Project, Tag 0A4J](https://stacks.math.columbia.edu/tag/0A4J)
* [Stacks Project, Tag 0BAM](https://stacks.math.columbia.edu/tag/0BAM)
* [Stacks Project, Tag 0BAN](https://stacks.math.columbia.edu/tag/0BAN)
* [Stacks Project, Tag 0BB6](https://stacks.math.columbia.edu/tag/0BB6)
* [Stacks Project, Tag 0CKV](https://stacks.math.columbia.edu/tag/0CKV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.OverShriek

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

/-- A presheaf on the big fppf site of `S` is represented by an object of the site whose
underlying scheme is separated and all of whose quasi-compact opens are affine. -/
def IsSeparatedSchemeWithAffineQuasiCompactOpens
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∃ A : BigFppfOver B S hS, Nonempty (yoneda.obj A ≅ X) ∧
    Scheme.IsSeparated ((BigFppfOver.toScheme B S hS).obj A) ∧
    ∀ U : ((BigFppfOver.toScheme B S hS).obj A).Opens,
      IsCompact (U : Set ((BigFppfOver.toScheme B S hS).obj A)) → IsAffineOpen U

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance (priority := high) hasPullback_presheaf_DimensionZeroSeparatedScheme
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Dimension zero at every point -/

/-- **Stacks 0BAN.** An algebraic space of dimension zero has local rings of dimension zero at
every point. -/
theorem localRingDimension_eq_zero_of_dimension_eq_zero (hX : IsAlgebraicSpace B S hS X)
    (hdim : dimension B S hS X hX = 0) (x : points B S hS X) :
    localRingDimension B S hS x = 0 := by
  have hle : ((localRingDimension B S hS x : ℕ∞) : WithBot ℕ∞) ≤ 0 := by
    rw [← hdim, dimension_eq_iSup_localRingDimension B S hS X hX]
    exact le_iSup
      (fun y : points B S hS X => ((localRingDimension B S hS y : ℕ∞) : WithBot ℕ∞)) x
  exact le_antisymm (by exact_mod_cast hle) zero_le

/-! ### Representability -/

/-- A quasi-separated algebraic space of dimension zero over `S` is representable. -/
@[stacks 06LZ "case (1): X is a scheme"]
theorem isRepresentable_of_isAbsolutelyQuasiSeparated_of_dimension_eq_zero
    (hX : IsAlgebraicSpace B S hS X) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (hdim : dimension B S hS X hX = 0) : X.IsRepresentable := by
  obtain ⟨hLopen, hLrep⟩ :=
    isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS hX
  have hsurjTop : Function.Surjective
      (pointsMap B S hS (⊤ : Subfunctor X).toFunctor (Subfunctor.ι (⊤ : Subfunctor X))) := by
    intro pt
    refine ⟨pointsMap B S hS X (inv (Subfunctor.ι (⊤ : Subfunctor X))) pt, ?_⟩
    rw [← pointsMap_comp_apply, IsIso.inv_hom_id, pointsMap_id]
    rfl
  have hLE : openSubspacesOrderIso B S hS X hX ⟨schematicLocus B S hS X, hLopen⟩ =
      openSubspacesOrderIso B S hS X hX ⟨⊤, isOpenSubspace_top hX⟩ := by
    apply TopologicalSpace.Opens.ext
    show Set.range (pointsMap B S hS (schematicLocus B S hS X).toFunctor
        (schematicLocus B S hS X).ι) =
      Set.range (pointsMap B S hS (⊤ : Subfunctor X).toFunctor
        (Subfunctor.ι (⊤ : Subfunctor X)))
    rw [Set.range_eq_univ.mpr hsurjTop]
    exact Set.eq_univ_of_forall fun x =>
      codimensionZero_mem_schematicLocus_of_isZariskiLocallyQuasiSeparated B S hS X hX
        (isZariskiLocallyQuasiSeparatedOver_of_quasiSeparated B S hS hZ X hX hqs) x
        (localRingDimension_eq_zero_of_dimension_eq_zero B S hS hX hdim x)
  have hLtop : schematicLocus B S hS X = ⊤ :=
    congrArg Subtype.val ((openSubspacesOrderIso B S hS X hX).injective hLE)
  rw [hLtop] at hLrep
  exact isRepresentable_of_natIso _ (asIso (Subfunctor.ι (⊤ : Subfunctor X)))

/-! ### The representing scheme is quasi-separated of dimension zero -/

/-- The scheme underlying an object of the site representing a quasi-separated algebraic space
of dimension zero is quasi-separated and of Krull dimension zero. -/
theorem quasiSeparatedSpace_and_topologicalKrullDim_eq_zero_of_yoneda_iso
    (hX : IsAlgebraicSpace B S hS X) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (hdim : dimension B S hS X hX = 0) (A : BigFppfOver B S hS) (e : yoneda.obj A ≅ X) :
    QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj A) ∧
      topologicalKrullDim ((BigFppfOver.toScheme B S hS).obj A) = 0 := by
  have hAalg : IsAlgebraicSpace B S hS (yoneda.obj A) := isAlgebraicSpace_yoneda B S hS A
  set h : points B S hS X ≃ₜ (BigFppfOver.toScheme B S hS).obj A :=
    (pointsHomeomorphOfIso B S hS e).symm.trans (schemePointsHomeomorph B S hS A)
  have hqsp : QuasiSeparatedSpace (points B S hS X) :=
    quasiSeparatedSpace_points_of_isAbsolutelyQuasiSeparated B S hS X hX hqs
  refine ⟨h.symm.isOpenEmbedding.quasiSeparatedSpace, ?_⟩
  have hehom : IsEtale B S hS e.hom :=
    isEtale_of_isOpenImmersion B S hS (MorphismProperty.presheaf_of_isIso _ e.hom)
  have hat : ∀ pt : (BigFppfOver.toScheme B S hS).obj A,
      topologicalKrullDimAt ((BigFppfOver.toScheme B S hS).obj A) pt = 0 := by
    intro pt
    have hle : topologicalKrullDimAt ((BigFppfOver.toScheme B S hS).obj A) pt ≤ 0 := by
      have hpt := topologicalKrullDimAt_eq_of_homeomorph
        (schemePointsHomeomorph B S hS A) ((schemePointsHomeomorph B S hS A).symm pt)
      rw [Homeomorph.apply_symm_apply] at hpt
      rw [← hpt, topologicalKrullDimAt_points_eq_dimensionAtPoint_of_isDecentSpace B S hS hAalg
        (isDecentSpace_yoneda B S hS A),
        dimensionAtPoint_eq_of_isEtale B S hS hAalg hX e.hom hehom, ← hdim]
      exact le_iSup (fun y : points B S hS X => dimensionAtPoint B S hS X hX y) _
    obtain ⟨n, hn⟩ := WithBot.ne_bot_iff_exists.mp (topologicalKrullDimAt_ne_bot pt)
    rw [← hn] at hle ⊢
    obtain rfl : n = 0 := le_antisymm (by exact_mod_cast hle) zero_le
    rfl
  have hne : Nonempty ((BigFppfOver.toScheme B S hS).obj A) :=
    ⟨h (Classical.choice (nonempty_points_of_dimension_eq_zero B S hS hX hdim))⟩
  rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
  simp_rw [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim, hat]
  exact iSup_const

/-! ### Stacks 06LZ at conditions (1) and (3) -/

/-- A quasi-separated algebraic space of dimension zero over `S` is a separated scheme, and every
quasi-compact open of it is affine. -/
@[stacks 06LZ "case (1)"]
theorem
    isSeparatedSchemeWithAffineQuasiCompactOpens_of_isAbsolutelyQuasiSeparated_of_dimension_eq_zero
    (hX : IsAlgebraicSpace B S hS X) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (hdim : dimension B S hS X hX = 0) :
    IsSeparatedSchemeWithAffineQuasiCompactOpens B S hS X := by
  have _ := isRepresentable_of_isAbsolutelyQuasiSeparated_of_dimension_eq_zero B S hS hZ hX hqs
    hdim
  obtain ⟨hqsA, hdimA⟩ := quasiSeparatedSpace_and_topologicalKrullDim_eq_zero_of_yoneda_iso
    B S hS hZ hX hqs hdim X.reprX X.representableBy.toIso
  exact ⟨X.reprX, ⟨X.representableBy.toIso⟩,
    ((separation_tfae_of_topologicalKrullDim_eq_zero
      ((BigFppfOver.toScheme B S hS).obj X.reprX) hdimA).out 1 2).mp hqsA,
    fun U hU => isAffineOpen_of_isCompact_of_topologicalKrullDim_eq_zero
      ((BigFppfOver.toScheme B S hS).obj X.reprX) hdimA U hU⟩

/-- A Noetherian algebraic space of dimension zero over `S` is a separated scheme, and every
quasi-compact open of it is affine. -/
@[stacks 06LZ "case (3)"]
theorem isSeparatedSchemeWithAffineQuasiCompactOpens_of_isNoetherian_of_dimension_eq_zero
    (hX : IsAlgebraicSpace B S hS X) (hnoeth : IsNoetherian B S hS hZ X)
    (hdim : dimension B S hS X hX = 0) :
    IsSeparatedSchemeWithAffineQuasiCompactOpens B S hS X :=
  isSeparatedSchemeWithAffineQuasiCompactOpens_of_isAbsolutelyQuasiSeparated_of_dimension_eq_zero
    B S hS hZ hX hnoeth.2.1 hdim

/-- A Noetherian algebraic space of dimension zero over `S` is representable. -/
@[stacks 06LZ "case (3): X is a scheme"]
theorem isRepresentable_of_isNoetherian_of_dimension_eq_zero
    (hX : IsAlgebraicSpace B S hS X) (hnoeth : IsNoetherian B S hS hZ X)
    (hdim : dimension B S hS X hX = 0) : X.IsRepresentable :=
  isRepresentable_of_isAbsolutelyQuasiSeparated_of_dimension_eq_zero B S hS hZ hX hnoeth.2.1 hdim

/-! ### Charts of a zero-dimensional space locally of finite type over a field -/

/-- An étale scheme chart of an algebraic space of dimension zero has Krull dimension zero. -/
theorem topologicalKrullDim_chart_le_zero (hX : IsAlgebraicSpace B S hS X)
    (hdim : dimension B S hS X hX = 0) (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    topologicalKrullDim ((BigFppfOver.toScheme B S hS).obj U) ≤ 0 := by
  rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
  refine iSup_le fun u ↦ ?_
  set y : points B S hS (yoneda.obj U) := (schemePointsHomeomorph B S hS U).symm u with hy
  have hu : pointsToScheme B S hS U y = u := by
    rw [hy, ← schemePointsHomeomorph_apply, Homeomorph.apply_symm_apply]
  have hall := (hasChartLocalRingDimension_iff_allChartsLocalRingDimension B S hS hX
    (pointsMap B S hS (yoneda.obj U) a y) 0).mp
    ((localRingDimension_eq_iff_hasChartLocalRingDimension B S hS hX _ 0).mp
      (localRingDimension_eq_zero_of_dimension_eq_zero B S hS hX hdim _))
  exact (hu ▸ hall U a (pointsToScheme B S hS U y) ha
    (chartPoint_pointsToScheme B S hS U a y)).le

/-- An étale chart of an algebraic space locally of finite type over a field is itself, as a
scheme, locally of finite type over that field, compatibly with every kernel pair of the chart. -/
private theorem exists_locallyOfFiniteType_of_chart {k : Type u} [Field k]
    {K : BigFppfOver B (⊤_ Scheme.{u}) hZ}
    (eK : (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj K ≅ Spec (.of k))
    {f : viewOverIntegers B S hS hZ X ⟶ yoneda.obj K}
    (hf : IsLocallyOfFiniteType B (⊤_ Scheme.{u}) hZ f)
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    ∃ q : (BigFppfOver.toScheme B S hS).obj U ⟶ Spec (.of k), LocallyOfFiniteType q ∧
      ∀ (R : BigFppfOver B S hS) (s t : R ⟶ U),
        IsPullback (yoneda.map s) (yoneda.map t) a a →
        (BigFppfOver.toScheme B S hS).map s ≫ q =
          (BigFppfOver.toScheme B S hS).map t ≫ q := by
  set g : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
  set b : yoneda.obj ((Over.map g).obj U) ⟶ viewOverIntegers B S hS hZ X :=
    ((relocalizeYonedaIso g).app U).inv ≫ (relocalizePresheafFunctor g).map a with hb
  have _ : MorphismProperty.RespectsIso (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hbEtale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf b := by
    rw [hb]
    exact MorphismProperty.RespectsIso.precomp _ _ _
      (@presheaf_map_relocalize _ _ _ _ g _ _
        (MorphismProperty.RespectsIso.inverseImage _ _) (fun _ hk => hk) _ _ _ ha)
  have _ := isMultiplicative_presheaf_etale B (⊤_ Scheme.{u}) hZ
  have hid : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf (𝟙 (yoneda.obj K)) :=
    MorphismProperty.id_mem _ _
  set c : (Over.map g).obj U ⟶ K := yoneda.preimage (b ≫ f)
  have hcmap : yoneda.map c = b ≫ f := yoneda.map_preimage _
  have hlft : LocallyOfFiniteType ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map c) :=
    hf _ K b (𝟙 _) c hbEtale hid (by rw [Category.comp_id, hcmap])
  refine ⟨(BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map c ≫ eK.hom, inferInstance,
    fun R s t hpb ↦ ?_⟩
  have hreloc := isPullback_relocalize_atlas B (B.obj hS) (B.obj hZ) g hpb
  have hw : (Over.map g).map s ≫ c = (Over.map g).map t ≫ c := by
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_comp, hcmap, ← Category.assoc, ← Category.assoc]
    exact congrArg (fun z ↦ z ≫ f) hreloc.w
  have hmap := congrArg ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map) hw
  rw [Functor.map_comp, Functor.map_comp] at hmap
  exact congrArg (fun z ↦ z ≫ eK.hom) hmap

/-- A quasi-compact scheme locally of finite type over a field and of Krull dimension at most
zero is finite over that field. -/
private theorem isFinite_of_topologicalKrullDim_le_zero (k : Type u) [Field k] {U : Scheme.{u}}
    [CompactSpace U] (q : U ⟶ Spec (.of k)) [LocallyOfFiniteType q]
    (hdim : topologicalKrullDim U ≤ 0) : _root_.AlgebraicGeometry.IsFinite q := by
  rcases isEmpty_or_nonempty U with _ | hne
  · infer_instance
  · have _ : Nonempty (TopologicalSpace.IrreducibleCloseds U) :=
      ⟨⟨closure {Classical.choice hne}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    exact isFinite_of_finiteType_of_dimension_zero k q
      (le_antisymm hdim Order.krullDim_nonneg)

/-- The two projections of a kernel pair of a chart are jointly monic against an arbitrary
scheme. -/
private theorem eq_of_kernelPair_comp_eq {U R : BigFppfOver B S hS} (a : yoneda.obj U ⟶ X)
    (s t : R ⟶ U) (hpb : IsPullback (yoneda.map s) (yoneda.map t) a a) {W : Scheme.{u}}
    (x y : W ⟶ (BigFppfOver.toScheme B S hS).obj R)
    (hs : x ≫ (BigFppfOver.toScheme B S hS).map s =
      y ≫ (BigFppfOver.toScheme B S hS).map s)
    (ht : x ≫ (BigFppfOver.toScheme B S hS).map t =
      y ≫ (BigFppfOver.toScheme B S hS).map t) : x = y := by
  classical
  obtain ⟨r⟩ := (isEquivalenceRelation_of_isPullback B S hS a s t
    hpb).nonempty_equivalenceRelation
  have hstructure (p : R ⟶ U) :
      (BigFppfOver.toScheme B S hS).map p ≫ B.inclusion.map (Over.hom U) =
        B.inclusion.map (Over.hom R) := congrArg B.inclusion.map (Over.w p)
  have hbase : y ≫ B.inclusion.map (Over.hom R) = x ≫ B.inclusion.map (Over.hom R) := by
    rw [← hstructure s, ← Category.assoc, ← hs, Category.assoc, hstructure s]
  let W' : Over ((B.obj hS).obj) := Over.mk (x ≫ B.inclusion.map (Over.hom R))
  let x' : W' ⟶ (Over.post B.inclusion).obj R := Over.homMk x (by simp [W', Over.post])
  let y' : W' ⟶ (Over.post B.inclusion).obj R :=
    Over.homMk y (by simpa [W', Over.post] using hbase)
  have h₁ : x' ≫ (Over.post B.inclusion).map s = y' ≫ (Over.post B.inclusion).map s :=
    Over.OverMorphism.ext (by exact hs)
  have h₂ : x' ≫ (Over.post B.inclusion).map t = y' ≫ (Over.post B.inclusion).map t :=
    Over.OverMorphism.ext (by exact ht)
  exact congrArg Over.Hom.left (r.right_cancellation x' y' h₁ h₂)

/-- The relation of an affine étale chart of a zero-dimensional algebraic space locally of
finite type over a field has finitely many points. -/
private theorem finite_relation_of_chart {k : Type u} [Field k] {U R : BigFppfOver B S hS}
    (a : yoneda.obj U ⟶ X) (s t : R ⟶ U)
    (hpb : IsPullback (yoneda.map s) (yoneda.map t) a a)
    (q : (BigFppfOver.toScheme B S hS).obj U ⟶ Spec (.of k))
    [_root_.AlgebraicGeometry.IsFinite q]
    (hcomm : (BigFppfOver.toScheme B S hS).map s ≫ q =
      (BigFppfOver.toScheme B S hS).map t ≫ q) :
    Finite ((BigFppfOver.toScheme B S hS).obj R) := by
  have _ : _root_.AlgebraicGeometry.IsFinite (pullback.fst q q) := inferInstance
  have _ : _root_.AlgebraicGeometry.IsFinite (pullback.fst q q ≫ q) := inferInstance
  have _ : Finite ↥(pullback q q) := finite_of_isFinite_over_field k (pullback.fst q q ≫ q)
  set m : (BigFppfOver.toScheme B S hS).obj R ⟶ pullback q q :=
    pullback.lift ((BigFppfOver.toScheme B S hS).map s)
      ((BigFppfOver.toScheme B S hS).map t) hcomm with hm
  have _ : Mono m := by
    refine ⟨fun {W} x y hxy ↦ ?_⟩
    refine eq_of_kernelPair_comp_eq B S hS a s t hpb x y ?_ ?_
    · simpa only [hm, Category.assoc, pullback.lift_fst] using
        congrArg (fun z ↦ z ≫ pullback.fst q q) hxy
    · simpa only [hm, Category.assoc, pullback.lift_snd] using
        congrArg (fun z ↦ z ≫ pullback.snd q q) hxy
  exact Finite.of_injective m m.injective

/-! ### Stacks 06LZ at condition (2) -/

/-- **Stacks 06LZ, case (2): the space is decent.** An algebraic space of dimension zero
locally of finite type over a field is decent. -/
theorem isDecentSpace_of_isLocallyOfFiniteType_over_field (hX : IsAlgebraicSpace B S hS X)
    (hdim : dimension B S hS X hX = 0) {k : Type u} [Field k]
    {K : BigFppfOver B (⊤_ Scheme.{u}) hZ}
    (eK : (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj K ≅ Spec (.of k))
    {f : viewOverIntegers B S hS hZ X ⟶ yoneda.obj K}
    (hf : IsLocallyOfFiniteType B (⊤_ Scheme.{u}) hZ f) :
    IsDecentSpace B S hS X := by
  rw [isDecentSpace_iff_hasFiniteChartAndRelationFibersAtEveryPoint B S hS X hX]
  intro x U hU φ hφ
  obtain ⟨q, hq, hrel⟩ := exists_locallyOfFiniteType_of_chart B S hS hZ eK hf U φ hφ
  have hdimU := topologicalKrullDim_chart_le_zero B S hS hX hdim U φ hφ
  have _ : _root_.AlgebraicGeometry.IsFinite q :=
    isFinite_of_topologicalKrullDim_le_zero k q hdimU
  have _ : Finite ((BigFppfOver.toScheme B S hS).obj U) :=
    finite_of_isFinite_over_field k q
  have _ : Finite (points B S hS (yoneda.obj U)) :=
    Finite.of_equiv _ (schemePointsHomeomorph B S hS U).toEquiv.symm
  obtain ⟨R, s, t, hpb⟩ : ∃ (R : BigFppfOver B S hS) (s t : R ⟶ U),
      IsPullback (yoneda.map s) (yoneda.map t) φ φ := by
    have hdiag := hX.diagonal_representable.of_diag φ
    exact ⟨hdiag.pullback φ, yoneda.preimage (hdiag.fst φ), hdiag.snd φ, by
      simpa using hdiag.isPullback φ⟩
  have _ : Finite ((BigFppfOver.toScheme B S hS).obj R) :=
    finite_relation_of_chart B S hS φ s t hpb q (hrel R s t hpb)
  have _ : Finite (points B S hS (yoneda.obj R)) :=
    Finite.of_equiv _ (schemePointsHomeomorph B S hS R).toEquiv.symm
  have _ : Finite (points B S hS (pullback φ φ)) :=
    Finite.of_equiv _ (pointsHomeomorphOfIso B S hS hpb.isoPullback).toEquiv
  exact ⟨Set.toFinite _, Set.toFinite _⟩

/-- **Stacks 06LZ, case (2): the space is quasi-separated.** An algebraic space of dimension
zero locally of finite type over a field is quasi-separated. -/
theorem isAbsolutelyQuasiSeparated_of_isLocallyOfFiniteType_over_field
    (hX : IsAlgebraicSpace B S hS X) (hdim : dimension B S hS X hX = 0) {k : Type u} [Field k]
    {K : BigFppfOver B (⊤_ Scheme.{u}) hZ}
    (eK : (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj K ≅ Spec (.of k))
    {f : viewOverIntegers B S hS hZ X ⟶ yoneda.obj K}
    (hf : IsLocallyOfFiniteType B (⊤_ Scheme.{u}) hZ f) :
    IsAbsolutelyQuasiSeparated B S hS hZ X := by
  refine isAbsolutelyQuasiSeparated_of_isLocallyNoetherian_of_isDecentSpace B S hS hZ X hX
    ?_ (isDecentSpace_of_isLocallyOfFiniteType_over_field B S hS hZ hX hdim eK hf)
  obtain ⟨U, a, hsurj, ha⟩ := hX.exists_atlas
  obtain ⟨q, hq, -⟩ := exists_locallyOfFiniteType_of_chart B S hS hZ eK hf U a ha
  exact ⟨U, a, hsurj, ha, LocallyOfFiniteType.isLocallyNoetherian q⟩

/-- An algebraic space over `S` of dimension zero which is locally of finite type over a field `k`
is a separated scheme, and every quasi-compact open of it is affine. -/
@[stacks 06LZ "case (2)"]
theorem isSeparatedSchemeWithAffineQuasiCompactOpens_of_isLocallyOfFiniteType_over_field
    (hX : IsAlgebraicSpace B S hS X) {k : Type u} [Field k]
    {K : BigFppfOver B (⊤_ Scheme.{u}) hZ}
    (eK : (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj K ≅ Spec (.of k))
    {f : viewOverIntegers B S hS hZ X ⟶ yoneda.obj K}
    (hf : IsLocallyOfFiniteType B (⊤_ Scheme.{u}) hZ f)
    (hdim : dimension B S hS X hX = 0) :
    IsSeparatedSchemeWithAffineQuasiCompactOpens B S hS X :=
  isSeparatedSchemeWithAffineQuasiCompactOpens_of_isAbsolutelyQuasiSeparated_of_dimension_eq_zero
    B S hS hZ hX
    (isAbsolutelyQuasiSeparated_of_isLocallyOfFiniteType_over_field B S hS hZ hX hdim eK hf) hdim

/-- An algebraic space over `S` of dimension zero which is locally of finite type over a field is
representable. -/
@[stacks 06LZ "case (2): X is a scheme"]
theorem isRepresentable_of_isLocallyOfFiniteType_over_field (hX : IsAlgebraicSpace B S hS X)
    {k : Type u} [Field k] {K : BigFppfOver B (⊤_ Scheme.{u}) hZ}
    (eK : (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj K ≅ Spec (.of k))
    {f : viewOverIntegers B S hS hZ X ⟶ yoneda.obj K}
    (hf : IsLocallyOfFiniteType B (⊤_ Scheme.{u}) hZ f)
    (hdim : dimension B S hS X hX = 0) : X.IsRepresentable :=
  isRepresentable_of_isAbsolutelyQuasiSeparated_of_dimension_eq_zero B S hS hZ hX
    (isAbsolutelyQuasiSeparated_of_isLocallyOfFiniteType_over_field B S hS hZ hX hdim eK hf) hdim

end AlgebraicGeometry.Space

end

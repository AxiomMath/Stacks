module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.EtaleAt
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Finiteness
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionZeroPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.EtaleAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty

/-!
# Finiteness of the normalization over an analytically unramified local ring

Let `(A, m)` be a Noetherian local ring which is analytically unramified, let `F` be an
algebraic space locally of finite type over `A`, and assume the structure morphism of `F` is
étale at every point of codimension zero. Then the normalization morphism of any normalization
datum `AlgebraicGeometry.Space.NormalizationData` of `F` is finite. A locally Noetherian algebraic
space has finitely many irreducible components over every quasi-compact open of every étale
scheme chart.

## Main results

* `Space.hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian`: a locally Noetherian
  algebraic space has finitely many irreducible components over every quasi-compact open of every
  étale scheme chart.
* `Space.NormalizationData.isFinite_pullback_snd_of_isAnalyticallyUnramified`: the base change
  of the normalization morphism along a surjective étale scheme chart is a finite morphism of
  algebraic spaces.
* `Space.NormalizationData.isFinite_of_representable_of_isAnalyticallyUnramified`: for a
  representable algebraic space, the normalization morphism is finite.
* `Space.NormalizationData.isFinite_hom_of_isAnalyticallyUnramified`: the normalization morphism of
  any normalization datum of such an algebraic space is finite.

## References

* [Stacks Project, Tag 0BHR](https://stacks.math.columbia.edu/tag/0BHR)
* [Stacks Project, Tag 0GMB](https://stacks.math.columbia.edu/tag/0GMB)
* [Stacks Project, Tag 0BG8](https://stacks.math.columbia.edu/tag/0BG8)
* [Stacks Project, Tag 07U4](https://stacks.math.columbia.edu/tag/07U4)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes locally of finite type over a locally Noetherian scheme whose
restriction to an open neighbourhood of a point is étale is étale at that point. -/
private theorem etaleAt_of_etale_opens_ι_comp {X Y : Scheme.{u}} (k : X ⟶ Y)
    [LocallyOfFiniteType k] [IsLocallyNoetherian Y] (V : X.Opens) {x : X} (hx : x ∈ V)
    (h : Etale (V.ι ≫ k)) : EtaleAt k x := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian k
  let xV : V.toScheme := ⟨x, hx⟩
  have hV : IsEtaleAt (V.ι ≫ k) xV := (etale_iff_forall_isEtaleAt (V.ι ≫ k)).mp h _
  have hstalk : IsIso (V.ι.stalkMap xV) := inferInstance
  rw [← isEtaleAt_iff_etaleAt]
  change ((V.ι ≫ k).stalkMap xV).hom.Flat ∧ ((V.ι ≫ k).stalkMap xV).hom.FormallyUnramified ∧
    ((V.ι ≫ k).stalkMap xV).hom.EssFiniteType at hV
  rw [Scheme.Hom.stalkMap_comp V.ι k xV] at hV
  exact ⟨(@RingHom.RespectsIso.cancel_right_isIso _ RingHom.Flat.respectsIso _ _ _
      (k.stalkMap x) (V.ι.stalkMap xV) hstalk).mp hV.1,
    (@RingHom.RespectsIso.cancel_right_isIso _ RingHom.FormallyUnramified.respectsIso _ _ _
      (k.stalkMap x) (V.ι.stalkMap xV) hstalk).mp hV.2.1,
    (@RingHom.RespectsIso.cancel_right_isIso _ RingHom.EssFiniteType.respectsIso _ _ _
      (k.stalkMap x) (V.ι.stalkMap xV) hstalk).mp hV.2.2⟩

namespace Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A locally Noetherian algebraic space over `S` has finitely many irreducible components over
every quasi-compact open of every étale scheme chart. -/
@[stacks 0GMB]
theorem hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (hN : HasEtaleLocalProperty B S hS F (fun T : Scheme.{u} ↦ IsLocallyNoetherian T)) :
    HasLocallyFiniteIrreducibleComponents B S hS F := fun U f hf V hV ↦
  have _ : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U) :=
    (exists_atlas_iff_forall_etale B S hS F (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) hF).mp
      hN U f ((isEtale_iff_presheaf_of_yoneda B S hS f).mp hf)
  finite_irreducibleComponents_of_isCompact ((BigFppfOver.toScheme B S hS).obj U) V hV

/-- The structure morphism of an étale scheme chart of an algebraic space whose own structure
morphism is étale at every codimension-zero point is étale on an open neighbourhood of every
generic point of the chart. -/
private theorem exists_opens_etale_restrict_of_mem_genericPoints
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {Z : BigFppfOver B S hS} (f : F ⟶ yoneda.obj Z)
    (het : ∀ x : points B S hS F, localRingDimension B S hS x = 0 → IsEtaleAt B S hS f x)
    {U : BigFppfOver B S hS} (g : yoneda.obj U ⟶ F) (hge : IsEtale B S hS g)
    (h : U ⟶ Z) (hh : yoneda.map h = g ≫ f)
    {x : (BigFppfOver.toScheme B S hS).obj U}
    (hx : x ∈ genericPoints ((BigFppfOver.toScheme B S hS).obj U)) :
    ∃ V : ((BigFppfOver.toScheme B S hS).obj U).Opens, x ∈ V ∧
      Etale (V.ι ≫ (BigFppfOver.toScheme B S hS).map h) := by
  classical
  obtain ⟨y, hyx⟩ := surjective_pointsToScheme B S hS U x
  have hchart : ChartPoint B S hS U g x (pointsMap B S hS (yoneda.obj U) g y) := by
    rw [← hyx]
    exact chartPoint_pointsToScheme B S hS U g y
  have hdim : localRingDimension B S hS (pointsMap B S hS (yoneda.obj U) g y) = 0 :=
    (localRingDimension_eq_zero_iff_exists_etale_genericPoint B S hS hF _).mpr
      ⟨U, g, x, hge, hchart, hx⟩
  obtain ⟨A, hA, z, hz, hAf⟩ := het _ hdim
  have hRopen : IsOpen (Set.range (pointsMap B S hS A.toFunctor A.ι)) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS A.ι hA.2
  obtain ⟨V, hxV, hmemV⟩ : ∃ V : ((BigFppfOver.toScheme B S hS).obj U).Opens, x ∈ V ∧
      ∀ p : points B S hS (yoneda.obj U), pointsToScheme B S hS U p ∈ V ↔
        pointsMap B S hS (yoneda.obj U) g p ∈ Set.range (pointsMap B S hS A.toFunctor A.ι) := by
    obtain ⟨Vset, hVopen, hVeq⟩ := (isSchemeOpen_iff_preimage B S hS U _).mp
      ((isOpen_yoneda_iff_isSchemeOpen B S hS U
        (pointsMap B S hS (yoneda.obj U) g ⁻¹' Set.range (pointsMap B S hS A.toFunctor A.ι))).mp
        (hRopen.preimage (continuous_pointsMap B S hS g)))
    have hmem : ∀ p : points B S hS (yoneda.obj U), pointsToScheme B S hS U p ∈ Vset ↔
        pointsMap B S hS (yoneda.obj U) g p ∈
          Set.range (pointsMap B S hS A.toFunctor A.ι) := fun p ↦
      (Set.ext_iff.mp hVeq p).symm
    exact ⟨⟨Vset, hVopen⟩, hyx ▸ (hmem y).mpr ⟨z, hz⟩, hmem⟩
  have hiV : (BigFppfOver.toScheme B S hS).map (openSiteObjectHom B S hS U V) = V.ι :=
    map_openSiteObjectHom B S hS U V
  have hiEtale : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map (openSiteObjectHom B S hS U V)) :=
    (presheaf_yoneda_map_etale_iff B S hS (openSiteObjectHom B S hS U V)).mpr
      (by
        have hopen : Etale V.ι := inferInstance
        rw [hiV]
        exact hopen)
  have hcompEtale : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
        (yoneda.map (openSiteObjectHom B S hS U V) ≫ g) :=
    hge (openSiteObject B S hS U V) (yoneda.map (openSiteObjectHom B S hS U V)) hiEtale
  have hsub : Set.range (pointsMap B S hS (yoneda.obj (openSiteObject B S hS U V))
      (yoneda.map (openSiteObjectHom B S hS U V) ≫ g)) ⊆
        Set.range (pointsMap B S hS A.toFunctor A.ι) := by
    rintro - ⟨w, rfl⟩
    rw [congrFun (pointsMap_comp B S hS (yoneda.obj (openSiteObject B S hS U V))
      (yoneda.map (openSiteObjectHom B S hS U V)) g) w]
    refine (hmemV _).mp ?_
    rw [pointsToScheme_pointsMap B S hS (openSiteObjectHom B S hS U V) w, hiV]
    exact (pointsToScheme B S hS (openSiteObject B S hS U V) w).2
  obtain ⟨gA, hgA⟩ :=
    (factorsThrough_openSubspace_iff_points B S hS hF
      (isAlgebraicSpace_yoneda B S hS (openSiteObject B S hS U V)) A hA
      (yoneda.map (openSiteObjectHom B S hS U V) ≫ g)).mpr hsub
  have hsq : IsPullback (𝟙 (yoneda.obj (openSiteObject B S hS U V))) gA
      (yoneda.map (openSiteObjectHom B S hS U V) ≫ g) A.ι :=
    IsPullback.of_horiz_isIso_mono ⟨by simpa using hgA.symm⟩
  have hfinal : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
        (yoneda.map (openSiteObjectHom B S hS U V ≫ h)) := by
    have hstep := hAf (openSiteObject B S hS U V) gA
      (presheaf_of_isPullback B S hS hsq hcompEtale)
    rwa [show gA ≫ A.ι ≫ f = yoneda.map (openSiteObjectHom B S hS U V ≫ h) by
      rw [← Category.assoc, hgA, yoneda.map_comp, hh, Category.assoc]] at hstep
  refine ⟨V, hxV, ?_⟩
  have hetale :=
    (presheaf_yoneda_map_etale_iff B S hS (openSiteObjectHom B S hS U V ≫ h)).mp hfinal
  rwa [Functor.map_comp, hiV] at hetale

namespace NormalizationData

/-- A morphism of the big fppf site of `S` whose underlying morphism of schemes is finite is
representable with finite represented base changes, as a morphism of the presheaves it
represents. -/
public theorem relative_inverseImage_isFinite_yoneda_map
    {Xν X : BigFppfOver B S hS} (p : Xν ⟶ X)
    (hp : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map p)) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative yoneda (yoneda.map p) := by
  have _ : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    BigFppfOver.isStableUnderBaseChange_inverseImage B S hS
      (@_root_.AlgebraicGeometry.IsFinite.{u})
  exact MorphismProperty.relative_map hp

/-- If the underlying morphism of schemes of `p` is the normalization morphism up to an
isomorphism, and the latter is finite, then `p` is representable with finite represented base
changes. -/
private theorem relative_inverseImage_isFinite_yoneda_map_of_normalization
    {Xν X : BigFppfOver B S hS} (p : Xν ⟶ X)
    {hX : ∀ V : ((BigFppfOver.toScheme B S hS).obj X).Opens,
      IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj X)) →
        (irreducibleComponents V).Finite}
    (e : (BigFppfOver.toScheme B S hS).obj Xν ≅
      Scheme.normalizationScheme ((BigFppfOver.toScheme B S hS).obj X) hX)
    (hp : (BigFppfOver.toScheme B S hS).map p =
      e.hom ≫ Scheme.normalization ((BigFppfOver.toScheme B S hS).obj X) hX)
    (hchart : _root_.AlgebraicGeometry.IsFinite
      (Scheme.normalization ((BigFppfOver.toScheme B S hS).obj X) hX)) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative yoneda (yoneda.map p) :=
  relative_inverseImage_isFinite_yoneda_map p (by rw [hp]; infer_instance)

/-- The normalization of a surjective étale scheme chart of an algebraic space locally of finite
type over an analytically unramified Noetherian local ring, whose structure morphism is étale at
every codimension-zero point, is a finite morphism of schemes. -/
private theorem isFinite_normalization_chart {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (hA : IsAnalyticallyUnramified A)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {Z : BigFppfOver B S hS} (f : F ⟶ yoneda.obj Z)
    (a : (BigFppfOver.toScheme B S hS).obj Z ⟶ Spec (.of A)) [IsIso a]
    (hft : IsLocallyOfFiniteType B S hS f)
    (het : ∀ x : points B S hS F, localRingDimension B S hS x = 0 → IsEtaleAt B S hS f x)
    {U : BigFppfOver B S hS} (g : yoneda.obj U ⟶ F) (hge : IsEtale B S hS g)
    (hU : ∀ V : ((BigFppfOver.toScheme B S hS).obj U).Opens,
      IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj U)) →
        (irreducibleComponents V).Finite) :
    _root_.AlgebraicGeometry.IsFinite
      (Scheme.normalization ((BigFppfOver.toScheme B S hS).obj U) hU) := by
  set h : U ⟶ Z := yoneda.preimage (g ≫ f)
  have hh : yoneda.map h = g ≫ f := yoneda.map_preimage (g ≫ f)
  have hZid : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (𝟙 (yoneda.obj Z)) :=
    (isEtale_iff_presheaf_of_yoneda B S hS (𝟙 (yoneda.obj Z))).mp
      (isEtale_id B S hS (yoneda.obj Z))
  have hlft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map h) :=
    hft U Z g (𝟙 (yoneda.obj Z)) h
      ((isEtale_iff_presheaf_of_yoneda B S hS g).mp hge) hZid (by rw [hh]; simp)
  have _ : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map h ≫ a) := inferInstance
  have hgen : ∀ x : (BigFppfOver.toScheme B S hS).obj U,
      x ∈ genericPoints ((BigFppfOver.toScheme B S hS).obj U) →
        EtaleAt ((BigFppfOver.toScheme B S hS).map h ≫ a) x := by
    intro x hx
    obtain ⟨V, hxV, hVetale⟩ :=
      exists_opens_etale_restrict_of_mem_genericPoints hF f het g hge h hh hx
    refine etaleAt_of_etale_opens_ι_comp _ V hxV ?_
    rw [← Category.assoc]
    have _ : Etale (V.ι ≫ (BigFppfOver.toScheme B S hS).map h) := hVetale
    infer_instance
  exact Scheme.normalization_isFinite_of_etaleAt_genericPoints A
    ((BigFppfOver.toScheme B S hS).map h ≫ a) hA hgen

/-- Let `(A, m)` be an analytically
unramified Noetherian local ring, let `F` be an algebraic space over `S` whose structure morphism
goes to an object of the site with underlying scheme `Spec A`, assume `F` is locally of finite
type over `A` and that its structure morphism is étale at every point of codimension zero, and
let `D` be normalization data for `F`. Then the base change of the normalization morphism along
any surjective étale scheme chart of `F` is a finite morphism of algebraic spaces. -/
theorem isFinite_pullback_snd_of_isAnalyticallyUnramified {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (hA : IsAnalyticallyUnramified A)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {Z : BigFppfOver B S hS} (f : F ⟶ yoneda.obj Z)
    (a : (BigFppfOver.toScheme B S hS).obj Z ⟶ Spec (.of A)) [IsIso a]
    (hft : IsLocallyOfFiniteType B S hS f)
    (het : ∀ x : points B S hS F, localRingDimension B S hS x = 0 → IsEtaleAt B S hS f x)
    (D : NormalizationData B S hS F) {U : BigFppfOver B S hS} (g : yoneda.obj U ⟶ F)
    (hg : IsSurjective B S hS g) (hge : IsEtale B S hS g) :
    IsFinite B S hS (pullback.snd D.hom g) := by
  obtain ⟨hU, Uν, p, q, e, hp, hpb⟩ := D.chart U g hg hge
  have hUspace : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hPull : IsAlgebraicSpace B S hS (pullback D.hom g) :=
    isAlgebraicSpace_pullback B S hS D.hom g D.isAlgebraicSpace hUspace hF
  have hchart := isFinite_normalization_chart hA hF f a hft het g hge hU
  have hrelq : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative yoneda (pullback.snd D.hom g) := by
    refine (((MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative yoneda).cancel_left_of_respectsIso
      hpb.isoPullback.hom (pullback.snd D.hom g)).mp ?_
    rw [hpb.isoPullback_hom_snd]
    exact relative_inverseImage_isFinite_yoneda_map_of_normalization p e hp hchart
  exact (isFinite_iff_representable B S hS (pullback.snd D.hom g) hPull hUspace).2
    ⟨hrelq.1, hrelq⟩

/-- The normalization morphism of the
algebraic space represented by an object `X` of the big fppf site of `S` is finite, provided
`X` is locally of finite type over an analytically unramified Noetherian local ring `A` and its
structure morphism is étale at every point of codimension zero. -/
theorem isFinite_of_representable_of_isAnalyticallyUnramified {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (hA : IsAnalyticallyUnramified A)
    {X Z : BigFppfOver B S hS} (f : yoneda.obj X ⟶ yoneda.obj Z)
    (a : (BigFppfOver.toScheme B S hS).obj Z ⟶ Spec (.of A)) [IsIso a]
    (hft : IsLocallyOfFiniteType B S hS f)
    (het : ∀ x : points B S hS (yoneda.obj X), localRingDimension B S hS x = 0 →
      IsEtaleAt B S hS f x)
    (D : NormalizationData B S hS (yoneda.obj X)) :
    IsFinite B S hS D.hom := by
  obtain ⟨hX, Xν, p, q, e, hp, hpb⟩ := D.chart_self
  have hqiso : IsIso q := hpb.isIso_fst_of_isIso
  have hchart := isFinite_normalization_chart hA (isAlgebraicSpace_yoneda B S hS X) f a hft het
    (𝟙 (yoneda.obj X)) (isEtale_id B S hS (yoneda.obj X)) hX
  have hD : D.hom = inv q ≫ yoneda.map p := by
    rw [← cancel_epi q, IsIso.hom_inv_id_assoc]
    simpa only [Category.comp_id] using hpb.w
  have hrel := (((MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative yoneda).cancel_left_of_respectsIso
      (inv q) (yoneda.map p)).mpr
      (relative_inverseImage_isFinite_yoneda_map_of_normalization p e hp hchart)
  rw [hD]
  exact (isFinite_iff_representable B S hS (inv q ≫ yoneda.map p) D.isAlgebraicSpace
    (isAlgebraicSpace_yoneda B S hS X)).2 ⟨hrel.1, hrel⟩

/-- Let `(A, m)` be an analytically unramified Noetherian local ring and let `F` be an algebraic
space over `S` whose structure morphism goes to an object of the site with underlying scheme
`Spec A`. If `F` is locally of finite type over `A` and its structure morphism is étale at every
point of codimension zero, then the normalization morphism of any normalization datum of `F` is a
finite morphism of algebraic spaces. -/
@[sga "3 XXV 4.2" "more general"]
theorem isFinite_hom_of_isAnalyticallyUnramified {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (hA : IsAnalyticallyUnramified A)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {Z : BigFppfOver B S hS} (f : F ⟶ yoneda.obj Z)
    (a : (BigFppfOver.toScheme B S hS).obj Z ⟶ Spec (.of A)) [IsIso a]
    (hft : IsLocallyOfFiniteType B S hS f)
    (het : ∀ x : points B S hS F, localRingDimension B S hS x = 0 → IsEtaleAt B S hS f x)
    (D : NormalizationData B S hS F) :
    IsFinite B S hS D.hom := by
  obtain ⟨U, g, hgs, hge⟩ := hF.exists_atlas
  have hgs' : IsSurjective B S hS g := isSurjective_of_presheafSurjective B S hS g hgs
  have hge' : IsEtale B S hS g := (isEtale_iff_presheaf_of_yoneda B S hS g).mpr hge
  exact isFinite_of_surjectiveEtaleChart B S hS D.isAlgebraicSpace hF D.hom hgs' hge'
    (isFinite_pullback_snd_of_isAnalyticallyUnramified hA hF f a hft het D g hgs' hge')

end NormalizationData

end Space

end AlgebraicGeometry

end

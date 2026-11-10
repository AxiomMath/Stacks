module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.GenericPointsSize
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Normalization
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationConstruction

/-!
# The normalization of the reduction of an algebraic space

Let `F` be an algebraic space over a scheme `S` of a big fppf site with a normalization
`ν : F^ν ⟶ F` in the sense of `AlgebraicGeometry.Space.NormalizationData`, and let `R` be a
closed subspace of `F` carrying every point of `F` — in particular the reduction.
`StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Normalization` proves that `ν` factors uniquely
through `R`, `AlgebraicGeometry.Space.NormalizationData.existsUnique_lift_hom_reduction`.  This
file proves that the factorization *is* the normalization of `R`: it is normalization data for
`R`, on the same algebraic space.  This is the construction half of Tag 0BB3.

## Main definitions

* `AlgebraicGeometry.Space.NormalizationData.onReduction` is the normalization of the reduction:
  the normalization data for a closed subspace carrying every point of the space, on the same
  algebraic space, with the factorization of the normalization morphism as its normalization
  morphism.

## Main statements

* `AlgebraicGeometry.Space.NormalizationData.chart_of_hom_reduction`: the chart condition for
  the factorization, along every étale scheme chart of the subspace.

## References

* [Stacks Project, Tag 035Q](https://stacks.math.columbia.edu/tag/035Q)
* [Stacks Project, Tag 0BB3](https://stacks.math.columbia.edu/tag/0BB3)
* [Stacks Project, Tag 0BB4](https://stacks.math.columbia.edu/tag/0BB4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- At a point of an étale scheme chart of an algebraic space, the local ring dimension of the
image point is zero exactly when the point of the chart is a generic point. -/
private theorem localRingDimension_pointsMap_eq_zero_iff {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : IsAlgebraicSpace B S hS G) (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ G)
    (ha : IsEtale B S hS a) (z : points B S hS (yoneda.obj U)) :
    localRingDimension B S hS (pointsMap B S hS (yoneda.obj U) a z) = 0 ↔
      pointsToScheme B S hS U z ∈ genericPoints ((BigFppfOver.toScheme B S hS).obj U) :=
  ⟨fun hz => (localRingDimension_eq_zero_iff_all_etale_genericPoints B S hS hG _).mp hz U a _ ha
      (chartPoint_pointsToScheme B S hS U a z),
    fun hz => (localRingDimension_eq_zero_iff_exists_etale_genericPoint B S hS hG _).mpr
      ⟨U, a, _, ha, chartPoint_pointsToScheme B S hS U a z, hz⟩⟩

/-- An algebraic space has a surjective étale atlas by a scheme of the site. -/
private theorem exists_isSurjective_isEtale_of_isAlgebraicSpace
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) :
    ∃ (A : BigFppfOver B S hS) (a : yoneda.obj A ⟶ F),
      IsSurjective B S hS a ∧ IsEtale B S hS a := by
  obtain ⟨A, a, haS, haE⟩ := hF.exists_atlas
  exact ⟨A, a, (surjective_iff_surjective_pointsMap B S hS F hF A a).mp haS,
    (isEtale_iff_presheaf_of_yoneda B S hS a).mpr haE⟩

/-- The base change of a surjective étale chart along a closed subspace carrying every point is a
surjective étale chart of the subspace, whose underlying space is homeomorphic to the chart. -/
private theorem exists_isPullback_ι_homeomorph_of_range_eq_univ
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) {R : Subfunctor F} (hR : IsClosedSubspace B S hS R)
    (hfull : Set.range (pointsMap B S hS R.toFunctor R.ι) = Set.univ) (U : BigFppfOver B S hS)
    (a : yoneda.obj U ⟶ F) (ha : IsSurjective B S hS a) (hae : IsEtale B S hS a) :
    ∃ (P : BigFppfOver B S hS) (j : P ⟶ U) (i : yoneda.obj P ⟶ R.toFunctor)
      (e : ((BigFppfOver.toScheme B S hS).obj P) ≃ₜ ((BigFppfOver.toScheme B S hS).obj U)),
      IsPullback i (yoneda.map j) R.ι a ∧ IsSurjective B S hS i ∧ IsEtale B S hS i ∧
        ∀ x, e x = (BigFppfOver.toScheme B S hS).map j x := by
  obtain ⟨P, j, i, hij⟩ := hR.2.1 a
  have hjClosed : AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map j) := hR.2.2 a i j hij
  -- read the cartesian square in the category of algebraic spaces over `S`
  let Psp : AlgebraicSpaces B S hS := ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩
  let Usp : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  let Rsp : AlgebraicSpaces B S hS := ⟨R.toFunctor, hR.1⟩
  let Fsp : AlgebraicSpaces B S hS := ⟨F, hF⟩
  have hsq : IsPullback (ObjectProperty.homMk i : Psp ⟶ Rsp)
      (ObjectProperty.homMk (yoneda.map j) : Psp ⟶ Usp)
      (ObjectProperty.homMk R.ι : Rsp ⟶ Fsp) (ObjectProperty.homMk a : Usp ⟶ Fsp) := by
    apply IsPullback.of_map_of_faithful (ObjectProperty.ι _)
    simpa using hij
  have hjSurj : Function.Surjective
      (pointsMap B S hS (yoneda.obj P) (yoneda.map j)) := fun x => by
    obtain ⟨z, hz⟩ : ∃ z, pointsMap B S hS R.toFunctor R.ι z =
        pointsMap B S hS (yoneda.obj U) a x :=
      Set.range_eq_univ.mp hfull _
    obtain ⟨w, -, hw⟩ := exists_point_of_isPullback B S hS hsq z x (by simpa using hz)
    exact ⟨w, by simpa using hw⟩
  have hjSurjScheme : AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map j) :=
    (presheaf_yoneda_map_iff B S hS inferInstance j).mp
      ((surjective_yonedaMap_iff_surjective_pointsMap B S hS j).mpr hjSurj)
  refine ⟨P, j, i,
    ((BigFppfOver.toScheme B S hS).map j).isClosedEmbedding.isEmbedding.toHomeomorphOfSurjective
      hjSurjScheme.surj, hij, fun z => ?_, isEtale_of_isPullback B S hS _ _ _ _ hsq.flip hae,
    fun x => Topology.IsEmbedding.toHomeomorphOfSurjective_apply _ _ x⟩
  obtain ⟨y, hy⟩ := ha (pointsMap B S hS R.toFunctor R.ι z)
  obtain ⟨w, hw, -⟩ := exists_point_of_isPullback B S hS hsq z y (by simpa using hy.symm)
  exact ⟨w, by simpa using hw⟩

/-- On a closed subspace carrying every point, a point has local ring dimension zero exactly when
its image in the ambient algebraic space does. -/
private theorem localRingDimension_eq_zero_iff_pointsMap_ι {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) {R : Subfunctor F} (hR : IsClosedSubspace B S hS R)
    (hfull : Set.range (pointsMap B S hS R.toFunctor R.ι) = Set.univ)
    (x : points B S hS R.toFunctor) : localRingDimension B S hS x = 0 ↔
      localRingDimension B S hS (pointsMap B S hS R.toFunctor R.ι x) = 0 := by
  obtain ⟨U, a, ha, hae⟩ := exists_isSurjective_isEtale_of_isAlgebraicSpace B S hS hF
  obtain ⟨P, j, i, e, hij, hiSurj, hiEtale, heval⟩ :=
    exists_isPullback_ι_homeomorph_of_range_eq_univ B S hS hF hR hfull U a ha hae
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
  rw [← hz, ← haz, localRingDimension_pointsMap_eq_zero_iff B S hS hF U a hae, hjz, hgen,
    localRingDimension_pointsMap_eq_zero_iff B S hS hR.1 P i hiEtale]

namespace NormalizationData

variable {B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The factorization of the normalization morphism through a closed subspace carrying every
point preserves local ring dimension zero. -/
private theorem localRingDimension_pointsMap_eq_zero_of_comp_eq (D : NormalizationData B S hS F)
    (hF : IsAlgebraicSpace B S hS F) (R : Subfunctor F) (hR : IsClosedSubspace B S hS R)
    (hfull : Set.range (pointsMap B S hS R.toFunctor R.ι) = Set.univ)
    (g : D.space ⟶ R.toFunctor) (hg : g ≫ R.ι = D.hom) (z : points B S hS D.space)
    (hz : localRingDimension B S hS z = 0) :
    localRingDimension B S hS (pointsMap B S hS D.space g z) = 0 := by
  refine (localRingDimension_eq_zero_iff_pointsMap_ι B S hS hF hR hfull _).2 ?_
  rw [← pointsMap_comp_apply, hg]
  exact (D.bijOn_codimensionZeroPoints_hom hF).1 hz

/-- The base change of the normalization morphism along an étale scheme chart of `F`, read
through a factorization `g` of the normalization morphism over a subfunctor, is a base change
of `g`. -/
private theorem exists_isPullback_of_comp_eq (D : NormalizationData B S hS F)
    (hF : IsAlgebraicSpace B S hS F) (R : Subfunctor F) (g : D.space ⟶ R.toFunctor)
    (hg : g ≫ R.ι = D.hom) {U : BigFppfOver B S hS} (f : yoneda.obj U ⟶ R.toFunctor) :
    ∃ (W : BigFppfOver B S hS) (π : W ⟶ U) (ψ : yoneda.obj W ⟶ D.space),
      IsPullback ψ (yoneda.map π) g f := by
  have hrep : yoneda.relativelyRepresentable D.hom :=
    ((isIntegralHom_iff_representable B S hS D.hom D.isAlgebraicSpace hF).1
      (D.isIntegralHom_hom hF)).1
  obtain ⟨W, π, ψ, hpbF⟩ : ∃ (W : BigFppfOver B S hS) (π : W ⟶ U)
      (ψ : yoneda.obj W ⟶ D.space), IsPullback ψ (yoneda.map π) D.hom (f ≫ R.ι) :=
    ⟨hrep.pullback (f ≫ R.ι), hrep.snd (f ≫ R.ι), hrep.fst (f ≫ R.ι), hrep.isPullback _⟩
  -- the inclusion of `R` is a monomorphism, so the square may be read over `R`
  have hwR : ψ ≫ g = yoneda.map π ≫ f := by
    rw [← cancel_mono R.ι, Category.assoc, hg, Category.assoc]
    exact hpbF.w
  have hbot : IsPullback f (𝟙 (yoneda.obj U)) R.ι (f ≫ R.ι) := by
    have h₁ : IsPullback f (𝟙 (yoneda.obj U)) (𝟙 R.toFunctor) f :=
      IsPullback.of_vert_isIso ⟨by simp⟩
    have h₂ : IsPullback (𝟙 R.toFunctor) (𝟙 R.toFunctor) R.ι R.ι :=
      IsKernelPair.id_of_mono R.ι
    simpa using h₁.paste_horiz h₂
  exact ⟨W, π, ψ, IsPullback.of_bot (by rwa [Category.comp_id, hg]) hwR hbot⟩

/-- A normal object of the site over an étale chart of a closed subspace carrying every point,
mapping generic points to generic points, lifts uniquely through the normalization morphism. -/
private theorem existsUnique_lift_of_isNormal (D : NormalizationData B S hS F)
    (hF : IsAlgebraicSpace B S hS F) (R : Subfunctor F) (hR : IsClosedSubspace B S hS R)
    (hfull : Set.range (pointsMap B S hS R.toFunctor R.ι) = Set.univ)
    {U : BigFppfOver B S hS} (f : yoneda.obj U ⟶ R.toFunctor) (hfe : IsEtale B S hS f)
    {V : BigFppfOver B S hS} (p : V ⟶ U) (hV : IsNormal ((BigFppfOver.toScheme B S hS).obj V))
    (hp : ∀ η ∈ genericPoints ((BigFppfOver.toScheme B S hS).obj V),
      (BigFppfOver.toScheme B S hS).map p η ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj U)) :
    ∃! β : yoneda.obj V ⟶ D.space, β ≫ D.hom = yoneda.map p ≫ f ≫ R.ι := by
  have hgen : ∀ z : points B S hS (yoneda.obj V), localRingDimension B S hS z = 0 →
      localRingDimension B S hS
        (pointsMap B S hS (yoneda.obj V) (yoneda.map p ≫ f ≫ R.ι) z) = 0 := by
    intro z hz
    have hz' := (localRingDimension_pointsMap_eq_zero_iff B S hS
      (isAlgebraicSpace_yoneda B S hS V) V (𝟙 _) (isEtale_id B S hS _) z).mp
        (by simpa only [pointsMap_id, id_eq] using hz)
    rw [pointsMap_comp_apply, pointsMap_comp_apply]
    refine (localRingDimension_eq_zero_iff_pointsMap_ι B S hS hF hR hfull _).1
      ((localRingDimension_pointsMap_eq_zero_iff B S hS hR.1 U f hfe _).mpr ?_)
    rw [pointsToScheme_pointsMap B S hS p z]
    exact hp _ hz'
  exact D.existsUnique_lift_hom hF (isAlgebraicSpace_yoneda B S hS V)
    (hasEtaleLocalProperty_of_representable B S hS (yoneda.obj V)
      (fun X : Scheme.{u} => IsNormal X) V (Iso.refl _) hV) (yoneda.map p ≫ f ≫ R.ι) hgen

/-- The base change of a factorization `g` of the normalization morphism along an étale chart
maps generic points to generic points. -/
private theorem map_mem_genericPoints_of_isPullback (D : NormalizationData B S hS F)
    (hF : IsAlgebraicSpace B S hS F) (R : Subfunctor F) (hR : IsClosedSubspace B S hS R)
    (hfull : Set.range (pointsMap B S hS R.toFunctor R.ι) = Set.univ)
    (g : D.space ⟶ R.toFunctor) (hg : g ≫ R.ι = D.hom) {U : BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ R.toFunctor) (hfe : IsEtale B S hS f) {W : BigFppfOver B S hS}
    (π : W ⟶ U) (ψ : yoneda.obj W ⟶ D.space) (hpb : IsPullback ψ (yoneda.map π) g f)
    (η : (BigFppfOver.toScheme B S hS).obj W)
    (hη : η ∈ genericPoints ((BigFppfOver.toScheme B S hS).obj W)) :
    (BigFppfOver.toScheme B S hS).map π η ∈
      genericPoints ((BigFppfOver.toScheme B S hS).obj U) := by
  have hzs : pointsToScheme B S hS W ((schemePointsHomeomorph B S hS W).symm η) = η :=
    (schemePointsHomeomorph B S hS W).apply_symm_apply η
  have h₁ := (localRingDimension_pointsMap_eq_zero_iff B S hS D.isAlgebraicSpace W ψ
    (isEtale_of_isPullback_yoneda B S hS hpb.flip hfe)
    ((schemePointsHomeomorph B S hS W).symm η)).mpr (by rwa [hzs])
  have h₂ := D.localRingDimension_pointsMap_eq_zero_of_comp_eq hF R hR hfull g hg _ h₁
  rw [← pointsMap_comp_apply, hpb.w, pointsMap_comp_apply] at h₂
  have h₃ := (localRingDimension_pointsMap_eq_zero_iff B S hS hR.1 U f hfe _).mp h₂
  rwa [pointsToScheme_pointsMap B S hS π _, hzs] at h₃

/-- A normal object of the site over an étale chart, mapping generic points to generic points,
factors through the base change of a factorization `g` of the normalization morphism. -/
private theorem exists_hom_comp_eq_of_isNormal (D : NormalizationData B S hS F)
    (hF : IsAlgebraicSpace B S hS F) (R : Subfunctor F) (hR : IsClosedSubspace B S hS R)
    (hfull : Set.range (pointsMap B S hS R.toFunctor R.ι) = Set.univ)
    (g : D.space ⟶ R.toFunctor) (hg : g ≫ R.ι = D.hom) {U : BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ R.toFunctor) (hfe : IsEtale B S hS f) {W : BigFppfOver B S hS}
    (π : W ⟶ U) (ψ : yoneda.obj W ⟶ D.space) (hpb : IsPullback ψ (yoneda.map π) g f)
    {V : BigFppfOver B S hS} (p : V ⟶ U) (hV : IsNormal ((BigFppfOver.toScheme B S hS).obj V))
    (hp : ∀ η ∈ genericPoints ((BigFppfOver.toScheme B S hS).obj V),
      (BigFppfOver.toScheme B S hS).map p η ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj U)) :
    ∃ c : V ⟶ W, c ≫ π = p := by
  obtain ⟨β, hβ, -⟩ := D.existsUnique_lift_of_isNormal hF R hR hfull f hfe p hV hp
  have hβg : β ≫ g = yoneda.map p ≫ f := by
    rw [← cancel_mono R.ι, Category.assoc, hg, Category.assoc]
    exact hβ
  obtain ⟨c, hc⟩ : ∃ c : V ⟶ W, yoneda.map c = hpb.lift β (yoneda.map p) hβg :=
    ⟨yoneda.preimage _, yoneda.map_preimage _⟩
  exact ⟨c, Yoneda.fullyFaithful.map_injective (C := BigFppfOver B S hS)
    (by rw [Functor.map_comp, hc, hpb.lift_snd])⟩

/-- The base change of a factorization `g` of the normalization morphism along an étale chart
has normal underlying scheme. -/
private theorem isNormal_of_isPullback (D : NormalizationData B S hS F)
    (hF : IsAlgebraicSpace B S hS F)
    {R : Subfunctor F} (g : D.space ⟶ R.toFunctor) {U : BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ R.toFunctor) (hfe : IsEtale B S hS f) {W : BigFppfOver B S hS}
    (π : W ⟶ U) (ψ : yoneda.obj W ⟶ D.space) (hpb : IsPullback ψ (yoneda.map π) g f) :
    IsNormal ((BigFppfOver.toScheme B S hS).obj W) :=
  (exists_atlas_iff_forall_etale B S hS D.space (fun X : Scheme.{u} => IsNormal X)
    D.isAlgebraicSpace).1 (D.hasEtaleLocalProperty_isNormal hF) W ψ
    ((isEtale_iff_presheaf_of_yoneda B S hS ψ).1
      (isEtale_of_isPullback_yoneda B S hS hpb.flip hfe))

/-- An endomorphism over `U` of the base change of a factorization `g` of the normalization
morphism along an étale chart `U` is the identity. -/
private theorem eq_id_of_isPullback_of_comp_eq (D : NormalizationData B S hS F)
    (hF : IsAlgebraicSpace B S hS F) (R : Subfunctor F) (hR : IsClosedSubspace B S hS R)
    (hfull : Set.range (pointsMap B S hS R.toFunctor R.ι) = Set.univ)
    (g : D.space ⟶ R.toFunctor) (hg : g ≫ R.ι = D.hom) {U : BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ R.toFunctor) (hfe : IsEtale B S hS f) {W : BigFppfOver B S hS}
    (π : W ⟶ U) (ψ : yoneda.obj W ⟶ D.space) (hpb : IsPullback ψ (yoneda.map π) g f)
    (d : W ⟶ W) (hd : d ≫ π = π) : d = 𝟙 W := by
  have hcomm : ψ ≫ D.hom = yoneda.map π ≫ f ≫ R.ι := by
    rw [← hg, ← Category.assoc, hpb.w, Category.assoc]
  obtain ⟨σ, -, hliftu⟩ := D.existsUnique_lift_of_isNormal hF R hR hfull f hfe π
    (D.isNormal_of_isPullback hF g f hfe π ψ hpb)
    (D.map_mem_genericPoints_of_isPullback hF R hR hfull g hg f hfe π ψ hpb)
  have hdψ : yoneda.map d ≫ ψ = ψ := by
    refine (hliftu _ ?_).trans (hliftu ψ hcomm).symm
    change (yoneda.map d ≫ ψ) ≫ D.hom = yoneda.map π ≫ f ≫ R.ι
    rw [Category.assoc, hcomm, ← Category.assoc, ← Functor.map_comp, hd]
  refine Yoneda.fullyFaithful.map_injective (C := BigFppfOver B S hS) (hpb.hom_ext ?_ ?_)
  · rw [hdψ, CategoryTheory.Functor.map_id, Category.id_comp]
  · rw [← Functor.map_comp, hd, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The underlying scheme of an étale chart of a closed subspace carrying every point of an
algebraic space with a normalization has locally finitely many irreducible components. -/
private theorem finite_irreducibleComponents_of_range_eq_univ (D : NormalizationData B S hS F)
    (hF : IsAlgebraicSpace B S hS F) (R : Subfunctor F) (hR : IsClosedSubspace B S hS R)
    (hfull : Set.range (pointsMap B S hS R.toFunctor R.ι) = Set.univ) {U : BigFppfOver B S hS}
    (f : yoneda.obj U ⟶ R.toFunctor) (hfe : IsEtale B S hS f) :
    ∀ V : ((BigFppfOver.toScheme B S hS).obj U).Opens,
      IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj U)) →
        (irreducibleComponents V).Finite :=
  hasLocallyFiniteIrreducibleComponents_of_range_pointsMap_eq_univ B S hS hF (by
    obtain ⟨A, a, haS, haE⟩ := exists_isSurjective_isEtale_of_isAlgebraicSpace B S hS hF
    exact (exists_surjective_etale_chart_iff_hasLocallyFiniteIrreducibleComponents
      B S hS hF).mp ⟨A, a, haS, haE,
        fun V hV => D.finite_irreducibleComponents_of_chart A a haS haE V hV⟩) R hR hfull U f hfe

/-- A morphism of underlying schemes lying over a morphism of the site underlies a morphism of
the site over the same target. -/
private theorem exists_hom_of_comp_toScheme_map_eq {U V W : BigFppfOver B S hS} (p : V ⟶ U)
    (π : W ⟶ U) (α : (BigFppfOver.toScheme B S hS).obj W ⟶ (BigFppfOver.toScheme B S hS).obj V)
    (hα : α ≫ (BigFppfOver.toScheme B S hS).map p = (BigFppfOver.toScheme B S hS).map π) :
    ∃ a : W ⟶ V, (BigFppfOver.toScheme B S hS).map a = α ∧ a ≫ p = π := by
  have hαcomp : α ≫ B.inclusion.map V.hom = B.inclusion.map W.hom := by
    rw [← toScheme_map_comp_inclusion_hom B S hS p, ← Category.assoc, hα,
      toScheme_map_comp_inclusion_hom B S hS π]
  obtain ⟨a, ha⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS α hαcomp
  exact ⟨a, ha, Functor.map_injective (BigFppfOver.toScheme B S hS)
    (by rw [Functor.map_comp, ha, hα])⟩

/-- **The chart condition for the factorization through a closed subspace carrying every
point.** Let `g` factor the normalization morphism of `F` through such a subspace `R`. Then
along every étale scheme chart `f : U ⟶ R` the morphism `g` base changes to the normalization
of the underlying scheme of `U`.

The base change itself is formed inside the site: the normalization morphism is integral, hence
representable, and its base change along `f ≫ R.ι` is the base change of `g` along `f` because
the inclusion of a subfunctor is a monomorphism, so cancelling it from the Cartesian square
keeps the square Cartesian. Writing `W` for the resulting object of the site, its projection to
the normalization is a surjective étale chart of it, so the underlying scheme of `W` is normal
by Stacks 03E8.

That the projection `W ⟶ U` *is* the normalization of the underlying scheme of `U` is then two
universal properties. Stacks 035Q, part (4), applied to the projection — whose source is normal
and which carries generic points to generic points, because the chart `f` and the chart `ψ` of
the normalization both reflect and preserve codimension zero and the normalization morphism
bijects codimension-zero points by Stacks 0BB4, part (3) — gives a morphism from `W` to the
normalization scheme over `U`. In the other direction the normalization scheme, read in the
site, is a normal algebraic space carrying codimension zero to codimension zero, so Stacks
0BB4, part (4), lifts it over `F` through the normalization morphism, and the Cartesian square
turns that lift into a morphism into `W` over `U`. The two composites are identities by the
uniqueness halves of the same two properties. -/
theorem chart_of_hom_reduction (D : NormalizationData B S hS F)
    (hF : IsAlgebraicSpace B S hS F) (R : Subfunctor F) (hR : IsClosedSubspace B S hS R)
    (hfull : Set.range (pointsMap B S hS R.toFunctor R.ι) = Set.univ)
    (g : D.space ⟶ R.toFunctor) (hg : g ≫ R.ι = D.hom) (U : BigFppfOver B S hS)
    (f : yoneda.obj U ⟶ R.toFunctor) (hfe : IsEtale B S hS f) :
    ∃ (hU : ∀ V : ((BigFppfOver.toScheme B S hS).obj U).Opens,
        IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj U)) →
          (irreducibleComponents V).Finite)
      (Uν : BigFppfOver B S hS) (p : Uν ⟶ U) (q : yoneda.obj Uν ⟶ D.space)
      (e : ((BigFppfOver.toScheme B S hS).obj Uν) ≅
        Scheme.normalizationScheme ((BigFppfOver.toScheme B S hS).obj U) hU),
      (BigFppfOver.toScheme B S hS).map p =
          e.hom ≫ Scheme.normalization ((BigFppfOver.toScheme B S hS).obj U) hU ∧
        IsPullback q (yoneda.map p) g f := by
  -- condition (2) of Stacks 0BB1 for `F`, hence for `R`, hence on the chart `U`
  have hU := D.finite_irreducibleComponents_of_range_eq_univ hF R hR hfull f hfe
  -- the base change of `g` along `f`, formed in the site
  obtain ⟨W, π, ψ, hpb⟩ := D.exists_isPullback_of_comp_eq hF R g hg f
  -- the normalization of the chart, as an object of the site: containment is a bound on
  -- `Scheme.size`, and a normalization is no larger than what it normalizes
  have hcontains : B.Contains
      (Scheme.normalizationScheme ((BigFppfOver.toScheme B S hS).obj U) hU) :=
    (Scheme.size_normalizationScheme_le _ hU).trans_lt U.left.property
  set Uν : BigFppfOver B S hS := BigFppfOver.mk B S hS hcontains
    (Scheme.normalization ((BigFppfOver.toScheme B S hS).obj U) hU ≫
      B.inclusion.map U.hom)
  obtain ⟨p, hp⟩ : ∃ p : Uν ⟶ U, (BigFppfOver.toScheme B S hS).map p =
      Scheme.normalization ((BigFppfOver.toScheme B S hS).obj U) hU :=
    BigFppfOver.exists_hom_of_comp_eq B S hS _ rfl
  have hν : IsNormal (Scheme.normalizationScheme ((BigFppfOver.toScheme B S hS).obj U) hU) :=
    Scheme.isNormal_normalizationScheme _ hU
  -- Stacks 0BB4, part (4): the normalized chart lifts through the normalization morphism
  obtain ⟨c, hcπ⟩ := D.exists_hom_comp_eq_of_isNormal hF R hR hfull g hg f hfe π ψ hpb p hν
    (fun η hη => by rw [hp]; exact Scheme.normalization_mem_genericPoints _ hU hη)
  have := D.isNormal_of_isPullback hF g f hfe π ψ hpb
  -- Stacks 035Q, part (4): the projection of `W` is dominated by the normalization scheme
  obtain ⟨α, hαnorm, -⟩ : ∃! α : (BigFppfOver.toScheme B S hS).obj W ⟶
      (BigFppfOver.toScheme B S hS).obj Uν,
      α ≫ Scheme.normalization ((BigFppfOver.toScheme B S hS).obj U) hU =
        (BigFppfOver.toScheme B S hS).map π := Scheme.existsUnique_lift_normalization hU _
    (fun η => D.map_mem_genericPoints_of_isPullback hF R hR hfull g hg f hfe π ψ hpb η.1 η.2)
  -- read the comparison as a morphism into the underlying scheme of `Uν`
  have hα : α ≫ (BigFppfOver.toScheme B S hS).map p = (BigFppfOver.toScheme B S hS).map π := by
    rwa [hp]
  -- the comparison is a morphism over `U`, hence a morphism of the site
  obtain ⟨a, ha, hap⟩ := exists_hom_of_comp_toScheme_map_eq p π α hα
  -- the first composite is the identity, by uniqueness in Stacks 035Q, part (4)
  have hcα : (BigFppfOver.toScheme B S hS).map c ≫ α =
      𝟙 ((BigFppfOver.toScheme B S hS).obj Uν) := by
    have hcαp : ((BigFppfOver.toScheme B S hS).map c ≫ α) ≫
        (BigFppfOver.toScheme B S hS).map p = (BigFppfOver.toScheme B S hS).map p := by
      rw [Category.assoc, hα, ← Functor.map_comp, hcπ]
    rw [hp] at hcαp
    exact (Scheme.existsUnique_lift_normalization hU
      (Scheme.normalization ((BigFppfOver.toScheme B S hS).obj U) hU)
      (fun η => Scheme.normalization_mem_genericPoints _ hU η.2)).unique hcαp (Category.id_comp _)
  -- the second composite is the identity, by uniqueness in Stacks 0BB4, part (4)
  have hαc : α ≫ (BigFppfOver.toScheme B S hS).map c =
      𝟙 ((BigFppfOver.toScheme B S hS).obj W) := by
    rw [← ha, ← Functor.map_comp, D.eq_id_of_isPullback_of_comp_eq hF R hR hfull g hg f hfe π ψ
      hpb (a ≫ c) (by rw [Category.assoc, hcπ, hap]), CategoryTheory.Functor.map_id]
  exact ⟨hU, W, π, ψ, ⟨α, (BigFppfOver.toScheme B S hS).map c, hαc, hcα⟩, hαnorm.symm, hpb⟩

/-- **Stacks 0BB3, the normalization of the reduction.** The normalization of an algebraic
space *is* the normalization of its reduction: the factorization of the normalization morphism
through any closed subspace whose points are all the points of the space — in particular
through the reduced one — is itself normalization data for that subspace, on the same
algebraic space.

The morphism is the unique factorization of
`AlgebraicGeometry.Space.NormalizationData.existsUnique_lift_hom_reduction`, and the chart
condition is `AlgebraicGeometry.Space.NormalizationData.chart_of_hom_reduction`. Nothing is
assumed about the subspace beyond being closed and carrying every point: no normalization of
it is given, it is constructed. -/
@[stacks 0BB3 "the normalization of the reduction: the factorization is normalization data"]
noncomputable def onReduction (D : NormalizationData B S hS F)
    (hF : IsAlgebraicSpace B S hS F) (R : Subfunctor F) (hR : IsClosedSubspace B S hS R)
    (hfull : Set.range (pointsMap B S hS R.toFunctor R.ι) = Set.univ) :
    NormalizationData B S hS R.toFunctor where
  space := D.space
  isAlgebraicSpace := D.isAlgebraicSpace
  hom := (D.existsUnique_lift_hom_reduction hF R hR hfull).choose
  chart U f _ hfe := chart_of_hom_reduction D hF R hR hfull _
    (D.existsUnique_lift_hom_reduction hF R hR hfull).choose_spec.1 U f hfe

/-- The normalization of the reduction is carried by the same algebraic space as the
normalization of the space. -/
@[simp]
theorem onReduction_space (D : NormalizationData B S hS F) (hF : IsAlgebraicSpace B S hS F)
    (R : Subfunctor F) (hR : IsClosedSubspace B S hS R)
    (hfull : Set.range (pointsMap B S hS R.toFunctor R.ι) = Set.univ) :
    (D.onReduction hF R hR hfull).space = D.space := rfl

/-- The normalization morphism of the reduction is the factorization of the normalization
morphism of the space: it is a morphism over the ambient space. -/
@[simp]
theorem onReduction_hom_comp_ι (D : NormalizationData B S hS F)
    (hF : IsAlgebraicSpace B S hS F) (R : Subfunctor F) (hR : IsClosedSubspace B S hS R)
    (hfull : Set.range (pointsMap B S hS R.toFunctor R.ι) = Set.univ) :
    (D.onReduction hF R hR hfull).hom ≫ R.ι = D.hom :=
  (D.existsUnique_lift_hom_reduction hF R hR hfull).choose_spec.1

end NormalizationData

end AlgebraicGeometry.Space

end
